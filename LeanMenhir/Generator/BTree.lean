/-
A balanced binary search tree over `Nat` keys, used as *immutable data* (a shared
literal) for kernel-reducible `O(log n)` table lookups.

Why this exists: the verified `safeValidator`/`completeValidator` index the generated
tables once per state/terminal/nonterminal. Reducing those lookups in the kernel
(needed for a kernel-checked `by rfl` certificate, as opposed to `native_decide`)
must be both fast and bounded-memory. The two obvious encodings fail:

* `Array.getD` reduces fine but is `O(index)` (the kernel walks the backing `List`),
  so a 480-state automaton's validators take many minutes.
* a "jump table" encoded as a nested-`cond` *function* (`fun n => cond … cond …`)
  reduces in `O(log n)`, but each application **beta-substitutes the key into the
  entire function body** — an `O(tree size)` copy per call — which blows memory up
  (observed: 68 GB on L0).

A `BTree` is *data*: `BTree.find` descends it by matching constructors and recursing
into **shared subterms**, so a lookup is `O(log n)` reductions with no substitution
of the key into a large body — fast *and* bounded memory.

NB: the `decide` *tactic* refuses to reduce custom recursive functions like
`BTree.find` (it reports "stuck"). Certificates over `BTree`-backed tables must be
discharged with `by rfl` (kernel definitional equality), which does reduce it. The
result is still a fully kernel-checked proof (axioms `{propext, Quot.sound}`), with
no compiler-trust (`Lean.ofReduceBool`) axiom.

LGPL-3.0-or-later (derivative of coq-menhirlib).
-/

namespace LeanMenhir.Gen

universe u

/-- A binary search tree keyed by `Nat`. Built balanced by `build_tables%`. -/
inductive BTree (α : Type u) where
  | leaf
  | node (key : Nat) (val : α) (lo hi : BTree α)

instance {α : Type u} : Inhabited (BTree α) := ⟨.leaf⟩

/-- `O(log n)` lookup. Structurally recursive on the tree (so it reduces under the
kernel / `rfl`), descending into shared subterms — no large beta-substitution. -/
def BTree.find {α : Type u} (dflt : α) (q : Nat) : BTree α → α
  | .leaf => dflt
  | .node k v lo hi => if q < k then lo.find dflt q else if q == k then v else hi.find dflt q

/-- In-order list of `(key, value)` entries. Used by the validators to iterate the
*defined* table entries (a sparse `O(entries)` traversal) instead of probing every
possible key (a dense `O(domain)` scan of `BTree.find`s). -/
def BTree.toList {α : Type u} : BTree α → List (Nat × α)
  | .leaf => []
  | .node k v lo hi => lo.toList ++ (k, v) :: hi.toList

/-- If `find` returns a non-default value, that `(key, value)` is in `toList`. This
is the soundness bridge for sparse iteration: every defined entry (one that `find`
distinguishes from the default) is enumerated by `toList`. Needs no search-tree
invariant — `find` only returns a node's value when the query equals that node's key. -/
theorem BTree.find_mem_toList {α : Type u} (dflt : α) (q : Nat) :
    ∀ (t : BTree α), BTree.find dflt q t ≠ dflt → (q, BTree.find dflt q t) ∈ t.toList := by
  intro t
  induction t with
  | leaf => intro h; exact absurd rfl h
  | node k v lo hi ihlo ihhi =>
    intro h
    simp only [BTree.find] at h ⊢
    by_cases h1 : q < k
    · simp only [h1, if_true] at h ⊢
      exact List.mem_append_left _ (ihlo h)
    · simp only [h1, if_false] at h ⊢
      by_cases h2 : q == k
      · have hqk : q = k := eq_of_beq h2
        subst hqk
        simp only [h2, if_true] at h ⊢
        exact List.mem_append_right _ (by simp)
      · simp only [h2] at h ⊢
        exact List.mem_append_right _ (List.mem_cons_of_mem _ (ihhi h))

end LeanMenhir.Gen
