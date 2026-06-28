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

end LeanMenhir.Gen
