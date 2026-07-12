/-
The grammar cross-check: `tablesMatchGrammar` (leak-2 fix).

The safety/completeness validators certify the *automaton* half of a
`GenTables` blob — they are structurally incapable of certifying its *grammar*
half: a generator bug that drops or mangles a production can still yield a
perfectly `safe` and `complete` automaton **for the wrong grammar**, and every
theorem (soundness, completeness, unambiguity) would then silently speak about
that wrong grammar instead of the `Grammar0` the human wrote and reviews.

`tablesMatchGrammar t g` closes that gap decidably. It compares, production by
production, the grammar data the verified bridges actually consume —

* the jump-table fields `prodLhsFn`/`prodRhsRevFn` (read by
  `automatonOfTablesTyped` / `automatonOfTablesBT` via `prodLhsOf` /
  `prodRhsRevOf`), and
* the plain arrays `prodLhs`/`prodRhsRev` (read by `automatonOfTables`)

— against the human-readable `g.prods` (RHS reversed, as the bridges store it),
plus `numTerm`/`numNonterm`/`numProd`/`startNonterm`, and checks that every
index is **in range**. In-rangeness is what makes the `Fin`-padding conversion
`cl` the identity (see `cl_val_of_le`), so no silent clamping occurs, the dummy
padding production/nonterminal stays unreachable from the start symbol, and the
`ParseTree`s the top-level theorems quantify over are exactly the derivations of
`g`.

Each example discharges `tablesMatchGrammar tables grammar = true` by
`decide`/`rfl`/`native_decide` next to its validator certificates; the
`TablesMatchGrammar` structure and the faithfulness lemmas below turn that
boolean into quotable propositions about the built automaton.

LGPL-3.0-or-later (derivative of coq-menhirlib).
-/
import LeanMenhir.Generator.LR1

namespace LeanMenhir
namespace Gen

/-- A generator symbol lies within the grammar's alphabets. -/
def gsymInRange (g : Grammar0) : GSym → Bool
  | .term i => decide (i < g.numTerm)
  | .nonterm i => decide (i < g.numNonterm)

/-- The decidable grammar cross-check (see the module docstring). -/
def tablesMatchGrammar (t : GenTables) (g : Grammar0) : Bool :=
  decide (t.numTerm = g.numTerm) &&
  decide (t.numNonterm = g.numNonterm) &&
  decide (t.numProd = g.prods.size) &&
  decide (t.startNonterm = g.start) &&
  decide (g.start < g.numNonterm) &&
  (List.range g.prods.size).all fun i =>
    decide (t.prodLhsFn i = (g.prods.getD i (0, #[])).1) &&
    decide (t.prodLhs.getD i 0 = (g.prods.getD i (0, #[])).1) &&
    decide ((g.prods.getD i (0, #[])).1 < g.numNonterm) &&
    decide ((t.prodRhsRevFn i).toList = (g.prods.getD i (0, #[])).2.toList.reverse) &&
    decide ((t.prodRhsRev.getD i #[]).toList = (g.prods.getD i (0, #[])).2.toList.reverse) &&
    (g.prods.getD i (0, #[])).2.toList.all (gsymInRange g)

/-- The propositional content of `tablesMatchGrammar` (see
`tablesMatchGrammar_spec`). -/
structure TablesMatchGrammar (t : GenTables) (g : Grammar0) : Prop where
  numTerm_eq : t.numTerm = g.numTerm
  numNonterm_eq : t.numNonterm = g.numNonterm
  numProd_eq : t.numProd = g.prods.size
  start_eq : t.startNonterm = g.start
  start_lt : g.start < g.numNonterm
  /-- The jump-table lhs (consumed by the typed/BT bridges) is the grammar's. -/
  lhsFn_eq : ∀ i, i < g.prods.size → t.prodLhsFn i = (g.prods.getD i (0, #[])).1
  /-- The array lhs (consumed by the array bridge) is the grammar's. -/
  lhsArr_eq : ∀ i, i < g.prods.size → t.prodLhs.getD i 0 = (g.prods.getD i (0, #[])).1
  lhs_lt : ∀ i, i < g.prods.size → (g.prods.getD i (0, #[])).1 < g.numNonterm
  /-- The jump-table RHS (consumed by the typed/BT bridges) is the grammar's,
  reversed. -/
  rhsFn_eq : ∀ i, i < g.prods.size →
    (t.prodRhsRevFn i).toList = (g.prods.getD i (0, #[])).2.toList.reverse
  /-- The array RHS (consumed by the array bridge) is the grammar's, reversed. -/
  rhsArr_eq : ∀ i, i < g.prods.size →
    (t.prodRhsRev.getD i #[]).toList = (g.prods.getD i (0, #[])).2.toList.reverse
  rhs_inRange : ∀ i, i < g.prods.size →
    ∀ s ∈ (g.prods.getD i (0, #[])).2.toList, gsymInRange g s = true

theorem tablesMatchGrammar_spec {t : GenTables} {g : Grammar0}
    (h : tablesMatchGrammar t g = true) : TablesMatchGrammar t g := by
  unfold tablesMatchGrammar at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact {
    numTerm_eq := h1
    numNonterm_eq := h2
    numProd_eq := h3
    start_eq := h4
    start_lt := h5
    lhsFn_eq := fun i hi => (h6 i hi).1.1.1.1.1
    lhsArr_eq := fun i hi => (h6 i hi).1.1.1.1.2
    lhs_lt := fun i hi => (h6 i hi).1.1.1.2
    rhsFn_eq := fun i hi => (h6 i hi).1.1.2
    rhsArr_eq := fun i hi => (h6 i hi).1.2
    rhs_inRange := fun i hi => (h6 i hi).2 }

/-! ### Faithfulness: under the cross-check, no clamping occurs -/

/-- On in-range indices, the `Fin`-padding conversion `cl` is the identity. -/
theorem cl_val_of_le {n i : Nat} (h : i ≤ n) : (cl n i).val = i := by
  simp only [cl]
  omega

/-- On in-range terminal symbols, `gsymToSymbol` performs no clamping. -/
theorem gsymToSymbol_term (t : GenTables) {i : Nat} (h : i ≤ t.numTerm) :
    gsymToSymbol t (.term i) = .T ⟨i, Nat.lt_succ_of_le h⟩ := by
  simp only [gsymToSymbol]
  exact congrArg Symbol.T (Fin.ext (cl_val_of_le h))

/-- On in-range nonterminal symbols, `gsymToSymbol` performs no clamping. -/
theorem gsymToSymbol_nonterm (t : GenTables) {i : Nat} (h : i ≤ t.numNonterm) :
    gsymToSymbol t (.nonterm i) = .NT ⟨i, Nat.lt_succ_of_le h⟩ := by
  simp only [gsymToSymbol]
  exact congrArg Symbol.NT (Fin.ext (cl_val_of_le h))

/-- **Faithfulness of the lhs** (typed/BT bridges): under the cross-check, the
automaton's `prod_lhs` of a real production `p` — `prodLhsOf t p`, as consumed
by `automatonOfTablesTyped`/`automatonOfTablesBT` — is *exactly* the `Grammar0`
lhs, with no clamping. -/
theorem TablesMatchGrammar.prodLhsOf_val {t : GenTables} {g : Grammar0}
    (h : TablesMatchGrammar t g) (p : Fin (t.numProd + 1)) (hp : p.val < t.numProd) :
    (prodLhsOf t p).val = (g.prods.getD p.val (0, #[])).1 := by
  have hp' : p.val < g.prods.size := h.numProd_eq ▸ hp
  unfold prodLhsOf
  rw [if_pos hp, h.lhsFn_eq p.val hp']
  exact cl_val_of_le (by rw [h.numNonterm_eq]; exact Nat.le_of_lt (h.lhs_lt p.val hp'))

/-- **Faithfulness of the RHS** (typed/BT bridges): under the cross-check, the
automaton's `prod_rhs_rev` of a real production `p` — `prodRhsRevOf t p`, as
consumed by `automatonOfTablesTyped`/`automatonOfTablesBT` — is *exactly* the
reversed `Grammar0` RHS (mapped into automaton symbols; by `rhs_inRange` and
`gsymToSymbol_term`/`gsymToSymbol_nonterm` that map performs no clamping). -/
theorem TablesMatchGrammar.prodRhsRevOf_eq {t : GenTables} {g : Grammar0}
    (h : TablesMatchGrammar t g) (p : Fin (t.numProd + 1)) (hp : p.val < t.numProd) :
    prodRhsRevOf t p =
      ((g.prods.getD p.val (0, #[])).2.toList.reverse).map (gsymToSymbol t) := by
  unfold prodRhsRevOf
  rw [h.rhsFn_eq p.val (h.numProd_eq ▸ hp)]

/-- **Faithfulness of the start symbol**: under the cross-check, the automaton's
`start_nt` — every bridge defines it as `cl t.numNonterm t.startNonterm` — is
*exactly* the `Grammar0` start nonterminal. In particular it is a *real*
nonterminal, not the dummy padding index `numNonterm`. -/
theorem TablesMatchGrammar.startNt_val {t : GenTables} {g : Grammar0}
    (h : TablesMatchGrammar t g) :
    (cl t.numNonterm t.startNonterm).val = g.start := by
  rw [h.start_eq]
  exact cl_val_of_le (by rw [h.numNonterm_eq]; exact Nat.le_of_lt h.start_lt)

/-- **Faithfulness of the lhs** (array bridge): the analogue of `prodLhsOf_val`
for `automatonOfTables`, which reads the plain `prodLhs` array. -/
theorem TablesMatchGrammar.prodLhsArr_val {t : GenTables} {g : Grammar0}
    (h : TablesMatchGrammar t g) (p : Fin (t.numProd + 1)) (hp : p.val < t.numProd) :
    (if p.val < t.numProd then cl t.numNonterm (t.prodLhs.getD p.val 0)
     else cl t.numNonterm t.numNonterm).val = (g.prods.getD p.val (0, #[])).1 := by
  have hp' : p.val < g.prods.size := h.numProd_eq ▸ hp
  rw [if_pos hp, h.lhsArr_eq p.val hp']
  exact cl_val_of_le (by rw [h.numNonterm_eq]; exact Nat.le_of_lt (h.lhs_lt p.val hp'))

/-- **Faithfulness of the RHS** (array bridge): the analogue of `prodRhsRevOf_eq`
for `automatonOfTables`, which reads the plain `prodRhsRev` array. -/
theorem TablesMatchGrammar.prodRhsRevArr_eq {t : GenTables} {g : Grammar0}
    (h : TablesMatchGrammar t g) (p : Fin (t.numProd + 1)) (hp : p.val < t.numProd) :
    (t.prodRhsRev.getD p.val #[]).toList.map (gsymToSymbol t) =
      ((g.prods.getD p.val (0, #[])).2.toList.reverse).map (gsymToSymbol t) := by
  rw [h.rhsArr_eq p.val (h.numProd_eq ▸ hp)]

end Gen
end LeanMenhir
