/-
`Grammar0` — the human-written grammar entrypoint — and its **definitional**
interpretation as a verified `Grammar` (the D9 data-flow reversal).

Before this file, the grammar half of the verified `Grammar` was reconstructed
from the *untrusted generated tables* (`GenTables`), and a decidable
cross-check (`tablesMatchGrammar`, leak-2) tied it back to the `Grammar0` a
human reviews. Now the flow is reversed:

* `Grammar0.toGrammar` / `Grammar0.toGrammarTyped` build the `Grammar` **as a
  definitional function of `g0`** (plus the user's semantic types/actions) — so
  every theorem's grammar visibly *is* the reviewed `Grammar0`;
* the tables contribute only the **automaton half**
  (`automatonOfG0Tables` / `automatonOfG0TablesTyped`): all *types* come from
  `g0` (via `GenTables.withDims`), all table *content* is untrusted — a
  mangled blob can only fail the `isSafe`/`isComplete` validators, never
  smuggle in a different grammar;
* `ProdLookup g0` carries kernel-fast production lookups **with intrinsic
  agreement proofs** against `g0.prods`: `ProdLookup.default` (naive array
  reads, proofs by `rfl` — fine for small grammars) or `ProdLookup.ofTables`
  (the `build_tables%` jump trees, agreement certified by kernel
  `rfl`/`decide` — the `O(log n)` kernel-reduction path for large grammars);
* `Grammar0.wf` is the residual decidable well-formedness check (indices in
  range, start in range) that makes the `Fin`-padding `cl` provably the
  identity on all real data (`prodLhs0_val`, `prodRhsRev0_eq`).

LGPL-3.0-or-later (derivative of coq-menhirlib).
-/
import LeanMenhir.Generator.Tables

namespace LeanMenhir
namespace Gen

/-- A grammar description for the generator. Terminals `0..numTerm-1`,
nonterminals `0..numNonterm-1`. `start` must have exactly the productions whose
RHS ends in `eof` (checkable via `isEofAnchored` on the derived grammar). -/
structure Grammar0 where
  numTerm : Nat
  numNonterm : Nat
  /-- Each production: `(lhs, rhs)` with `rhs` in forward order. -/
  prods : Array (Nat × Array GSym)
  start : Nat
  eof : Nat
deriving Inhabited

namespace Grammar0

/-- Decidable well-formedness: the start symbol and every production index lie
within the declared alphabets. Under `wf`, the `Fin`-padding `cl` in the derived
grammar is the identity on all real data and the dummy padding symbols are
unreachable. -/
def wf (g0 : Grammar0) : Bool :=
  decide (g0.start < g0.numNonterm) &&
  g0.prods.all fun p =>
    decide (p.1 < g0.numNonterm) &&
    p.2.all fun s =>
      match s with
      | .term i => decide (i < g0.numTerm)
      | .nonterm i => decide (i < g0.numNonterm)

end Grammar0

/-! ### Production lookups with intrinsic faithfulness -/

/-- Boolean agreement of candidate lookup functions with `g0.prods` (the RHS in
*reversed* order, as the machine stores it). -/
def prodLookupAgrees (g0 : Grammar0) (lhsFn : Nat → Nat) (rhsRevFn : Nat → Array GSym) : Bool :=
  (List.range g0.prods.size).all fun i =>
    lhsFn i == (g0.prods.getD i (0, #[])).1 &&
    (rhsRevFn i).toList == (g0.prods.getD i (0, #[])).2.toList.reverse

/-- Kernel-fast production lookups **with intrinsic agreement proofs** against
`g0.prods`. The derived grammar reads productions only through a `ProdLookup`,
so faithfulness to the human-written `Grammar0` holds *by construction* — the
lookup's provenance (naive reads, `build_tables%` jump trees, …) is irrelevant. -/
structure ProdLookup (g0 : Grammar0) where
  /-- lhs of production `i`. -/
  lhsFn : Nat → Nat
  /-- *Reversed* RHS of production `i`. -/
  rhsRevFn : Nat → Array GSym
  lhs_eq : ∀ i, i < g0.prods.size → lhsFn i = (g0.prods.getD i (0, #[])).1
  rhsRev_eq : ∀ i, i < g0.prods.size →
    (rhsRevFn i).toList = (g0.prods.getD i (0, #[])).2.toList.reverse

/-- The naive lookup: direct array reads (`O(i)` kernel reduction per query —
fine for small grammars); agreement is definitional. -/
@[reducible] def ProdLookup.default (g0 : Grammar0) : ProdLookup g0 where
  lhsFn := fun i => (g0.prods.getD i (0, #[])).1
  -- `Array.mk (… .toList.reverse)`, not `Array.reverse`: the latter's loop does
  -- not kernel-reduce, and the validators reduce these lookups under `decide`.
  rhsRevFn := fun i => ⟨(g0.prods.getD i (0, #[])).2.toList.reverse⟩
  lhs_eq := fun _ _ => rfl
  rhsRev_eq := fun _ _ => rfl

/-- Package candidate lookup functions with a decided agreement certificate. -/
@[reducible] def ProdLookup.ofFns (g0 : Grammar0) (lhsFn : Nat → Nat) (rhsRevFn : Nat → Array GSym)
    (h : prodLookupAgrees g0 lhsFn rhsRevFn = true) : ProdLookup g0 where
  lhsFn := lhsFn
  rhsRevFn := rhsRevFn
  lhs_eq := by
    intro i hi
    rw [prodLookupAgrees, List.all_eq_true] at h
    have := h i (List.mem_range.2 hi)
    rw [Bool.and_eq_true] at this
    exact eq_of_beq this.1
  rhsRev_eq := by
    intro i hi
    rw [prodLookupAgrees, List.all_eq_true] at h
    have := h i (List.mem_range.2 hi)
    rw [Bool.and_eq_true] at this
    exact eq_of_beq this.2

/-- The `build_tables%` jump trees as a `ProdLookup`: `O(log n)` kernel reduction
per query; agreement with `g0.prods` certified by kernel `rfl`/`decide`. -/
@[reducible] def ProdLookup.ofTables (g0 : Grammar0) (t : GenTables)
    (h : prodLookupAgrees g0 t.prodLhsFn t.prodRhsRevFn = true) : ProdLookup g0 :=
  .ofFns g0 t.prodLhsFn t.prodRhsRevFn h

/-! ### The definitional grammar -/

namespace Grammar0

variable (g0 : Grammar0) (lk : ProdLookup g0)

/-- lhs of production `p` in the derived grammar (the dummy padding production
`prods.size` maps to the dummy nonterminal `numNonterm`, which never occurs in a
real RHS under `wf`). -/
def prodLhs0 (p : Fin (g0.prods.size + 1)) : Fin (g0.numNonterm + 1) :=
  if p.val < g0.prods.size then cl g0.numNonterm (lk.lhsFn p.val)
  else cl g0.numNonterm g0.numNonterm

/-- Reversed RHS of production `p` in the derived grammar. -/
def prodRhsRev0 (p : Fin (g0.prods.size + 1)) :
    List (Symbol (Fin (g0.numTerm + 1)) (Fin (g0.numNonterm + 1))) :=
  (lk.rhsRevFn p.val).toList.map (gsymToSymbolD g0.numTerm g0.numNonterm)

/-- **Faithfulness of the lhs, by construction**: on real productions the derived
lhs is exactly the `Grammar0` lhs (no clamping, given in-rangeness — e.g. from
`wf`). -/
theorem prodLhs0_val (p : Fin (g0.prods.size + 1)) (hp : p.val < g0.prods.size)
    (hlt : (g0.prods.getD p.val (0, #[])).1 ≤ g0.numNonterm) :
    (prodLhs0 g0 lk p).val = (g0.prods.getD p.val (0, #[])).1 := by
  unfold prodLhs0
  rw [if_pos hp, lk.lhs_eq p.val hp]
  exact cl_val_of_le hlt

/-- **Faithfulness of the RHS, by construction**: on real productions the derived
reversed RHS is exactly the reversed `Grammar0` RHS. -/
theorem prodRhsRev0_eq (p : Fin (g0.prods.size + 1)) (hp : p.val < g0.prods.size) :
    prodRhsRev0 g0 lk p =
      ((g0.prods.getD p.val (0, #[])).2.toList.reverse).map
        (gsymToSymbolD g0.numTerm g0.numNonterm) := by
  unfold prodRhsRev0
  rw [lk.rhsRev_eq p.val hp]

/-- The heterogeneous semantic-value type of a symbol of the derived grammar. -/
def symType0 (ntType : Fin (g0.numNonterm + 1) → Type)
    (termType : Fin (g0.numTerm + 1) → Type) :
    Symbol (Fin (g0.numTerm + 1)) (Fin (g0.numNonterm + 1)) → Type
  | .T t => termType t
  | .NT n => ntType n

/-- The **monomorphic** verified grammar, as a definitional function of the
human-written `g0` (and the user's semantic value type/actions). This — not the
generated tables — is the grammar every theorem quantifies over. -/
@[reducible]
def toGrammar (Val : Type) (actions : Nat → List Val → Val) : Grammar where
  Terminal := Fin (g0.numTerm + 1)
  Nonterminal := Fin (g0.numNonterm + 1)
  terminalAlphabet := inferInstance
  nonterminalAlphabet := inferInstance
  symbol_semantic_type := fun _ => Val
  Production := Fin (g0.prods.size + 1)
  productionAlphabet := inferInstance
  prod_lhs := prodLhs0 g0 lk
  prod_rhs_rev := prodRhsRev0 g0 lk
  prod_action := fun p => collectArrows (actions p.val) (prodRhsRev0 g0 lk p) []
  Token := Fin (g0.numTerm + 1) × Val
  token_term := fun t => t.1
  token_sem := fun t => t.2

/-- The **typed** verified grammar (heterogeneous semantic values, tokens carry
caller-chosen `Info`), as a definitional function of `g0`. -/
@[reducible]
def toGrammarTyped (ntType : Fin (g0.numNonterm + 1) → Type)
    (termType : Fin (g0.numTerm + 1) → Type) (Info : Type)
    (actions : (p : Fin (g0.prods.size + 1)) →
      arrowsRight (symType0 g0 ntType termType (.NT (prodLhs0 g0 lk p)))
                  ((prodRhsRev0 g0 lk p).map (symType0 g0 ntType termType))) : Grammar where
  Terminal := Fin (g0.numTerm + 1)
  Nonterminal := Fin (g0.numNonterm + 1)
  terminalAlphabet := inferInstance
  nonterminalAlphabet := inferInstance
  symbol_semantic_type := symType0 g0 ntType termType
  Production := Fin (g0.prods.size + 1)
  productionAlphabet := inferInstance
  prod_lhs := prodLhs0 g0 lk
  prod_rhs_rev := prodRhsRev0 g0 lk
  prod_action := actions
  Token := Info × ((t : Fin (g0.numTerm + 1)) × termType t)
  token_term := fun x => x.2.1
  token_sem := fun x => x.2.2

end Grammar0

/-! ### The automaton half (tables contribute content, `g0` contributes types) -/

/-- The automaton half of the **array-backed monomorphic** bridge, typed against
the `Grammar0`-derived grammar. `t` supplies only untrusted content: every type
is `g0`-dimensioned via `withDims`, and a dimension-mangled blob merely fails
the validators. -/
@[reducible]
def automatonOfG0Tables (g0 : Grammar0) (lk : ProdLookup g0) (Val : Type)
    (actions : Nat → List Val → Val) (t : GenTables) :
    Automaton (g0.toGrammar lk Val actions) where
  NonInitState := Fin ((t.withDims g0.numTerm g0.numNonterm g0.prods.size g0.start).numNonInit + 1)
  noninitstateAlphabet := inferInstance
  InitState := Fin 1
  initstateAlphabet := inferInstance
  last_symb_of_non_init_state :=
    lastSymbOf (t.withDims g0.numTerm g0.numNonterm g0.prods.size g0.start)
  start_nt := fun _ => cl g0.numNonterm g0.start
  action_table := fun s =>
    let td := t.withDims g0.numTerm g0.numNonterm g0.prods.size g0.start
    let flat := match s with | .Init _ => 0 | .Ninit n => n.val + 1
    gActionToAction td (td.action.getD flat (.lookahead #[]))
  goto_table := fun s nt =>
    let td := t.withDims g0.numTerm g0.numNonterm g0.prods.size g0.start
    let flat := match s with | .Init _ => 0 | .Ninit n => n.val + 1
    match (td.goto.getD flat #[]).getD nt.val none with
    | none => none
    | some tgt =>
        let target : Fin (td.numNonInit + 1) := cl td.numNonInit (tgt - 1)
        if h : (Symbol.NT nt : Symbol (Fin (g0.numTerm + 1)) (Fin (g0.numNonterm + 1)))
            = lastSymbOf td target then some ⟨target, h⟩ else none
  past_symb_of_non_init_state := fun n =>
    let td := t.withDims g0.numTerm g0.numNonterm g0.prods.size g0.start
    (td.pastSymb.getD (n.val + 1) #[]).toList.map (gsymToSymbol td)
  past_state_of_non_init_state := fun n =>
    let td := t.withDims g0.numTerm g0.numNonterm g0.prods.size g0.start
    (td.pastStateSets.getD (n.val + 1) #[]).toList.map (fun (stateSet : Array Nat) =>
      fun (s : State (Fin 1) (Fin (td.numNonInit + 1))) =>
        let flat := match s with | .Init _ => 0 | .Ninit m => m.val + 1
        stateSet.toList.contains flat)
  items_of_state := fun s =>
    let td := t.withDims g0.numTerm g0.numNonterm g0.prods.size g0.start
    let flat := match s with | .Init _ => 0 | .Ninit n => n.val + 1
    (td.items.getD flat #[]).toList.map (fun it =>
      { prod_item := cl g0.prods.size it.1
        dot_pos_item := it.2.1
        lookaheads_item := [cl g0.numTerm it.2.2] })
  nullable_nterm := fun nt =>
    if nt.val < g0.numNonterm then t.nullable.getD nt.val false else true
  first_nterm := fun nt => (t.first.getD nt.val #[]).toList.map (cl g0.numTerm)
  goto_enum := allPairs
  goto_enum_complete := fun s nt _ => mem_allPairs s nt

/-- The automaton half of the **BTree-backed typed** bridge, typed against the
`Grammar0`-derived grammar (kernel-`rfl` certificate path for large automata). -/
@[reducible]
def automatonOfG0TablesTyped (g0 : Grammar0) (lk : ProdLookup g0)
    (ntType : Fin (g0.numNonterm + 1) → Type) (termType : Fin (g0.numTerm + 1) → Type)
    (Info : Type)
    (actions : (p : Fin (g0.prods.size + 1)) →
      arrowsRight (Grammar0.symType0 g0 ntType termType (.NT (Grammar0.prodLhs0 g0 lk p)))
                  ((Grammar0.prodRhsRev0 g0 lk p).map (Grammar0.symType0 g0 ntType termType)))
    (t : GenTables) :
    Automaton (g0.toGrammarTyped lk ntType termType Info actions) where
  NonInitState := Fin ((t.withDims g0.numTerm g0.numNonterm g0.prods.size g0.start).numNonInit + 1)
  noninitstateAlphabet := inferInstance
  InitState := Fin 1
  initstateAlphabet := inferInstance
  last_symb_of_non_init_state :=
    lastSymbOfBT (t.withDims g0.numTerm g0.numNonterm g0.prods.size g0.start)
  start_nt := fun _ => cl g0.numNonterm g0.start
  action_table := fun s =>
    let td := t.withDims g0.numTerm g0.numNonterm g0.prods.size g0.start
    let flat := match s with | .Init _ => 0 | .Ninit n => n.val + 1
    gActionToActionBT td (BTree.find (.lookahead #[]) flat td.actionBT)
  goto_table := gotoTableOfBT (t.withDims g0.numTerm g0.numNonterm g0.prods.size g0.start)
  past_symb_of_non_init_state := fun n =>
    let td := t.withDims g0.numTerm g0.numNonterm g0.prods.size g0.start
    (BTree.find #[] (n.val + 1) td.pastSymbBT).toList.map (gsymToSymbol td)
  past_state_of_non_init_state := fun n =>
    let td := t.withDims g0.numTerm g0.numNonterm g0.prods.size g0.start
    (BTree.find #[] (n.val + 1) td.pastStateSetsBT).toList.map (fun (stateSet : Array Nat) =>
      fun (s : State (Fin 1) (Fin (td.numNonInit + 1))) =>
        let flat := match s with | .Init _ => 0 | .Ninit m => m.val + 1
        stateSet.toList.contains flat)
  items_of_state := fun s =>
    let td := t.withDims g0.numTerm g0.numNonterm g0.prods.size g0.start
    let flat := match s with | .Init _ => 0 | .Ninit n => n.val + 1
    (BTree.find #[] flat td.itemsBT).toList.map (fun it =>
      { prod_item := cl g0.prods.size it.1
        dot_pos_item := it.2.1
        lookaheads_item := [cl g0.numTerm it.2.2] })
  nullable_nterm := fun nt =>
    if nt.val < g0.numNonterm then BTree.find false nt.val t.nullableBT else true
  first_nterm := fun nt => (BTree.find #[] nt.val t.firstBT).toList.map (cl g0.numTerm)
  goto_enum := gotoEnumOfBT (t.withDims g0.numTerm g0.numNonterm g0.prods.size g0.start)
  goto_enum_complete :=
    gotoEnumOfBT_complete (t.withDims g0.numTerm g0.numNonterm g0.prods.size g0.start)

end Gen
end LeanMenhir
