/-
Strategy C: a `build_tables%` term elaborator that runs the (untrusted) SLR(1)
generator `Grammar0.buildTablesSLR` **at elaboration time** and splices the
resulting `GenTables` back into the program as a concrete literal.

Why an elaborator (rather than `def tables := grammar.buildTablesSLR`)? The
heterogeneous bridge `automatonOfTablesTyped` needs the production data of the
tables to *reduce* (so the dependent `actions` dispatcher's per-branch types
reduce to concrete arrow types). `buildTablesSLR` is a `partial def`, so its
applications are opaque and never reduce. `build_tables% grammar` instead
evaluates the compiled generator once during elaboration and emits a fully
concrete `GenTables` literal — which reduces, supports kernel `decide`
certificates (no `native_decide`/compiler-trust), and keeps a single-phase
`lake build` (no separate codegen executable).

The generator remains *untrusted*: a buggy table is rejected by the verified
`safeValidator`/`completeValidator` (a failed `decide`), never silently accepted.

LGPL-3.0-or-later (derivative of coq-menhirlib).
-/
import LeanMenhir.Generator.LR1
import Lean

namespace LeanMenhir.Gen

open Lean Lean.Elab Lean.Elab.Term Lean.Meta

/-! ### `ToExpr` for the table types

These let `Lean.toExpr` reify computed field values back into literal `Expr`s. The
standard `ToExpr` instances for `Nat`/`Bool`/`Array`/`Option`/`Prod` cover the
remaining field types.

Note `GenTables` *itself* is deliberately not `ToExpr`: it now carries the function
fields `prodLhsFn`/`prodRhsRevFn`, and functions have no `ToExpr` instance.
`build_tables%` instead builds the `GenTables` literal field by field via
`mkGenTablesExpr`, synthesising those two function fields as balanced decision
trees (see `mkLookupLambda`). -/

deriving instance ToExpr for GSym
deriving instance ToExpr for GLookahead
deriving instance ToExpr for GAction

/-! ### Jump-table synthesis

`build_tables%` compiles the array fields `prodLhs`/`prodRhsRev` into the function
fields `prodLhsFn`/`prodRhsRevFn` as *balanced binary search trees* over numeric
literals. Each lookup then reduces in the kernel in `O(log numProd)` via the
accelerated `Nat.ble`/`Nat.beq`, instead of the `O(index)` backing-`List` walk that
`Array.getD` incurs. That is what makes the heterogeneous `actions` dispatcher —
whose dependent return type forces one production lookup *per arm* — elaborate in
`O(numProd · log numProd)` rather than `O(numProd²)`, and without retaining huge
intermediate `List`/`Array` states (the real memory blow-up on large grammars). -/

/-- A balanced binary-search tree `Expr` over `vals` (covering indices
`0 … vals.size-1`): reduces to `vals[i]` when the lookup key equals `i`, else to
`default`. `key` is the `Expr` of the lookup variable (a loose `bvar`); `α`/`u` are
the element type and its `Sort` level (e.g. `Nat : Sort 1`, so `u = 1`). -/
partial def mkLookupTree (α : Expr) (u : Level) (default : Expr) (vals : Array Expr)
    (key : Expr) (lo hi : Nat) : Expr :=
  if hi - lo ≤ 1 then
    if lo < hi then
      -- leaf: `cond (key == lo) vals[lo] default`
      mkApp4 (mkConst ``cond [u]) α (mkApp2 (mkConst ``Nat.beq) key (mkNatLit lo)) vals[lo]! default
    else default
  else
    let mid := (lo + hi) / 2
    -- `cond (mid ≤ key) <right [mid,hi)> <left [lo,mid)>`
    mkApp4 (mkConst ``cond [u]) α (mkApp2 (mkConst ``Nat.ble) (mkNatLit mid) key)
      (mkLookupTree α u default vals key mid hi)
      (mkLookupTree α u default vals key lo mid)

/-- Build `fun (n : Nat) => <balanced tree over `vals`>` as a closed `Expr`. -/
def mkLookupLambda (α : Expr) (u : Level) (default : Expr) (vals : Array Expr) : Expr :=
  .lam `n (mkConst ``Nat) (mkLookupTree α u default vals (.bvar 0) 0 vals.size) .default

/-- `prodLhsFn` as a balanced lookup tree of `Nat` literals (`Nat : Sort 1`). -/
def mkProdLhsFnExpr (t : GenTables) : Expr :=
  mkLookupLambda (mkConst ``Nat) (.succ .zero) (mkNatLit 0) (t.prodLhs.map mkNatLit)

/-- `prodRhsRevFn` as a balanced lookup tree of `Array GSym` literals
(`Array GSym : Sort 1`). -/
def mkProdRhsRevFnExpr (t : GenTables) : Expr :=
  let arrTy := mkApp (mkConst ``Array [.zero]) (mkConst ``GSym)
  mkLookupLambda arrTy (.succ .zero) (toExpr (#[] : Array GSym)) (t.prodRhsRev.map toExpr)

/-- Build a concrete `GenTables` literal `Expr` field by field: `toExpr` for each
data field, the synthesised balanced trees for `prodLhsFn`/`prodRhsRevFn`. The
argument order MUST match the `GenTables` field declaration order. -/
def mkGenTablesExpr (t : GenTables) : Expr :=
  mkAppN (mkConst ``GenTables.mk) #[
    toExpr t.numTerm, toExpr t.numNonterm, toExpr t.numProd, toExpr t.numStates,
    toExpr t.startNonterm, toExpr t.prodLhs, toExpr t.prodRhsRev,
    mkProdLhsFnExpr t, mkProdRhsRevFnExpr t,
    toExpr t.incoming, toExpr t.action, toExpr t.goto,
    toExpr t.pastSymb, toExpr t.pastStateSets, toExpr t.nullable,
    toExpr t.first, toExpr t.items ]


/-! ### The elaborator -/

/-- Evaluate `Grammar0.buildTablesSLR gExpr` using the compiled generator. This is
`unsafe` (via `evalExpr`); it is exposed through the `implemented_by` wrapper
`buildTablesEval` below so it can be called from the safe elaborator. -/
unsafe def buildTablesEvalImpl (gExpr : Expr) : MetaM GenTables :=
  evalExpr GenTables (mkConst ``GenTables) (mkApp (mkConst ``Grammar0.buildTablesSLR) gExpr)

@[implemented_by buildTablesEvalImpl]
opaque buildTablesEval (gExpr : Expr) : MetaM GenTables

/-- `build_tables% g` : run the SLR(1) generator on the `Grammar0` `g` at
elaboration time and splice the resulting tables as a concrete `GenTables`
literal. `g` must elaborate to a closed `Grammar0` (e.g. a top-level `def`). -/
syntax (name := buildTablesSyntax) "build_tables% " term : term

@[term_elab buildTablesSyntax]
def elabBuildTables : TermElab := fun stx _ => do
  match stx with
  | `(build_tables% $g) => do
      let gExpr ← elabTermEnsuringType g (mkConst ``Grammar0)
      synthesizeSyntheticMVarsNoPostponing
      let gExpr ← instantiateMVars gExpr
      if gExpr.hasMVar || gExpr.hasFVar then
        throwError "build_tables%: the grammar must be a closed term (no metavariables or local variables)"
      return mkGenTablesExpr (← buildTablesEval gExpr)
  | _ => throwUnsupportedSyntax

end LeanMenhir.Gen
