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

/-! ### Balanced `BTree` *data* literals (for kernel-`rfl` validator certificates)

Unlike the `…Fn` cond-lambda jump tables above (which the `decide` *tactic* reduces
but which beta-copy the whole tree per call — fine for the few-hundred-arm `actions`
dispatcher, fatal for the validators' tens-of-thousands of lookups), the validator
tables are emitted as `BTree` *data*. `BTree.find` descends the shared literal in
`O(log n)` with no large substitution, so a kernel-`rfl` certificate over a
480-state automaton reduces in bounded memory. See `Generator/BTree.lean`. -/

private def gsymTy : Expr := mkConst ``GSym
private def arrTyOf (a : Expr) : Expr := mkApp (mkConst ``Array [.zero]) a
private def optTyOf (a : Expr) : Expr := mkApp (mkConst ``Option [.zero]) a
private def natNatNatTy : Expr :=
  mkApp2 (mkConst ``Prod [.zero, .zero]) (mkConst ``Nat)
    (mkApp2 (mkConst ``Prod [.zero, .zero]) (mkConst ``Nat) (mkConst ``Nat))

/-- Balanced `BTree` literal `Expr` over `vals` keyed by index `0 … vals.size-1`
(`BTree.find dflt i = vals[i]` for in-range `i`). `α` is the element type. -/
partial def mkBTreeLit (α : Expr) (vals : Array Expr) (lo hi : Nat) : Expr :=
  if lo ≥ hi then mkApp (mkConst ``BTree.leaf [.zero]) α
  else
    let mid := (lo + hi) / 2
    mkAppN (mkConst ``BTree.node [.zero])
      #[α, mkNatLit mid, vals[mid]!, mkBTreeLit α vals lo mid, mkBTreeLit α vals (mid + 1) hi]

private def mkBT (α : Expr) (vals : Array Expr) : Expr := mkBTreeLit α vals 0 vals.size

/-- Build a concrete `GenTables` literal `Expr` field by field: `toExpr` for each
data field, the synthesised balanced trees for `prodLhsFn`/`prodRhsRevFn`, and
balanced `BTree` literals for the validator tables. The argument order MUST match
the `GenTables` field declaration order.

The eight state/nonterminal-indexed *array* validator tables (`incoming`,
`action`, `goto`, `pastSymb`, `pastStateSets`, `nullable`, `first`, `items`) are
emitted **empty**: the only bridges that read `build_tables%` output
(`automatonOfTablesTyped`, `automatonOfTablesBT`) go through the corresponding
`…BT` trees, so the arrays are dead weight here and emitting them roughly doubles
literal-elaboration time. `prodLhs`/`prodRhsRev` are kept (the monomorphic array
bridge for hand-literals, and reify-bug sanity checks, still read them). A
`build_tables%` result is therefore consumed only via the BTree-backed bridges,
not the monomorphic `automatonOfTables` array bridge. -/
def mkGenTablesExpr (t : GenTables) : Expr :=
  -- Flatten the 2-D `goto`, width `numNonterm + 1` (see `GenTables.gotoBT`).
  let w := t.numNonterm + 1
  let gotoVals : Array Expr := Id.run do
    let mut acc : Array Expr := Array.mkEmpty (t.numStates * w)
    for s in [0:t.numStates] do
      for nt in [0:w] do
        acc := acc.push (toExpr ((t.goto.getD s #[]).getD nt none))
    return acc
  mkAppN (mkConst ``GenTables.mk) #[
    -- scalar + array data + cond-lambda jump tables (declaration order)
    toExpr t.numTerm, toExpr t.numNonterm, toExpr t.numProd, toExpr t.numStates,
    toExpr t.startNonterm, toExpr t.prodLhs, toExpr t.prodRhsRev,
    mkProdLhsFnExpr t, mkProdRhsRevFnExpr t,
    -- the eight array validator tables: emitted empty (the BTrees below carry the
    -- real data; nothing reads these arrays from a build_tables% result)
    toExpr (#[] : Array (Option GSym)), toExpr (#[] : Array GAction),
    toExpr (#[] : Array (Array (Option Nat))), toExpr (#[] : Array (Array GSym)),
    toExpr (#[] : Array (Array (Array Nat))), toExpr (#[] : Array Bool),
    toExpr (#[] : Array (Array Nat)), toExpr (#[] : Array (Array (Nat × Nat × Nat))),
    -- BTree data for the verified accessors (incomingBT, actionBT, gotoBT,
    -- pastSymbBT, pastStateSetsBT, nullableBT, firstBT, itemsBT)
    mkBT (optTyOf gsymTy) (t.incoming.map toExpr),
    mkBT (mkConst ``GAction) (t.action.map toExpr),
    mkBT (optTyOf (mkConst ``Nat)) gotoVals,
    mkBT (arrTyOf gsymTy) (t.pastSymb.map toExpr),
    mkBT (arrTyOf (arrTyOf (mkConst ``Nat))) (t.pastStateSets.map toExpr),
    mkBT (mkConst ``Bool) (t.nullable.map toExpr),
    mkBT (arrTyOf (mkConst ``Nat)) (t.first.map toExpr),
    mkBT (arrTyOf natNatNatTy) (t.items.map toExpr) ]


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
