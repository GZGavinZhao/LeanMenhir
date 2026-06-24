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

These let `Lean.toExpr (tables : GenTables)` reify a computed value back into a
literal `Expr`. The standard `ToExpr` instances for `Nat`/`Bool`/`Array`/`Option`/
`Prod` cover the remaining field types. -/

deriving instance ToExpr for GSym
deriving instance ToExpr for GLookahead
deriving instance ToExpr for GAction
deriving instance ToExpr for GenTables

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
      return toExpr (← buildTablesEval gExpr)
  | _ => throwUnsupportedSyntax

end LeanMenhir.Gen
