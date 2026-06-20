/-
Port of `coq-menhirlib`'s `Main.v` to Lean 4.

Original: Copyright Inria and CNRS, LGPL-3.0-or-later.
This Lean port is a derivative work, distributed under LGPL-3.0-or-later.

The user-facing entry points: the boolean validators, the runnable `parse`, and
the soundness theorem. (Completeness and unambiguity will join here once the
completeness module is ported.)
-/
import LeanMenhir.Interpreter.Correct

namespace LeanMenhir
namespace Main

open Stream'

variable [A : Automaton]

/-- The safety validator: `safeValidator () = true` is the precondition discharged
(by `decide`/`native_decide`) for a concrete automaton (Coq `safe_validator`). -/
def safeValidator (_ : Unit) : Bool := isSafe ()

/-- The runnable parser: given a machine-checked proof that the safety validator
accepts the tables, parse `buffer` with budget `2 ^ logNSteps` (Coq `Main.parse`). -/
def parse (init : A.InitState) (hsafe : safeValidator () = true) (logNSteps : Nat)
    (buffer : Buffer) : ParseResult (A.symbol_semantic_type (.NT (A.start_nt init))) :=
  LeanMenhir.parse init (safe_is_validator hsafe) buffer logNSteps

/-- **Soundness** (Coq `Main.parse_correct`): a successful parse returns a real
parse tree of the recognised word with the produced semantic value. -/
theorem parse_correct (init : A.InitState) (hsafe : safeValidator () = true)
    (logNSteps : Nat) (buffer : Buffer) :
    match parse init hsafe logNSteps buffer with
    | .Parsed sem bufferNew =>
        ∃ (word : List A.Token) (pt : ParseTree (.NT (A.start_nt init)) word),
          buffer = word ++ₛ bufferNew ∧ ptSem pt = sem
    | _ => True :=
  LeanMenhir.parse_correct init (safe_is_validator hsafe) buffer logNSteps

end Main
end LeanMenhir
