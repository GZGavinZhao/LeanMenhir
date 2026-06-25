/-
A small, **grammar-agnostic** runtime that drives the verified parser
(`Main.parse`) over a finite token list. A BNFC-style backend emits the
grammar-specific glue (grammar, tables via `build_tables%`, `ntType`/`termType`/
`actions`, the automaton, and a token adapter) and calls into here.

Nothing in this module is grammar-specific; it only:
  * computes a step budget from the token count,
  * pads the finite token list into the infinite `Buffer` the interpreter wants,
  * maps the `ParseResult` (`Parsed`/`Fail`/`Timeout`) into an `Except`.

Tokens built by `Gen.automatonOfTablesTyped` have the shape `Info × Σ t, termType t`;
`onFail` receives the failing lookahead token, so the caller can read a source
position out of its `Info` component (`.1`) for error messages.

LGPL-3.0-or-later (derivative of coq-menhirlib).
-/
import LeanMenhir.Main
import Mathlib.Data.Stream.Init

namespace LeanMenhir.Runtime

open LeanMenhir Stream'

variable {A : Automaton}

/-- A fuel **exponent** generous enough for an input of `n` tokens. `Main.parse`
runs with a budget of `2 ^ logNSteps` steps and a complete parse takes `O(n)`
steps, so any `logNSteps ≥ log₂ n + c` suffices; we add slack. Too-small fuel
only yields a `Timeout` error — never an unsound result — so over-provisioning is
safe (the loop stops as soon as the parse accepts or fails). -/
def fuelFor (n : Nat) : Nat := Nat.log2 (n + 1) + 6

/-- The semantic-value type produced by parsing from initial state `init`: the
value type of the start nonterminal. -/
abbrev ResultType (A : Automaton) (init : A.InitState) : Type :=
  A.symbol_semantic_type (.NT (A.start_nt init))

/-- Run the verified parser on the finite token list `toks`, padding the buffer
with the infinite `eof` filler, and project the `ParseResult` into `Except E`.
`onFail`/`onTimeout` build the caller's error type from the failure cases. -/
def parseList {E : Type}
    (init : A.InitState) (hsafe : Main.safeValidator () = true)
    (eof : A.Token) (toks : List A.Token)
    (onFail : A.State → A.Token → E) (onTimeout : E) :
    Except E (ResultType A init) :=
  match Main.parse init hsafe (fuelFor toks.length) (toks ++ₛ Stream'.const eof) with
  | .Parsed v _ => .ok v
  | .Fail st tok => .error (onFail st tok)
  | .Timeout => .error onTimeout

/-- Convenience wrapper: convert each external token via `adapt` (which may fail —
e.g. an unlexable token), then `parseList`. The external token type `Tok` is
whatever the lexer produces (e.g. BNFC's `Token`). -/
def parseWith {Tok E : Type}
    (init : A.InitState) (hsafe : Main.safeValidator () = true)
    (eof : A.Token) (adapt : Tok → Except E A.Token)
    (onFail : A.State → A.Token → E) (onTimeout : E)
    (input : List Tok) :
    Except E (ResultType A init) := do
  parseList init hsafe eof (← input.mapM adapt) onFail onTimeout

end LeanMenhir.Runtime
