/-
Port of `coq-menhirlib`'s `Main.v` to Lean 4.

Original: Copyright Inria and CNRS, LGPL-3.0-or-later.
This Lean port is a derivative work, distributed under LGPL-3.0-or-later.

The user-facing entry points: the boolean validators, the runnable `parse`, the
soundness theorem, and (given the completeness validator accepts) the
completeness and unambiguity theorems.
-/
import LeanMenhir.Interpreter.Correct
import LeanMenhir.Interpreter.Complete

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

/-- The completeness validator: `completeValidator () = true` is discharged (by
`decide`/`native_decide`) for a concrete automaton (Coq `complete_validator`). -/
def completeValidator (_ : Unit) : Bool := isComplete ()

/-- **Completeness** (Coq `Main.parse_complete`): if the completeness validator
accepts the tables, then for *every* parse tree of `word`, parsing `word`
(followed by any `bufferEnd`) with budget `2 ^ logNSteps` returns that tree's
semantics, consumes exactly `word`, and `pt_size tree ≤ 2 ^ logNSteps`; with too
little fuel it times out, and it never fails. -/
theorem parse_complete (init : A.InitState) (hsafe : safeValidator () = true)
    (hcomplete : completeValidator () = true) (logNSteps : Nat) (word : List A.Token)
    (bufferEnd : Buffer) (tree : ParseTree (.NT (A.start_nt init)) word) :
    match parse init hsafe logNSteps (word ++ₛ bufferEnd) with
    | .Parsed sem buff =>
        sem = ptSem tree ∧ buff = bufferEnd ∧ ptSize tree ≤ 2 ^ logNSteps
    | .Timeout => 2 ^ logNSteps < ptSize tree
    | .Fail _ _ => False :=
  LeanMenhir.parse_complete init word bufferEnd (safe_is_validator hsafe)
    (complete_is_validator hcomplete) tree logNSteps

/-- **Unambiguity** (Coq `Main.unambiguity`): if both validators accept and the
token type is inhabited, any two parse trees of the same word have the same
semantic value. -/
theorem unambiguity (hsafe : safeValidator () = true) (hcomplete : completeValidator () = true)
    (tok : A.Token) (init : A.InitState) (word : List A.Token)
    (tree1 tree2 : ParseTree (.NT (A.start_nt init)) word) :
    ptSem tree1 = ptSem tree2 := by
  have H1 := parse_complete init hsafe hcomplete (ptSize tree1) word (Stream'.const tok) tree1
  have H2 := parse_complete init hsafe hcomplete (ptSize tree1) word (Stream'.const tok) tree2
  cases hp : parse init hsafe (ptSize tree1) (word ++ₛ Stream'.const tok) with
  | Fail st t => rw [hp] at H1; exact H1.elim
  | Timeout =>
    rw [hp] at H1
    exact absurd (Nat.lt_two_pow_self.trans H1) (Nat.lt_irrefl _)
  | Parsed sem buff =>
    rw [hp] at H1 H2
    exact H1.1.symm.trans H2.1

end Main
end LeanMenhir
