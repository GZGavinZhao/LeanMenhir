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

open LeanMenhir.Buf

variable [G : Grammar] [A : Automaton G]

/-- The runnable parser: given a proof that the automaton is `safe` (discharged by
`by decide`/`by native_decide` via the `Decidable safe` instance), parse `buffer`
with budget `2 ^ logNSteps` (Coq `Main.parse`). -/
def parse (init : A.InitState) (hsafe : safe) (logNSteps : Nat)
    (buffer : Buffer) : ParseResult (A.symbol_semantic_type (.NT (A.start_nt init))) :=
  LeanMenhir.parse init hsafe buffer logNSteps

/-- **Soundness** (Coq `Main.parse_correct`): a successful parse exhibits a real
parse tree of the consumed word whose semantics is the value returned. Stated in
the idiomatic hypothesis-driven form — given the parser produced `.Parsed sem
bufferNew`, the tree exists — rather than a `match … | _ => True`. -/
theorem parse_correct (init : A.InitState) (hsafe : safe) (logNSteps : Nat) (buffer : Buffer)
    {sem : A.symbol_semantic_type (.NT (A.start_nt init))} {bufferNew : Buffer}
    (hrun : parse init hsafe logNSteps buffer = .Parsed sem bufferNew) :
    ∃ (word : List A.Token) (pt : ParseTree (.NT (A.start_nt init)) word),
      buffer.get = (word ++ₛ bufferNew).get ∧ ptSem pt = sem := by
  have H := LeanMenhir.parse_correct init hsafe buffer logNSteps
  simp only [parse] at hrun
  rw [hrun] at H
  exact H

/-- **Completeness** (Coq `Main.parse_complete`): if the automaton is `complete`,
then any parse `tree` of `word` is recognised — given enough fuel
(`ptSize tree ≤ 2 ^ logNSteps`), parsing `word` followed by any `bufferEnd`
returns exactly that tree's semantics and consumes exactly `word`. This is the
headline guarantee; `parsed_eq`, `not_fail`, and `timeout_lt` record the precise
behaviour in each of the other result branches. -/
theorem parse_complete (init : A.InitState) (hsafe : safe) (hcomplete : complete)
    (logNSteps : Nat) (word : List A.Token) (bufferEnd : Buffer)
    (tree : ParseTree (.NT (A.start_nt init)) word) (hfuel : ptSize tree ≤ 2 ^ logNSteps) :
    parse init hsafe logNSteps (word ++ₛ bufferEnd) = .Parsed (ptSem tree) bufferEnd := by
  have H := LeanMenhir.parse_complete init word bufferEnd hsafe hcomplete tree logNSteps
  simp only [parse]
  cases hp : LeanMenhir.parse init hsafe (word ++ₛ bufferEnd) logNSteps with
  | Parsed sem buff => rw [hp] at H; obtain ⟨h1, h2, _⟩ := H; rw [h1, h2]
  | Timeout => rw [hp] at H; omega
  | Fail s t => rw [hp] at H; exact H.elim

/-- On a successful complete parse, the returned value is exactly the tree's
semantics, the leftover buffer is exactly `bufferEnd`, and the tree fits the
budget. -/
theorem parsed_eq (init : A.InitState) (hsafe : safe) (hcomplete : complete)
    (logNSteps : Nat) (word : List A.Token) (bufferEnd : Buffer)
    (tree : ParseTree (.NT (A.start_nt init)) word)
    {sem : A.symbol_semantic_type (.NT (A.start_nt init))} {buff : Buffer}
    (hrun : parse init hsafe logNSteps (word ++ₛ bufferEnd) = .Parsed sem buff) :
    sem = ptSem tree ∧ buff = bufferEnd ∧ ptSize tree ≤ 2 ^ logNSteps := by
  have H := LeanMenhir.parse_complete init word bufferEnd hsafe hcomplete tree logNSteps
  simp only [parse] at hrun
  rw [hrun] at H
  exact H

/-- The parser never fails on input that has a parse tree. -/
theorem not_fail (init : A.InitState) (hsafe : safe) (hcomplete : complete)
    (logNSteps : Nat) (word : List A.Token) (bufferEnd : Buffer)
    (tree : ParseTree (.NT (A.start_nt init)) word) (st : A.State) (tok : A.Token) :
    parse init hsafe logNSteps (word ++ₛ bufferEnd) ≠ .Fail st tok := by
  have H := LeanMenhir.parse_complete init word bufferEnd hsafe hcomplete tree logNSteps
  simp only [parse]
  intro hrun
  rw [hrun] at H
  exact H

/-- A timeout means the step budget was too small for this tree. -/
theorem timeout_lt (init : A.InitState) (hsafe : safe) (hcomplete : complete)
    (logNSteps : Nat) (word : List A.Token) (bufferEnd : Buffer)
    (tree : ParseTree (.NT (A.start_nt init)) word)
    (hrun : parse init hsafe logNSteps (word ++ₛ bufferEnd) = .Timeout) :
    2 ^ logNSteps < ptSize tree := by
  have H := LeanMenhir.parse_complete init word bufferEnd hsafe hcomplete tree logNSteps
  simp only [parse] at hrun
  rw [hrun] at H
  exact H

/-- **Unambiguity** (Coq `Main.unambiguity`): if the automaton is `safe` and
`complete` and the token type is inhabited, any two parse trees of the same word
have the same semantic value. -/
theorem unambiguity (hsafe : safe) (hcomplete : complete)
    (tok : A.Token) (init : A.InitState) (word : List A.Token)
    (tree1 tree2 : ParseTree (.NT (A.start_nt init)) word) :
    ptSem tree1 = ptSem tree2 := by
  cases hp : parse init hsafe (ptSize tree1) (word ++ₛ Buf.const tok) with
  | Fail st t =>
    exact absurd hp (not_fail init hsafe hcomplete (ptSize tree1) word (Buf.const tok) tree1 st t)
  | Timeout =>
    have H1 := timeout_lt init hsafe hcomplete (ptSize tree1) word (Buf.const tok) tree1 hp
    exact absurd (Nat.lt_trans Nat.lt_two_pow_self H1) (Nat.lt_irrefl _)
  | Parsed sem buff =>
    have e1 := parsed_eq init hsafe hcomplete (ptSize tree1) word (Buf.const tok) tree1 hp
    have e2 := parsed_eq init hsafe hcomplete (ptSize tree1) word (Buf.const tok) tree2 hp
    exact e1.1.symm.trans e2.1

end Main
end LeanMenhir
