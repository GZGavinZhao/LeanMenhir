/-
Port of `coq-menhirlib`'s `Interpreter_correct.v` to Lean 4.

Original: Copyright Inria and CNRS, LGPL-3.0-or-later.
This Lean port is a derivative work, distributed under LGPL-3.0-or-later.

Soundness of the interpreter: if a parse succeeds and returns a semantic value,
then the input word really has a parse tree with that semantic value.
-/
import LeanMenhir.Interpreter
import Mathlib.Data.Stream.Init

namespace LeanMenhir

open Stream'

variable [A : Automaton] (init : A.InitState)

/-- `WordHasStackSemantics word stk` : `word` is a concatenation of words whose
semantic values are exactly those stored on the stack (Coq
`word_has_stack_semantics`). -/
inductive WordHasStackSemantics : List A.Token → Stack → Prop
  | nil : WordHasStackSemantics [] []
  | cons {wordq : List A.Token} {stackq : Stack} :
      WordHasStackSemantics wordq stackq →
      {wordt : List A.Token} → (s : A.NonInitState) →
      (pt : ParseTree (A.last_symb_of_non_init_state s) wordt) →
      WordHasStackSemantics (wordq ++ wordt) (⟨s, ptSem pt⟩ :: stackq)

/-- `pop` produces a parse-tree list whose semantics match the popped values
(Coq `pop_spec_ptl`). -/
theorem pop_spec_ptl {R : Type} (symbolsToPop : List (Symbol A.Terminal A.Nonterminal))
    (action : arrowsRight R (symbolsToPop.map A.symbol_semantic_type))
    (wordStk : List A.Token) (stk : Stack) (res : R) (stk' : Stack)
    (hspec : PopSpec symbolsToPop stk action stk' res)
    (hword : WordHasStackSemantics wordStk stk) :
    ∃ (wordStk' wordRes : List A.Token) (ptl : ParseTreeList symbolsToPop wordRes),
      wordStk' ++ wordRes = wordStk ∧ WordHasStackSemantics wordStk' stk' ∧
      ptlSem ptl action = res := by
  sorry

/-- `reduceStep` is sound (Coq `reduce_step_invariant`). -/
theorem reduceStep_sound (stk : Stack) (prod : A.Production)
    (Hval : validForReduce (stateOfStack init stk) prod) (Hi : StackInvariant init stk)
    (word : List A.Token) (buffer : Buffer) (hword : WordHasStackSemantics word stk) :
    match reduceStep init stk prod buffer Hval Hi with
    | .Accept sem bufferNew =>
        ∃ pt : ParseTree (.NT (A.start_nt init)) word, buffer = bufferNew ∧ ptSem pt = sem
    | .Progress stk' bufferNew => buffer = bufferNew ∧ WordHasStackSemantics word stk'
    | .Fail _ _ => True := by
  sorry

/-- `step` is sound (Coq `step_invariant`). -/
theorem step_sound (hsafe : safe) (stk : Stack) (word : List A.Token) (buffer : Buffer)
    (Hi : StackInvariant init stk) (hword : WordHasStackSemantics word stk) :
    match step init hsafe stk buffer Hi with
    | .Accept sem bufferNew =>
        ∃ (wordNew : List A.Token) (pt : ParseTree (.NT (A.start_nt init)) wordNew),
          word ++ₛ buffer = wordNew ++ₛ bufferNew ∧ ptSem pt = sem
    | .Progress stkNew bufferNew =>
        ∃ wordNew : List A.Token,
          word ++ₛ buffer = wordNew ++ₛ bufferNew ∧ WordHasStackSemantics wordNew stkNew
    | .Fail _ _ => True := by
  sorry

/-- The parse loop is sound (Coq `parse_fix_invariant`). -/
theorem parseFix_sound (hsafe : safe) (stk : Stack) (word : List A.Token) (buffer : Buffer)
    (logNSteps : Nat) (Hi : StackInvariant init stk) (hword : WordHasStackSemantics word stk) :
    match (parseFix init hsafe stk buffer logNSteps Hi).1 with
    | .Accept sem bufferNew =>
        ∃ (wordNew : List A.Token) (pt : ParseTree (.NT (A.start_nt init)) wordNew),
          word ++ₛ buffer = wordNew ++ₛ bufferNew ∧ ptSem pt = sem
    | .Progress stkNew bufferNew =>
        ∃ wordNew : List A.Token,
          word ++ₛ buffer = wordNew ++ₛ bufferNew ∧ WordHasStackSemantics wordNew stkNew
    | .Fail _ _ => True := by
  sorry

/-- **Soundness.** If the parser returns `Parsed sem buffer'`, the consumed input
`word ++ buffer'` has a parse tree of head `start_nt init` with semantics `sem`
(Coq `parse_correct`). -/
theorem parse_correct (hsafe : safe) (buffer : Buffer) (logNSteps : Nat) :
    match parse init hsafe buffer logNSteps with
    | .Parsed sem bufferNew =>
        ∃ (word : List A.Token) (pt : ParseTree (.NT (A.start_nt init)) word),
          buffer = word ++ₛ bufferNew ∧ ptSem pt = sem
    | _ => True := by
  have hfix := parseFix_sound init hsafe [] [] buffer logNSteps (initStackInvariant init)
    WordHasStackSemantics.nil
  unfold parse
  cases h : (parseFix init hsafe [] buffer logNSteps (initStackInvariant init)).1 with
  | Fail st tok => trivial
  | Accept sem buf =>
      rw [h] at hfix
      obtain ⟨word, pt, hbuf, hsem⟩ := hfix
      exact ⟨word, pt, by simpa using hbuf, hsem⟩
  | Progress _ _ => trivial

end LeanMenhir
