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
  induction hspec generalizing wordStk with
  | nil stk0 sem =>
    exact ⟨wordStk, [], ParseTreeList.Nil_ptl, by simp, hword, by simp only [ptlSem]⟩
  | cons st stk0 action0 sem stk'0 res0 hspec' ih =>
    cases hword with
    | cons hwordq s pt =>
      obtain ⟨wordStk', wordRes, ptl, heq1, hword', heq2⟩ := ih _ hwordq
      exact ⟨wordStk', wordRes ++ _, ParseTreeList.Cons_ptl ptl pt,
        by rw [← List.append_assoc, heq1], hword', by rw [ptlSem]; exact heq2⟩

/-- Transporting a parse tree along a symbol equality casts its semantic value. -/
theorem ptSem_cast {s1 s2 : Symbol A.Terminal A.Nonterminal} {w : List A.Token}
    (h : s1 = s2) (pt : ParseTree s1 w) :
    ptSem (h ▸ pt) = cast (congrArg A.symbol_semantic_type h) (ptSem pt) := by
  subst h; rfl

/-- When a reduce's goto fails, the residual stack is empty and the produced
nonterminal is the start symbol (the core of `reduceStep`'s accept case). -/
theorem reduce_none_aux (stk : Stack) (prod : A.Production)
    (Hval : validForReduce (stateOfStack init stk) prod) (Hi : StackInvariant init stk)
    (hpref : Prefix (A.prod_rhs_rev prod) (symbStackOfStack stk))
    (hgoto : A.goto_table (stateOfStack init
      (pop (A.prod_rhs_rev prod) stk hpref (A.prod_action prod)).1) (A.prod_lhs prod) = none) :
    (pop (A.prod_rhs_rev prod) stk hpref (A.prod_action prod)).1 = [] ∧
      A.prod_lhs prod = A.start_nt init := by
  have hsv := pop_state_valid init (A.prod_rhs_rev prod) stk hpref (A.prod_action prod)
    (headStatesOfState (stateOfStack init stk)) (Hi.state_prefix init)
  have hg := Hval.2 _ hsv
  rw [hgoto] at hg
  cases hc : (pop (A.prod_rhs_rev prod) stk hpref (A.prod_action prod)).1 with
  | nil => rw [hc] at hg; exact ⟨rfl, hg⟩
  | cons cell rec => rw [hc] at hg; exact hg.elim

/-- `reduceStep` is sound (Coq `reduce_step_invariant`). -/
theorem reduceStep_sound (stk : Stack) (prod : A.Production)
    (Hval : validForReduce (stateOfStack init stk) prod) (Hi : StackInvariant init stk)
    (word : List A.Token) (buffer : Buffer) (hword : WordHasStackSemantics word stk) :
    match reduceStep init stk prod buffer Hval Hi with
    | .Accept sem bufferNew =>
        ∃ pt : ParseTree (.NT (A.start_nt init)) word, buffer = bufferNew ∧ ptSem pt = sem
    | .Progress stk' bufferNew => buffer = bufferNew ∧ WordHasStackSemantics word stk'
    | .Fail _ _ => True := by
  have hpref : Prefix (A.prod_rhs_rev prod) (symbStackOfStack stk) :=
    Prefix.trans Hval.1 (Hi.symb_prefix init)
  have hps : PopSpec (A.prod_rhs_rev prod) stk (A.prod_action prod)
      (pop (A.prod_rhs_rev prod) stk hpref (A.prod_action prod)).1
      (pop (A.prod_rhs_rev prod) stk hpref (A.prod_action prod)).2 :=
    pop_spec_ok _ _ _ _ _ _ rfl
  obtain ⟨word1, word2, ptl, hwordeq, hword1, hptlsem⟩ := pop_spec_ptl _ _ word _ _ _ hps hword
  have hval2 : (pop (A.prod_rhs_rev prod) stk hpref (A.prod_action prod)).2
      = ptSem (ParseTree.Non_terminal_pt prod ptl) := by rw [← hptlsem, ptSem]
  simp only [reduceStep]
  split
  · -- outer Accept
    rename_i sem bufferNew heqv
    split at heqv
    · simp at heqv
    · rename_i hgoto
      obtain ⟨hnil, e2⟩ := reduce_none_aux init stk prod Hval Hi hpref hgoto
      injection heqv with hsem hbuf
      rw [hnil] at hword1
      cases hword1
      rw [List.nil_append] at hwordeq
      subst hwordeq
      refine ⟨(congrArg Symbol.NT e2) ▸ ParseTree.Non_terminal_pt prod ptl, hbuf, ?_⟩
      rw [ptSem_cast, ← hval2]
      exact hsem
  · -- outer Progress
    rename_i stk' bufferNew heqv
    split at heqv
    · rename_i sn e hgoto
      injection heqv with hstk hbuf
      subst hstk
      refine ⟨hbuf, ?_⟩
      rw [← hwordeq]
      have key := WordHasStackSemantics.cons hword1 sn (e ▸ ParseTree.Non_terminal_pt prod ptl)
      rw [ptSem_cast e (ParseTree.Non_terminal_pt prod ptl), ← hval2] at key
      exact key
    · simp at heqv
  · -- outer Fail
    trivial

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
  simp only [step]
  split
  · -- outer Accept
    rename_i sem bn heqa
    split at heqa
    · -- Default reduce
      rename_i prod haction
      have Hv : validForReduce (stateOfStack init stk) prod := by
        have h := reduceOk_of_safe hsafe (stateOfStack init stk); rw [haction] at h; exact h
      have heq2 : reduceStep init stk prod buffer Hv Hi = .Accept sem bn := heqa
      have hr := reduceStep_sound init stk prod Hv Hi word buffer hword
      rw [heq2] at hr
      obtain ⟨pt, hb, hs⟩ := hr
      exact ⟨word, pt, by rw [hb], hs⟩
    · -- Lookahead
      rename_i awt haction
      split at heqa
      · simp at heqa
      · rename_i prod hawt
        have Hv : validForReduce (stateOfStack init stk) prod := by
          have h := reduceOk_of_safe hsafe (stateOfStack init stk); rw [haction] at h
          have h2 := h (A.token_term buffer.head); rw [hawt] at h2; exact h2
        have heq2 : reduceStep init stk prod buffer Hv Hi = .Accept sem bn := heqa
        have hr := reduceStep_sound init stk prod Hv Hi word buffer hword
        rw [heq2] at hr
        obtain ⟨pt, hb, hs⟩ := hr
        exact ⟨word, pt, by rw [hb], hs⟩
      · simp at heqa
  · -- outer Progress
    rename_i stk' bn heqp
    split at heqp
    · -- Default reduce
      rename_i prod haction
      have Hv : validForReduce (stateOfStack init stk) prod := by
        have h := reduceOk_of_safe hsafe (stateOfStack init stk); rw [haction] at h; exact h
      have heq2 : reduceStep init stk prod buffer Hv Hi = .Progress stk' bn := heqp
      have hr := reduceStep_sound init stk prod Hv Hi word buffer hword
      rw [heq2] at hr
      obtain ⟨hb, hw⟩ := hr
      exact ⟨word, by rw [hb], hw⟩
    · -- Lookahead
      rename_i awt haction
      split at heqp
      · -- shift: push the read token
        rename_i sn e hawt
        injection heqp with hst hbuf
        subst hst; subst hbuf
        refine ⟨word ++ [buffer.head], ?_, ?_⟩
        · rw [Stream'.append_append_stream]
          congr 1
          rw [Stream'.cons_append_stream, Stream'.nil_append_stream]
          exact (Stream'.eta buffer).symm
        · have key := WordHasStackSemantics.cons hword sn (e ▸ ParseTree.Terminal_pt buffer.head)
          rw [ptSem_cast e (ParseTree.Terminal_pt buffer.head), ptSem] at key
          exact key
      · rename_i prod hawt
        have Hv : validForReduce (stateOfStack init stk) prod := by
          have h := reduceOk_of_safe hsafe (stateOfStack init stk); rw [haction] at h
          have h2 := h (A.token_term buffer.head); rw [hawt] at h2; exact h2
        have heq2 : reduceStep init stk prod buffer Hv Hi = .Progress stk' bn := heqp
        have hr := reduceStep_sound init stk prod Hv Hi word buffer hword
        rw [heq2] at hr
        obtain ⟨hb, hw⟩ := hr
        exact ⟨word, by rw [hb], hw⟩
      · simp at heqp
  · -- outer Fail
    trivial

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
  induction logNSteps generalizing stk word buffer Hi with
  | zero => exact step_sound init hsafe stk word buffer Hi hword
  | succ n ih =>
    have IH := ih stk word buffer Hi hword
    rcases hpf : parseFix init hsafe stk buffer n Hi with ⟨sr, hsr⟩
    rw [hpf] at IH
    rw [parseFix_succ, hpf]
    cases sr with
    | Accept s b => exact IH
    | Fail s t => trivial
    | Progress stk2 buf2 =>
      obtain ⟨word2, hb, hw2⟩ := IH
      have IH2 := ih stk2 word2 buf2 (hsr stk2 buf2 rfl) hw2
      revert IH2
      cases (parseFix init hsafe stk2 buf2 n (hsr stk2 buf2 rfl)).1 with
      | Accept s b =>
        intro IH2; obtain ⟨w, pt, he, hs⟩ := IH2; exact ⟨w, pt, by rw [hb]; exact he, hs⟩
      | Progress s2 b2 =>
        intro IH2; obtain ⟨w, he, hh⟩ := IH2; exact ⟨w, by rw [hb]; exact he, hh⟩
      | Fail _ _ => intro _; trivial

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
