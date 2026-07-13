/-
Extensionality of the interpreter in the input buffer.

`step`/`parseFix`/`parse` observe the input buffer only through `Buf.head` and
`Buf.tail`, so two buffers with the same denotation (`b₁.get = b₂.get`) drive
the parser identically: same result constructor, same semantic value/stack/fail
report, and denotationally equal residual buffers. This is the bridge that lets
the completeness theorem — stated for push-list buffers `word ++ₛ bufferEnd` —
cover the array-backed buffers (`Buf.ofListEof`) the runtime driver actually
executes (see `Main.parse_complete_ext` and `Runtime.parseList_complete`).

The Coq original needs no counterpart of this file: there the buffer is a
coinductive stream, the consumed word can be peeled off by `destruct`, and the
completeness theorem applies to the executed term directly. Swapping the
representation for an O(1) buffer turned "denotes the same stream" into a real
(and provable) side condition.

LGPL-3.0-or-later (derivative of coq-menhirlib).
-/
import LeanMenhir.Interpreter.Correct
import LeanMenhir.Interpreter.Complete

namespace LeanMenhir

variable {G : Grammar} {A : Automaton G} (init : A.InitState)

/-! ### Result equivalence up to buffer denotation -/

/-- Two step results that are equal *up to the denotation of their buffers*:
same constructor, equal payloads, and `get`-equal buffers. -/
def StepResult.BufEquiv : StepResult init → StepResult init → Prop
  | .Fail st tok, .Fail st' tok' => st = st' ∧ tok = tok'
  | .Accept sem b, .Accept sem' b' => sem = sem' ∧ b.get = b'.get
  | .Progress stk b, .Progress stk' b' => stk = stk' ∧ b.get = b'.get
  | _, _ => False

theorem StepResult.BufEquiv.symm {init : A.InitState} {r₁ r₂ : StepResult init}
    (h : BufEquiv init r₁ r₂) :
    BufEquiv init r₂ r₁ := by
  cases r₁ <;> cases r₂ <;> first
    | exact ⟨h.1.symm, h.2.symm⟩
    | exact h.elim

theorem StepResult.BufEquiv.trans {init : A.InitState} {r₁ r₂ r₃ : StepResult init}
    (h₁ : BufEquiv init r₁ r₂)
    (h₂ : BufEquiv init r₂ r₃) : BufEquiv init r₁ r₃ := by
  cases r₁ <;> cases r₂ <;> cases r₃ <;> first
    | exact h₁.elim
    | exact h₂.elim
    | exact ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

/-- Two parse results that are equal *up to the denotation of their buffers*. -/
def ParseResult.BufEquiv {R : Type} : ParseResult A R → ParseResult A R → Prop
  | .Fail st tok, .Fail st' tok' => st = st' ∧ tok = tok'
  | .Timeout, .Timeout => True
  | .Parsed v b, .Parsed v' b' => v = v' ∧ b.get = b'.get
  | _, _ => False

/-! ### `reduceStep` congruence -/

/-- `reduceStep` threads the buffer through untouched, so denotationally equal
buffers yield the same result. -/
theorem reduceStep_congr (stk : Stack A) (prod : G.Production) {b₁ b₂ : Buffer G}
    (h : b₁.get = b₂.get) (Hval : validForReduce (stateOfStack init stk) prod)
    (Hi : StackInvariant init stk) :
    StepResult.BufEquiv init (reduceStep init stk prod b₁ Hval Hi)
      (reduceStep init stk prod b₂ Hval Hi) := by
  rcases hpop : pop (G.prod_rhs_rev prod) stk (Prefix.trans Hval.1 (Hi.symb_prefix init))
      (G.prod_action prod) with ⟨stk0, sem⟩
  cases hgoto : A.goto_table (stateOfStack init stk0) (G.prod_lhs prod) with
  | some v =>
    obtain ⟨stateNew, e⟩ := v
    rw [reduceStep_progress_eq init stk prod b₁ Hval Hi stk0 sem stateNew e hpop hgoto,
        reduceStep_progress_eq init stk prod b₂ Hval Hi stk0 sem stateNew e hpop hgoto]
    exact ⟨rfl, h⟩
  | none =>
    have hgoto' : A.goto_table (stateOfStack init
        (pop (G.prod_rhs_rev prod) stk (Prefix.trans Hval.1 (Hi.symb_prefix init))
          (G.prod_action prod)).1) (G.prod_lhs prod) = none := by
      rw [hpop]; exact hgoto
    have e2 : G.prod_lhs prod = A.start_nt init :=
      (reduce_none_aux init stk prod Hval Hi
        (Prefix.trans Hval.1 (Hi.symb_prefix init)) hgoto').2
    rw [reduceStep_accept_eq init stk prod b₁ Hval Hi stk0 sem e2 hpop hgoto,
        reduceStep_accept_eq init stk prod b₂ Hval Hi stk0 sem e2 hpop hgoto]
    exact ⟨rfl, h⟩

/-! ### Two more evaluation lemmas for `step`

`Interpreter/Complete.lean` provides `step_eq_reduceStep_default`,
`step_eq_reduceStep_lookahead` and `step_shift_eq` (the latter for a buffer of
the literal form `cons tok rest`); here we add the general-buffer shift equation
and the fail equation, completing the case analysis of `step`. -/

/-- `step` shifts on a shift action, pushing the read head and dropping to the
tail (general-buffer variant of `step_shift_eq`). -/
theorem step_shift_eq' (hsafe : Safe A) (stk : Stack A) (buffer : Buffer G)
    (Hi : StackInvariant init stk)
    (awt : (term : G.Terminal) → A.LookaheadAction term)
    (haction : A.action_table (stateOfStack init stk) = .Lookahead_act awt)
    (stateNew : A.NonInitState)
    (e : Symbol.T (G.token_term buffer.head) = A.last_symb_of_non_init_state stateNew)
    (hawt : awt (G.token_term buffer.head) = .Shift_act stateNew e) :
    step init hsafe stk buffer Hi =
      .Progress (⟨stateNew, cast (congrArg G.symbol_semantic_type e)
        (G.token_sem buffer.head)⟩ :: stk) buffer.tail := by
  unfold step
  split
  · rename_i prod' haction'
    rw [haction] at haction'; exact absurd haction' (by simp)
  · rename_i awt' haction'
    rw [haction] at haction'; injection haction' with haw; subst haw
    dsimp only
    split
    · rename_i sn e' hawt'
      rw [hawt] at hawt'; injection hawt' with hsn; subst hsn; rfl
    · rename_i prod'' hawt'
      rw [hawt] at hawt'; exact absurd hawt' (by simp)
    · rename_i hawt'
      rw [hawt] at hawt'; exact absurd hawt' (by simp)

/-- `step` fails on a fail action, reporting the current state and head token. -/
theorem step_fail_eq (hsafe : Safe A) (stk : Stack A) (buffer : Buffer G)
    (Hi : StackInvariant init stk)
    (awt : (term : G.Terminal) → A.LookaheadAction term)
    (haction : A.action_table (stateOfStack init stk) = .Lookahead_act awt)
    (hawt : awt (G.token_term buffer.head) = .Fail_act) :
    step init hsafe stk buffer Hi = .Fail (stateOfStack init stk) buffer.head := by
  unfold step
  split
  · rename_i prod' haction'
    rw [haction] at haction'; exact absurd haction' (by simp)
  · rename_i awt' haction'
    rw [haction] at haction'; injection haction' with haw; subst haw
    dsimp only
    split
    · rename_i sn e' hawt'
      rw [hawt] at hawt'; exact absurd hawt' (by simp)
    · rename_i prod'' hawt'
      rw [hawt] at hawt'; exact absurd hawt' (by simp)
    · rfl

/-! ### `step` congruence -/

/-- `step` on `cons b.head b.tail` behaves like `step` on `b` (η for the one
head/tail observation `step` makes). -/
theorem step_eta (hsafe : Safe A) (stk : Stack A) (b : Buffer G) (Hi : StackInvariant init stk) :
    StepResult.BufEquiv init (step init hsafe stk (Buf.cons b.head b.tail) Hi)
      (step init hsafe stk b Hi) := by
  cases haction : A.action_table (stateOfStack init stk) with
  | Default_reduce_act prod =>
    have Hval : validForReduce (stateOfStack init stk) prod := by
      have h := reduceOk_of_safe hsafe (stateOfStack init stk); rw [haction] at h; exact h
    rw [step_eq_reduceStep_default init hsafe stk (Buf.cons b.head b.tail) Hi prod Hval haction,
        step_eq_reduceStep_default init hsafe stk b Hi prod Hval haction]
    exact reduceStep_congr init stk prod (Buf.get_eta b) Hval Hi
  | Lookahead_act awt =>
    cases hawt : awt (G.token_term b.head) with
    | Shift_act stateNew e =>
      rw [step_shift_eq init hsafe stk b.head b.tail Hi awt haction stateNew e hawt,
          step_shift_eq' init hsafe stk b Hi awt haction stateNew e hawt]
      exact ⟨rfl, rfl⟩
    | Reduce_act prod =>
      have Hval : validForReduce (stateOfStack init stk) prod := by
        have h := reduceOk_of_safe hsafe (stateOfStack init stk); rw [haction] at h
        have h2 := h (G.token_term b.head); rw [hawt] at h2; exact h2
      rw [step_eq_reduceStep_lookahead init hsafe stk (Buf.cons b.head b.tail) Hi prod Hval
            awt haction hawt,
          step_eq_reduceStep_lookahead init hsafe stk b Hi prod Hval awt haction hawt]
      exact reduceStep_congr init stk prod (Buf.get_eta b) Hval Hi
    | Fail_act =>
      rw [step_fail_eq init hsafe stk (Buf.cons b.head b.tail) Hi awt haction hawt,
          step_fail_eq init hsafe stk b Hi awt haction hawt]
      exact ⟨rfl, rfl⟩

/-- `step` congruence for buffers sharing the same (literal) head token. -/
theorem step_cons_congr (hsafe : Safe A) (stk : Stack A) (tok : G.Token) {r₁ r₂ : Buffer G}
    (h : r₁.get = r₂.get) (Hi : StackInvariant init stk) :
    StepResult.BufEquiv init (step init hsafe stk (Buf.cons tok r₁) Hi)
      (step init hsafe stk (Buf.cons tok r₂) Hi) := by
  have hc : (Buf.cons tok r₁).get = (Buf.cons tok r₂).get := Buf.cons_get_congr tok h
  cases haction : A.action_table (stateOfStack init stk) with
  | Default_reduce_act prod =>
    have Hval : validForReduce (stateOfStack init stk) prod := by
      have hv := reduceOk_of_safe hsafe (stateOfStack init stk); rw [haction] at hv; exact hv
    rw [step_eq_reduceStep_default init hsafe stk (Buf.cons tok r₁) Hi prod Hval haction,
        step_eq_reduceStep_default init hsafe stk (Buf.cons tok r₂) Hi prod Hval haction]
    exact reduceStep_congr init stk prod hc Hval Hi
  | Lookahead_act awt =>
    cases hawt : awt (G.token_term tok) with
    | Shift_act stateNew e =>
      rw [step_shift_eq init hsafe stk tok r₁ Hi awt haction stateNew e hawt,
          step_shift_eq init hsafe stk tok r₂ Hi awt haction stateNew e hawt]
      exact ⟨rfl, h⟩
    | Reduce_act prod =>
      have Hval : validForReduce (stateOfStack init stk) prod := by
        have hv := reduceOk_of_safe hsafe (stateOfStack init stk); rw [haction] at hv
        have hv2 := hv (G.token_term tok); rw [hawt] at hv2; exact hv2
      rw [step_eq_reduceStep_lookahead init hsafe stk (Buf.cons tok r₁) Hi prod Hval
            awt haction hawt,
          step_eq_reduceStep_lookahead init hsafe stk (Buf.cons tok r₂) Hi prod Hval
            awt haction hawt]
      exact reduceStep_congr init stk prod hc Hval Hi
    | Fail_act =>
      rw [step_fail_eq init hsafe stk (Buf.cons tok r₁) Hi awt haction hawt,
          step_fail_eq init hsafe stk (Buf.cons tok r₂) Hi awt haction hawt]
      exact ⟨rfl, rfl⟩

/-- **`step` congruence**: denotationally equal buffers produce equivalent step
results. -/
theorem step_congr (hsafe : Safe A) (stk : Stack A) {b₁ b₂ : Buffer G} (h : b₁.get = b₂.get)
    (Hi : StackInvariant init stk) :
    StepResult.BufEquiv init (step init hsafe stk b₁ Hi) (step init hsafe stk b₂ Hi) := by
  have hhead : b₁.head = b₂.head := congrFun h 0
  have htail : b₁.tail.get = b₂.tail.get := funext fun n => congrFun h (n + 1)
  have s₁ : StepResult.BufEquiv init (step init hsafe stk b₁ Hi)
      (step init hsafe stk (Buf.cons b₁.head b₂.tail) Hi) :=
    (step_eta init hsafe stk b₁ Hi).symm.trans
      (step_cons_congr init hsafe stk b₁.head htail Hi)
  have s₂ : StepResult.BufEquiv init (step init hsafe stk b₁ Hi)
      (step init hsafe stk (Buf.cons b₂.head b₂.tail) Hi) := hhead ▸ s₁
  exact s₂.trans (step_eta init hsafe stk b₂ Hi)

/-! ### `parseFix` and `parse` congruence -/

/-- **`parseFix` congruence**: denotationally equal buffers produce equivalent
results after any number of steps. -/
theorem parseFix_congr (hsafe : Safe A) (stk : Stack A) {b₁ b₂ : Buffer G} (h : b₁.get = b₂.get)
    (logNSteps : Nat) (Hi : StackInvariant init stk) :
    StepResult.BufEquiv init (parseFix init hsafe stk b₁ logNSteps Hi).1
      (parseFix init hsafe stk b₂ logNSteps Hi).1 := by
  induction logNSteps generalizing stk b₁ b₂ h Hi with
  | zero => exact step_congr init hsafe stk h Hi
  | succ n ih =>
    have IH := ih stk h Hi
    rw [parseFix_succ, parseFix_succ]
    rcases h₁ : parseFix init hsafe stk b₁ n Hi with ⟨sr₁, hsr₁⟩
    rcases h₂ : parseFix init hsafe stk b₂ n Hi with ⟨sr₂, hsr₂⟩
    rw [h₁, h₂] at IH
    cases sr₁ with
    | Progress stk₁' buf₁' =>
      cases sr₂ with
      | Progress stk₂' buf₂' =>
        obtain ⟨hstk, hbuf⟩ := IH
        subst hstk
        exact ih stk₁' hbuf _
      | Fail st tok => exact IH.elim
      | Accept sem buf => exact IH.elim
    | Fail st tok =>
      cases sr₂ with
      | Fail st' tok' => exact IH
      | Progress stk' buf' => exact IH.elim
      | Accept sem buf => exact IH.elim
    | Accept sem buf =>
      cases sr₂ with
      | Accept sem' buf' => exact IH
      | Progress stk' buf' => exact IH.elim
      | Fail st tok => exact IH.elim

/-- **`parse` congruence**: the parser cannot distinguish denotationally equal
input buffers — same outcome, same semantic value, `get`-equal residual buffer.
This is the extensionality bridge used by `Main.parse_complete_ext`. -/
theorem parse_congr (hsafe : Safe A) {b₁ b₂ : Buffer G} (h : b₁.get = b₂.get) (logNSteps : Nat) :
    ParseResult.BufEquiv (parse init hsafe b₁ logNSteps) (parse init hsafe b₂ logNSteps) := by
  have H := parseFix_congr init hsafe [] h logNSteps (initStackInvariant init)
  unfold parse
  cases h₁ : (parseFix init hsafe [] b₁ logNSteps (initStackInvariant init)).1 <;>
    cases h₂ : (parseFix init hsafe [] b₂ logNSteps (initStackInvariant init)).1 <;>
    rw [h₁, h₂] at H <;>
    first
      | exact H
      | exact H.elim
      | trivial

end LeanMenhir
