/-
Port of `coq-menhirlib`'s `Interpreter.v` to Lean 4.

Original: Copyright Inria and CNRS, LGPL-3.0-or-later.
This Lean port is a derivative work, distributed under LGPL-3.0-or-later.

The LR(1) parser interpreter: the automaton stack, the `pop`/`reduceStep`/`step`
operations, and the fuel-based `parse` loop, together with the stack invariant
preserved by each step. The interpreter is parameterised by a proof `hsafe :
safe` that the safety validator accepts the tables.

Unlike the Coq version, equality proofs are carried directly (Lean erases `Prop`,
so casts are runtime no-ops and the proofs cannot block computation).
-/
import LeanMenhir.Validator.Safe
import Mathlib.Data.Stream.Init

namespace LeanMenhir

variable [A : Automaton]

/-! ### Input buffers -/

/-- The input is an infinite stream of tokens (Coq's coinductive `buffer`). -/
abbrev Buffer : Type := Stream' A.Token

/-! ### The automaton stack -/

/-- The semantic-value type associated with a non-initial state: the value of its
last symbol (Coq `noninitstate_type`). -/
def noninitstateType (s : A.NonInitState) : Type :=
  A.symbol_semantic_type (A.last_symb_of_non_init_state s)

/-- The automaton stack: non-initial states paired with a semantic value for
their last symbol (Coq `stack`). -/
def Stack : Type := List ((s : A.NonInitState) × noninitstateType s)

/-- The symbols recorded on a stack (Coq `symb_stack_of_stack`). -/
def symbStackOfStack (stk : Stack) : List (Symbol A.Terminal A.Nonterminal) :=
  stk.map (fun cell => A.last_symb_of_non_init_state cell.1)

/-! ### `pop` -/

/-- `pop` pops `symbolsToPop` symbols off the stack, threading the popped semantic
values into `action` and discarding the popped states (Coq `pop`). It requires a
proof that the symbols form a prefix of the stack. -/
def pop {R : Type} :
    (symbolsToPop : List (Symbol A.Terminal A.Nonterminal)) → (stk : Stack) →
    Prefix symbolsToPop (symbStackOfStack stk) →
    arrowsRight R (symbolsToPop.map A.symbol_semantic_type) →
    Stack × R
  | [], stk, _, action => (stk, action)
  | t :: q, ⟨stateCur, sem⟩ :: stackRec, hp, action =>
      let e : t = A.last_symb_of_non_init_state stateCur := (Prefix.inv_cons hp).1
      let hp' : Prefix q (symbStackOfStack stackRec) := (Prefix.inv_cons hp).2
      let semConv : A.symbol_semantic_type t :=
        cast (congrArg A.symbol_semantic_type e.symm) sem
      pop q stackRec hp' (action semConv)
  | _ :: _, [], hp, _ => nomatch hp

/-- Declarative specification of `pop`, avoiding the dependent-type reasoning
(Coq `pop_spec`). -/
inductive PopSpec {R : Type} : (symbolsToPop : List (Symbol A.Terminal A.Nonterminal)) →
    Stack → arrowsRight R (symbolsToPop.map A.symbol_semantic_type) → Stack → R → Prop
  | nil (stk : Stack) (sem : R) : PopSpec [] stk sem stk sem
  | cons {symbolsToPop : List (Symbol A.Terminal A.Nonterminal)} (st : A.NonInitState)
      (stk : Stack)
      (action : arrowsRight R
        ((A.last_symb_of_non_init_state st :: symbolsToPop).map A.symbol_semantic_type))
      (sem : noninitstateType st) (stk' : Stack) (res : R) :
      PopSpec symbolsToPop stk (action sem) stk' res →
      PopSpec (A.last_symb_of_non_init_state st :: symbolsToPop) (⟨st, sem⟩ :: stk) action stk' res

/-- The dependent `pop` agrees with its declarative spec (Coq `pop_spec_ok`,
forward direction, which is what soundness needs). -/
theorem pop_spec_ok {R : Type} :
    ∀ (symbolsToPop : List (Symbol A.Terminal A.Nonterminal)) (stk : Stack)
      (hp : Prefix symbolsToPop (symbStackOfStack stk))
      (action : arrowsRight R (symbolsToPop.map A.symbol_semantic_type)) (stk' : Stack) (res : R),
      pop symbolsToPop stk hp action = (stk', res) → PopSpec symbolsToPop stk action stk' res := by
  intro symbolsToPop
  induction symbolsToPop with
  | nil =>
    intro stk hp action stk' res heq
    rw [pop] at heq
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ heq
    exact PopSpec.nil _ _
  | cons t q ih =>
    intro stk hp action stk' res heq
    cases stk with
    | nil => exact (nomatch hp)
    | cons cell stackRec =>
      obtain ⟨st, sem⟩ := cell
      obtain ⟨e, hp'⟩ := Prefix.inv_cons hp
      subst e
      rw [pop] at heq
      have hcast : cast (congrArg A.symbol_semantic_type (Prefix.inv_cons hp).1.symm) sem = sem :=
        eq_of_heq (cast_heq _ _)
      rw [hcast] at heq
      exact PopSpec.cons st stackRec action sem stk' res (ih stackRec _ _ stk' res heq)

/-! ### Stack state helpers and the stack invariant -/

variable (init : A.InitState)

/-- The top state of a stack (Coq `state_of_stack`). -/
def stateOfStack (stk : Stack) : A.State :=
  match stk with
  | [] => .Init init
  | ⟨s, _⟩ :: _ => .Ninit s

/-- The stack of state-predicates of a stack (Coq `state_stack_of_stack`). -/
def stateStackOfStack (stk : Stack) : List (A.State → Bool) :=
  stk.map (fun cell => singletonStatePred (.Ninit cell.1)) ++ [singletonStatePred (.Init init)]

/- The stack invariant: the recorded symbol/state assumptions hold all the way
down the stack (Coq `stack_invariant` / `stack_invariant_next`). -/
mutual
inductive StackInvariant : Stack → Prop
  | mk (stk : Stack) :
      Prefix (headSymbsOfState (stateOfStack init stk)) (symbStackOfStack stk) →
      PrefixPred (headStatesOfState (stateOfStack init stk)) (stateStackOfStack init stk) →
      StackInvariantNext stk → StackInvariant stk
inductive StackInvariantNext : Stack → Prop
  | nil : StackInvariantNext []
  | cons (stateCur : A.NonInitState) (st : noninitstateType stateCur) (stackRec : Stack) :
      StackInvariant stackRec → StackInvariantNext (⟨stateCur, st⟩ :: stackRec)
end

theorem StackInvariant.symb_prefix {stk} (Hi : StackInvariant init stk) :
    Prefix (headSymbsOfState (stateOfStack init stk)) (symbStackOfStack stk) := by
  cases Hi with | mk _ h _ _ => exact h

theorem StackInvariant.state_prefix {stk} (Hi : StackInvariant init stk) :
    PrefixPred (headStatesOfState (stateOfStack init stk)) (stateStackOfStack init stk) := by
  cases Hi with | mk _ _ h _ => exact h

theorem StackInvariant.next {stk} (Hi : StackInvariant init stk) : StackInvariantNext init stk := by
  cases Hi with | mk _ _ _ h => exact h

/-- The state-predicate stack always begins with the singleton predicate of the
top state. -/
theorem stateStackOfStack_cons_form (stk : Stack) :
    stateStackOfStack init stk =
      singletonStatePred (stateOfStack init stk) ::
        (match stk with | [] => [] | _ :: rec => stateStackOfStack init rec) := by
  cases stk with
  | nil => rfl
  | cons cell rec => obtain ⟨s, sem⟩ := cell; simp [stateStackOfStack, stateOfStack]

/-- `pop` preserves the stack invariant (Coq `pop_preserves_invariant`). -/
theorem pop_preserves_invariant {R : Type} :
    ∀ (symbolsToPop : List (Symbol A.Terminal A.Nonterminal)) (stk : Stack)
      (hp : Prefix symbolsToPop (symbStackOfStack stk))
      (action : arrowsRight R (symbolsToPop.map A.symbol_semantic_type)),
      StackInvariant init stk → StackInvariant init (pop symbolsToPop stk hp action).1 := by
  intro symbolsToPop
  induction symbolsToPop with
  | nil => intro stk hp action Hi; exact Hi
  | cons t q ih =>
    intro stk hp action Hi
    cases stk with
    | nil => exact (nomatch hp)
    | cons cell stackRec =>
      obtain ⟨st, sem⟩ := cell
      have hrec : StackInvariant init stackRec := by
        cases Hi.next with | cons _ _ _ h => exact h
      exact ih stackRec _ _ hrec

/-- After popping, the resulting top state is valid for the popped symbols
(Coq `pop_state_valid`). -/
theorem pop_state_valid {R : Type} :
    ∀ (symbolsToPop : List (Symbol A.Terminal A.Nonterminal)) (stk : Stack)
      (hp : Prefix symbolsToPop (symbStackOfStack stk))
      (action : arrowsRight R (symbolsToPop.map A.symbol_semantic_type))
      (lpred : List (A.State → Bool)) (hpp : PrefixPred lpred (stateStackOfStack init stk)),
      StateValidAfterPop (stateOfStack init (pop symbolsToPop stk hp action).1) symbolsToPop lpred := by
  intro symbolsToPop
  induction symbolsToPop with
  | nil =>
    intro stk hp action lpred hpp
    show StateValidAfterPop (stateOfStack init stk) [] lpred
    cases lpred with
    | nil => exact StateValidAfterPop.nil2 []
    | cons pred lpred' =>
      apply StateValidAfterPop.nil1
      rw [stateStackOfStack_cons_form] at hpp
      have himpl := (PrefixPred.inv_cons hpp).1 (stateOfStack init stk)
      rw [singletonStatePred_self] at himpl
      simpa [implb] using himpl
  | cons t q ih =>
    intro stk hp action lpred hpp
    cases stk with
    | nil => exact (nomatch hp)
    | cons cell stackRec =>
      obtain ⟨st, sem⟩ := cell
      cases lpred with
      | nil => exact StateValidAfterPop.nil2 (t :: q)
      | cons pred lpred' =>
        apply StateValidAfterPop.cons
        rw [stateStackOfStack_cons_form] at hpp
        exact ih stackRec _ _ lpred' (PrefixPred.inv_cons hpp).2

/-! ### Step results -/

/-- The result of one step: failure, acceptance with the final semantic value, or
progress with a new stack/buffer (Coq `step_result`). -/
inductive StepResult where
  | Fail : A.State → A.Token → StepResult
  | Accept : A.symbol_semantic_type (.NT (A.start_nt init)) → Buffer → StepResult
  | Progress : Stack → Buffer → StepResult

/-! ### `reduceStep` -/

/-- A reduce action: pop the RHS of `prod`, run its semantic action, then follow
the goto for the produced nonterminal (Coq `reduce_step`). -/
def reduceStep (stk : Stack) (prod : A.Production) (buffer : Buffer)
    (Hval : validForReduce (stateOfStack init stk) prod) (Hi : StackInvariant init stk) :
    StepResult init :=
  let hpref : Prefix (A.prod_rhs_rev prod) (symbStackOfStack stk) :=
    Prefix.trans Hval.1 (Hi.symb_prefix init)
  match hpop : pop (A.prod_rhs_rev prod) stk hpref (A.prod_action prod) with
  | (stk', sem) =>
    match hg : A.goto_table (stateOfStack init stk') (A.prod_lhs prod) with
    | some ⟨stateNew, e⟩ =>
        .Progress (⟨stateNew, cast (congrArg A.symbol_semantic_type e) sem⟩ :: stk') buffer
    | none =>
        let e2 : A.prod_lhs prod = A.start_nt init := by
          have hsv := pop_state_valid init (A.prod_rhs_rev prod) stk hpref (A.prod_action prod)
            (headStatesOfState (stateOfStack init stk)) (Hi.state_prefix init)
          rw [hpop] at hsv
          have hgoto := Hval.2 (stateOfStack init stk') hsv
          rw [hg] at hgoto
          cases stk' with
          | nil => exact hgoto
          | cons cell rec => exact hgoto.elim
        .Accept (cast (congrArg (fun nt => A.symbol_semantic_type (Symbol.NT nt)) e2) sem) buffer

/-- `reduceStep` preserves the stack invariant on `Progress`
(Coq `reduce_step_stack_invariant_preserved`). -/
theorem reduceStep_stack_invariant_preserved (hsafe : safe) (stk : Stack) (prod : A.Production)
    (buffer : Buffer) (Hval : validForReduce (stateOfStack init stk) prod)
    (Hi : StackInvariant init stk) (stk' : Stack) (buffer' : Buffer) :
    reduceStep init stk prod buffer Hval Hi = .Progress stk' buffer' → StackInvariant init stk' := by
  have Hi' := pop_preserves_invariant init (A.prod_rhs_rev prod) stk
    (Prefix.trans Hval.1 (Hi.symb_prefix init)) (A.prod_action prod) Hi
  have Hsv := pop_state_valid init (A.prod_rhs_rev prod) stk
    (Prefix.trans Hval.1 (Hi.symb_prefix init)) (A.prod_action prod)
    (headStatesOfState (stateOfStack init stk)) (Hi.state_prefix init)
  intro heq
  simp only [reduceStep] at heq
  split at heq
  · -- shift to a new state via goto
    rename_i sn e hgoto
    set stk0 := (pop (A.prod_rhs_rev prod) stk (Prefix.trans Hval.1 (Hi.symb_prefix init))
      (A.prod_action prod)).1 with hpop_eq
    injection heq with hstk _
    subst hstk
    have Hgoto1 := gotoHeadSymbs_of_safe hsafe (stateOfStack init stk0) (A.prod_lhs prod)
    have Hgoto2 := gotoPastState_of_safe hsafe (stateOfStack init stk0) (A.prod_lhs prod)
    rw [hgoto] at Hgoto1 Hgoto2
    refine StackInvariant.mk _ ?_ ?_ (StackInvariantNext.cons sn _ stk0 Hi')
    · exact Prefix.cons _ (Prefix.trans Hgoto1 (Hi'.symb_prefix init))
    · rw [stateStackOfStack_cons_form]
      exact PrefixPred.cons _ _ (fun x => implb_self _)
        (PrefixPred.trans Hgoto2 (Hi'.state_prefix init))
  · -- accept: cannot equal `Progress`
    simp at heq

/-! ### `step` -/

/-- One parsing step (Coq `step`). -/
def step (hsafe : safe) (stk : Stack) (buffer : Buffer) (Hi : StackInvariant init stk) :
    StepResult init :=
  match haction : A.action_table (stateOfStack init stk) with
  | .Default_reduce_act prod =>
      have Hv : validForReduce (stateOfStack init stk) prod := by
        have := (reduceOk_of_safe hsafe) (stateOfStack init stk)
        rw [haction] at this; exact this
      reduceStep init stk prod buffer Hv Hi
  | .Lookahead_act awt =>
      let tok := buffer.head
      match hawt : awt (A.token_term tok) with
      | .Shift_act stateNew e =>
          let semConv : noninitstateType stateNew :=
            cast (congrArg A.symbol_semantic_type e) (A.token_sem tok)
          .Progress (⟨stateNew, semConv⟩ :: stk) buffer.tail
      | .Reduce_act prod =>
          have Hv : validForReduce (stateOfStack init stk) prod := by
            have := (reduceOk_of_safe hsafe) (stateOfStack init stk)
            rw [haction] at this
            have := this (A.token_term tok)
            rw [hawt] at this; exact this
          reduceStep init stk prod buffer Hv Hi
      | .Fail_act => .Fail (stateOfStack init stk) tok

/-- `step` preserves the stack invariant on `Progress`
(Coq `step_stack_invariant_preserved`). -/
theorem step_stack_invariant_preserved (hsafe : safe) (stk : Stack) (buffer : Buffer)
    (Hi : StackInvariant init stk) (stk' : Stack) (buffer' : Buffer) :
    step init hsafe stk buffer Hi = .Progress stk' buffer' → StackInvariant init stk' := by
  intro heq
  simp only [step] at heq
  split at heq
  · -- Default_reduce_act
    exact reduceStep_stack_invariant_preserved init hsafe stk _ buffer _ Hi stk' buffer' heq
  · -- Lookahead_act
    rename_i awt hact
    split at heq
    · -- Shift_act: push the read token
      rename_i sn e hawt
      injection heq with hstk _
      subst hstk
      have Hshift1 := shiftHeadSymbs_of_safe hsafe (stateOfStack init stk)
      have Hshift2 := shiftPastState_of_safe hsafe (stateOfStack init stk)
      rw [hact] at Hshift1 Hshift2
      have H1 := Hshift1 (A.token_term buffer.head)
      have H2 := Hshift2 (A.token_term buffer.head)
      rw [hawt] at H1 H2
      refine StackInvariant.mk _ ?_ ?_ (StackInvariantNext.cons sn _ stk Hi)
      · exact Prefix.cons _ (Prefix.trans H1 (Hi.symb_prefix init))
      · rw [stateStackOfStack_cons_form]
        exact PrefixPred.cons _ _ (fun x => implb_self _)
          (PrefixPred.trans H2 (Hi.state_prefix init))
    · -- Reduce_act
      exact reduceStep_stack_invariant_preserved init hsafe stk _ buffer _ Hi stk' buffer' heq
    · -- Fail_act
      simp at heq

/-! ### The fuel-based parse loop -/

/-- The final parse result (Coq `parse_result`). -/
inductive ParseResult (R : Type) where
  | Fail : A.State → A.Token → ParseResult R
  | Timeout : ParseResult R
  | Parsed : R → Buffer → ParseResult R

/-- The parse loop, running `2 ^ logNSteps` steps (Coq `parse_fix`). -/
def parseFix (hsafe : safe) (stk : Stack) (buffer : Buffer) (logNSteps : Nat)
    (Hi : StackInvariant init stk) :
    { sr : StepResult init // ∀ stk' buffer', sr = .Progress stk' buffer' → StackInvariant init stk' } :=
  match logNSteps with
  | 0 => ⟨step init hsafe stk buffer Hi, step_stack_invariant_preserved init hsafe stk buffer Hi⟩
  | n + 1 =>
      match parseFix hsafe stk buffer n Hi with
      | ⟨.Progress stk2 buffer2, Hi'⟩ =>
          parseFix hsafe stk2 buffer2 n (Hi' stk2 buffer2 rfl)
      | ⟨sr, hsr⟩ => ⟨sr, hsr⟩

/-- The empty stack satisfies the stack invariant (Coq `parse_subproof`). -/
theorem initStackInvariant : StackInvariant init ([] : Stack) := by
  refine StackInvariant.mk [] ?_ ?_ StackInvariantNext.nil
  · exact Prefix.nil _
  · refine PrefixPred.cons _ _ (fun x => implb_self _) (PrefixPred.nil _)

/-- Run the parser (Coq `parse`). -/
def parse (hsafe : safe) (buffer : Buffer) (logNSteps : Nat) :
    ParseResult (A.symbol_semantic_type (.NT (A.start_nt init))) :=
  match (parseFix init hsafe [] buffer logNSteps (initStackInvariant init)).1 with
  | .Fail st tok => .Fail st tok
  | .Accept sem buffer' => .Parsed sem buffer'
  | .Progress _ _ => .Timeout

end LeanMenhir

