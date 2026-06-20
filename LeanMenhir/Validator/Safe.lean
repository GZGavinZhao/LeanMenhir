/-
Port of `coq-menhirlib`'s `Validator_safe.v` to Lean 4.

Original: Copyright Inria and CNRS, LGPL-3.0-or-later.
This Lean port is a derivative work, distributed under LGPL-3.0-or-later.

The safety validator: definitions of the automaton invariants (`shiftHeadSymbs`,
`gotoHeadSymbs`, …, `reduceOk`, bundled as `safe`), the boolean validator
`isSafe`, and the proof that `isSafe () = true → safe`. Soundness of the
interpreter holds whenever this validator accepts the tables.
-/
import LeanMenhir.Automaton
import LeanMenhir.Validator.Classes

namespace LeanMenhir

/-! ### Prefix of symbol lists (generic) -/

/-- `Prefix l₁ l₂` : `l₁` is a prefix of `l₂` (Coq `prefix`). -/
inductive Prefix {σ : Type} : List σ → List σ → Prop
  | nil (l : List σ) : Prefix [] l
  | cons {l1 l2 : List σ} (x : σ) : Prefix l1 l2 → Prefix (x :: l1) (x :: l2)

theorem Prefix.inv_cons {σ : Type} {x y : σ} {l1 l2 : List σ}
    (h : Prefix (x :: l1) (y :: l2)) : x = y ∧ Prefix l1 l2 := by
  cases h with
  | cons _ h' => exact ⟨rfl, h'⟩

theorem Prefix.trans {σ : Type} {l1 l2 l3 : List σ}
    (h1 : Prefix l1 l2) (h2 : Prefix l2 l3) : Prefix l1 l3 := by
  induction h1 generalizing l3 with
  | nil => exact Prefix.nil l3
  | cons x _ ih => cases h2 with
    | cons _ h2' => exact Prefix.cons x (ih h2')

/-- Boolean prefix test (Coq `is_prefix`). -/
def isPrefix {σ : Type} [Comparable σ] : List σ → List σ → Bool
  | [], _ => true
  | t1 :: q1, t2 :: q2 => compareEqb t1 t2 && isPrefix q1 q2
  | _ :: _, [] => false

theorem isPrefix_correct {σ : Type} [Comparable σ] [ComparableLeibnizEq σ] :
    ∀ l1 l2 : List σ, isPrefix l1 l2 = true → Prefix l1 l2
  | [], l2, _ => Prefix.nil l2
  | _ :: _, [], h => by simp [isPrefix] at h
  | t1 :: q1, t2 :: q2, h => by
    simp only [isPrefix, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rw [compareEqb_iff] at h1
    subst h1
    exact Prefix.cons t1 (isPrefix_correct q1 q2 h2)

/-! ### Prefix of predicate lists (generic) -/

/-- Boolean implication. -/
def implb (a b : Bool) : Bool := !a || b

theorem implb_eq_true {a b : Bool} : implb a b = true ↔ (a = true → b = true) := by
  cases a <;> cases b <;> simp [implb]

theorem implb_self (a : Bool) : implb a a = true := by cases a <;> rfl

/-- A "prefix" relation on predicate lists: each predicate of `l₂` entails the
corresponding predicate of `l₁` (Coq `prefix_pred`). -/
inductive PrefixPred {st : Type} : List (st → Bool) → List (st → Bool) → Prop
  | nil (l : List (st → Bool)) : PrefixPred [] l
  | cons {l1 l2 : List (st → Bool)} (f1 f2 : st → Bool) :
      (∀ x, implb (f2 x) (f1 x) = true) → PrefixPred l1 l2 →
      PrefixPred (f1 :: l1) (f2 :: l2)

theorem PrefixPred.trans {st : Type} {l1 l2 l3 : List (st → Bool)}
    (h1 : PrefixPred l1 l2) (h2 : PrefixPred l2 l3) : PrefixPred l1 l3 := by
  induction h1 generalizing l3 with
  | nil => exact PrefixPred.nil l3
  | cons f1 f2 hf2f1 _ ih => cases h2 with
    | cons _ f3 hf3f2 h2' =>
      refine PrefixPred.cons f1 f3 (fun x => ?_) (ih h2')
      have a := hf2f1 x; have b := hf3f2 x
      revert a b; cases f1 x <;> cases f2 x <;> cases f3 x <;> simp [implb]

theorem PrefixPred.inv_cons {st : Type} {f1 f2 : st → Bool} {l1 l2 : List (st → Bool)}
    (h : PrefixPred (f1 :: l1) (f2 :: l2)) :
    (∀ x, implb (f2 x) (f1 x) = true) ∧ PrefixPred l1 l2 := by
  cases h with
  | cons _ _ himpl h' => exact ⟨himpl, h'⟩

variable [A : Automaton]

/-! ### State annotations -/

/-- The singleton predicate for states (Coq `singleton_state_pred`). -/
def singletonStatePred (s : A.State) : A.State → Bool := fun s' => compareEqb s s'

theorem singletonStatePred_self (s : A.State) : singletonStatePred s s = true :=
  compareEqb_refl s

/-- `past_state_of_non_init_state`, extended to all states (Coq
`past_state_of_state`). -/
def pastStateOfState : A.State → List (A.State → Bool)
  | .Init _ => []
  | .Ninit nis => A.past_state_of_non_init_state nis

/-- The known top symbols of a state: its last symbol then its past symbols
(Coq `head_symbs_of_state`). -/
def headSymbsOfState : A.State → List (Symbol A.Terminal A.Nonterminal)
  | .Init _ => []
  | .Ninit s => A.last_symb_of_non_init_state s :: A.past_symb_of_non_init_state s

/-- The known states below the top (Coq `head_states_of_state`). -/
def headStatesOfState (s : A.State) : List (A.State → Bool) :=
  singletonStatePred s :: pastStateOfState s

/-- Boolean predicate-prefix test (Coq `is_prefix_pred`). -/
def isPrefixPred : List (A.State → Bool) → List (A.State → Bool) → Bool
  | [], _ => true
  | f1 :: q1, f2 :: q2 =>
      Allb A.State (fun x => implb (f2 x) (f1 x)) && isPrefixPred q1 q2
  | _ :: _, [] => false

theorem isPrefixPred_correct :
    ∀ l1 l2 : List (A.State → Bool), isPrefixPred l1 l2 = true → PrefixPred l1 l2
  | [], l2, _ => PrefixPred.nil l2
  | _ :: _, [], h => by simp [isPrefixPred] at h
  | f1 :: q1, f2 :: q2, h => by
    simp only [isPrefixPred, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    refine PrefixPred.cons f1 f2 (fun x => ?_) (isPrefixPred_correct q1 q2 h2)
    exact forall_of_Allb (fun x hx => hx) h1 x

/-! ### State valid after pop -/

/-- The states possible after popping the given symbols, given the state's
annotation (Coq `state_valid_after_pop`). -/
inductive StateValidAfterPop (s : A.State) :
    List (Symbol A.Terminal A.Nonterminal) → List (A.State → Bool) → Prop
  | nil1 (p : A.State → Bool) (pl) : p s = true → StateValidAfterPop s [] (p :: pl)
  | nil2 (sl) : StateValidAfterPop s sl []
  | cons (st sq p pl) : StateValidAfterPop s sq pl →
      StateValidAfterPop s (st :: sq) (p :: pl)

/-- Boolean test for `StateValidAfterPop` (Coq `is_state_valid_after_pop`). -/
def isStateValidAfterPop (s : A.State) (toPop : List (Symbol A.Terminal A.Nonterminal))
    (annot : List (A.State → Bool)) : Bool :=
  match annot, toPop with
  | [], _ => true
  | p :: _, [] => p s
  | _ :: pl, _ :: sl => isStateValidAfterPop s sl pl

theorem isStateValidAfterPop_complete {s : A.State} {sl pl}
    (h : StateValidAfterPop s sl pl) : isStateValidAfterPop s sl pl = true := by
  induction h with
  | nil1 p pl hp => simp [isStateValidAfterPop, hp]
  | nil2 sl => simp [isStateValidAfterPop]
  | cons st sq p pl _ ih => simp [isStateValidAfterPop, ih]

/-! ### The safety invariants -/

/-- If we shift, the destination's past symbols prefix the source's head symbols
(Coq `shift_head_symbs`). -/
def shiftHeadSymbs : Prop :=
  ∀ s, match A.action_table s with
    | .Lookahead_act awp => ∀ t, match awp t with
        | .Shift_act s2 _ =>
            Prefix (A.past_symb_of_non_init_state s2) (headSymbsOfState s)
        | _ => True
    | _ => True

/-- Same, for gotos (Coq `goto_head_symbs`). -/
def gotoHeadSymbs : Prop :=
  ∀ s nt, match A.goto_table s nt with
    | some ⟨s2, _⟩ => Prefix (A.past_symb_of_non_init_state s2) (headSymbsOfState s)
    | none => True

/-- The state-stack assumptions are preserved by shift (Coq `shift_past_state`). -/
def shiftPastState : Prop :=
  ∀ s, match A.action_table s with
    | .Lookahead_act awp => ∀ t, match awp t with
        | .Shift_act s2 _ =>
            PrefixPred (A.past_state_of_non_init_state s2) (headStatesOfState s)
        | _ => True
    | _ => True

/-- Same, for gotos (Coq `goto_past_state`). -/
def gotoPastState : Prop :=
  ∀ s nt, match A.goto_table s nt with
    | some ⟨s2, _⟩ => PrefixPred (A.past_state_of_non_init_state s2) (headStatesOfState s)
    | none => True

/-- A state is valid for reducing a production (Coq `valid_for_reduce`). -/
def validForReduce (s : A.State) (prod : A.Production) : Prop :=
  Prefix (A.prod_rhs_rev prod) (headSymbsOfState s) ∧
  ∀ stateNew, StateValidAfterPop stateNew (A.prod_rhs_rev prod) (headStatesOfState s) →
    match A.goto_table stateNew (A.prod_lhs prod) with
    | none => match stateNew with
        | .Init i => A.prod_lhs prod = A.start_nt i
        | .Ninit _ => False
    | some _ => True

/-- Every state that reduces is valid for reduction (Coq `reduce_ok`). -/
def reduceOk : Prop :=
  ∀ s, match A.action_table s with
    | .Lookahead_act awp => ∀ t, match awp t with
        | .Reduce_act p => validForReduce s p
        | _ => True
    | .Default_reduce_act p => validForReduce s p

/-- The automaton is safe (Coq `safe`). -/
def safe : Prop :=
  shiftHeadSymbs ∧ gotoHeadSymbs ∧ shiftPastState ∧ gotoPastState ∧ reduceOk

theorem shiftHeadSymbs_of_safe (h : safe) : shiftHeadSymbs := h.1
theorem gotoHeadSymbs_of_safe (h : safe) : gotoHeadSymbs := h.2.1
theorem shiftPastState_of_safe (h : safe) : shiftPastState := h.2.2.1
theorem gotoPastState_of_safe (h : safe) : gotoPastState := h.2.2.2.1
theorem reduceOk_of_safe (h : safe) : reduceOk := h.2.2.2.2

/-! ### The boolean validator -/

/-- Boolean test for `validForReduce`. -/
def isValidForReduce (s : A.State) (prod : A.Production) : Bool :=
  isPrefix (A.prod_rhs_rev prod) (headSymbsOfState s) &&
  Allb A.State (fun stateNew =>
    if isStateValidAfterPop stateNew (A.prod_rhs_rev prod) (headStatesOfState s) then
      match A.goto_table stateNew (A.prod_lhs prod) with
      | none => match stateNew with
          | .Init i => compareEqb (A.prod_lhs prod) (A.start_nt i)
          | .Ninit _ => false
      | some _ => true
    else true)

theorem isValidForReduce_correct (s : A.State) (prod : A.Production) :
    isValidForReduce s prod = true → validForReduce s prod := by
  intro h
  simp only [isValidForReduce, Bool.and_eq_true] at h
  obtain ⟨hpref, hall⟩ := h
  refine ⟨isPrefix_correct _ _ hpref, ?_⟩
  intro stateNew hvalid
  have hsv : isStateValidAfterPop stateNew (A.prod_rhs_rev prod) (headStatesOfState s) = true :=
    isStateValidAfterPop_complete hvalid
  have key := forall_of_Allb (f := fun stateNew =>
      if isStateValidAfterPop stateNew (A.prod_rhs_rev prod) (headStatesOfState s) then
        match A.goto_table stateNew (A.prod_lhs prod) with
        | none => match stateNew with
            | .Init i => compareEqb (A.prod_lhs prod) (A.start_nt i)
            | .Ninit _ => false
        | some _ => true
      else true)
    (P := fun stateNew => _) (fun x hx => hx) hall stateNew
  simp only [hsv, if_true] at key
  revert key
  cases hg : A.goto_table stateNew (A.prod_lhs prod) with
  | some v => intro _; trivial
  | none =>
    cases stateNew with
    | Init i => intro hk; exact (compareEqb_iff _ _).1 hk
    | Ninit n => intro hk; exact absurd hk (by simp)

/-- Boolean validator for `shiftHeadSymbs`. -/
def isShiftHeadSymbs : Bool :=
  Allb A.State (fun s => match A.action_table s with
    | .Lookahead_act awp => Allb A.Terminal (fun t => match awp t with
        | .Shift_act s2 _ => isPrefix (A.past_symb_of_non_init_state s2) (headSymbsOfState s)
        | _ => true)
    | _ => true)

theorem isShiftHeadSymbs_correct : isShiftHeadSymbs = true → shiftHeadSymbs := by
  intro h
  refine forall_of_Allb (P := fun s => _) (fun s hs => ?_) h
  revert hs
  cases A.action_table s with
  | Default_reduce_act p => intro _; trivial
  | Lookahead_act awp =>
    intro hs
    refine forall_of_Allb (P := fun t => _) (fun t ht => ?_) hs
    revert ht
    cases awp t with
    | Shift_act s2 e => intro ht; exact isPrefix_correct _ _ ht
    | Reduce_act p => intro _; trivial
    | Fail_act => intro _; trivial

/-- Boolean validator for `gotoHeadSymbs`. -/
def isGotoHeadSymbs : Bool :=
  Allb A.State (fun s => Allb A.Nonterminal (fun nt =>
    match A.goto_table s nt with
    | some ⟨s2, _⟩ => isPrefix (A.past_symb_of_non_init_state s2) (headSymbsOfState s)
    | none => true))

theorem isGotoHeadSymbs_correct : isGotoHeadSymbs = true → gotoHeadSymbs := by
  intro h
  refine forall_of_Allb (P := fun s => _) (fun s hs => ?_) h
  refine forall_of_Allb (P := fun nt => _) (fun nt hnt => ?_) hs
  revert hnt
  cases hg : A.goto_table s nt with
  | none => intro _; trivial
  | some v => obtain ⟨s2, e⟩ := v; intro hnt; exact isPrefix_correct _ _ hnt

/-- Boolean validator for `shiftPastState`. -/
def isShiftPastState : Bool :=
  Allb A.State (fun s => match A.action_table s with
    | .Lookahead_act awp => Allb A.Terminal (fun t => match awp t with
        | .Shift_act s2 _ =>
            isPrefixPred (A.past_state_of_non_init_state s2) (headStatesOfState s)
        | _ => true)
    | _ => true)

theorem isShiftPastState_correct : isShiftPastState = true → shiftPastState := by
  intro h
  refine forall_of_Allb (P := fun s => _) (fun s hs => ?_) h
  revert hs
  cases A.action_table s with
  | Default_reduce_act p => intro _; trivial
  | Lookahead_act awp =>
    intro hs
    refine forall_of_Allb (P := fun t => _) (fun t ht => ?_) hs
    revert ht
    cases awp t with
    | Shift_act s2 e => intro ht; exact isPrefixPred_correct _ _ ht
    | Reduce_act p => intro _; trivial
    | Fail_act => intro _; trivial

/-- Boolean validator for `gotoPastState`. -/
def isGotoPastState : Bool :=
  Allb A.State (fun s => Allb A.Nonterminal (fun nt =>
    match A.goto_table s nt with
    | some ⟨s2, _⟩ => isPrefixPred (A.past_state_of_non_init_state s2) (headStatesOfState s)
    | none => true))

theorem isGotoPastState_correct : isGotoPastState = true → gotoPastState := by
  intro h
  refine forall_of_Allb (P := fun s => _) (fun s hs => ?_) h
  refine forall_of_Allb (P := fun nt => _) (fun nt hnt => ?_) hs
  revert hnt
  cases hg : A.goto_table s nt with
  | none => intro _; trivial
  | some v => obtain ⟨s2, e⟩ := v; intro hnt; exact isPrefixPred_correct _ _ hnt

/-- Boolean validator for `reduceOk`. -/
def isReduceOk : Bool :=
  Allb A.State (fun s => match A.action_table s with
    | .Default_reduce_act p => isValidForReduce s p
    | .Lookahead_act awp => Allb A.Terminal (fun t => match awp t with
        | .Reduce_act p => isValidForReduce s p
        | _ => true))

theorem isReduceOk_correct : isReduceOk = true → reduceOk := by
  intro h
  refine forall_of_Allb (P := fun s => _) (fun s hs => ?_) h
  revert hs
  cases A.action_table s with
  | Default_reduce_act p => intro hs; exact isValidForReduce_correct _ _ hs
  | Lookahead_act awp =>
    intro hs
    refine forall_of_Allb (P := fun t => _) (fun t ht => ?_) hs
    revert ht
    cases awp t with
    | Shift_act s2 e => intro _; trivial
    | Reduce_act p => intro ht; exact isValidForReduce_correct _ _ ht
    | Fail_act => intro _; trivial

/-- The boolean safety validator (Coq `is_safe`). -/
def isSafe (_ : Unit) : Bool :=
  isShiftHeadSymbs && isGotoHeadSymbs && isShiftPastState && isGotoPastState && isReduceOk

/-- The validator is correct: if `isSafe () = true`, the automaton is `safe`
(Coq `safe_is_validator`). -/
theorem safe_is_validator : isSafe () = true → safe := by
  intro h
  simp only [isSafe, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨isShiftHeadSymbs_correct h1, isGotoHeadSymbs_correct h2,
    isShiftPastState_correct h3, isGotoPastState_correct h4, isReduceOk_correct h5⟩

end LeanMenhir
