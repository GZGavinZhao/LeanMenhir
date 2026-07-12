/-
Port of `coq-menhirlib`'s `Validator_complete.v` to Lean 4.

Original: Copyright Inria and CNRS, LGPL-3.0-or-later.
This Lean port is a derivative work, distributed under LGPL-3.0-or-later.

The completeness validator: definitions of the automaton invariants needed for
completeness (`nullableStable`, `firstStable`, `startFuture`, `terminalShift`,
`endReduce`, `nonTerminalGoto`, `startGoto`, `nonTerminalClosed`, bundled as
`complete`), the boolean validator `isComplete`, and the proof that
`isComplete A = true → complete A`. Completeness of the interpreter holds whenever
this validator accepts the tables.

Unlike the Coq version, which uses `Derive` to synthesise the validator from an
`IsValidator` reflection class together with AVL `FSet`/`FMap` structures, we
define `state_has_future` directly over `items_of_state` (membership) and write
the boolean validator explicitly, mirroring `Validator/Safe.lean`. The
`Interpreter_complete` proof only uses the eight `complete` sub-properties
abstractly, so this representation choice is invisible there.
-/
import LeanMenhir.Automaton
import LeanMenhir.Validator.Classes
import LeanMenhir.Validator.Safe

namespace LeanMenhir

variable {G : Grammar} {A : Automaton G}

/-! ### Nullable / first sets (as lists) -/

/-- A symbol is nullable iff it is a nonterminal that can produce the empty
string (Coq `nullable_symb`). -/
def nullableSymb (A : Automaton G) (s : Symbol G.Terminal G.Nonterminal) : Bool :=
  match s with
  | .NT nt => A.nullable_nterm nt
  | .T _ => false

/-- A word (list of symbols) is nullable iff each of its symbols is
(Coq `nullable_word`). -/
def nullableWord (A : Automaton G) (w : List (Symbol G.Terminal G.Nonterminal)) : Bool :=
  w.all (nullableSymb A)

/-- The FIRST set of a nonterminal, as the automaton's `first_nterm` list
(Coq `first_nterm_set`). -/
def firstNtermSet (A : Automaton G) (nt : G.Nonterminal) : List G.Terminal :=
  A.first_nterm nt

/-- The FIRST set of a symbol (Coq `first_symb_set`). -/
def firstSymbSet (A : Automaton G) (s : Symbol G.Terminal G.Nonterminal) : List G.Terminal :=
  match s with
  | .NT nt => firstNtermSet A nt
  | .T t => [t]

/-- The FIRST set of a word (Coq `first_word_set`). -/
def firstWordSet (A : Automaton G) : List (Symbol G.Terminal G.Nonterminal) → List G.Terminal
  | [] => []
  | t :: q =>
    if nullableSymb A t then firstSymbSet A t ++ firstWordSet A q
    else firstSymbSet A t

/-! ### Items and futures -/

/-- The portion of production `prod`'s RHS that comes after `dotPos` symbols
(Coq `future_of_prod`). Coq's hand-rolled `loop` is exactly `List.drop`. -/
def futureOfProd (prod : G.Production) (dotPos : Nat) :
    List (Symbol G.Terminal G.Nonterminal) :=
  (G.prod_rhs_rev prod).reverse.drop dotPos

/-- The lookahead set recorded for the item `(state, prod, dotPos)`: the union of
the lookaheads of all items of `state` with that core (Coq `find_items_map`
applied to `items_map ()`). -/
def findItemsMap (s : A.State) (prod : G.Production) (dotPos : Nat) : List G.Terminal :=
  (A.items_of_state s).flatMap (fun it =>
    if it.prod_item = prod ∧ it.dot_pos_item = dotPos then it.lookaheads_item else [])

/-- `state` predicts that production `prod` has `fut` after the dot, with
`lookahead` as a valid lookahead (Coq `state_has_future`). -/
def stateHasFuture (s : A.State) (prod : G.Production)
    (fut : List (Symbol G.Terminal G.Nonterminal)) (lookahead : G.Terminal) : Prop :=
  ∃ dotPos : Nat,
    fut = futureOfProd prod dotPos ∧ lookahead ∈ findItemsMap s prod dotPos

/-! ### The completeness invariants -/

/-- The nullable predicate is a fixpoint (Coq `nullable_stable`). -/
def nullableStable (A : Automaton G) : Prop :=
  ∀ p : G.Production,
    if nullableWord A (G.prod_rhs_rev p) then A.nullable_nterm (G.prod_lhs p) = true else True

/-- The first predicate is a fixpoint (Coq `first_stable`). -/
def firstStable (A : Automaton G) : Prop :=
  ∀ p : G.Production, ∀ t : G.Terminal,
    t ∈ firstWordSet A ((G.prod_rhs_rev p).reverse) → t ∈ firstNtermSet A (G.prod_lhs p)

/-- The initial state has all the `S → .u` items (Coq `start_future`). -/
def startFuture (A : Automaton G) : Prop :=
  ∀ (init : A.InitState) (p : G.Production), G.prod_lhs p = A.start_nt init →
    ∀ t : G.Terminal,
      stateHasFuture (.Init init) p (futureOfProd p 0) t

/-- Reading a terminal `a` from an item `A → _.av[[b]]` shifts to a state with
item `A → _.v[[b]]` (Coq `terminal_shift`). -/
def terminalShift (A : Automaton G) : Prop :=
  ∀ (s1 : A.State) (prod : G.Production) (fut) (lookahead : G.Terminal),
    stateHasFuture s1 prod fut lookahead →
    match fut with
    | .T t :: q =>
      match A.action_table s1 with
      | .Lookahead_act awp =>
        match awp t with
        | .Shift_act s2 _ => stateHasFuture (.Ninit s2) prod q lookahead
        | _ => False
      | _ => False
    | _ => True

/-- An item `A → _.[[a]]` either default-reduces, or reduces on reading `a`
(Coq `end_reduce`). -/
def endReduce (A : Automaton G) : Prop :=
  ∀ (s : A.State) (prod : G.Production) (fut) (lookahead : G.Terminal),
    stateHasFuture s prod fut lookahead →
    match fut with
    | [] =>
      match A.action_table s with
      | .Default_reduce_act p => p = prod
      | .Lookahead_act awt =>
        match awt lookahead with
        | .Reduce_act p => p = prod
        | _ => False
    | _ => True

/-- From item `A → _.Bv[[b]]`, the goto table goes to a state with item
`A → _.v[[b]]` (Coq `non_terminal_goto`). -/
def nonTerminalGoto (A : Automaton G) : Prop :=
  ∀ (s1 : A.State) (prod : G.Production) (fut) (lookahead : G.Terminal),
    stateHasFuture s1 prod fut lookahead →
    match fut with
    | .NT nt :: q =>
      match A.goto_table s1 nt with
      | some ⟨s2, _⟩ => stateHasFuture (.Ninit s2) prod q lookahead
      | none => False
    | _ => True

/-- The initial state has no goto on its own start nonterminal
(Coq `start_goto`). -/
def startGoto (A : Automaton G) : Prop :=
  ∀ init : A.InitState,
    match A.goto_table (.Init init) (A.start_nt init) with
    | none => True
    | some _ => False

/-- Closure property: from item `A → _.Bv[[b]]`, for each production `B → u` and
each `a ∈ first(vb)`, the state has item `B → _.u[[a]]` (Coq
`non_terminal_closed`). -/
def nonTerminalClosed (A : Automaton G) : Prop :=
  ∀ (s1 : A.State) (prod : G.Production) (fut) (lookahead : G.Terminal),
    stateHasFuture s1 prod fut lookahead →
    match fut with
    | .NT nt :: q =>
      ∀ p : G.Production, G.prod_lhs p = nt →
        (if nullableWord A q then stateHasFuture s1 p (futureOfProd p 0) lookahead else True) ∧
        (∀ lookahead2 : G.Terminal,
          lookahead2 ∈ firstWordSet A q → stateHasFuture s1 p (futureOfProd p 0) lookahead2)
    | _ => True

/-- The automaton is complete (Coq `complete`). -/
def complete (A : Automaton G) : Prop :=
  nullableStable A ∧ firstStable A ∧ startFuture A ∧ terminalShift A
  ∧ endReduce A ∧ nonTerminalGoto A ∧ startGoto A ∧ nonTerminalClosed A

theorem nullableStable_of_complete (h : complete A) : nullableStable A := h.1
theorem firstStable_of_complete (h : complete A) : firstStable A := h.2.1
theorem startFuture_of_complete (h : complete A) : startFuture A := h.2.2.1
theorem terminalShift_of_complete (h : complete A) : terminalShift A := h.2.2.2.1
theorem endReduce_of_complete (h : complete A) : endReduce A := h.2.2.2.2.1
theorem nonTerminalGoto_of_complete (h : complete A) : nonTerminalGoto A := h.2.2.2.2.2.1
theorem startGoto_of_complete (h : complete A) : startGoto A := h.2.2.2.2.2.2.1
theorem nonTerminalClosed_of_complete (h : complete A) : nonTerminalClosed A := h.2.2.2.2.2.2.2

/-! ### Helper lemmas -/

/-- Membership in `findItemsMap` comes from a witnessing item. -/
theorem mem_findItemsMap {s : A.State} {prod : G.Production} {dotPos : Nat}
    {look : G.Terminal} (h : look ∈ findItemsMap s prod dotPos) :
    ∃ it ∈ A.items_of_state s,
      it.prod_item = prod ∧ it.dot_pos_item = dotPos ∧ look ∈ it.lookaheads_item := by
  unfold findItemsMap at h
  rw [List.mem_flatMap] at h
  obtain ⟨it, hit, hlook⟩ := h
  refine ⟨it, hit, ?_⟩
  by_cases hc : it.prod_item = prod ∧ it.dot_pos_item = dotPos
  · simp only [hc] at hlook; exact ⟨hc.1, hc.2, hlook⟩
  · simp only [hc, if_false, List.not_mem_nil] at hlook

/-- Membership in a lookahead set yields a `stateHasFuture`. -/
theorem stateHasFuture_of_mem {s : A.State} {prod : G.Production} {dotPos : Nat}
    {look : G.Terminal} (h : look ∈ findItemsMap s prod dotPos) :
    stateHasFuture s prod (futureOfProd prod dotPos) look :=
  ⟨dotPos, rfl, h⟩

/-- Dropping one more symbol from a future. -/
theorem futureOfProd_succ {prod : G.Production} {pos : Nat}
    {x : Symbol G.Terminal G.Nonterminal} {q} (h : futureOfProd prod pos = x :: q) :
    futureOfProd prod (pos + 1) = q := by
  unfold futureOfProd at h ⊢
  rw [← List.drop_drop, h, List.drop_succ_cons, List.drop_zero]

/-! ### The "for all items" combinator -/

/-- Boolean iteration over every item (and every lookahead) of every state. -/
def allbItems (A : Automaton G)
    (b : A.State → G.Production → Nat → G.Terminal → Bool) : Bool :=
  Allb A.State (fun s =>
    (A.items_of_state s).all (fun it =>
      it.lookaheads_item.all (fun look => b s it.prod_item it.dot_pos_item look)))

theorem allbItems_correct
    {Q : A.State → G.Production → List (Symbol G.Terminal G.Nonterminal) → G.Terminal → Prop}
    {b : A.State → G.Production → Nat → G.Terminal → Bool}
    (hb : ∀ s prod pos look, b s prod pos look = true → Q s prod (futureOfProd prod pos) look)
    (hall : allbItems A b = true) :
    ∀ s prod fut look, stateHasFuture s prod fut look → Q s prod fut look := by
  intro s prod fut look hsf
  obtain ⟨dotPos, hfut, hmem⟩ := hsf
  obtain ⟨it, hit, hpi, hdp, hlook⟩ := mem_findItemsMap hmem
  subst hfut; subst hpi; subst hdp
  apply hb
  have hstate := forall_of_Allb (P := fun s =>
      (A.items_of_state s).all (fun it =>
        it.lookaheads_item.all (fun look => b s it.prod_item it.dot_pos_item look)) = true)
    (fun s hs => hs) hall s
  rw [List.all_eq_true] at hstate
  have hitall := hstate it hit
  rw [List.all_eq_true] at hitall
  exact hitall look hlook

/-! ### The eight boolean validators -/

/-- Boolean validator for `nullableStable`. -/
def isNullableStable (A : Automaton G) : Bool :=
  Allb G.Production (fun p => implb (nullableWord A (G.prod_rhs_rev p)) (A.nullable_nterm (G.prod_lhs p)))

theorem isNullableStable_correct : isNullableStable A = true → nullableStable A := by
  intro h
  refine forall_of_Allb (P := fun p => _) (fun p hp => ?_) h
  rw [implb_eq_true] at hp
  by_cases hc : nullableWord A (G.prod_rhs_rev p) = true
  · simp only [hc, if_true]; exact hp hc
  · simp only [Bool.not_eq_true] at hc; simp only [hc, Bool.false_eq_true, if_false]

/-- Boolean validator for `firstStable`. -/
def isFirstStable (A : Automaton G) : Bool :=
  Allb G.Production (fun p =>
    (firstWordSet A ((G.prod_rhs_rev p).reverse)).all
      (fun t => decide (t ∈ firstNtermSet A (G.prod_lhs p))))

theorem isFirstStable_correct : isFirstStable A = true → firstStable A := by
  intro h
  refine forall_of_Allb (P := fun p => _) (fun p hp => ?_) h
  intro t ht
  rw [List.all_eq_true] at hp
  exact of_decide_eq_true (hp t ht)

/-- Boolean validator for `startGoto`. -/
def isStartGoto (A : Automaton G) : Bool :=
  Allb A.InitState (fun init =>
    match A.goto_table (.Init init) (A.start_nt init) with
    | none => true
    | some _ => false)

theorem isStartGoto_correct : isStartGoto A = true → startGoto A := by
  intro h
  refine forall_of_Allb (P := fun init => _) (fun init hi => ?_) h
  revert hi
  cases hg : A.goto_table (.Init init) (A.start_nt init) with
  | none => intro _; show True; trivial
  | some v => intro hi; simp at hi

/-- Boolean validator for `startFuture`. -/
def isStartFuture (A : Automaton G) : Bool :=
  Allb A.InitState (fun init =>
    Allb G.Production (fun p =>
      implb (compareEqb (G.prod_lhs p) (A.start_nt init))
        (Allb G.Terminal (fun t => decide (t ∈ findItemsMap (.Init init) p 0)))))

theorem isStartFuture_correct : isStartFuture A = true → startFuture A := by
  intro h
  refine forall_of_Allb (P := fun init => _) (fun init hi => ?_) h
  intro p hlhs t
  have hp := forall_of_Allb
    (P := fun p => implb (compareEqb (G.prod_lhs p) (A.start_nt init))
      (Allb G.Terminal (fun t => decide (t ∈ findItemsMap (.Init init) p 0))) = true)
    (fun p hp => hp) hi p
  rw [implb_eq_true] at hp
  have hcmp : compareEqb (G.prod_lhs p) (A.start_nt init) = true := (compareEqb_iff _ _).2 hlhs
  have hall := hp hcmp
  have ht := forall_of_Allb
    (P := fun t => decide (t ∈ findItemsMap (.Init init) p 0) = true)
    (fun t ht => ht) hall t
  exact stateHasFuture_of_mem (of_decide_eq_true ht)

/-- Boolean validator for `terminalShift`. -/
def isTerminalShift (A : Automaton G) : Bool :=
  allbItems A (fun s prod pos look =>
    match futureOfProd prod pos with
    | .T t :: _ =>
      match A.action_table s with
      | .Lookahead_act awp =>
        match awp t with
        | .Shift_act s2 _ => decide (look ∈ findItemsMap (.Ninit s2) prod (pos + 1))
        | _ => false
      | _ => false
    | _ => true)

theorem isTerminalShift_correct : isTerminalShift A = true → terminalShift A := by
  intro h
  refine allbItems_correct (Q := fun s prod fut look =>
    match fut with
    | .T t :: q =>
      match A.action_table s with
      | .Lookahead_act awp =>
        match awp t with
        | .Shift_act s2 _ => stateHasFuture (.Ninit s2) prod q look
        | _ => False
      | _ => False
    | _ => True) (fun s prod pos look hb => ?_) h
  cases hf : futureOfProd prod pos with
  | nil => trivial
  | cons x q =>
    cases x with
    | NT nt => trivial
    | T t =>
      cases ha : A.action_table s with
      | Default_reduce_act p => simp only [hf, ha] at hb; exact absurd hb (by decide)
      | Lookahead_act awp =>
        cases haw : awp t with
        | Shift_act s2 e =>
          simp only [hf, ha, haw] at hb ⊢
          have hsf := stateHasFuture_of_mem (of_decide_eq_true hb)
          rwa [futureOfProd_succ hf] at hsf
        | Reduce_act p => simp only [hf, ha, haw] at hb; exact absurd hb (by decide)
        | Fail_act => simp only [hf, ha, haw] at hb; exact absurd hb (by decide)

/-- Boolean validator for `endReduce`. -/
def isEndReduce (A : Automaton G) : Bool :=
  allbItems A (fun s prod pos look =>
    match futureOfProd prod pos with
    | [] =>
      match A.action_table s with
      | .Default_reduce_act p => compareEqb p prod
      | .Lookahead_act awt =>
        match awt look with
        | .Reduce_act p => compareEqb p prod
        | _ => false
    | _ => true)

theorem isEndReduce_correct : isEndReduce A = true → endReduce A := by
  intro h
  refine allbItems_correct (Q := fun s prod fut look =>
    match fut with
    | [] =>
      match A.action_table s with
      | .Default_reduce_act p => p = prod
      | .Lookahead_act awt =>
        match awt look with
        | .Reduce_act p => p = prod
        | _ => False
    | _ => True) (fun s prod pos look hb => ?_) h
  cases hf : futureOfProd prod pos with
  | cons x q => trivial
  | nil =>
    cases ha : A.action_table s with
    | Default_reduce_act p =>
      simp only [hf, ha] at hb ⊢
      exact (compareEqb_iff _ _).1 hb
    | Lookahead_act awt =>
      cases haw : awt look with
      | Shift_act s2 e => simp only [hf, ha, haw] at hb; exact absurd hb (by decide)
      | Reduce_act p =>
        simp only [hf, ha, haw] at hb ⊢
        exact (compareEqb_iff _ _).1 hb
      | Fail_act => simp only [hf, ha, haw] at hb; exact absurd hb (by decide)

/-- Boolean validator for `nonTerminalGoto`. -/
def isNonTerminalGoto (A : Automaton G) : Bool :=
  allbItems A (fun s prod pos look =>
    match futureOfProd prod pos with
    | .NT nt :: _ =>
      match A.goto_table s nt with
      | some ⟨s2, _⟩ => decide (look ∈ findItemsMap (.Ninit s2) prod (pos + 1))
      | none => false
    | _ => true)

theorem isNonTerminalGoto_correct : isNonTerminalGoto A = true → nonTerminalGoto A := by
  intro h
  refine allbItems_correct (Q := fun s prod fut look =>
    match fut with
    | .NT nt :: q =>
      match A.goto_table s nt with
      | some ⟨s2, _⟩ => stateHasFuture (.Ninit s2) prod q look
      | none => False
    | _ => True) (fun s prod pos look hb => ?_) h
  cases hf : futureOfProd prod pos with
  | nil => trivial
  | cons x q =>
    cases x with
    | T t => trivial
    | NT nt =>
      cases hg : A.goto_table s nt with
      | none => simp only [hf, hg] at hb; exact absurd hb (by decide)
      | some v =>
        obtain ⟨s2, e⟩ := v
        simp only [hf, hg] at hb ⊢
        have hsf := stateHasFuture_of_mem (of_decide_eq_true hb)
        rwa [futureOfProd_succ hf] at hsf

/-- Boolean validator for `nonTerminalClosed`. -/
def isNonTerminalClosed (A : Automaton G) : Bool :=
  allbItems A (fun s1 prod pos look =>
    match futureOfProd prod pos with
    | .NT nt :: q =>
      Allb G.Production (fun p =>
        implb (compareEqb (G.prod_lhs p) nt)
          (implb (nullableWord A q) (decide (look ∈ findItemsMap s1 p 0)) &&
            (firstWordSet A q).all (fun look2 => decide (look2 ∈ findItemsMap s1 p 0))))
    | _ => true)

theorem isNonTerminalClosed_correct : isNonTerminalClosed A = true → nonTerminalClosed A := by
  intro h
  refine allbItems_correct (Q := fun s1 prod fut look =>
    match fut with
    | .NT nt :: q =>
      ∀ p : G.Production, G.prod_lhs p = nt →
        (if nullableWord A q then stateHasFuture s1 p (futureOfProd p 0) look else True) ∧
        (∀ look2 : G.Terminal,
          look2 ∈ firstWordSet A q → stateHasFuture s1 p (futureOfProd p 0) look2)
    | _ => True) (fun s1 prod pos look hb => ?_) h
  cases hf : futureOfProd prod pos with
  | nil => trivial
  | cons x q =>
    cases x with
    | T t => trivial
    | NT nt =>
      simp only [hf] at hb
      intro p hlhs
      unfold Allb at hb
      rw [List.all_eq_true] at hb
      have hgp := hb p (allList_complete p)
      rw [implb_eq_true] at hgp
      have hconj := hgp ((compareEqb_iff _ _).2 hlhs)
      rw [Bool.and_eq_true] at hconj
      obtain ⟨hnull, hfirst⟩ := hconj
      rw [implb_eq_true] at hnull
      refine ⟨?_, ?_⟩
      · by_cases hc : nullableWord A q = true
        · simp only [hc, if_true]
          exact stateHasFuture_of_mem (of_decide_eq_true (hnull hc))
        · simp only [Bool.not_eq_true] at hc; simp only [hc, Bool.false_eq_true, if_false]
      · intro look2 hlook2
        rw [List.all_eq_true] at hfirst
        exact stateHasFuture_of_mem (of_decide_eq_true (hfirst look2 hlook2))

/-! ### The complete validator -/

/-- The boolean completeness validator (Coq `is_complete`). -/
def isComplete (A : Automaton G) : Bool :=
  isNullableStable A && isFirstStable A && isStartFuture A && isTerminalShift A
  && isEndReduce A && isNonTerminalGoto A && isStartGoto A && isNonTerminalClosed A

/-- The validator is correct: if `isComplete A = true`, the automaton is
`complete` (Coq `complete_is_validator`). -/
theorem complete_is_validator : isComplete A = true → complete A := by
  intro h
  simp only [isComplete, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨isNullableStable_correct h1, isFirstStable_correct h2, isStartFuture_correct h3,
    isTerminalShift_correct h4, isEndReduce_correct h5, isNonTerminalGoto_correct h6,
    isStartGoto_correct h7, isNonTerminalClosed_correct h8⟩

end LeanMenhir
