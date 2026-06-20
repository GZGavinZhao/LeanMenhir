/-
Port of `coq-menhirlib`'s `Automaton.v` to Lean 4.

Original: Copyright Inria and CNRS, LGPL-3.0-or-later.
This Lean port is a derivative work, distributed under LGPL-3.0-or-later.

The LR automaton table interface: states, actions (shift/reduce/fail), the
action/goto tables, and the validation annotations.
-/
import LeanMenhir.Grammar

namespace LeanMenhir

/-! ### States -/

/-- The states of the automaton: an initial state or a non-initial state. The
initial state behaves differently, so the two are kept separate (Coq `state`).
Initial states compare less than non-initial states. -/
inductive State (InitState NonInitState : Type) where
  | Init : InitState → State InitState NonInitState
  | Ninit : NonInitState → State InitState NonInitState
deriving DecidableEq

namespace State
variable {InitState NonInitState : Type}

/-- Comparison on states (Coq `StateAlph`): `Init _ < Ninit _`. -/
def cmp [Comparable InitState] [Comparable NonInitState] :
    State InitState NonInitState → State InitState NonInitState → Ordering
  | Init x, Init y => Comparable.compare x y
  | Ninit x, Ninit y => Comparable.compare x y
  | Init _, Ninit _ => Ordering.lt
  | Ninit _, Init _ => Ordering.gt

instance instComparable [Comparable InitState] [Comparable NonInitState] :
    Comparable (State InitState NonInitState) where
  compare := cmp
  compare_antisym x y := by
    cases x <;> cases y <;> simp only [cmp]
    · exact compare_antisym _ _
    · rfl
    · rfl
    · exact compare_antisym _ _
  compare_trans x y z c hxy hyz := by
    cases x <;> cases y <;> cases z <;> simp only [cmp] at hxy hyz ⊢
    · exact compare_trans _ _ _ _ hxy hyz
    · exact hyz
    · exact absurd (hxy.trans hyz.symm) (by decide)
    · exact hxy
    · exact hxy
    · exact absurd (hxy.trans hyz.symm) (by decide)
    · exact hyz
    · exact compare_trans _ _ _ _ hxy hyz

instance instComparableLeibnizEq [Comparable InitState] [Comparable NonInitState]
    [ComparableLeibnizEq InitState] [ComparableLeibnizEq NonInitState] :
    ComparableLeibnizEq (State InitState NonInitState) where
  compare_eq x y h := by
    change cmp x y = Ordering.eq at h
    cases x <;> cases y <;> simp only [cmp] at h
    · exact congrArg Init (compare_eq _ _ h)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact congrArg Ninit (compare_eq _ _ h)

instance instEnumerable [Enumerable InitState] [Enumerable NonInitState] :
    Enumerable (State InitState NonInitState) where
  allList := (allList (α := InitState)).map Init ++ (allList (α := NonInitState)).map Ninit
  allList_complete x := by
    rw [List.mem_append]
    cases x with
    | Init i => exact Or.inl (List.mem_map.2 ⟨i, allList_complete i, rfl⟩)
    | Ninit n => exact Or.inr (List.mem_map.2 ⟨n, allList_complete n, rfl⟩)

instance instAlphabet [Alphabet InitState] [Alphabet NonInitState] :
    Alphabet (State InitState NonInitState) := {}

end State

/-! ### Actions and items -/

/-- An action available at a state for a given lookahead `term`inal: shift to a
non-initial state (carrying a proof that the read symbol matches), reduce a
production, or fail. Mirrors Coq `lookahead_action`. -/
inductive LookaheadAction {Terminal Nonterminal NonInitState : Type}
    (lastSymb : NonInitState → Symbol Terminal Nonterminal) (Production : Type)
    (term : Terminal) where
  | Shift_act : (s : NonInitState) → Symbol.T term = lastSymb s →
      LookaheadAction lastSymb Production term
  | Reduce_act : Production → LookaheadAction lastSymb Production term
  | Fail_act : LookaheadAction lastSymb Production term

/-- The action attached to a state: either a default reduction (performed without
reading the input), or a lookahead-driven action. Mirrors Coq `action`. -/
inductive Action {Terminal Nonterminal NonInitState : Type}
    (lastSymb : NonInitState → Symbol Terminal Nonterminal) (Production : Type) where
  | Default_reduce_act : Production → Action lastSymb Production
  | Lookahead_act : ((term : Terminal) → LookaheadAction lastSymb Production term) →
      Action lastSymb Production

/-- An item is a set of LR(1) items sharing the same core (used to validate
completeness). Mirrors Coq `item`. -/
structure Item (Terminal Production : Type) where
  prod_item : Production
  dot_pos_item : Nat
  lookaheads_item : List Terminal

/-! ### The automaton interface -/

/-- The automaton interface, mirroring Coq `Automaton.T` (which bundles `AutInit`,
`Types`, and the table/annotation parameters). Extends `Grammar`. -/
class Automaton extends Grammar where
  NonInitState : Type
  noninitstateAlphabet : Alphabet NonInitState
  InitState : Type
  initstateAlphabet : Alphabet InitState
  /-- When in this state, this symbol is known to be on top of the stack. -/
  last_symb_of_non_init_state : NonInitState → Symbol Terminal Nonterminal
  /-- For each initial state, the nonterminal it recognises. -/
  start_nt : InitState → Nonterminal
  /-- The action table. -/
  action_table : State InitState NonInitState →
    Action last_symb_of_non_init_state Production
  /-- The goto table. -/
  goto_table : State InitState NonInitState → (nt : Nonterminal) →
    Option { s : NonInitState // Symbol.NT nt = last_symb_of_non_init_state s }
  /-- Symbols known to be just below the top of the stack in this state. -/
  past_symb_of_non_init_state : NonInitState → List (Symbol Terminal Nonterminal)
  /-- Predicates the strictly-previous states satisfy in this state. -/
  past_state_of_non_init_state : NonInitState → List (State InitState NonInitState → Bool)
  /-- The items of a state. -/
  items_of_state : State InitState NonInitState → List (Item Terminal Production)
  /-- True iff the nonterminal can produce the empty string. -/
  nullable_nterm : Nonterminal → Bool
  /-- Terminals that can begin a word produced by the nonterminal. -/
  first_nterm : Nonterminal → List Terminal

instance instNonInitStateAlphabet [A : Automaton] : Alphabet A.NonInitState :=
  A.noninitstateAlphabet
instance instInitStateAlphabet [A : Automaton] : Alphabet A.InitState :=
  A.initstateAlphabet

namespace Automaton
variable (A : Automaton)

/-- The state type of the automaton. -/
abbrev State : Type := LeanMenhir.State A.InitState A.NonInitState
/-- The action type of the automaton. -/
abbrev Action : Type := LeanMenhir.Action A.last_symb_of_non_init_state A.Production
/-- The lookahead-action type of the automaton at terminal `term`. -/
abbrev LookaheadAction (term : A.Terminal) : Type :=
  LeanMenhir.LookaheadAction A.last_symb_of_non_init_state A.Production term
/-- The item type of the automaton. -/
abbrev Item : Type := LeanMenhir.Item A.Terminal A.Production

end Automaton

end LeanMenhir
