/-
Port of `coq-menhirlib`'s `Automaton.v` to Lean 4.

Original: Copyright Inria and CNRS, LGPL-3.0-or-later.
This Lean port is a derivative work, distributed under LGPL-3.0-or-later.

The LR automaton table interface: states, actions (shift/reduce/fail), the
action/goto tables, and the validation annotations.
-/
import LeanMenhir.Spec.Grammar

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
def cmp [Ord InitState] [Ord NonInitState] :
    State InitState NonInitState → State InitState NonInitState → Ordering
  | Init x, Init y => compare x y
  | Ninit x, Ninit y => compare x y
  | Init _, Ninit _ => Ordering.lt
  | Ninit _, Init _ => Ordering.gt

instance instOrd [Ord InitState] [Ord NonInitState] :
    Ord (State InitState NonInitState) := ⟨cmp⟩

instance instTransOrd [Ord InitState] [Ord NonInitState]
    [Std.TransOrd InitState] [Std.TransOrd NonInitState] :
    Std.TransOrd (State InitState NonInitState) where
  eq_swap {x y} := by
    show cmp x y = (cmp y x).swap
    cases x <;> cases y <;> simp only [cmp] <;>
      first | rfl | exact Std.OrientedCmp.eq_swap
  isLE_trans {x y z} hxy hyz := by
    change (cmp x y).isLE = true at hxy
    change (cmp y z).isLE = true at hyz
    show (cmp x z).isLE = true
    cases x <;> cases y <;> cases z <;> simp only [cmp] at hxy hyz ⊢ <;>
      first | exact Std.TransCmp.isLE_trans hxy hyz | assumption | decide | grind [Ordering.isLE]

instance instLawfulEqOrd [Ord InitState] [Ord NonInitState]
    [Std.LawfulEqOrd InitState] [Std.LawfulEqOrd NonInitState] :
    Std.LawfulEqOrd (State InitState NonInitState) where
  compare_self {x} := by
    show cmp x x = .eq
    cases x <;> simp only [cmp] <;> exact Std.ReflCmp.compare_self
  eq_of_compare {x y} h := by
    change cmp x y = Ordering.eq at h
    cases x <;> cases y <;> simp only [cmp] at h <;>
      first
        | exact congrArg Init (Std.LawfulEqCmp.eq_of_compare h)
        | exact congrArg Ninit (Std.LawfulEqCmp.eq_of_compare h)
        | grind

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

/-- An LR machine **for** grammar `G` (Coq `Automaton.T` bundled the grammar via
a module functor; here `G` is an explicit structure parameter, so `Automaton G`
visibly means "an automaton for the grammar `G`"). The fields from
`past_symb_of_non_init_state` on are *validator annotations*: untrusted
certificate data consumed only by the safety/completeness validators, never by
the interpreter's computation. -/
structure Automaton (G : Grammar) where
  NonInitState : Type
  noninitstateAlphabet : Alphabet NonInitState
  InitState : Type
  initstateAlphabet : Alphabet InitState
  /-- When in this state, this symbol is known to be on top of the stack. -/
  last_symb_of_non_init_state : NonInitState → Symbol G.Terminal G.Nonterminal
  /-- For each initial state, the nonterminal it recognises. -/
  start_nt : InitState → G.Nonterminal
  /-- The action table. -/
  action_table : State InitState NonInitState →
    Action last_symb_of_non_init_state G.Production
  /-- The goto table. -/
  goto_table : State InitState NonInitState → (nt : G.Nonterminal) →
    Option { s : NonInitState // Symbol.NT nt = last_symb_of_non_init_state s }
  /-- Symbols known to be just below the top of the stack in this state. -/
  past_symb_of_non_init_state : NonInitState → List (Symbol G.Terminal G.Nonterminal)
  /-- Predicates the strictly-previous states satisfy in this state. -/
  past_state_of_non_init_state : NonInitState → List (State InitState NonInitState → Bool)
  /-- The items of a state. -/
  items_of_state : State InitState NonInitState → List (Item G.Terminal G.Production)
  /-- True iff the nonterminal can produce the empty string. -/
  nullable_nterm : G.Nonterminal → Bool
  /-- Terminals that can begin a word produced by the nonterminal. -/
  first_nterm : G.Nonterminal → List G.Terminal
  /-- An over-approximation of the automaton's defined gotos: it must contain every
  `(s, nt)` for which `goto_table s nt` is defined (see `goto_enum_complete`). The
  goto-based safety validators iterate this list — the *defined* gotos, which are
  sparse — instead of probing every `(state, nonterminal)` pair (the dominant
  kernel-`rfl` cost). Table bridges supply the sparse list from `gotoBT.toList`;
  small/array bridges may supply the dense enumeration of all pairs. -/
  goto_enum : List (State InitState NonInitState × G.Nonterminal)
  /-- `goto_enum` covers every defined goto. This is what makes iterating
  `goto_enum` sound: a `(s, nt)` whose goto is defined cannot be skipped. -/
  goto_enum_complete : ∀ (s : State InitState NonInitState) (nt : G.Nonterminal),
    goto_table s nt ≠ none → (s, nt) ∈ goto_enum

instance instNonInitStateAlphabet {G : Grammar} (A : Automaton G) :
    Alphabet A.NonInitState := A.noninitstateAlphabet
instance instInitStateAlphabet {G : Grammar} (A : Automaton G) :
    Alphabet A.InitState := A.initstateAlphabet

namespace Automaton
variable {G : Grammar} (A : Automaton G)

/-- The state type of the automaton. -/
abbrev State : Type := LeanMenhir.State A.InitState A.NonInitState
/-- The action type of the automaton. -/
abbrev Action : Type := LeanMenhir.Action A.last_symb_of_non_init_state G.Production
/-- The lookahead-action type of the automaton at terminal `term`. -/
abbrev LookaheadAction (term : G.Terminal) : Type :=
  LeanMenhir.LookaheadAction A.last_symb_of_non_init_state G.Production term
/-- The item type of the automaton. -/
abbrev Item : Type := LeanMenhir.Item G.Terminal G.Production

end Automaton

end LeanMenhir
