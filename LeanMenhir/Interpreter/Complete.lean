/-
Port of `coq-menhirlib`'s `Interpreter_complete.v` to Lean 4.

Original: Copyright Inria and CNRS, LGPL-3.0-or-later.
This Lean port is a derivative work, distributed under LGPL-3.0-or-later.

Completeness of the interpreter: if the automaton is `safe` and `complete`, then
for every parse tree of the input the parser succeeds (with enough fuel),
returning that tree's semantic value and consuming exactly the right prefix.

The proof follows the Coq development: it traverses the parse tree using
"dotted parse trees" (a parse tree with a hole = a `pt_zipper` plus a sub-tree),
showing each parser step corresponds to one traversal step.
-/
import LeanMenhir.Interpreter
import LeanMenhir.Validator.Complete
import Mathlib.Data.Stream.Init

namespace LeanMenhir

variable [A : Automaton]

/-! ### Fixpoint-correctness lemmas for `nullable` and `first` -/

/- If a parse tree recognises the empty word, its head symbol is nullable
(Coq `nullable_correct` / `nullable_correct_list`). -/
mutual
theorem nullable_correct (hc : complete) :
    {head : Symbol A.Terminal A.Nonterminal} → {word : List A.Token} →
    word = [] → ParseTree head word → nullableSymb head = true
  | _, _, hw, .Terminal_pt _ => by simp at hw
  | _, _, hw, .Non_terminal_pt prod ptl => by
    have hnull := nullable_correct_list hc hw ptl
    have hs := nullableStable_of_complete hc prod
    rw [if_pos hnull] at hs
    exact hs
theorem nullable_correct_list (hc : complete) :
    {heads : List (Symbol A.Terminal A.Nonterminal)} → {word : List A.Token} →
    word = [] → ParseTreeList heads word → nullableWord heads = true
  | _, _, _, .Nil_ptl => rfl
  | _, _, hw, .Cons_ptl q t => by
    obtain ⟨hq, ht⟩ := List.append_eq_nil_iff.1 hw
    have h1 := nullable_correct_list hc hq q
    have h2 := nullable_correct hc ht t
    simp only [nullableWord, List.all_cons]
    rw [Bool.and_eq_true]
    exact ⟨h2, h1⟩
end

/-- `firstWordSet` distributes over append (Coq `first_word_set_app`). -/
theorem first_word_set_app (t : A.Terminal)
    (word1 word2 : List (Symbol A.Terminal A.Nonterminal)) :
    t ∈ firstWordSet (word1 ++ word2) ↔
    t ∈ firstWordSet word1 ∨ (t ∈ firstWordSet word2 ∧ nullableWord word1.reverse = true) := by
  induction word1 with
  | nil => simp [firstWordSet, nullableWord]
  | cons s word1 IH =>
    rw [List.cons_append]
    by_cases hs : nullableSymb s = true
    · simp only [firstWordSet, hs, if_true, List.mem_append, IH, List.reverse_cons,
        nullableWord, List.all_append, List.all_cons, List.all_nil, Bool.and_true]
      tauto
    · simp only [Bool.not_eq_true] at hs
      simp only [firstWordSet, hs, Bool.false_eq_true, if_false, List.reverse_cons,
        nullableWord, List.all_append, List.all_cons, List.all_nil, Bool.and_true,
        Bool.and_false, and_false, or_false]

/- If a parse tree recognises a word starting with `t`, then `token_term t` is in
the first set of the head symbol (Coq `first_correct` / `first_correct_list`). -/
mutual
theorem first_correct (hc : complete) :
    {head : Symbol A.Terminal A.Nonterminal} → {t : A.Token} → {q : List A.Token} →
    ParseTree head (t :: q) → A.token_term t ∈ firstSymbSet head
  | _, _, _, .Terminal_pt _ => by simp [firstSymbSet]
  | _, _, _, .Non_terminal_pt prod ptl => by
    simp only [firstSymbSet]
    exact firstStable_of_complete hc prod _ (first_correct_list hc rfl ptl)
theorem first_correct_list (hc : complete) :
    {heads : List (Symbol A.Terminal A.Nonterminal)} → {word : List A.Token} →
    {t : A.Token} → {q : List A.Token} →
    word = t :: q → ParseTreeList heads word →
    A.token_term t ∈ firstWordSet heads.reverse
  | _, _, _, _, hw, .Nil_ptl => by simp at hw
  | _, _, _, _, hw, .Cons_ptl ptlq pt => by
    rw [List.reverse_cons, first_word_set_app]
    rcases List.append_eq_cons_iff.1 hw with ⟨h1, h2⟩ | ⟨wordq', h1, h2⟩
    · refine Or.inr ⟨?_, ?_⟩
      · simp only [firstWordSet, List.append_nil, ite_self]
        exact first_correct hc (h2 ▸ pt)
      · rw [List.reverse_reverse]
        exact nullable_correct_list hc h1 ptlq
    · exact Or.inl (first_correct_list hc h1 ptlq)
end

/-! ### Stack compatibility for parse-tree lists -/

/-- A parse-tree list is compatible with a stack when the top of the stack holds
exactly the semantic values of the list (Coq `ptl_stack_compat`). -/
def ptlStackCompat (stk0 : Stack) :
    {symbs : List (Symbol A.Terminal A.Nonterminal)} → {word : List A.Token} →
    ParseTreeList symbs word → Stack → Prop
  | _, _, .Nil_ptl, stk => stk0 = stk
  | _, _, .Cons_ptl ptl' pt, stk =>
      match stk with
      | [] => False
      | cell :: stk' =>
          ptlStackCompat stk0 ptl' stk' ∧
          ∃ e : _ = A.last_symb_of_non_init_state cell.1,
            cell.2 = cast (congrArg A.symbol_semantic_type e) (ptSem pt)

/-- When a parse-tree list is compatible with a stack, `pop`ping it (per the
declarative spec) yields the list's semantic value (Coq
`pop_stack_compat_pop_spec`). -/
theorem pop_stack_compat_pop_spec {R : Type} :
    {symbs : List (Symbol A.Terminal A.Nonterminal)} → {word : List A.Token} →
    (ptl : ParseTreeList symbs word) → (stk stk0 : Stack) →
    (action : arrowsRight R (symbs.map A.symbol_semantic_type)) →
    ptlStackCompat stk0 ptl stk → PopSpec symbs stk action stk0 (ptlSem ptl action)
  | _, _, .Nil_ptl, stk, stk0, action, h => by
    simp only [ptlStackCompat] at h; subst h
    simp only [ptlSem]; exact PopSpec.nil stk0 action
  | _, _, .Cons_ptl ptl' pt, stk, stk0, action, h => by
    cases stk with
    | nil => simp only [ptlStackCompat] at h
    | cons cell stk' =>
      obtain ⟨st, sem⟩ := cell
      simp only [ptlStackCompat] at h
      obtain ⟨hcompat, e, hsem⟩ := h
      subst e
      rw [cast_eq] at hsem
      subst hsem
      simp only [ptlSem]
      exact PopSpec.cons st stk' action (ptSem pt) stk0 (ptlSem ptl' (action (ptSem pt)))
        (pop_stack_compat_pop_spec ptl' stk' stk0 (action (ptSem pt)) hcompat)

end LeanMenhir
