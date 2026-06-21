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

/-! ### Dotted parse trees -/

section Completeness

/- The initial state, the full word to be parsed, and the buffer left over at the
end of parsing are fixed throughout the completeness proof (Coq's section
`Variable`s). -/
variable (init : A.InitState) (full_word : List A.Token) (buffer_end : Buffer)

/- A "parse tree zipper" is a parse tree with a hole, represented upside-down: the
root of the original tree is a leaf of the zipper and the hole is its root. Coq
`pt_zipper` / `ptl_zipper`. -/
mutual
inductive PtZipper : Symbol A.Terminal A.Nonterminal → List A.Token → Type where
  | Top_ptz : PtZipper (.NT (A.start_nt init)) full_word
  | Cons_ptl_ptz {head_symbolsq : List (Symbol A.Terminal A.Nonterminal)}
      {wordq : List A.Token} : ParseTreeList head_symbolsq wordq →
      {head_symbolt : Symbol A.Terminal A.Nonterminal} → {wordt : List A.Token} →
      PtlZipper (head_symbolt :: head_symbolsq) (wordq ++ wordt) →
      PtZipper head_symbolt wordt
inductive PtlZipper : List (Symbol A.Terminal A.Nonterminal) → List A.Token → Type where
  | Non_terminal_pt_ptlz {p : A.Production} {word : List A.Token} :
      PtZipper (.NT (A.prod_lhs p)) word → PtlZipper (A.prod_rhs_rev p) word
  | Cons_ptl_ptlz {head_symbolsq : List (Symbol A.Terminal A.Nonterminal)}
      {wordq : List A.Token} {head_symbolt : Symbol A.Terminal A.Nonterminal}
      {wordt : List A.Token} : ParseTree head_symbolt wordt →
      PtlZipper (head_symbolt :: head_symbolsq) (wordq ++ wordt) →
      PtlZipper head_symbolsq wordq
end

/-- A dotted parse tree: a zipper plus the sub-tree under the dot, in either a
reduce or a shift configuration (Coq `pt_dot`). -/
inductive PtDot : Type where
  | Reduce_ptd {prod : A.Production} {word : List A.Token} :
      ParseTreeList (A.prod_rhs_rev prod) word →
      PtZipper init full_word (.NT (A.prod_lhs prod)) word → PtDot
  | Shift_ptd (tok : A.Token) {symbolsq : List (Symbol A.Terminal A.Nonterminal)}
      {wordq : List A.Token} : ParseTreeList symbolsq wordq →
      PtlZipper init full_word (.T (A.token_term tok) :: symbolsq) (wordq ++ [tok]) → PtDot

/- The semantic value of a dotted parse tree, computed from the zipper part
(Coq `ptlz_sem` / `ptz_sem`). -/
mutual
def ptlzSem : {holeSymbs : List (Symbol A.Terminal A.Nonterminal)} → {holeWord : List A.Token} →
    PtlZipper init full_word holeSymbs holeWord →
    (∀ B : Type, arrowsRight B (holeSymbs.map A.symbol_semantic_type) → B) →
    A.symbol_semantic_type (.NT (A.start_nt init))
  | _, _, .Non_terminal_pt_ptlz (p := prod) ptz, k => ptzSem ptz (k _ (A.prod_action prod))
  | _, _, .Cons_ptl_ptlz pt ptlz, k => ptlzSem ptlz (fun _ f => k _ (f (ptSem pt)))
def ptzSem : {holeSymb : Symbol A.Terminal A.Nonterminal} → {holeWord : List A.Token} →
    PtZipper init full_word holeSymb holeWord →
    A.symbol_semantic_type holeSymb → A.symbol_semantic_type (.NT (A.start_nt init))
  | _, _, .Top_ptz, sem => sem
  | _, _, .Cons_ptl_ptz ptl ptlz, sem => ptlzSem ptlz (fun _ f => ptlSem ptl (f sem))
end

/-- The semantic value of a dotted parse tree (Coq `ptd_sem`). -/
def ptdSem : PtDot init full_word → A.symbol_semantic_type (.NT (A.start_nt init))
  | .Reduce_ptd (prod := prod) ptl ptz => ptzSem init full_word ptz (ptlSem ptl (A.prod_action prod))
  | .Shift_ptd tok ptl ptlz =>
      ptlzSem init full_word ptlz (fun _ f => ptlSem ptl (f (A.token_sem tok)))

/- The buffer left to read at a dotted parse tree (Coq `ptlz_buffer` / `ptz_buffer`). -/
mutual
def ptlzBuffer : {holeSymbs : List (Symbol A.Terminal A.Nonterminal)} → {holeWord : List A.Token} →
    PtlZipper init full_word holeSymbs holeWord → Buffer
  | _, _, .Non_terminal_pt_ptlz ptz => ptzBuffer ptz
  | _, _, .Cons_ptl_ptlz (wordt := wordt) _ ptlz => wordt ++ₛ ptlzBuffer ptlz
def ptzBuffer : {holeSymb : Symbol A.Terminal A.Nonterminal} → {holeWord : List A.Token} →
    PtZipper init full_word holeSymb holeWord → Buffer
  | _, _, .Top_ptz => buffer_end
  | _, _, .Cons_ptl_ptz _ ptlz => ptlzBuffer ptlz
end

/-- The buffer at a dotted parse tree (Coq `ptd_buffer`). -/
def ptdBuffer : PtDot init full_word → Buffer
  | .Reduce_ptd _ ptz => ptzBuffer init full_word buffer_end ptz
  | .Shift_ptd tok _ ptlz => Stream'.cons tok (ptlzBuffer init full_word buffer_end ptlz)

/-- The production at the root of a parse-tree-list zipper (Coq `ptlz_prod`). -/
def ptlzProd : {holeSymbs : List (Symbol A.Terminal A.Nonterminal)} → {holeWord : List A.Token} →
    PtlZipper init full_word holeSymbs holeWord → A.Production
  | _, _, .Non_terminal_pt_ptlz (p := prod) _ => prod
  | _, _, .Cons_ptl_ptlz _ ptlz => ptlzProd ptlz

/-- The symbols still to be read in the current production (Coq `ptlz_future`). -/
def ptlzFuture : {holeSymbs : List (Symbol A.Terminal A.Nonterminal)} → {holeWord : List A.Token} →
    PtlZipper init full_word holeSymbs holeWord → List (Symbol A.Terminal A.Nonterminal)
  | _, _, .Non_terminal_pt_ptlz _ => []
  | _, _, .Cons_ptl_ptlz (head_symbolt := s) _ ptlz => s :: ptlzFuture ptlz

/-- The lookahead terminal of a parse-tree-list zipper (Coq `ptlz_lookahead`). -/
def ptlzLookahead : {holeSymbs : List (Symbol A.Terminal A.Nonterminal)} → {holeWord : List A.Token} →
    PtlZipper init full_word holeSymbs holeWord → A.Terminal
  | _, _, .Non_terminal_pt_ptlz ptz => A.token_term (ptzBuffer init full_word buffer_end ptz).head
  | _, _, .Cons_ptl_ptlz _ ptlz => ptlzLookahead ptlz

/- A stack is compatible with a parse-tree zipper when it is built from stack
fragments matching each partially-recognised production in the zipper, with each
fragment's top state predicting the corresponding item (Coq `ptz_stack_compat` /
`ptlz_stack_compat`). -/
mutual
def ptzStackCompat : {holeSymb : Symbol A.Terminal A.Nonterminal} → {holeWord : List A.Token} →
    Stack → PtZipper init full_word holeSymb holeWord → Prop
  | _, _, stk, .Top_ptz => stk = []
  | holeSymb, _, stk, .Cons_ptl_ptz ptl ptlz =>
      ∃ stk0, stateHasFuture (stateOfStack init stk) (ptlzProd init full_word ptlz)
          (holeSymb :: ptlzFuture init full_word ptlz)
          (ptlzLookahead init full_word buffer_end ptlz) ∧
        ptlStackCompat stk0 ptl stk ∧ ptlzStackCompat stk0 ptlz
def ptlzStackCompat : {holeSymbs : List (Symbol A.Terminal A.Nonterminal)} → {holeWord : List A.Token} →
    Stack → PtlZipper init full_word holeSymbs holeWord → Prop
  | _, _, stk, .Non_terminal_pt_ptlz ptz => ptzStackCompat stk ptz
  | _, _, stk, .Cons_ptl_ptlz _ ptlz => ptlzStackCompat stk ptlz
end

/-- A stack is compatible with a dotted parse tree (Coq `ptd_stack_compat`). -/
def ptdStackCompat : PtDot init full_word → Stack → Prop
  | .Reduce_ptd (prod := prod) ptl ptz, stk =>
      ∃ stk0, stateHasFuture (stateOfStack init stk) prod []
          (A.token_term (ptzBuffer init full_word buffer_end ptz).head) ∧
        ptlStackCompat stk0 ptl stk ∧ ptzStackCompat init full_word buffer_end stk0 ptz
  | .Shift_ptd tok ptl ptlz, stk =>
      ∃ stk0, stateHasFuture (stateOfStack init stk) (ptlzProd init full_word ptlz)
          (.T (A.token_term tok) :: ptlzFuture init full_word ptlz)
          (ptlzLookahead init full_word buffer_end ptlz) ∧
        ptlStackCompat stk0 ptl stk ∧ ptlzStackCompat init full_word buffer_end stk0 ptlz

/-- The top of a `Cons_ptl_ptz`-compatible stack predicts the zipper's item
(Coq `ptz_stack_compat_cons_state_has_future`). -/
theorem ptz_stack_compat_cons_state_has_future {symbsq : List (Symbol A.Terminal A.Nonterminal)}
    {wordq : List A.Token} {symbt : Symbol A.Terminal A.Nonterminal} {wordt : List A.Token}
    (stk : Stack) (ptl : ParseTreeList symbsq wordq)
    (ptlz : PtlZipper init full_word (symbt :: symbsq) (wordq ++ wordt))
    (h : ptzStackCompat init full_word buffer_end stk (.Cons_ptl_ptz ptl ptlz)) :
    stateHasFuture (stateOfStack init stk) (ptlzProd init full_word ptlz)
      (symbt :: ptlzFuture init full_word ptlz) (ptlzLookahead init full_word buffer_end ptlz) := by
  simp only [ptzStackCompat] at h
  obtain ⟨stk0, hsf, _, _⟩ := h
  exact hsf

/-- The future plus the recognised symbols reverse-append to the production's RHS
(Coq `ptlz_future_ptlz_prod`). -/
theorem ptlz_future_ptlz_prod :
    {holeSymbs : List (Symbol A.Terminal A.Nonterminal)} → {holeWord : List A.Token} →
    (ptlz : PtlZipper init full_word holeSymbs holeWord) →
    List.reverseAux (ptlzFuture init full_word ptlz) holeSymbs =
      A.prod_rhs_rev (ptlzProd init full_word ptlz)
  | _, _, .Non_terminal_pt_ptlz _ => by simp [ptlzFuture, ptlzProd]
  | _, _, .Cons_ptl_ptlz pt ptlz' => by
      simp only [ptlzFuture, ptlzProd, List.reverseAux]
      exact ptlz_future_ptlz_prod ptlz'

/-- The lookahead of a zipper is in the first set of its future, or the future is
nullable and the lookahead equals the recorded lookahead (Coq `ptlz_future_first`). -/
theorem ptlz_future_first (hc : complete) :
    {symbs : List (Symbol A.Terminal A.Nonterminal)} → {word : List A.Token} →
    (ptlz : PtlZipper init full_word symbs word) →
    A.token_term (ptlzBuffer init full_word buffer_end ptlz).head ∈
        firstWordSet (ptlzFuture init full_word ptlz) ∨
    (A.token_term (ptlzBuffer init full_word buffer_end ptlz).head =
        ptlzLookahead init full_word buffer_end ptlz ∧
      nullableWord (ptlzFuture init full_word ptlz) = true)
  | _, _, .Non_terminal_pt_ptlz ptz => by
      refine Or.inr ⟨?_, ?_⟩
      · simp [ptlzBuffer, ptlzLookahead]
      · simp [ptlzFuture, nullableWord]
  | _, _, .Cons_ptl_ptlz (head_symbolt := s) (wordt := wordt) pt ptlz' => by
      have IH := ptlz_future_first hc ptlz'
      simp only [ptlzBuffer, ptlzFuture, ptlzLookahead]
      cases wordt with
      | nil =>
          rw [Stream'.nil_append_stream]
          have hnull := nullable_correct hc rfl pt
          rcases IH with hl | ⟨he, hn⟩
          · left
            simp only [firstWordSet, hnull, if_true]
            exact List.mem_append.2 (Or.inr hl)
          · right
            refine ⟨he, ?_⟩
            simp only [nullableWord, List.all_cons, hnull, Bool.true_and]
            exact hn
      | cons c wordt'' =>
          rw [Stream'.cons_append_stream]
          left
          have hfirst := first_correct hc pt
          show A.token_term c ∈ firstWordSet (s :: ptlzFuture init full_word ptlz')
          simp only [firstWordSet]
          by_cases hn : nullableSymb s = true
          · simp only [hn, if_true]
            exact List.mem_append.2 (Or.inl hfirst)
          · simp only [Bool.not_eq_true] at hn
            simp only [hn, Bool.false_eq_true, if_false]
            exact hfirst
  termination_by _ _ ptlz => sizeOf ptlz

/-! ### Moving the dot: `build_pt_dot_from_pt` and `next_ptd` -/

/-- A `Type`-valued witness that a parse-tree list is non-nil (mirrors Coq's
`is_notnil`, but in `Type` since Lean's `Option` cannot wrap a `Prop`). -/
abbrev NonNilT (symbs : List (Symbol A.Terminal A.Nonterminal)) : Type :=
  match symbs with | [] => Empty | _ => Unit

def nonNilProof : {symbs : List (Symbol A.Terminal A.Nonterminal)} → {word : List A.Token} →
    ParseTreeList symbs word → Option (NonNilT symbs)
  | _, _, .Nil_ptl => none
  | _, _, .Cons_ptl _ _ => some Unit.unit

/- Build the next dotted parse tree from a parse tree under the dot (Coq
`build_pt_dot_from_pt` / `build_pt_dot_from_pt_rec`). -/
mutual
def buildPtDotFromPt : {symb : Symbol A.Terminal A.Nonterminal} → {word : List A.Token} →
    ParseTree symb word → PtZipper init full_word symb word → PtDot init full_word
  | _, _, .Terminal_pt tok, ptz =>
      match ptz with
      | .Cons_ptl_ptz ptl ptlz => .Shift_ptd tok ptl ptlz
  | _, _, .Non_terminal_pt _ ptl, ptz =>
      match nonNilProof ptl with
      | none => .Reduce_ptd ptl ptz
      | some H => buildPtDotFromPtRec ptl H (.Non_terminal_pt_ptlz ptz)
def buildPtDotFromPtRec : {symbs : List (Symbol A.Terminal A.Nonterminal)} → {word : List A.Token} →
    (ptl : ParseTreeList symbs word) → NonNilT symbs →
    PtlZipper init full_word symbs word → PtDot init full_word
  | _, _, .Nil_ptl, hsymbs, _ => hsymbs.elim
  | _, _, .Cons_ptl ptl' pt, _, ptlz =>
      match ptl' with
      | .Nil_ptl => buildPtDotFromPt pt (.Cons_ptl_ptz .Nil_ptl ptlz)
      | .Cons_ptl a b => buildPtDotFromPtRec (.Cons_ptl a b) Unit.unit (.Cons_ptl_ptlz pt ptlz)
end

/-- Build the next dotted parse tree from a completed parse-tree list under a
zipper (Coq `build_pt_dot_from_ptl`). -/
def buildPtDotFromPtl : {symbs : List (Symbol A.Terminal A.Nonterminal)} → {word : List A.Token} →
    ParseTreeList symbs word → PtlZipper init full_word symbs word → PtDot init full_word
  | _, _, ptl, .Non_terminal_pt_ptlz ptz => .Reduce_ptd ptl ptz
  | _, _, ptl, .Cons_ptl_ptlz pt ptlz => buildPtDotFromPt init full_word pt (.Cons_ptl_ptz ptl ptlz)

/-- The dotted parse tree after one parser action (Coq `next_ptd`). -/
def nextPtd : PtDot init full_word → Option (PtDot init full_word)
  | .Shift_ptd tok ptl ptlz =>
      some (buildPtDotFromPtl init full_word (.Cons_ptl ptl (.Terminal_pt tok)) ptlz)
  | .Reduce_ptd (prod := prod) (word := w) ptl ptz =>
      match (Symbol.NT (A.prod_lhs prod) : Symbol A.Terminal A.Nonterminal), w, ptz,
          ParseTree.Non_terminal_pt prod ptl with
      | _, _, .Top_ptz, _ => none
      | _, _, .Cons_ptl_ptz ptl' ptlz, pt =>
          some (buildPtDotFromPtl init full_word (.Cons_ptl ptl' pt) ptlz)

/-- Iterating `nextPtd` `2 ^ log_n_steps` times (Coq `next_ptd_iter`). -/
def nextPtdIter : PtDot init full_word → Nat → Option (PtDot init full_word)
  | ptd, 0 => nextPtd init full_word ptd
  | ptd, n + 1 =>
      match nextPtdIter ptd n with
      | none => none
      | some ptd' => nextPtdIter ptd' n

end Completeness

end LeanMenhir
