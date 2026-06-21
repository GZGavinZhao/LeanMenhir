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

/-- The reduce-step continuation, over a *generic* nonterminal so that `cases`
on the zipper works (the index is a variable). Splits on whether the zipper is
the top (parsing done) or nested. -/
def nextPtdAux {nt : A.Nonterminal} {word : List A.Token}
    (pt : ParseTree (.NT nt) word) (ptz : PtZipper init full_word (.NT nt) word) :
    Option (PtDot init full_word) :=
  match ptz, pt with
  | .Top_ptz, _ => none
  | .Cons_ptl_ptz ptl' ptlz, pt => some (buildPtDotFromPtl init full_word (.Cons_ptl ptl' pt) ptlz)

/-- The dotted parse tree after one parser action (Coq `next_ptd`). -/
def nextPtd : PtDot init full_word → Option (PtDot init full_word)
  | .Shift_ptd tok ptl ptlz =>
      some (buildPtDotFromPtl init full_word (.Cons_ptl ptl (.Terminal_pt tok)) ptlz)
  | .Reduce_ptd (prod := prod) ptl ptz =>
      nextPtdAux init full_word (.Non_terminal_pt prod ptl) ptz

/-- Iterating `nextPtd` `2 ^ log_n_steps` times (Coq `next_ptd_iter`). -/
def nextPtdIter : PtDot init full_word → Nat → Option (PtDot init full_word)
  | ptd, 0 => nextPtd init full_word ptd
  | ptd, n + 1 =>
      match nextPtdIter ptd n with
      | none => none
      | some ptd' => nextPtdIter ptd' n

/-! ### `build_pt_dot` preserves semantics -/

/- The dotted parse tree built from a parse tree has the same semantic value
(Coq `sem_build_from_pt` / `sem_build_from_pt_rec`). -/
mutual
theorem sem_build_from_pt : {symb : Symbol A.Terminal A.Nonterminal} → {word : List A.Token} →
    (pt : ParseTree symb word) → (ptz : PtZipper init full_word symb word) →
    ptzSem init full_word ptz (ptSem pt) =
      ptdSem init full_word (buildPtDotFromPt init full_word pt ptz)
  | _, _, .Terminal_pt tok, ptz => by
      cases ptz with
      | Cons_ptl_ptz ptl ptlz =>
        simp only [buildPtDotFromPt, ptSem, ptdSem, ptzSem]
  | _, _, .Non_terminal_pt prod ptl, ptz => by
      simp only [buildPtDotFromPt, ptSem]
      cases h : nonNilProof ptl with
      | none => simp only [ptdSem]
      | some H =>
        rw [← sem_build_from_pt_rec ptl H (.Non_terminal_pt_ptlz ptz)]
        simp only [ptlzSem]
theorem sem_build_from_pt_rec : {symbs : List (Symbol A.Terminal A.Nonterminal)} →
    {word : List A.Token} → (ptl : ParseTreeList symbs word) → (H : NonNilT symbs) →
    (ptlz : PtlZipper init full_word symbs word) →
    ptlzSem init full_word ptlz (fun _ f => ptlSem ptl f) =
      ptdSem init full_word (buildPtDotFromPtRec init full_word ptl H ptlz)
  | _, _, .Nil_ptl, H, _ => H.elim
  | _, _, .Cons_ptl ptl' pt, _, ptlz => by
      cases ptl' with
      | Nil_ptl =>
        simp only [buildPtDotFromPtRec]
        rw [← sem_build_from_pt pt (.Cons_ptl_ptz .Nil_ptl ptlz)]
        simp only [ptzSem, ptlSem]
      | Cons_ptl a b =>
        simp only [buildPtDotFromPtRec]
        rw [← sem_build_from_pt_rec (.Cons_ptl a b) Unit.unit (.Cons_ptl_ptlz pt ptlz)]
        simp only [ptlzSem, ptlSem]
end

/-- The dotted parse tree built from a completed list has the same semantic value
(Coq `sem_build_from_ptl`). -/
theorem sem_build_from_ptl {symbs : List (Symbol A.Terminal A.Nonterminal)} {word : List A.Token}
    (ptl : ParseTreeList symbs word) (ptlz : PtlZipper init full_word symbs word) :
    ptlzSem init full_word ptlz (fun _ f => ptlSem ptl f) =
      ptdSem init full_word (buildPtDotFromPtl init full_word ptl ptlz) := by
  cases ptlz with
  | Non_terminal_pt_ptlz ptz => simp only [buildPtDotFromPtl, ptdSem, ptlzSem]
  | Cons_ptl_ptlz pt ptlz' =>
    simp only [buildPtDotFromPtl]
    rw [← sem_build_from_pt init full_word pt (.Cons_ptl_ptz ptl ptlz')]
    simp only [ptzSem, ptlzSem]

/-- `nextPtdAux` preserves the semantic value. -/
theorem sem_nextPtdAux {nt : A.Nonterminal} {word : List A.Token}
    (pt : ParseTree (.NT nt) word) (ptz : PtZipper init full_word (.NT nt) word) :
    match nextPtdAux init full_word pt ptz with
    | none => True
    | some ptd' => ptzSem init full_word ptz (ptSem pt) = ptdSem init full_word ptd' := by
  cases ptz with
  | Top_ptz => trivial
  | Cons_ptl_ptz ptl' ptlz =>
    simp only [nextPtdAux]
    rw [← sem_build_from_ptl]
    simp only [ptzSem, ptlSem]

/-- `nextPtd` preserves the semantic value (Coq `sem_next_ptd`). -/
theorem sem_next_ptd (ptd : PtDot init full_word) :
    match nextPtd init full_word ptd with
    | none => True
    | some ptd' => ptdSem init full_word ptd = ptdSem init full_word ptd' := by
  cases ptd with
  | Shift_ptd tok ptl ptlz =>
    simp only [nextPtd]
    rw [← sem_build_from_ptl]
    simp only [ptdSem, ptlSem, ptSem]
  | @Reduce_ptd prod word ptl ptz =>
    have h := sem_nextPtdAux init full_word (.Non_terminal_pt prod ptl) ptz
    simp only [ptSem] at h
    simp only [nextPtd, ptdSem]
    exact h

/-- `nextPtdIter` preserves the semantic value (Coq `sem_next_ptd_iter`). -/
theorem sem_next_ptd_iter (ptd : PtDot init full_word) (logNSteps : Nat) :
    match nextPtdIter init full_word ptd logNSteps with
    | none => True
    | some ptd' => ptdSem init full_word ptd = ptdSem init full_word ptd' := by
  induction logNSteps generalizing ptd with
  | zero => exact sem_next_ptd init full_word ptd
  | succ n ih =>
    have IH1 := ih ptd
    cases h : nextPtdIter init full_word ptd n with
    | none => simp only [nextPtdIter, h]
    | some ptd' =>
      rw [h] at IH1
      simp only [nextPtdIter, h]
      have IH2 := ih ptd'
      cases h2 : nextPtdIter init full_word ptd' n with
      | none => trivial
      | some ptd'' =>
        rw [h2] at IH2
        exact IH1.trans IH2

/-! ### `build_pt_dot` preserves the remaining buffer -/

/-- If `nonNilProof` says nil, the word is empty. -/
theorem nonNilProof_none {symbs : List (Symbol A.Terminal A.Nonterminal)} {word : List A.Token}
    (ptl : ParseTreeList symbs word) (h : nonNilProof ptl = none) : word = [] := by
  cases ptl with
  | Nil_ptl => rfl
  | Cons_ptl _ _ => simp [nonNilProof] at h

/- The buffer of the dotted parse tree built from a parse tree is the recognised
word followed by the zipper's buffer (Coq `ptd_buffer_build_from_pt`). -/
mutual
theorem ptd_buffer_build_from_pt : {symb : Symbol A.Terminal A.Nonterminal} →
    {word : List A.Token} → (pt : ParseTree symb word) → (ptz : PtZipper init full_word symb word) →
    word ++ₛ ptzBuffer init full_word buffer_end ptz =
      ptdBuffer init full_word buffer_end (buildPtDotFromPt init full_word pt ptz)
  | _, _, .Terminal_pt tok, ptz => by
      cases ptz with
      | Cons_ptl_ptz ptl ptlz =>
        simp only [buildPtDotFromPt, ptdBuffer, ptzBuffer, Stream'.cons_append_stream,
          Stream'.nil_append_stream]
  | _, _, .Non_terminal_pt prod ptl, ptz => by
      simp only [buildPtDotFromPt]
      cases h : nonNilProof ptl with
      | none =>
        have hw := nonNilProof_none ptl h
        subst hw
        simp only [ptdBuffer, Stream'.nil_append_stream]
      | some H =>
        rw [← ptd_buffer_build_from_pt_rec ptl H (.Non_terminal_pt_ptlz ptz)]
        simp only [ptlzBuffer]
theorem ptd_buffer_build_from_pt_rec : {symbs : List (Symbol A.Terminal A.Nonterminal)} →
    {word : List A.Token} → (ptl : ParseTreeList symbs word) → (H : NonNilT symbs) →
    (ptlz : PtlZipper init full_word symbs word) →
    word ++ₛ ptlzBuffer init full_word buffer_end ptlz =
      ptdBuffer init full_word buffer_end (buildPtDotFromPtRec init full_word ptl H ptlz)
  | _, _, .Nil_ptl, H, _ => H.elim
  | _, _, .Cons_ptl ptl' pt, _, ptlz => by
      cases ptl' with
      | Nil_ptl =>
        simp only [buildPtDotFromPtRec, List.nil_append]
        rw [← ptd_buffer_build_from_pt pt (.Cons_ptl_ptz .Nil_ptl ptlz)]
        simp only [ptzBuffer]
        rfl
      | Cons_ptl a b =>
        simp only [buildPtDotFromPtRec]
        rw [← ptd_buffer_build_from_pt_rec (.Cons_ptl a b) Unit.unit (.Cons_ptl_ptlz pt ptlz)]
        simp only [ptlzBuffer, Stream'.append_append_stream]
end

/-- The buffer of the dotted parse tree built from a completed list
(Coq `ptd_buffer_build_from_ptl`). -/
theorem ptd_buffer_build_from_ptl {symbs : List (Symbol A.Terminal A.Nonterminal)}
    {word : List A.Token} (ptl : ParseTreeList symbs word)
    (ptlz : PtlZipper init full_word symbs word) :
    ptlzBuffer init full_word buffer_end ptlz =
      ptdBuffer init full_word buffer_end (buildPtDotFromPtl init full_word ptl ptlz) := by
  cases ptlz with
  | Non_terminal_pt_ptlz ptz => simp only [buildPtDotFromPtl, ptdBuffer, ptlzBuffer]
  | Cons_ptl_ptlz pt ptlz' =>
    simp only [buildPtDotFromPtl, ptlzBuffer]
    rw [← ptd_buffer_build_from_pt init full_word buffer_end pt (.Cons_ptl_ptz ptl ptlz')]
    simp only [ptzBuffer]

/-! ### `build_pt_dot` preserves stack compatibility -/

/-- From a stack compatible with a zipper whose hole is `NT nt` (with `prod` a
production for `nt`), the top state predicts `prod` at the dot's start. This is
the heart of `ptd_stack_compat_build_from_pt`'s non-terminal case; phrased over a
generic `nt` so the zipper can be `cases`d (Coq's `remember`/`destruct` step). -/
theorem stateHasFuture_of_ptzStackCompat (hc : complete) {nt : A.Nonterminal}
    {word : List A.Token} (ptz : PtZipper init full_word (.NT nt) word) (stk : Stack)
    (prod : A.Production) (hprod : A.prod_lhs prod = nt)
    (Hstk : ptzStackCompat init full_word buffer_end stk ptz) :
    stateHasFuture (stateOfStack init stk) prod (futureOfProd prod 0)
      (A.token_term (ptzBuffer init full_word buffer_end ptz).head) := by
  cases ptz with
  | Top_ptz =>
    simp only [ptzStackCompat] at Hstk
    subst Hstk
    exact startFuture_of_complete hc init prod hprod _
  | Cons_ptl_ptz ptl0 ptlz0 =>
    simp only [ptzStackCompat] at Hstk
    obtain ⟨stk0, Hf, _, _⟩ := Hstk
    have hclosed := nonTerminalClosed_of_complete hc _ _ _ _ Hf
    have hp := hclosed prod hprod
    obtain ⟨hnull, hfirst⟩ := hp
    simp only [ptzBuffer]
    rcases ptlz_future_first init full_word buffer_end hc ptlz0 with hl | ⟨he, hnu⟩
    · exact hfirst _ hl
    · rw [he]; rw [if_pos hnu] at hnull; exact hnull

/-- If `nonNilProof` says nil, the symbol list is empty. -/
theorem nonNilProof_none_symbs {symbs : List (Symbol A.Terminal A.Nonterminal)}
    {word : List A.Token} (ptl : ParseTreeList symbs word) (h : nonNilProof ptl = none) :
    symbs = [] := by
  cases ptl with
  | Nil_ptl => rfl
  | Cons_ptl _ _ => simp [nonNilProof] at h

/-- A nil parse-tree list is stack-compatible with any stack (reflexively). -/
theorem ptlStackCompat_nil {symbs : List (Symbol A.Terminal A.Nonterminal)} {word : List A.Token}
    (ptl : ParseTreeList symbs word) (stk0 : Stack) (h : nonNilProof ptl = none) :
    ptlStackCompat stk0 ptl stk0 := by
  cases ptl with
  | Nil_ptl => simp only [ptlStackCompat]
  | Cons_ptl _ _ => simp [nonNilProof] at h

/-- `futureOfProd` of a zipper's production at the start equals the recognised
symbols (reversed) followed by the future. -/
theorem futureOfProd_ptlzProd {symbs : List (Symbol A.Terminal A.Nonterminal)}
    {word : List A.Token} (ptlz : PtlZipper init full_word symbs word) :
    futureOfProd (ptlzProd init full_word ptlz) 0 = symbs.reverse ++ ptlzFuture init full_word ptlz := by
  simp only [futureOfProd, List.drop_zero]
  rw [← ptlz_future_ptlz_prod init full_word ptlz, List.reverseAux_eq]
  simp [List.reverse_append, List.reverse_reverse]

/- The dotted parse tree built from a parse tree is stack-compatible (Coq
`ptd_stack_compat_build_from_pt` / `ptd_stack_compat_build_from_pt_rec`). -/
mutual
theorem ptd_stack_compat_build_from_pt (hc : complete) :
    {symb : Symbol A.Terminal A.Nonterminal} → {word : List A.Token} →
    (pt : ParseTree symb word) → (ptz : PtZipper init full_word symb word) → (stk : Stack) →
    ptzStackCompat init full_word buffer_end stk ptz →
    ptdStackCompat init full_word buffer_end (buildPtDotFromPt init full_word pt ptz) stk
  | _, _, .Terminal_pt _, ptz, stk, Hstk => by
      cases ptz with
      | Cons_ptl_ptz ptl ptlz =>
        simpa only [buildPtDotFromPt, ptdStackCompat, ptzStackCompat] using Hstk
  | _, _, .Non_terminal_pt prod ptl, ptz, stk, Hstk => by
      have Hassert := stateHasFuture_of_ptzStackCompat init full_word buffer_end hc ptz stk prod rfl Hstk
      simp only [buildPtDotFromPt]
      cases h : nonNilProof ptl with
      | none =>
        have hsymbs := nonNilProof_none_symbs ptl h
        simp only [futureOfProd, hsymbs, List.reverse_nil, List.drop_nil] at Hassert
        exact ⟨stk, Hassert, ptlStackCompat_nil ptl stk h, Hstk⟩
      | some H =>
        exact ptd_stack_compat_build_from_pt_rec hc ptl H (.Non_terminal_pt_ptlz ptz) stk
          (by simpa only [ptlzStackCompat] using Hstk)
          (by simpa only [ptlzProd, ptlzLookahead] using Hassert)
theorem ptd_stack_compat_build_from_pt_rec (hc : complete) :
    {symbs : List (Symbol A.Terminal A.Nonterminal)} → {word : List A.Token} →
    (ptl : ParseTreeList symbs word) → (H : NonNilT symbs) →
    (ptlz : PtlZipper init full_word symbs word) → (stk : Stack) →
    ptlzStackCompat init full_word buffer_end stk ptlz →
    stateHasFuture (stateOfStack init stk) (ptlzProd init full_word ptlz)
      (futureOfProd (ptlzProd init full_word ptlz) 0) (ptlzLookahead init full_word buffer_end ptlz) →
    ptdStackCompat init full_word buffer_end (buildPtDotFromPtRec init full_word ptl H ptlz) stk
  | _, _, .Nil_ptl, H, _, _, _, _ => H.elim
  | _, _, .Cons_ptl ptl' pt, _, ptlz, stk, Hstk, Hfut => by
      cases ptl' with
      | Nil_ptl =>
        simp only [buildPtDotFromPtRec]
        rw [futureOfProd_ptlzProd init full_word ptlz] at Hfut
        simp only [List.reverse_cons, List.reverse_nil, List.nil_append] at Hfut
        apply ptd_stack_compat_build_from_pt hc pt (.Cons_ptl_ptz .Nil_ptl ptlz) stk
        exact ⟨stk, Hfut, by simp only [ptlStackCompat], Hstk⟩
      | Cons_ptl a b =>
        simp only [buildPtDotFromPtRec]
        exact ptd_stack_compat_build_from_pt_rec hc (.Cons_ptl a b) Unit.unit
          (.Cons_ptl_ptlz pt ptlz) stk
          (by simpa only [ptlzStackCompat] using Hstk)
          (by simpa only [ptlzProd, ptlzLookahead] using Hfut)
end

/-- The dotted parse tree built from a completed list is stack-compatible (Coq
`ptd_stack_compat_build_from_ptl`). -/
theorem ptd_stack_compat_build_from_ptl (hc : complete)
    {symbs : List (Symbol A.Terminal A.Nonterminal)} {word : List A.Token}
    (ptl : ParseTreeList symbs word) (ptlz : PtlZipper init full_word symbs word)
    (stk stk0 : Stack) (Hstk0 : ptlzStackCompat init full_word buffer_end stk0 ptlz)
    (Hstk : ptlStackCompat stk0 ptl stk)
    (Hfut : stateHasFuture (stateOfStack init stk) (ptlzProd init full_word ptlz)
      (ptlzFuture init full_word ptlz) (ptlzLookahead init full_word buffer_end ptlz)) :
    ptdStackCompat init full_word buffer_end (buildPtDotFromPtl init full_word ptl ptlz) stk := by
  cases ptlz with
  | Non_terminal_pt_ptlz ptz =>
    simp only [buildPtDotFromPtl, ptdStackCompat]
    refine ⟨stk0, ?_, Hstk, ?_⟩
    · simpa only [ptlzProd, ptlzFuture, ptlzLookahead] using Hfut
    · simpa only [ptlzStackCompat] using Hstk0
  | Cons_ptl_ptlz pt ptlz' =>
    simp only [buildPtDotFromPtl]
    apply ptd_stack_compat_build_from_pt init full_word buffer_end hc pt (.Cons_ptl_ptz ptl ptlz') stk
    simp only [ptzStackCompat]
    refine ⟨stk0, ?_, Hstk, ?_⟩
    · simpa only [ptlzProd, ptlzFuture, ptlzLookahead] using Hfut
    · simpa only [ptlzStackCompat] using Hstk0

end Completeness

end LeanMenhir
