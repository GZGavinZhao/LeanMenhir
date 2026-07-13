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


namespace LeanMenhir

open Buf

variable {G : Grammar} {A : Automaton G}

/-! ### Fixpoint-correctness lemmas for `nullable` and `first` -/

/- If a parse tree recognises the empty word, its head symbol is nullable
(Coq `nullable_correct` / `nullable_correct_list`). -/
mutual
theorem nullable_correct (hc : Complete A) :
    {head : Symbol G.Terminal G.Nonterminal} → {word : List G.Token} →
    word = [] → ParseTree G head word → nullableSymb A head = true
  | _, _, hw, .Terminal_pt _ => by simp at hw
  | _, _, hw, .Non_terminal_pt prod ptl => by
    have hnull := nullable_correct_list hc hw ptl
    have hs := nullableStable_of_complete hc prod
    rw [if_pos hnull] at hs
    exact hs
theorem nullable_correct_list (hc : Complete A) :
    {heads : List (Symbol G.Terminal G.Nonterminal)} → {word : List G.Token} →
    word = [] → ParseTreeList G heads word → nullableWord A heads = true
  | _, _, _, .Nil_ptl => rfl
  | _, _, hw, .Cons_ptl q t => by
    obtain ⟨hq, ht⟩ := List.append_eq_nil_iff.1 hw
    have h1 := nullable_correct_list hc hq q
    have h2 := nullable_correct hc ht t
    simp only [nullableWord, List.all_cons]
    rw [Bool.and_eq_true]
    exact ⟨h2, h1⟩
end

/-- `firstWordSet A` distributes over append (Coq `first_word_set_app`). -/
theorem first_word_set_app (t : G.Terminal)
    (word1 word2 : List (Symbol G.Terminal G.Nonterminal)) :
    t ∈ firstWordSet A (word1 ++ word2) ↔
    t ∈ firstWordSet A word1 ∨ (t ∈ firstWordSet A word2 ∧ nullableWord A word1.reverse = true) := by
  induction word1 with
  | nil => simp [firstWordSet, nullableWord]
  | cons s word1 IH =>
    rw [List.cons_append]
    by_cases hs : nullableSymb A s = true
    · simp only [firstWordSet, hs, if_true, List.mem_append, IH, List.reverse_cons,
        nullableWord, List.all_append, List.all_cons, List.all_nil, Bool.and_true]
      grind
    · simp only [Bool.not_eq_true] at hs
      simp only [firstWordSet, hs, Bool.false_eq_true, if_false, List.reverse_cons,
        nullableWord, List.all_append, List.all_cons, List.all_nil, Bool.and_true,
        Bool.and_false, and_false, or_false]

/- If a parse tree recognises a word starting with `t`, then `token_term t` is in
the first set of the head symbol (Coq `first_correct` / `first_correct_list`). -/
mutual
theorem first_correct (hc : Complete A) :
    {head : Symbol G.Terminal G.Nonterminal} → {t : G.Token} → {q : List G.Token} →
    ParseTree G head (t :: q) → G.token_term t ∈ firstSymbSet A head
  | _, _, _, .Terminal_pt _ => by simp [firstSymbSet]
  | _, _, _, .Non_terminal_pt prod ptl => by
    simp only [firstSymbSet]
    exact firstStable_of_complete hc prod _ (first_correct_list hc rfl ptl)
theorem first_correct_list (hc : Complete A) :
    {heads : List (Symbol G.Terminal G.Nonterminal)} → {word : List G.Token} →
    {t : G.Token} → {q : List G.Token} →
    word = t :: q → ParseTreeList G heads word →
    G.token_term t ∈ firstWordSet A heads.reverse
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

/-! ### Stack A compatibility for parse-tree lists -/

/-- A parse-tree list is compatible with a stack when the top of the stack holds
exactly the semantic values of the list (Coq `ptl_stack_compat`). -/
def ptlStackCompat (stk0 : Stack A) :
    {symbs : List (Symbol G.Terminal G.Nonterminal)} → {word : List G.Token} →
    ParseTreeList G symbs word → Stack A → Prop
  | _, _, .Nil_ptl, stk => stk0 = stk
  | _, _, .Cons_ptl ptl' pt, stk =>
      match stk with
      | [] => False
      | cell :: stk' =>
          ptlStackCompat stk0 ptl' stk' ∧
          ∃ e : _ = A.last_symb_of_non_init_state cell.1,
            cell.2 = cast (congrArg G.symbol_semantic_type e) (ptSem pt)

/-- When a parse-tree list is compatible with a stack, `pop`ping it (per the
declarative spec) yields the list's semantic value (Coq
`pop_stack_compat_pop_spec`). -/
theorem pop_stack_compat_pop_spec {R : Type} :
    {symbs : List (Symbol G.Terminal G.Nonterminal)} → {word : List G.Token} →
    (ptl : ParseTreeList G symbs word) → (stk stk0 : Stack A) →
    (action : arrowsRight R (symbs.map G.symbol_semantic_type)) →
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

/-- The concrete `pop` agrees with any `PopSpec` derivation (reverse of
`pop_spec_ok`). -/
theorem pop_eq_of_popSpec {R : Type} {symbs : List (Symbol G.Terminal G.Nonterminal)} {stk : Stack A}
    {action : arrowsRight R (symbs.map G.symbol_semantic_type)} {stk0 : Stack A} {res : R}
    (h : PopSpec symbs stk action stk0 res) :
    ∀ hp : Prefix symbs (symbStackOfStack stk), pop symbs stk hp action = (stk0, res) := by
  induction h with
  | nil stk0 sem => intro hp; rfl
  | cons st stk0' action' sem stk' res' h' ih =>
    intro hp
    rw [pop]
    have hcast : cast (congrArg G.symbol_semantic_type (Prefix.inv_cons hp).1.symm) sem = sem :=
      eq_of_heq (cast_heq _ _)
    rw [hcast]
    exact ih _

/-! ### Dotted parse trees -/

section Completeness

/- The initial state, the full word to be parsed, and the buffer left over at the
end of parsing are fixed throughout the completeness proof (Coq's section
`Variable`s). -/
variable (init : A.InitState) (full_word : List G.Token) (buffer_end : Buffer G)

/- A "parse tree zipper" is a parse tree with a hole, represented upside-down: the
root of the original tree is a leaf of the zipper and the hole is its root. Coq
`pt_zipper` / `ptl_zipper`. -/
mutual
inductive PtZipper : Symbol G.Terminal G.Nonterminal → List G.Token → Type where
  | Top_ptz : PtZipper (.NT (A.start_nt init)) full_word
  | Cons_ptl_ptz {head_symbolsq : List (Symbol G.Terminal G.Nonterminal)}
      {wordq : List G.Token} : ParseTreeList G head_symbolsq wordq →
      {head_symbolt : Symbol G.Terminal G.Nonterminal} → {wordt : List G.Token} →
      PtlZipper (head_symbolt :: head_symbolsq) (wordq ++ wordt) →
      PtZipper head_symbolt wordt
inductive PtlZipper : List (Symbol G.Terminal G.Nonterminal) → List G.Token → Type where
  | Non_terminal_pt_ptlz {p : G.Production} {word : List G.Token} :
      PtZipper (.NT (G.prod_lhs p)) word → PtlZipper (G.prod_rhs_rev p) word
  | Cons_ptl_ptlz {head_symbolsq : List (Symbol G.Terminal G.Nonterminal)}
      {wordq : List G.Token} {head_symbolt : Symbol G.Terminal G.Nonterminal}
      {wordt : List G.Token} : ParseTree G head_symbolt wordt →
      PtlZipper (head_symbolt :: head_symbolsq) (wordq ++ wordt) →
      PtlZipper head_symbolsq wordq
end

/-- A dotted parse tree: a zipper plus the sub-tree under the dot, in either a
reduce or a shift configuration (Coq `pt_dot`). -/
inductive PtDot : Type where
  | Reduce_ptd {prod : G.Production} {word : List G.Token} :
      ParseTreeList G (G.prod_rhs_rev prod) word →
      PtZipper init full_word (.NT (G.prod_lhs prod)) word → PtDot
  | Shift_ptd (tok : G.Token) {symbolsq : List (Symbol G.Terminal G.Nonterminal)}
      {wordq : List G.Token} : ParseTreeList G symbolsq wordq →
      PtlZipper init full_word (.T (G.token_term tok) :: symbolsq) (wordq ++ [tok]) → PtDot

/- The semantic value of a dotted parse tree, computed from the zipper part
(Coq `ptlz_sem` / `ptz_sem`). -/
mutual
def ptlzSem : {holeSymbs : List (Symbol G.Terminal G.Nonterminal)} → {holeWord : List G.Token} →
    PtlZipper init full_word holeSymbs holeWord →
    (∀ B : Type, arrowsRight B (holeSymbs.map G.symbol_semantic_type) → B) →
    G.symbol_semantic_type (.NT (A.start_nt init))
  | _, _, .Non_terminal_pt_ptlz (p := prod) ptz, k => ptzSem ptz (k _ (G.prod_action prod))
  | _, _, .Cons_ptl_ptlz pt ptlz, k => ptlzSem ptlz (fun _ f => k _ (f (ptSem pt)))
def ptzSem : {holeSymb : Symbol G.Terminal G.Nonterminal} → {holeWord : List G.Token} →
    PtZipper init full_word holeSymb holeWord →
    G.symbol_semantic_type holeSymb → G.symbol_semantic_type (.NT (A.start_nt init))
  | _, _, .Top_ptz, sem => sem
  | _, _, .Cons_ptl_ptz ptl ptlz, sem => ptlzSem ptlz (fun _ f => ptlSem ptl (f sem))
end

/-- The semantic value of a dotted parse tree (Coq `ptd_sem`). -/
def ptdSem : PtDot init full_word → G.symbol_semantic_type (.NT (A.start_nt init))
  | .Reduce_ptd (prod := prod) ptl ptz => ptzSem init full_word ptz (ptlSem ptl (G.prod_action prod))
  | .Shift_ptd tok ptl ptlz =>
      ptlzSem init full_word ptlz (fun _ f => ptlSem ptl (f (G.token_sem tok)))

/- The buffer left to read at a dotted parse tree (Coq `ptlz_buffer` / `ptz_buffer`). -/
mutual
def ptlzBuffer : {holeSymbs : List (Symbol G.Terminal G.Nonterminal)} → {holeWord : List G.Token} →
    PtlZipper init full_word holeSymbs holeWord → Buffer G
  | _, _, .Non_terminal_pt_ptlz ptz => ptzBuffer ptz
  | _, _, .Cons_ptl_ptlz (wordt := wordt) _ ptlz => wordt ++ₛ ptlzBuffer ptlz
def ptzBuffer : {holeSymb : Symbol G.Terminal G.Nonterminal} → {holeWord : List G.Token} →
    PtZipper init full_word holeSymb holeWord → Buffer G
  | _, _, .Top_ptz => buffer_end
  | _, _, .Cons_ptl_ptz _ ptlz => ptlzBuffer ptlz
end

/-- The buffer at a dotted parse tree (Coq `ptd_buffer`). -/
def ptdBuffer : PtDot init full_word → Buffer G
  | .Reduce_ptd _ ptz => ptzBuffer init full_word buffer_end ptz
  | .Shift_ptd tok _ ptlz => Buf.cons tok (ptlzBuffer init full_word buffer_end ptlz)

/-- The production at the root of a parse-tree-list zipper (Coq `ptlz_prod`). -/
def ptlzProd : {holeSymbs : List (Symbol G.Terminal G.Nonterminal)} → {holeWord : List G.Token} →
    PtlZipper init full_word holeSymbs holeWord → G.Production
  | _, _, .Non_terminal_pt_ptlz (p := prod) _ => prod
  | _, _, .Cons_ptl_ptlz _ ptlz => ptlzProd ptlz

/-- The symbols still to be read in the current production (Coq `ptlz_future`). -/
def ptlzFuture : {holeSymbs : List (Symbol G.Terminal G.Nonterminal)} → {holeWord : List G.Token} →
    PtlZipper init full_word holeSymbs holeWord → List (Symbol G.Terminal G.Nonterminal)
  | _, _, .Non_terminal_pt_ptlz _ => []
  | _, _, .Cons_ptl_ptlz (head_symbolt := s) _ ptlz => s :: ptlzFuture ptlz

/-- The lookahead terminal of a parse-tree-list zipper (Coq `ptlz_lookahead`). -/
def ptlzLookahead : {holeSymbs : List (Symbol G.Terminal G.Nonterminal)} → {holeWord : List G.Token} →
    PtlZipper init full_word holeSymbs holeWord → G.Terminal
  | _, _, .Non_terminal_pt_ptlz ptz => G.token_term (ptzBuffer init full_word buffer_end ptz).head
  | _, _, .Cons_ptl_ptlz _ ptlz => ptlzLookahead ptlz

/- A stack is compatible with a parse-tree zipper when it is built from stack
fragments matching each partially-recognised production in the zipper, with each
fragment's top state predicting the corresponding item (Coq `ptz_stack_compat` /
`ptlz_stack_compat`). -/
mutual
def ptzStackCompat : {holeSymb : Symbol G.Terminal G.Nonterminal} → {holeWord : List G.Token} →
    Stack A → PtZipper init full_word holeSymb holeWord → Prop
  | _, _, stk, .Top_ptz => stk = []
  | holeSymb, _, stk, .Cons_ptl_ptz ptl ptlz =>
      ∃ stk0, stateHasFuture (stateOfStack init stk) (ptlzProd init full_word ptlz)
          (holeSymb :: ptlzFuture init full_word ptlz)
          (ptlzLookahead init full_word buffer_end ptlz) ∧
        ptlStackCompat stk0 ptl stk ∧ ptlzStackCompat stk0 ptlz
def ptlzStackCompat : {holeSymbs : List (Symbol G.Terminal G.Nonterminal)} → {holeWord : List G.Token} →
    Stack A → PtlZipper init full_word holeSymbs holeWord → Prop
  | _, _, stk, .Non_terminal_pt_ptlz ptz => ptzStackCompat stk ptz
  | _, _, stk, .Cons_ptl_ptlz _ ptlz => ptlzStackCompat stk ptlz
end

/-- A stack is compatible with a dotted parse tree (Coq `ptd_stack_compat`). -/
def ptdStackCompat : PtDot init full_word → Stack A → Prop
  | .Reduce_ptd (prod := prod) ptl ptz, stk =>
      ∃ stk0, stateHasFuture (stateOfStack init stk) prod []
          (G.token_term (ptzBuffer init full_word buffer_end ptz).head) ∧
        ptlStackCompat stk0 ptl stk ∧ ptzStackCompat init full_word buffer_end stk0 ptz
  | .Shift_ptd tok ptl ptlz, stk =>
      ∃ stk0, stateHasFuture (stateOfStack init stk) (ptlzProd init full_word ptlz)
          (.T (G.token_term tok) :: ptlzFuture init full_word ptlz)
          (ptlzLookahead init full_word buffer_end ptlz) ∧
        ptlStackCompat stk0 ptl stk ∧ ptlzStackCompat init full_word buffer_end stk0 ptlz

/-- The top of a `Cons_ptl_ptz`-compatible stack predicts the zipper's item
(Coq `ptz_stack_compat_cons_state_has_future`). -/
theorem ptz_stack_compat_cons_state_has_future {symbsq : List (Symbol G.Terminal G.Nonterminal)}
    {wordq : List G.Token} {symbt : Symbol G.Terminal G.Nonterminal} {wordt : List G.Token}
    (stk : Stack A) (ptl : ParseTreeList G symbsq wordq)
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
    {holeSymbs : List (Symbol G.Terminal G.Nonterminal)} → {holeWord : List G.Token} →
    (ptlz : PtlZipper init full_word holeSymbs holeWord) →
    List.reverseAux (ptlzFuture init full_word ptlz) holeSymbs =
      G.prod_rhs_rev (ptlzProd init full_word ptlz)
  | _, _, .Non_terminal_pt_ptlz _ => by simp [ptlzFuture, ptlzProd]
  | _, _, .Cons_ptl_ptlz pt ptlz' => by
      simp only [ptlzFuture, ptlzProd, List.reverseAux]
      exact ptlz_future_ptlz_prod ptlz'

/-- The lookahead of a zipper is in the first set of its future, or the future is
nullable and the lookahead equals the recorded lookahead (Coq `ptlz_future_first`). -/
theorem ptlz_future_first (hc : Complete A) :
    {symbs : List (Symbol G.Terminal G.Nonterminal)} → {word : List G.Token} →
    (ptlz : PtlZipper init full_word symbs word) →
    G.token_term (ptlzBuffer init full_word buffer_end ptlz).head ∈
        firstWordSet A (ptlzFuture init full_word ptlz) ∨
    (G.token_term (ptlzBuffer init full_word buffer_end ptlz).head =
        ptlzLookahead init full_word buffer_end ptlz ∧
      nullableWord A (ptlzFuture init full_word ptlz) = true)
  | _, _, .Non_terminal_pt_ptlz ptz => by
      refine Or.inr ⟨?_, ?_⟩
      · simp [ptlzBuffer, ptlzLookahead]
      · simp [ptlzFuture, nullableWord]
  | _, _, .Cons_ptl_ptlz (head_symbolt := s) (wordt := wordt) pt ptlz' => by
      have IH := ptlz_future_first hc ptlz'
      simp only [ptlzBuffer, ptlzFuture, ptlzLookahead]
      cases wordt with
      | nil =>
          rw [Buf.nil_append_stream]
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
          rw [Buf.cons_append_stream]
          left
          have hfirst := first_correct hc pt
          show G.token_term c ∈ firstWordSet A (s :: ptlzFuture init full_word ptlz')
          simp only [firstWordSet]
          by_cases hn : nullableSymb A s = true
          · simp only [hn, if_true]
            exact List.mem_append.2 (Or.inl hfirst)
          · simp only [Bool.not_eq_true] at hn
            simp only [hn, Bool.false_eq_true, if_false]
            exact hfirst
  termination_by _ _ ptlz => sizeOf ptlz

/-! ### Moving the dot: `build_pt_dot_from_pt` and `next_ptd` -/

/-- A `Type`-valued witness that a parse-tree list is non-nil (mirrors Coq's
`is_notnil`, but in `Type` since Lean's `Option` cannot wrap a `Prop`). -/
abbrev NonNilT (symbs : List (Symbol G.Terminal G.Nonterminal)) : Type :=
  match symbs with | [] => Empty | _ => Unit

def nonNilProof : {symbs : List (Symbol G.Terminal G.Nonterminal)} → {word : List G.Token} →
    ParseTreeList G symbs word → Option (NonNilT symbs)
  | _, _, .Nil_ptl => none
  | _, _, .Cons_ptl _ _ => some Unit.unit

/- Build the next dotted parse tree from a parse tree under the dot (Coq
`build_pt_dot_from_pt` / `build_pt_dot_from_pt_rec`). -/
mutual
def buildPtDotFromPt : {symb : Symbol G.Terminal G.Nonterminal} → {word : List G.Token} →
    ParseTree G symb word → PtZipper init full_word symb word → PtDot init full_word
  | _, _, .Terminal_pt tok, ptz =>
      match ptz with
      | .Cons_ptl_ptz ptl ptlz => .Shift_ptd tok ptl ptlz
  | _, _, .Non_terminal_pt _ ptl, ptz =>
      match nonNilProof ptl with
      | none => .Reduce_ptd ptl ptz
      | some H => buildPtDotFromPtRec ptl H (.Non_terminal_pt_ptlz ptz)
def buildPtDotFromPtRec : {symbs : List (Symbol G.Terminal G.Nonterminal)} → {word : List G.Token} →
    (ptl : ParseTreeList G symbs word) → NonNilT symbs →
    PtlZipper init full_word symbs word → PtDot init full_word
  | _, _, .Nil_ptl, hsymbs, _ => hsymbs.elim
  | _, _, .Cons_ptl ptl' pt, _, ptlz =>
      match ptl' with
      | .Nil_ptl => buildPtDotFromPt pt (.Cons_ptl_ptz .Nil_ptl ptlz)
      | .Cons_ptl a b => buildPtDotFromPtRec (.Cons_ptl a b) Unit.unit (.Cons_ptl_ptlz pt ptlz)
end

/-- Build the next dotted parse tree from a completed parse-tree list under a
zipper (Coq `build_pt_dot_from_ptl`). -/
def buildPtDotFromPtl : {symbs : List (Symbol G.Terminal G.Nonterminal)} → {word : List G.Token} →
    ParseTreeList G symbs word → PtlZipper init full_word symbs word → PtDot init full_word
  | _, _, ptl, .Non_terminal_pt_ptlz ptz => .Reduce_ptd ptl ptz
  | _, _, ptl, .Cons_ptl_ptlz pt ptlz => buildPtDotFromPt init full_word pt (.Cons_ptl_ptz ptl ptlz)

/-- The reduce-step continuation, over a *generic* nonterminal so that `cases`
on the zipper works (the index is a variable). Splits on whether the zipper is
the top (parsing done) or nested. -/
def nextPtdAux {nt : G.Nonterminal} {word : List G.Token}
    (pt : ParseTree G (.NT nt) word) (ptz : PtZipper init full_word (.NT nt) word) :
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
theorem sem_build_from_pt : {symb : Symbol G.Terminal G.Nonterminal} → {word : List G.Token} →
    (pt : ParseTree G symb word) → (ptz : PtZipper init full_word symb word) →
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
theorem sem_build_from_pt_rec : {symbs : List (Symbol G.Terminal G.Nonterminal)} →
    {word : List G.Token} → (ptl : ParseTreeList G symbs word) → (H : NonNilT symbs) →
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
theorem sem_build_from_ptl {symbs : List (Symbol G.Terminal G.Nonterminal)} {word : List G.Token}
    (ptl : ParseTreeList G symbs word) (ptlz : PtlZipper init full_word symbs word) :
    ptlzSem init full_word ptlz (fun _ f => ptlSem ptl f) =
      ptdSem init full_word (buildPtDotFromPtl init full_word ptl ptlz) := by
  cases ptlz with
  | Non_terminal_pt_ptlz ptz => simp only [buildPtDotFromPtl, ptdSem, ptlzSem]
  | Cons_ptl_ptlz pt ptlz' =>
    simp only [buildPtDotFromPtl]
    rw [← sem_build_from_pt init full_word pt (.Cons_ptl_ptz ptl ptlz')]
    simp only [ptzSem, ptlzSem]

/-- `nextPtdAux` preserves the semantic value. -/
theorem sem_nextPtdAux {nt : G.Nonterminal} {word : List G.Token}
    (pt : ParseTree G (.NT nt) word) (ptz : PtZipper init full_word (.NT nt) word) :
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
theorem nonNilProof_none {symbs : List (Symbol G.Terminal G.Nonterminal)} {word : List G.Token}
    (ptl : ParseTreeList G symbs word) (h : nonNilProof ptl = none) : word = [] := by
  cases ptl with
  | Nil_ptl => rfl
  | Cons_ptl _ _ => simp [nonNilProof] at h

/- The buffer of the dotted parse tree built from a parse tree is the recognised
word followed by the zipper's buffer (Coq `ptd_buffer_build_from_pt`). -/
mutual
theorem ptd_buffer_build_from_pt : {symb : Symbol G.Terminal G.Nonterminal} →
    {word : List G.Token} → (pt : ParseTree G symb word) → (ptz : PtZipper init full_word symb word) →
    word ++ₛ ptzBuffer init full_word buffer_end ptz =
      ptdBuffer init full_word buffer_end (buildPtDotFromPt init full_word pt ptz)
  | _, _, .Terminal_pt tok, ptz => by
      cases ptz with
      | Cons_ptl_ptz ptl ptlz =>
        simp only [buildPtDotFromPt, ptdBuffer, ptzBuffer, Buf.cons_append_stream,
          Buf.nil_append_stream]
  | _, _, .Non_terminal_pt prod ptl, ptz => by
      simp only [buildPtDotFromPt]
      cases h : nonNilProof ptl with
      | none =>
        have hw := nonNilProof_none ptl h
        subst hw
        simp only [ptdBuffer, Buf.nil_append_stream]
      | some H =>
        rw [← ptd_buffer_build_from_pt_rec ptl H (.Non_terminal_pt_ptlz ptz)]
        simp only [ptlzBuffer]
theorem ptd_buffer_build_from_pt_rec : {symbs : List (Symbol G.Terminal G.Nonterminal)} →
    {word : List G.Token} → (ptl : ParseTreeList G symbs word) → (H : NonNilT symbs) →
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
        simp only [ptlzBuffer, Buf.append_append_stream]
end

/-- The buffer of the dotted parse tree built from a completed list
(Coq `ptd_buffer_build_from_ptl`). -/
theorem ptd_buffer_build_from_ptl {symbs : List (Symbol G.Terminal G.Nonterminal)}
    {word : List G.Token} (ptl : ParseTreeList G symbs word)
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
theorem stateHasFuture_of_ptzStackCompat (hc : Complete A) {nt : G.Nonterminal}
    {word : List G.Token} (ptz : PtZipper init full_word (.NT nt) word) (stk : Stack A)
    (prod : G.Production) (hprod : G.prod_lhs prod = nt)
    (Hstk : ptzStackCompat init full_word buffer_end stk ptz) :
    stateHasFuture (stateOfStack init stk) prod (futureOfProd prod 0)
      (G.token_term (ptzBuffer init full_word buffer_end ptz).head) := by
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
theorem nonNilProof_none_symbs {symbs : List (Symbol G.Terminal G.Nonterminal)}
    {word : List G.Token} (ptl : ParseTreeList G symbs word) (h : nonNilProof ptl = none) :
    symbs = [] := by
  cases ptl with
  | Nil_ptl => rfl
  | Cons_ptl _ _ => simp [nonNilProof] at h

/-- A nil parse-tree list is stack-compatible with any stack (reflexively). -/
theorem ptlStackCompat_nil {symbs : List (Symbol G.Terminal G.Nonterminal)} {word : List G.Token}
    (ptl : ParseTreeList G symbs word) (stk0 : Stack A) (h : nonNilProof ptl = none) :
    ptlStackCompat stk0 ptl stk0 := by
  cases ptl with
  | Nil_ptl => simp only [ptlStackCompat]
  | Cons_ptl _ _ => simp [nonNilProof] at h

/-- `futureOfProd` of a zipper's production at the start equals the recognised
symbols (reversed) followed by the future. -/
theorem futureOfProd_ptlzProd {symbs : List (Symbol G.Terminal G.Nonterminal)}
    {word : List G.Token} (ptlz : PtlZipper init full_word symbs word) :
    futureOfProd (ptlzProd init full_word ptlz) 0 = symbs.reverse ++ ptlzFuture init full_word ptlz := by
  simp only [futureOfProd, List.drop_zero]
  rw [← ptlz_future_ptlz_prod init full_word ptlz, List.reverseAux_eq]
  simp [List.reverse_append, List.reverse_reverse]

/- The dotted parse tree built from a parse tree is stack-compatible (Coq
`ptd_stack_compat_build_from_pt` / `ptd_stack_compat_build_from_pt_rec`). -/
mutual
theorem ptd_stack_compat_build_from_pt (hc : Complete A) :
    {symb : Symbol G.Terminal G.Nonterminal} → {word : List G.Token} →
    (pt : ParseTree G symb word) → (ptz : PtZipper init full_word symb word) → (stk : Stack A) →
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
theorem ptd_stack_compat_build_from_pt_rec (hc : Complete A) :
    {symbs : List (Symbol G.Terminal G.Nonterminal)} → {word : List G.Token} →
    (ptl : ParseTreeList G symbs word) → (H : NonNilT symbs) →
    (ptlz : PtlZipper init full_word symbs word) → (stk : Stack A) →
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
theorem ptd_stack_compat_build_from_ptl (hc : Complete A)
    {symbs : List (Symbol G.Terminal G.Nonterminal)} {word : List G.Token}
    (ptl : ParseTreeList G symbs word) (ptlz : PtlZipper init full_word symbs word)
    (stk stk0 : Stack A) (Hstk0 : ptlzStackCompat init full_word buffer_end stk0 ptlz)
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

/-! ### Cost (number of actions left) and fuel accounting -/

/- The number of parser actions left before completion (Coq `ptlz_cost` /
`ptz_cost`). -/
mutual
def ptlzCost : {holeSymbs : List (Symbol G.Terminal G.Nonterminal)} → {holeWord : List G.Token} →
    PtlZipper init full_word holeSymbs holeWord → Nat
  | _, _, .Non_terminal_pt_ptlz ptz => ptzCost ptz
  | _, _, .Cons_ptl_ptlz pt ptlz' => ptSize pt + ptlzCost ptlz'
def ptzCost : {holeSymb : Symbol G.Terminal G.Nonterminal} → {holeWord : List G.Token} →
    PtZipper init full_word holeSymb holeWord → Nat
  | _, _, .Top_ptz => 0
  | _, _, .Cons_ptl_ptz _ ptlz' => 1 + ptlzCost ptlz'
end

/-- The cost of a dotted parse tree (Coq `ptd_cost`). -/
def ptdCost : PtDot init full_word → Nat
  | .Reduce_ptd _ ptz => ptzCost init full_word ptz
  | .Shift_ptd _ _ ptlz => 1 + ptlzCost init full_word ptlz

/-- If `nonNilProof` says nil, the list has size zero. -/
theorem nonNilProof_none_size {symbs : List (Symbol G.Terminal G.Nonterminal)}
    {word : List G.Token} (ptl : ParseTreeList G symbs word) (h : nonNilProof ptl = none) :
    ptlSize ptl = 0 := by
  cases ptl with
  | Nil_ptl => rfl
  | Cons_ptl _ _ => simp [nonNilProof] at h

/- Building a dotted parse tree from a parse tree accounts for one extra action
(Coq `ptd_cost_build_from_pt` / `ptd_cost_build_from_pt_rec`). -/
mutual
theorem ptd_cost_build_from_pt : {symb : Symbol G.Terminal G.Nonterminal} →
    {word : List G.Token} → (pt : ParseTree G symb word) → (ptz : PtZipper init full_word symb word) →
    ptSize pt + ptzCost init full_word ptz =
      ptdCost init full_word (buildPtDotFromPt init full_word pt ptz) + 1
  | _, _, .Terminal_pt _, ptz => by
      cases ptz with
      | Cons_ptl_ptz ptl ptlz =>
        simp only [buildPtDotFromPt, ptdCost, ptzCost, ptSize]; omega
  | _, _, .Non_terminal_pt prod ptl, ptz => by
      simp only [buildPtDotFromPt, ptSize]
      cases h : nonNilProof ptl with
      | none =>
        have hsz := nonNilProof_none_size ptl h
        simp only [ptdCost]; omega
      | some H =>
        rw [← ptd_cost_build_from_pt_rec ptl H (.Non_terminal_pt_ptlz ptz)]
        simp only [ptlzCost]; omega
theorem ptd_cost_build_from_pt_rec : {symbs : List (Symbol G.Terminal G.Nonterminal)} →
    {word : List G.Token} → (ptl : ParseTreeList G symbs word) → (H : NonNilT symbs) →
    (ptlz : PtlZipper init full_word symbs word) →
    ptlSize ptl + ptlzCost init full_word ptlz =
      ptdCost init full_word (buildPtDotFromPtRec init full_word ptl H ptlz)
  | _, _, .Nil_ptl, H, _ => H.elim
  | _, _, .Cons_ptl ptl' pt, _, ptlz => by
      cases ptl' with
      | Nil_ptl =>
        simp only [buildPtDotFromPtRec, ptlSize]
        have := ptd_cost_build_from_pt pt (.Cons_ptl_ptz .Nil_ptl ptlz)
        simp only [ptzCost] at this
        omega
      | Cons_ptl a b =>
        simp only [buildPtDotFromPtRec, ptlSize]
        rw [← ptd_cost_build_from_pt_rec (.Cons_ptl a b) Unit.unit (.Cons_ptl_ptlz pt ptlz)]
        simp only [ptlzCost, ptlSize]; omega
end

/-- The cost of the dotted parse tree built from a completed list
(Coq `ptd_cost_build_from_ptl`). -/
theorem ptd_cost_build_from_ptl {symbs : List (Symbol G.Terminal G.Nonterminal)}
    {word : List G.Token} (ptl : ParseTreeList G symbs word)
    (ptlz : PtlZipper init full_word symbs word) :
    ptlzCost init full_word ptlz = ptdCost init full_word (buildPtDotFromPtl init full_word ptl ptlz) := by
  cases ptlz with
  | Non_terminal_pt_ptlz ptz => simp only [buildPtDotFromPtl, ptdCost, ptlzCost]
  | Cons_ptl_ptlz pt ptlz' =>
    simp only [buildPtDotFromPtl, ptlzCost]
    have := ptd_cost_build_from_pt init full_word pt (.Cons_ptl_ptz ptl ptlz')
    simp only [ptzCost] at this
    omega

/-- `nextPtdAux` cost accounting. -/
theorem cost_nextPtdAux {nt : G.Nonterminal} {word : List G.Token}
    (pt : ParseTree G (.NT nt) word) (ptz : PtZipper init full_word (.NT nt) word) :
    match nextPtdAux init full_word pt ptz with
    | none => ptzCost init full_word ptz = 0
    | some ptd' => ptzCost init full_word ptz = ptdCost init full_word ptd' + 1 := by
  cases ptz with
  | Top_ptz => simp only [nextPtdAux, ptzCost]
  | Cons_ptl_ptz ptl' ptlz =>
    simp only [nextPtdAux, ptzCost]
    rw [ptd_cost_build_from_ptl init full_word (.Cons_ptl ptl' pt) ptlz]
    omega

/-- `nextPtd` cost accounting (Coq `next_ptd_cost`). -/
theorem next_ptd_cost (ptd : PtDot init full_word) :
    match nextPtd init full_word ptd with
    | none => ptdCost init full_word ptd = 0
    | some ptd' => ptdCost init full_word ptd = ptdCost init full_word ptd' + 1 := by
  cases ptd with
  | Shift_ptd tok ptl ptlz =>
    simp only [nextPtd]
    rw [← ptd_cost_build_from_ptl init full_word (.Cons_ptl ptl (.Terminal_pt tok)) ptlz]
    simp only [ptdCost]; omega
  | @Reduce_ptd prod word ptl ptz =>
    have h := cost_nextPtdAux init full_word (.Non_terminal_pt prod ptl) ptz
    simp only [nextPtd, ptdCost]
    exact h

/-- `nextPtdIter` cost accounting (Coq `next_ptd_iter_cost`). -/
theorem next_ptd_iter_cost (ptd : PtDot init full_word) (logNSteps : Nat) :
    match nextPtdIter init full_word ptd logNSteps with
    | none => ptdCost init full_word ptd < 2 ^ logNSteps
    | some ptd' => ptdCost init full_word ptd = 2 ^ logNSteps + ptdCost init full_word ptd' := by
  induction logNSteps generalizing ptd with
  | zero =>
    have h := next_ptd_cost init full_word ptd
    simp only [nextPtdIter, Nat.pow_zero]
    cases hn : nextPtd init full_word ptd with
    | none => rw [hn] at h; omega
    | some ptd' => rw [hn] at h; omega
  | succ n ih =>
    have hp : (2 : Nat) ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [Nat.pow_succ]; omega
    have IH1 := ih ptd
    cases h : nextPtdIter init full_word ptd n with
    | none => rw [h] at IH1; simp only [nextPtdIter, h]; omega
    | some ptd' =>
      rw [h] at IH1
      have IH2 := ih ptd'
      simp only [nextPtdIter, h]
      cases h2 : nextPtdIter init full_word ptd' n with
      | none => simp only [h2] at IH2 ⊢; omega
      | some ptd'' => simp only [h2] at IH2 ⊢; omega

/-! ### Evaluating `reduceStep`

Two evaluation lemmas for `reduceStep`, derived from a `pop` equation, splitting
on whether the goto for the produced nonterminal succeeds. Proof irrelevance
(plus `injection` discarding the `Prop`-valued second component of the goto
`Sigma`) aligns the dependently-typed proof arguments inside `reduceStep`. -/

/-- If popping `prod`'s RHS yields `(stk0, sem)` and the goto on `prod_lhs prod`
succeeds, `reduceStep` makes progress, pushing the goto target. -/
theorem reduceStep_progress_eq (stk : Stack A) (prod : G.Production) (buf : Buffer G)
    (Hval : validForReduce (stateOfStack init stk) prod) (Hi : StackInvariant init stk)
    (stk0 : Stack A) (sem : G.symbol_semantic_type (.NT (G.prod_lhs prod)))
    (stateNew : A.NonInitState)
    (e : Symbol.NT (G.prod_lhs prod) = A.last_symb_of_non_init_state stateNew)
    (hpop : pop (G.prod_rhs_rev prod) stk (Prefix.trans Hval.1 (Hi.symb_prefix init))
      (G.prod_action prod) = (stk0, sem))
    (hgoto : A.goto_table (stateOfStack init stk0) (G.prod_lhs prod) = some ⟨stateNew, e⟩) :
    reduceStep init stk prod buf Hval Hi =
      .Progress (⟨stateNew, cast (congrArg G.symbol_semantic_type e) sem⟩ :: stk0) buf := by
  unfold reduceStep
  simp only [hpop]
  have h1 : (pop (G.prod_rhs_rev prod) stk (Prefix.trans Hval.1 (Hi.symb_prefix init))
      (G.prod_action prod)).1 = stk0 := congrArg Prod.fst hpop
  split
  · rename_i sn e' hg
    rw [h1, hgoto] at hg
    injection hg with hg'
    injection hg' with hsn
    subst hsn
    rfl
  · rename_i hg
    rw [h1, hgoto] at hg
    exact absurd hg (by simp)

/-- If popping `prod`'s RHS yields `(stk0, sem)` and the goto on `prod_lhs prod`
fails, `reduceStep` accepts with the (cast) popped value. -/
theorem reduceStep_accept_eq (stk : Stack A) (prod : G.Production) (buf : Buffer G)
    (Hval : validForReduce (stateOfStack init stk) prod) (Hi : StackInvariant init stk)
    (stk0 : Stack A) (sem : G.symbol_semantic_type (.NT (G.prod_lhs prod)))
    (e2 : G.prod_lhs prod = A.start_nt init)
    (hpop : pop (G.prod_rhs_rev prod) stk (Prefix.trans Hval.1 (Hi.symb_prefix init))
      (G.prod_action prod) = (stk0, sem))
    (hgoto : A.goto_table (stateOfStack init stk0) (G.prod_lhs prod) = none) :
    reduceStep init stk prod buf Hval Hi =
      .Accept (cast (congrArg (fun nt => G.symbol_semantic_type (Symbol.NT nt)) e2) sem) buf := by
  unfold reduceStep
  simp only [hpop]
  have h1 : (pop (G.prod_rhs_rev prod) stk (Prefix.trans Hval.1 (Hi.symb_prefix init))
      (G.prod_action prod)).1 = stk0 := congrArg Prod.fst hpop
  split
  · rename_i sn e' hg
    rw [h1, hgoto] at hg
    exact absurd hg (by simp)
  · rfl

/-! ### `reduce_step` follows `next_ptd` -/

/-- Transporting a parse tree along a nonterminal equality casts its semantics. -/
theorem ptSem_recNT {a b : G.Nonterminal} (h : a = b) {w : List G.Token}
    (x : ParseTree G (.NT a) w) :
    ptSem (h ▸ x) = cast (congrArg (fun n => G.symbol_semantic_type (.NT n)) h) (ptSem x) := by
  subst h; rfl

/-- Generic-nonterminal core of `reduce_step_next_ptd`: with the produced
nonterminal abstracted to a variable `nt`, `cases ptz` is legal. -/
theorem reduceStep_next_ptdAux (hc : Complete A) {nt : G.Nonterminal} {word : List G.Token}
    (prod : G.Production) (hnt : G.prod_lhs prod = nt)
    (ptl : ParseTreeList G (G.prod_rhs_rev prod) word)
    (ptz : PtZipper init full_word (.NT nt) word)
    (stk stk0 : Stack A)
    (Hval : validForReduce (stateOfStack init stk) prod) (Hi : StackInvariant init stk)
    (Hstk : ptlStackCompat stk0 ptl stk)
    (Hstk0 : ptzStackCompat init full_word buffer_end stk0 ptz)
    (pt : ParseTree G (.NT nt) word)
    (hpt : pt = hnt ▸ ParseTree.Non_terminal_pt prod ptl) :
    match nextPtdAux init full_word pt ptz with
    | none =>
      reduceStep init stk prod (ptzBuffer init full_word buffer_end ptz) Hval Hi =
        .Accept (ptzSem init full_word ptz (ptSem pt)) buffer_end
    | some ptd =>
      ∃ stk', reduceStep init stk prod (ptzBuffer init full_word buffer_end ptz) Hval Hi =
        .Progress stk' (ptdBuffer init full_word buffer_end ptd) ∧
        ptdStackCompat init full_word buffer_end ptd stk' := by
  have hpop : pop (G.prod_rhs_rev prod) stk (Prefix.trans Hval.1 (Hi.symb_prefix init))
      (G.prod_action prod) = (stk0, ptlSem ptl (G.prod_action prod)) :=
    pop_eq_of_popSpec (pop_stack_compat_pop_spec ptl stk stk0 (G.prod_action prod) Hstk) _
  cases ptz with
  | Top_ptz =>
    simp only [nextPtdAux, ptzBuffer, ptzSem]
    simp only [ptzStackCompat] at Hstk0
    subst Hstk0
    have hgoto : A.goto_table (stateOfStack init []) (G.prod_lhs prod) = none := by
      show A.goto_table (.Init init) (G.prod_lhs prod) = none
      rw [hnt]
      have hsg := startGoto_of_complete hc init
      cases hg2 : A.goto_table (.Init init) (A.start_nt init) with
      | none => rfl
      | some v => rw [hg2] at hsg; exact hsg.elim
    rw [reduceStep_accept_eq init stk prod buffer_end Hval Hi []
      (ptlSem ptl (G.prod_action prod)) hnt hpop hgoto]
    rw [hpt, ptSem_recNT]
    simp only [ptSem]
  | Cons_ptl_ptz ptl' ptlz =>
    simp only [nextPtdAux, ptzBuffer]
    subst hnt
    subst hpt
    simp only [ptzStackCompat] at Hstk0
    obtain ⟨stk0', Hfut, Hstk', Hstk0'⟩ := Hstk0
    have Hgoto := nonTerminalGoto_of_complete hc (stateOfStack init stk0)
      (ptlzProd init full_word ptlz) (Symbol.NT (G.prod_lhs prod) :: ptlzFuture init full_word ptlz)
      (ptlzLookahead init full_word buffer_end ptlz) Hfut
    dsimp only at Hgoto
    cases hg : A.goto_table (stateOfStack init stk0) (G.prod_lhs prod) with
    | none => rw [hg] at Hgoto; exact Hgoto.elim
    | some v =>
      obtain ⟨stateNew, e⟩ := v
      rw [hg] at Hgoto
      refine ⟨⟨stateNew, cast (congrArg G.symbol_semantic_type e)
        (ptlSem ptl (G.prod_action prod))⟩ :: stk0, ?_, ?_⟩
      · rw [reduceStep_progress_eq init stk prod (ptlzBuffer init full_word buffer_end ptlz) Hval Hi
          stk0 (ptlSem ptl (G.prod_action prod)) stateNew e hpop hg]
        rw [ptd_buffer_build_from_ptl init full_word buffer_end
          (ParseTreeList.Cons_ptl ptl' (.Non_terminal_pt prod ptl)) ptlz]
      · refine ptd_stack_compat_build_from_ptl init full_word buffer_end hc
          (ParseTreeList.Cons_ptl ptl' (.Non_terminal_pt prod ptl)) ptlz _ stk0' Hstk0' ?_ Hgoto
        simp only [ptlStackCompat]
        refine ⟨Hstk', e, ?_⟩
        simp only [ptSem]; rfl

/-- `reduce_step` follows `next_ptd` (Coq `reduce_step_next_ptd`). -/
theorem reduceStep_next_ptd (hc : Complete A) {prod : G.Production} {word : List G.Token}
    (ptl : ParseTreeList G (G.prod_rhs_rev prod) word)
    (ptz : PtZipper init full_word (.NT (G.prod_lhs prod)) word)
    (stk : Stack A) (Hval : validForReduce (stateOfStack init stk) prod)
    (Hi : StackInvariant init stk)
    (Hstk : ptdStackCompat init full_word buffer_end (.Reduce_ptd ptl ptz) stk) :
    match nextPtd init full_word (.Reduce_ptd ptl ptz) with
    | none =>
      reduceStep init stk prod (ptzBuffer init full_word buffer_end ptz) Hval Hi =
        .Accept (ptdSem init full_word (.Reduce_ptd ptl ptz)) buffer_end
    | some ptd =>
      ∃ stk', reduceStep init stk prod (ptzBuffer init full_word buffer_end ptz) Hval Hi =
        .Progress stk' (ptdBuffer init full_word buffer_end ptd) ∧
        ptdStackCompat init full_word buffer_end ptd stk' := by
  simp only [ptdStackCompat] at Hstk
  obtain ⟨stk0, _, Hstk', Hstk0⟩ := Hstk
  have h := reduceStep_next_ptdAux init full_word buffer_end hc prod rfl ptl ptz stk stk0
    Hval Hi Hstk' Hstk0 (.Non_terminal_pt prod ptl) rfl
  simp only [nextPtd, ptdSem, ptSem] at *
  exact h

/-! ### Evaluating `step` -/

/-- `step` reduces to `reduceStep` when the state default-reduces. -/
theorem step_eq_reduceStep_default (hsafe : Safe A) (stk : Stack A) (buffer : Buffer G)
    (Hi : StackInvariant init stk) (prod : G.Production)
    (Hval : validForReduce (stateOfStack init stk) prod)
    (haction : A.action_table (stateOfStack init stk) = .Default_reduce_act prod) :
    step init hsafe stk buffer Hi = reduceStep init stk prod buffer Hval Hi := by
  unfold step
  split
  · rename_i prod' haction'
    rw [haction] at haction'; injection haction' with hp; subst hp; rfl
  · rename_i awt haction'
    rw [haction] at haction'; exact absurd haction' (by simp)

/-- `step` reduces to `reduceStep` when the lookahead action is a reduce. -/
theorem step_eq_reduceStep_lookahead (hsafe : Safe A) (stk : Stack A) (buffer : Buffer G)
    (Hi : StackInvariant init stk) (prod : G.Production)
    (Hval : validForReduce (stateOfStack init stk) prod)
    (awt : (term : G.Terminal) → A.LookaheadAction term)
    (haction : A.action_table (stateOfStack init stk) = .Lookahead_act awt)
    (hawt : awt (G.token_term buffer.head) = .Reduce_act prod) :
    step init hsafe stk buffer Hi = reduceStep init stk prod buffer Hval Hi := by
  unfold step
  split
  · rename_i prod' haction'
    rw [haction] at haction'; exact absurd haction' (by simp)
  · rename_i awt' haction'
    rw [haction] at haction'; injection haction' with haw; subst haw
    dsimp only
    split
    · rename_i sn e hawt'
      rw [hawt] at hawt'; exact absurd hawt' (by simp)
    · rename_i prod'' hawt'
      rw [hawt] at hawt'; injection hawt' with hp; subst hp; rfl
    · rename_i hawt'
      rw [hawt] at hawt'; exact absurd hawt' (by simp)

/-- `step` shifts and pushes the read token when the lookahead action is a shift. -/
theorem step_shift_eq (hsafe : Safe A) (stk : Stack A) (tok : G.Token) (rest : Buffer G)
    (Hi : StackInvariant init stk)
    (awt : (term : G.Terminal) → A.LookaheadAction term)
    (haction : A.action_table (stateOfStack init stk) = .Lookahead_act awt)
    (stateNew : A.NonInitState)
    (e : Symbol.T (G.token_term tok) = A.last_symb_of_non_init_state stateNew)
    (hawt : awt (G.token_term tok) = .Shift_act stateNew e) :
    step init hsafe stk (Buf.cons tok rest) Hi =
      .Progress (⟨stateNew, cast (congrArg G.symbol_semantic_type e)
        (G.token_sem tok)⟩ :: stk) rest := by
  unfold step
  split
  · rename_i prod' haction'
    rw [haction] at haction'; exact absurd haction' (by simp)
  · rename_i awt' haction'
    rw [haction] at haction'; injection haction' with haw; subst haw
    simp only [Buf.head_cons, Buf.tail_cons]
    split
    · rename_i sn e' hawt'
      rw [hawt] at hawt'; injection hawt' with hsn; subst hsn; rfl
    · rename_i prod'' hawt'
      rw [hawt] at hawt'; exact absurd hawt' (by simp)
    · rename_i hawt'
      rw [hawt] at hawt'; exact absurd hawt' (by simp)

/-- Each parsing step follows `next_ptd` (Coq `step_next_ptd`). -/
theorem step_next_ptd (hsafe : Safe A) (hc : Complete A) (ptd : PtDot init full_word) (stk : Stack A)
    (Hi : StackInvariant init stk)
    (Hstk : ptdStackCompat init full_word buffer_end ptd stk) :
    match nextPtd init full_word ptd with
    | none =>
      step init hsafe stk (ptdBuffer init full_word buffer_end ptd) Hi =
        .Accept (ptdSem init full_word ptd) buffer_end
    | some ptd' =>
      ∃ stk', step init hsafe stk (ptdBuffer init full_word buffer_end ptd) Hi =
        .Progress stk' (ptdBuffer init full_word buffer_end ptd') ∧
        ptdStackCompat init full_word buffer_end ptd' stk' := by
  cases ptd with
  | @Reduce_ptd prod word ptl ptz =>
    simp only [ptdBuffer]
    have hsf : stateHasFuture (stateOfStack init stk) prod []
        (G.token_term (ptzBuffer init full_word buffer_end ptz).head) := by
      obtain ⟨stk0, h, _, _⟩ := Hstk; exact h
    have Hred := endReduce_of_complete hc (stateOfStack init stk) prod []
      (G.token_term (ptzBuffer init full_word buffer_end ptz).head) hsf
    dsimp only at Hred
    cases haction : A.action_table (stateOfStack init stk) with
    | Default_reduce_act p =>
      simp only [haction] at Hred
      subst p
      have hro := reduceOk_of_safe hsafe (stateOfStack init stk)
      rw [haction] at hro
      rw [step_eq_reduceStep_default init hsafe stk (ptzBuffer init full_word buffer_end ptz) Hi
        prod hro haction]
      exact reduceStep_next_ptd init full_word buffer_end hc ptl ptz stk hro Hi Hstk
    | Lookahead_act awt =>
      simp only [haction] at Hred
      cases hawt : awt (G.token_term (ptzBuffer init full_word buffer_end ptz).head) with
      | Shift_act s2 e => simp only [hawt] at Hred
      | Reduce_act p =>
        simp only [hawt] at Hred
        subst p
        have hro := reduceOk_of_safe hsafe (stateOfStack init stk)
        rw [haction] at hro
        have hro' := hro (G.token_term (ptzBuffer init full_word buffer_end ptz).head)
        rw [hawt] at hro'
        rw [step_eq_reduceStep_lookahead init hsafe stk (ptzBuffer init full_word buffer_end ptz) Hi
          prod hro' awt haction hawt]
        exact reduceStep_next_ptd init full_word buffer_end hc ptl ptz stk hro' Hi Hstk
      | Fail_act => simp only [hawt] at Hred
  | Shift_ptd tok ptl ptlz =>
    simp only [nextPtd]
    have hbuf : ptdBuffer init full_word buffer_end (PtDot.Shift_ptd tok ptl ptlz) =
        Buf.cons tok (ptlzBuffer init full_word buffer_end ptlz) := rfl
    rw [hbuf]
    simp only [ptdStackCompat] at Hstk
    obtain ⟨stk0, Hfut, Hstk', Hstk0⟩ := Hstk
    have Hact := terminalShift_of_complete hc (stateOfStack init stk) (ptlzProd init full_word ptlz)
      (Symbol.T (G.token_term tok) :: ptlzFuture init full_word ptlz)
      (ptlzLookahead init full_word buffer_end ptlz) Hfut
    dsimp only at Hact
    cases haction : A.action_table (stateOfStack init stk) with
    | Default_reduce_act p => simp only [haction] at Hact
    | Lookahead_act awt =>
      simp only [haction] at Hact
      cases hawt : awt (G.token_term tok) with
      | Shift_act s2 e =>
        simp only [hawt] at Hact
        refine ⟨⟨s2, cast (congrArg G.symbol_semantic_type e) (G.token_sem tok)⟩ :: stk, ?_, ?_⟩
        · rw [step_shift_eq init hsafe stk tok (ptlzBuffer init full_word buffer_end ptlz) Hi
            awt haction s2 e hawt]
          rw [← ptd_buffer_build_from_ptl init full_word buffer_end
            (.Cons_ptl ptl (.Terminal_pt tok)) ptlz]
        · refine ptd_stack_compat_build_from_ptl init full_word buffer_end hc
            (.Cons_ptl ptl (.Terminal_pt tok)) ptlz _ stk0 Hstk0 ?_ Hact
          simp only [ptlStackCompat]
          exact ⟨Hstk', e, by simp only [ptSem]; rfl⟩
      | Reduce_act p => simp only [hawt] at Hact
      | Fail_act => simp only [hawt] at Hact

/-- The parse loop follows `next_ptd_iter` (Coq `parse_fix_next_ptd_iter`). -/
theorem parseFix_next_ptd_iter (hsafe : Safe A) (hc : Complete A) (ptd : PtDot init full_word)
    (stk : Stack A) (logNSteps : Nat) (Hi : StackInvariant init stk)
    (Hstk : ptdStackCompat init full_word buffer_end ptd stk) :
    match nextPtdIter init full_word ptd logNSteps with
    | none =>
      (parseFix init hsafe stk (ptdBuffer init full_word buffer_end ptd) logNSteps Hi).1 =
        .Accept (ptdSem init full_word ptd) buffer_end
    | some ptd' =>
      ∃ stk', (parseFix init hsafe stk (ptdBuffer init full_word buffer_end ptd) logNSteps Hi).1 =
        .Progress stk' (ptdBuffer init full_word buffer_end ptd') ∧
        ptdStackCompat init full_word buffer_end ptd' stk' := by
  induction logNSteps generalizing ptd stk Hi Hstk with
  | zero => exact step_next_ptd init full_word buffer_end hsafe hc ptd stk Hi Hstk
  | succ n ih =>
    have IH1 := ih ptd stk Hi Hstk
    rcases hpf : parseFix init hsafe stk (ptdBuffer init full_word buffer_end ptd) n Hi with ⟨sr, hsr⟩
    rw [hpf] at IH1
    cases hni : nextPtdIter init full_word ptd n with
    | none =>
      rw [hni] at IH1
      simp only [nextPtdIter, hni]
      rw [parseFix_succ, hpf]
      cases sr with
      | Accept s b => exact IH1
      | Progress stk2 buf2 => exact absurd IH1 (by simp)
      | Fail s t => exact absurd IH1 (by simp)
    | some ptd' =>
      rw [hni] at IH1
      obtain ⟨stk', hsr_eq, Hstk'⟩ := IH1
      simp only [nextPtdIter, hni]
      have EQsem := sem_next_ptd_iter init full_word ptd n
      rw [hni] at EQsem
      rw [parseFix_succ, hpf]
      cases sr with
      | Accept s b => exact absurd hsr_eq (by simp)
      | Fail s t => exact absurd hsr_eq (by simp)
      | Progress stk2 buf2 =>
        injection hsr_eq with h1 h2
        subst h1; subst h2
        rw [EQsem]
        exact ih ptd' stk2 (hsr stk2 (ptdBuffer init full_word buffer_end ptd') rfl) Hstk'

/-- **Completeness of the interpreter** (Coq `parse_complete`). Given any parse
tree of the input, the parser succeeds with enough fuel, returns that tree's
semantics, consumes exactly `full_word`, and a tighter fuel bound holds. -/
theorem parse_complete (hsafe : Safe A) (hc : Complete A)
    (full_pt : ParseTree G (.NT (A.start_nt init)) full_word) (logNSteps : Nat) :
    match parse init hsafe (full_word ++ₛ buffer_end) logNSteps with
    | .Parsed sem buff =>
      sem = ptSem full_pt ∧ buff = buffer_end ∧ ptSize full_pt ≤ 2 ^ logNSteps
    | .Timeout => 2 ^ logNSteps < ptSize full_pt
    | .Fail _ _ => False := by
  let ptd0 := buildPtDotFromPt init full_word full_pt PtZipper.Top_ptz
  have hptd0 : ptd0 = buildPtDotFromPt init full_word full_pt PtZipper.Top_ptz := rfl
  have Hstk : ptdStackCompat init full_word buffer_end ptd0 [] := by
    rw [hptd0]
    exact ptd_stack_compat_build_from_pt init full_word buffer_end hc full_pt PtZipper.Top_ptz []
      (by simp only [ptzStackCompat])
  have hbuf : ptdBuffer init full_word buffer_end ptd0 = full_word ++ₛ buffer_end := by
    rw [hptd0, ← ptd_buffer_build_from_pt init full_word buffer_end full_pt PtZipper.Top_ptz]
    simp only [ptzBuffer]
  have hsem : ptdSem init full_word ptd0 = ptSem full_pt := by
    rw [hptd0, ← sem_build_from_pt init full_word full_pt PtZipper.Top_ptz]
    simp only [ptzSem]
  have hcost : ptSize full_pt = ptdCost init full_word ptd0 + 1 := by
    have h := ptd_cost_build_from_pt init full_word full_pt PtZipper.Top_ptz
    simp only [ptzCost, ← hptd0] at h; omega
  have Hparse := parseFix_next_ptd_iter init full_word buffer_end hsafe hc ptd0 [] logNSteps
    (initStackInvariant init) Hstk
  have Hcost := next_ptd_iter_cost init full_word ptd0 logNSteps
  unfold parse
  rw [← hbuf]
  cases hni : nextPtdIter init full_word ptd0 logNSteps with
  | none =>
    rw [hni] at Hparse Hcost
    rw [Hparse]
    refine ⟨hsem, rfl, ?_⟩
    omega
  | some ptd' =>
    rw [hni] at Hparse Hcost
    obtain ⟨stk', hpf, _⟩ := Hparse
    rw [hpf]
    omega

end Completeness

end LeanMenhir
