/-
EOF-anchoring (leak-3 fix): tying "the parse succeeded" to "the *whole* input
was consumed".

Soundness (`parse_correct`) only says that *some prefix* of the padded token
stream was recognised — a grammar that does not read an end marker can succeed
on `1+2 garbage` after consuming `1+2`, and the runtime driver discards the
residual buffer. Menhir's convention is that every start production ends in a
dedicated EOF terminal; this file makes that convention *checkable* and *pays
it off*:

* `isEofAnchored eoft startnt` — a decidable check on the grammar: the start
  nonterminal occurs in no RHS, every production of the start nonterminal ends
  in the EOF terminal (i.e. begins with it in the reversed RHS), and the EOF
  terminal occurs nowhere else.
* `EofAnchored` (Prop) + `isEofAnchored_spec` — the certified reading.
* `anchored_word_shape` — by induction over parse trees: every word of the
  start symbol has the shape `w' ++ [tk]` with `tk` the sole EOF token.
* `word_eq_append_eof` — pure list arithmetic: a word of that shape that agrees
  pointwise with `toks` padded by EOF-tokens, where the *lexer never emits the
  EOF terminal*, must be exactly `toks ++ [eof]`.

`Main.parse_correct_anchored` and `Runtime.parseList_sound_anchored` combine
these with soundness: **if the parser accepts, it consumed exactly the entire
input plus the EOF sentinel — no trailing garbage.**

LGPL-3.0-or-later (derivative of coq-menhirlib).
-/
import LeanMenhir.Grammar
import LeanMenhir.Validator.Classes

namespace LeanMenhir

variable {G : Grammar}

/-! ### The decidable anchoring check -/

/-- Boolean EOF-anchoring check (see `EofAnchored` for the certified reading). -/
def isEofAnchored (eoft : G.Terminal) (startnt : G.Nonterminal) : Bool :=
  Allb G.Production fun p =>
    ((G.prod_rhs_rev p).all fun s => decide (s ≠ Symbol.NT startnt)) &&
    (if G.prod_lhs p = startnt then
       match G.prod_rhs_rev p with
       | Symbol.T t :: rest =>
           decide (t = eoft) && rest.all fun s => decide (s ≠ Symbol.T eoft)
       | _ => false
     else (G.prod_rhs_rev p).all fun s => decide (s ≠ Symbol.T eoft))

/-- The grammar is EOF-anchored: the start nonterminal never occurs in a RHS,
every start production ends in the EOF terminal (= begins with it in the
*reversed* RHS) and mentions it nowhere else, and non-start productions never
mention the EOF terminal. -/
structure EofAnchored (eoft : G.Terminal) (startnt : G.Nonterminal) : Prop where
  no_start_in_rhs : ∀ p : G.Production, Symbol.NT startnt ∉ G.prod_rhs_rev p
  start_shape : ∀ p : G.Production, G.prod_lhs p = startnt →
    ∃ rest, G.prod_rhs_rev p = Symbol.T eoft :: rest ∧ Symbol.T eoft ∉ rest
  no_eof_elsewhere : ∀ p : G.Production, G.prod_lhs p ≠ startnt →
    Symbol.T eoft ∉ G.prod_rhs_rev p

theorem isEofAnchored_spec {eoft : G.Terminal} {startnt : G.Nonterminal}
    (h : isEofAnchored eoft startnt = true) : EofAnchored eoft startnt := by
  unfold isEofAnchored at h
  have hall := forall_of_Allb (P := fun p => _) (fun p hp => hp) h
  refine ⟨fun p hmem => ?_, fun p hlhs => ?_, fun p hlhs hmem => ?_⟩ <;>
    (have h12 := hall p; rw [Bool.and_eq_true] at h12)
  · have h1 := h12.1
    rw [List.all_eq_true] at h1
    exact of_decide_eq_true (h1 _ hmem) rfl
  · have h2 := h12.2
    rw [if_pos hlhs] at h2
    split at h2
    · rename_i t rest heq
      rw [Bool.and_eq_true] at h2
      obtain ⟨ht, hrest⟩ := h2
      cases of_decide_eq_true ht
      refine ⟨rest, heq, fun hmem => ?_⟩
      rw [List.all_eq_true] at hrest
      exact of_decide_eq_true (hrest _ hmem) rfl
    · exact absurd h2 (by simp)
  · have h2 := h12.2
    rw [if_neg hlhs, List.all_eq_true] at h2
    exact of_decide_eq_true (h2 _ hmem) rfl

/-! ### Words of an anchored grammar -/

mutual
/-- In an EOF-anchored grammar, the word of a parse tree headed by any symbol
other than the EOF terminal and the start nonterminal is EOF-free. -/
theorem eof_free_pt {eoft : G.Terminal} {startnt : G.Nonterminal}
    (h : EofAnchored eoft startnt) :
    {s : Symbol G.Terminal G.Nonterminal} → {w : List G.Token} →
    ParseTree G s w → s ≠ Symbol.T eoft → s ≠ Symbol.NT startnt →
    ∀ tok ∈ w, G.token_term tok ≠ eoft
  | _, _, .leaf tok, hs, _ => by
    intro tok' hmem heq
    rw [List.mem_singleton] at hmem
    subst hmem
    exact hs (congrArg Symbol.T heq)
  | _, _, .node prod ptl, _, hnt =>
    have hlhs : G.prod_lhs prod ≠ startnt := fun he => hnt (congrArg Symbol.NT he)
    eof_free_ptl h ptl (fun s hs =>
      ⟨fun he => h.no_eof_elsewhere prod hlhs (he ▸ hs),
       fun he => h.no_start_in_rhs prod (he ▸ hs)⟩)

/-- List version of `eof_free_pt`. -/
theorem eof_free_ptl {eoft : G.Terminal} {startnt : G.Nonterminal}
    (h : EofAnchored eoft startnt) :
    {ss : List (Symbol G.Terminal G.Nonterminal)} → {w : List G.Token} →
    ParseTreeList G ss w →
    (∀ s ∈ ss, s ≠ Symbol.T eoft ∧ s ≠ Symbol.NT startnt) →
    ∀ tok ∈ w, G.token_term tok ≠ eoft
  | _, _, .nil, _ => by intro tok hmem; exact absurd hmem List.not_mem_nil
  | _, _, .cons q t, hss => by
    intro tok hmem
    rcases List.mem_append.1 hmem with hq | ht
    · exact eof_free_ptl h q (fun s hs => hss s (List.mem_cons_of_mem _ hs)) tok hq
    · exact eof_free_pt h t (hss _ List.mem_cons_self).1 (hss _ List.mem_cons_self).2 tok ht
end

/-- In an EOF-anchored grammar, every word of the start symbol is `w' ++ [tk]`
with `tk` the sole EOF token. -/
theorem anchored_word_shape {eoft : G.Terminal} {startnt : G.Nonterminal}
    (h : EofAnchored eoft startnt) {w : List G.Token}
    (pt : ParseTree G (Symbol.NT startnt) w) :
    ∃ w' tk, w = w' ++ [tk] ∧ G.token_term tk = eoft ∧
      ∀ tok ∈ w', G.token_term tok ≠ eoft := by
  cases pt with
  | node prod ptl =>
    obtain ⟨rest, hshape, hrest⟩ := h.start_shape prod rfl
    rw [hshape] at ptl
    cases ptl with
    | cons q t =>
      cases t with
      | leaf tok =>
        refine ⟨_, tok, rfl, rfl, ?_⟩
        refine eof_free_ptl h q (fun s hs => ?_)
        refine ⟨fun he => hrest (he ▸ hs), fun he => h.no_start_in_rhs prod ?_⟩
        rw [hshape]
        exact List.mem_cons_of_mem _ (he ▸ hs)

/-- Transporting a parse tree along a word equality preserves its semantics. -/
theorem ptSem_cast_word {s : Symbol G.Terminal G.Nonterminal} {w1 w2 : List G.Token}
    (h : w1 = w2) (pt : ParseTree G s w1) : ptSem (h ▸ pt) = ptSem pt := by
  subst h; rfl

/-! ### Pinning the word to the input -/

omit G in
/-- Pure list arithmetic: if a word agrees pointwise with `toks` padded by
`eofv`, ends in its sole EOF token, and the real input `toks` contains no EOF
token, then the word is exactly `toks ++ [eofv]`. -/
theorem word_eq_append_eof {α β : Type} (term : α → β) (eofT : β)
    (word toks : List α) (eofv : α) (heofv : term eofv = eofT)
    (hpt : ∀ (i : Nat) (h : i < word.length), word[i] = toks.getD i eofv)
    (w' : List α) (tk : α) (hw : word = w' ++ [tk]) (htk : term tk = eofT)
    (hw' : ∀ tok ∈ w', term tok ≠ eofT)
    (hlex : ∀ tok ∈ toks, term tok ≠ eofT) :
    word = toks ++ [eofv] := by
  have hlen : word.length = w'.length + 1 := by rw [hw]; simp
  have hgetD : ∀ i, toks.getD i eofv = if h : i < toks.length then toks[i] else eofv := by
    intro i
    rcases Nat.lt_or_ge i toks.length with hi | hi
    · rw [dif_pos hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
    · rw [dif_neg (Nat.not_lt.2 hi), List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]; rfl
  have hwl : ∀ hi : w'.length < word.length, word[w'.length]'hi = tk := by
    intro hi
    subst hw
    rw [List.getElem_append_right (Nat.le_refl _)]
    simp
  have h1 : toks.length ≤ w'.length := by
    rcases Nat.lt_or_ge w'.length toks.length with hcon | hle
    · exfalso
      have hi : w'.length < word.length := by omega
      have hv := hpt w'.length hi
      rw [hwl hi, hgetD, dif_pos hcon] at hv
      exact hlex _ (hv ▸ List.getElem_mem hcon) htk
    · exact hle
  have h2 : w'.length ≤ toks.length := by
    rcases Nat.lt_or_ge toks.length w'.length with hcon | hle
    · exfalso
      have hi : toks.length < word.length := by omega
      have hv := hpt toks.length hi
      rw [hgetD, dif_neg (Nat.lt_irrefl _)] at hv
      have hmem : word[toks.length]'hi ∈ w' := by
        subst hw
        rw [List.getElem_append_left hcon]
        exact List.getElem_mem hcon
      exact hw' _ hmem (by rw [hv, heofv])
    · exact hle
  have hlen' : w'.length = toks.length := Nat.le_antisymm h2 h1
  have hw'eq : w' = toks := by
    apply List.ext_getElem hlen'
    intro i h1i h2i
    have hi : i < word.length := by omega
    have hv := hpt i hi
    rw [hgetD, dif_pos h2i] at hv
    rw [← hv]
    subst hw
    exact (List.getElem_append_left h1i).symm
  have htkeq : tk = eofv := by
    have hi : w'.length < word.length := by omega
    have hv := hpt w'.length hi
    rw [hwl hi, hgetD, dif_neg (by omega)] at hv
    exact hv
  rw [hw, hw'eq, htkeq]

end LeanMenhir
