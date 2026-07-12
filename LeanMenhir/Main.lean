/-
Port of `coq-menhirlib`'s `Main.v` to Lean 4.

Original: Copyright Inria and CNRS, LGPL-3.0-or-later.
This Lean port is a derivative work, distributed under LGPL-3.0-or-later.

The user-facing entry points: the boolean validators, the runnable `parse`, the
soundness theorem, and (given the completeness validator accepts) the
completeness and unambiguity theorems.
-/
import LeanMenhir.Interpreter.Correct
import LeanMenhir.Interpreter.Complete
import LeanMenhir.Interpreter.Congr
import LeanMenhir.Anchored

namespace LeanMenhir
namespace Main

open LeanMenhir.Buf

variable {G : Grammar} {A : Automaton G}

/-- The safety validator: `safeValidator A = true` is the precondition discharged
(by `decide`/`native_decide`) for a concrete automaton (Coq `safe_validator`;
the Coq `unit` thunk argument is dropped — the automaton is the argument). -/
def safeValidator (A : Automaton G) : Bool := isSafe A

/-- The runnable parser: given a machine-checked proof that the safety validator
accepts the tables, parse `buffer` with budget `2 ^ logNSteps` (Coq `Main.parse`). -/
def parse (init : A.InitState) (hsafe : safeValidator A = true) (logNSteps : Nat)
    (buffer : Buffer G) : ParseResult A (G.symbol_semantic_type (.NT (A.start_nt init))) :=
  LeanMenhir.parse init (safe_is_validator hsafe) buffer logNSteps

/-- **Soundness** (Coq `Main.parse_correct`): a successful parse returns a real
parse tree of the recognised word with the produced semantic value. -/
theorem parse_correct (init : A.InitState) (hsafe : safeValidator A = true)
    (logNSteps : Nat) (buffer : Buffer G) :
    match parse init hsafe logNSteps buffer with
    | .Parsed sem bufferNew =>
        ∃ (word : List G.Token) (pt : ParseTree G (.NT (A.start_nt init)) word),
          buffer.get = (word ++ₛ bufferNew).get ∧ ptSem pt = sem
    | _ => True :=
  LeanMenhir.parse_correct init (safe_is_validator hsafe) buffer logNSteps

/-- The completeness validator: `completeValidator A = true` is discharged (by
`decide`/`native_decide`) for a concrete automaton (Coq `complete_validator`;
Coq `unit` thunk dropped). -/
def completeValidator (A : Automaton G) : Bool := isComplete A

/-- **Completeness** (Coq `Main.parse_complete`): if the completeness validator
accepts the tables, then for *every* parse tree of `word`, parsing `word`
(followed by any `bufferEnd`) with budget `2 ^ logNSteps` returns that tree's
semantics, consumes exactly `word`, and `pt_size tree ≤ 2 ^ logNSteps`; with too
little fuel it times out, and it never fails. -/
theorem parse_complete (init : A.InitState) (hsafe : safeValidator A = true)
    (hcomplete : completeValidator A = true) (logNSteps : Nat) (word : List G.Token)
    (bufferEnd : Buffer G) (tree : ParseTree G (.NT (A.start_nt init)) word) :
    match parse init hsafe logNSteps (word ++ₛ bufferEnd) with
    | .Parsed sem buff =>
        sem = ptSem tree ∧ buff = bufferEnd ∧ ptSize tree ≤ 2 ^ logNSteps
    | .Timeout => 2 ^ logNSteps < ptSize tree
    | .Fail _ _ => False :=
  LeanMenhir.parse_complete init word bufferEnd (safe_is_validator hsafe)
    (complete_is_validator hcomplete) tree logNSteps

/-- **Completeness, extensionally** : `parse_complete` for *any* input buffer
that denotes the same token stream as `word ++ₛ bufferEnd` — in particular the
array-backed buffers built by `Buf.ofListEof` that the runtime driver executes
(via `parse_congr`, since the parser observes the buffer only through
`head`/`tail`). The residual buffer is pinned up to denotation. -/
theorem parse_complete_ext (init : A.InitState) (hsafe : safeValidator A = true)
    (hcomplete : completeValidator A = true) (logNSteps : Nat) (word : List G.Token)
    (bufferEnd : Buffer G) (buffer : Buffer G) (hbuf : buffer.get = (word ++ₛ bufferEnd).get)
    (tree : ParseTree G (.NT (A.start_nt init)) word) :
    match parse init hsafe logNSteps buffer with
    | .Parsed sem buff =>
        sem = ptSem tree ∧ buff.get = bufferEnd.get ∧ ptSize tree ≤ 2 ^ logNSteps
    | .Timeout => 2 ^ logNSteps < ptSize tree
    | .Fail _ _ => False := by
  have Hc := parse_complete init hsafe hcomplete logNSteps word bufferEnd tree
  have Hcg : ParseResult.BufEquiv (parse init hsafe logNSteps buffer)
      (parse init hsafe logNSteps (word ++ₛ bufferEnd)) :=
    parse_congr init (safe_is_validator hsafe) hbuf logNSteps
  cases hp : parse init hsafe logNSteps buffer with
  | Fail st tok =>
    rw [hp] at Hcg
    cases hq : parse init hsafe logNSteps (word ++ₛ bufferEnd) with
    | Fail st' tok' => rw [hq] at Hc; exact Hc
    | Timeout => rw [hq] at Hcg; exact Hcg.elim
    | Parsed sem' buff' => rw [hq] at Hcg; exact Hcg.elim
  | Timeout =>
    rw [hp] at Hcg
    cases hq : parse init hsafe logNSteps (word ++ₛ bufferEnd) with
    | Timeout => rw [hq] at Hc; exact Hc
    | Fail st' tok' => rw [hq] at Hcg; exact Hcg.elim
    | Parsed sem' buff' => rw [hq] at Hcg; exact Hcg.elim
  | Parsed sem buff =>
    rw [hp] at Hcg
    cases hq : parse init hsafe logNSteps (word ++ₛ bufferEnd) with
    | Parsed sem' buff' =>
      rw [hq] at Hc Hcg
      obtain ⟨hsem, hbg⟩ := Hcg
      obtain ⟨h1, h2, h3⟩ := Hc
      exact ⟨hsem.trans h1, by rw [hbg, h2], h3⟩
    | Fail st' tok' => rw [hq] at Hcg; exact Hcg.elim
    | Timeout => rw [hq] at Hcg; exact Hcg.elim

/-- **Exact-consumption soundness** for EOF-anchored grammars: if the grammar is
EOF-anchored (`EofAnchored`, certified by the decidable `isEofAnchored`) and the
lexer never emits the EOF terminal, then a successful parse of the padded input
`Buf.ofListEof toks eofTok` recognised *exactly* `toks ++ [eofTok]` — the whole
input, anchored at EOF, no trailing garbage — and returned the semantics of one
of its parse trees. This upgrades `parse_correct`'s "some prefix of the padded
stream was recognised" to what a user actually expects of a parser. -/
theorem parse_correct_anchored (init : A.InitState) (hsafe : safeValidator A = true)
    (logNSteps : Nat) (toks : List G.Token) (eofTok : G.Token)
    (hanch : EofAnchored (G.token_term eofTok) (A.start_nt init))
    (hlex : ∀ tok ∈ toks, G.token_term tok ≠ G.token_term eofTok)
    {sem : G.symbol_semantic_type (.NT (A.start_nt init))} {rest : Buffer G}
    (hp : parse init hsafe logNSteps (Buf.ofListEof toks eofTok) = .Parsed sem rest) :
    ∃ pt : ParseTree G (.NT (A.start_nt init)) (toks ++ [eofTok]), ptSem pt = sem := by
  have Hc := parse_correct init hsafe logNSteps (Buf.ofListEof toks eofTok)
  rw [hp] at Hc
  obtain ⟨word, pt, hbuf, hsem⟩ := Hc
  have hpt : ∀ (i : Nat) (h : i < word.length), word[i] = toks.getD i eofTok := by
    intro i hi
    have h1 : (word ++ₛ rest).get i = word[i] := Buf.get_appendList_lt word rest i hi
    have h2 := congrFun hbuf i
    have h3 : (Buf.ofListEof toks eofTok).get i = toks.getD i eofTok := by
      rw [Buf.get_ofListEof]
      exact Buf.get_appendList_const eofTok toks i
    rw [← h1, ← h2]
    exact h3
  obtain ⟨w', tk, hw, htk, hw'⟩ := anchored_word_shape hanch pt
  have hweq : word = toks ++ [eofTok] :=
    word_eq_append_eof G.token_term (G.token_term eofTok) word toks eofTok rfl hpt
      w' tk hw htk hw' hlex
  exact ⟨hweq ▸ pt, by rw [ptSem_cast_word hweq pt]; exact hsem⟩

/-- **Unambiguity** (Coq `Main.unambiguity`): if both validators accept and the
token type is inhabited, any two parse trees of the same word have the same
semantic value. -/
theorem unambiguity (hsafe : safeValidator A = true) (hcomplete : completeValidator A = true)
    (tok : G.Token) (init : A.InitState) (word : List G.Token)
    (tree1 tree2 : ParseTree G (.NT (A.start_nt init)) word) :
    ptSem tree1 = ptSem tree2 := by
  have H1 := parse_complete init hsafe hcomplete (ptSize tree1) word (Buf.const tok) tree1
  have H2 := parse_complete init hsafe hcomplete (ptSize tree1) word (Buf.const tok) tree2
  cases hp : parse init hsafe (ptSize tree1) (word ++ₛ Buf.const tok) with
  | Fail st t => rw [hp] at H1; exact H1.elim
  | Timeout =>
    rw [hp] at H1
    exact absurd (Nat.lt_trans Nat.lt_two_pow_self H1) (Nat.lt_irrefl _)
  | Parsed sem buff =>
    rw [hp] at H1 H2
    exact H1.1.symm.trans H2.1

end Main
end LeanMenhir
