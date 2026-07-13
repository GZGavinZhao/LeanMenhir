/-
Port of `coq-menhirlib`'s `Main.v` to Lean 4.

Original: Copyright Inria and CNRS, LGPL-3.0-or-later.
This Lean port is a derivative work, distributed under LGPL-3.0-or-later.

The user-facing entry points: the boolean validators, the runnable `parse`, the
soundness theorem, and (given the completeness validator accepts) the
completeness and unambiguity theorems.
-/
import LeanMenhir.Correctness.Sound
import LeanMenhir.Correctness.CompleteProof
import LeanMenhir.Correctness.Congr
import LeanMenhir.Correctness.Anchored

namespace LeanMenhir
namespace Main

open LeanMenhir.Buf

variable {G : Grammar} {A : Automaton G}

/-- The runnable parser: given the safety invariant (`Safe A`, discharged by
`Safe.of_check (by decide)` for a concrete automaton), parse `buffer` with
budget `2 ^ logNSteps` (Coq `Main.parse`, minus the boolean-reflection detour). -/
def parse (init : A.InitState) (hsafe : Safe A) (logNSteps : Nat)
    (buffer : Buffer G) : ParseResult A (G.symbol_semantic_type (.NT (A.start_nt init))) :=
  LeanMenhir.parse init hsafe buffer logNSteps

/-- **Soundness**, Coq-shaped match-conclusion statement (Coq
`Main.parse_correct`). Prefer the equation-hypothesis primary `parse_sound`. -/
theorem parse_correct (init : A.InitState) (hsafe : Safe A)
    (logNSteps : Nat) (buffer : Buffer G) :
    match parse init hsafe logNSteps buffer with
    | .Parsed sem bufferNew =>
        ∃ (word : List G.Token) (pt : ParseTree G (.NT (A.start_nt init)) word),
          buffer.get = (word ++ₛ bufferNew).get ∧ ptSem pt = sem
    | _ => True :=
  LeanMenhir.parse_correct init hsafe buffer logNSteps

/-- **Completeness** (Coq `Main.parse_complete`): if the completeness validator
accepts the tables, then for *every* parse tree of `word`, parsing `word`
(followed by any `bufferEnd`) with budget `2 ^ logNSteps` returns that tree's
semantics, consumes exactly `word`, and `pt_size tree ≤ 2 ^ logNSteps`; with too
little fuel it times out, and it never fails.

Coq-shaped match-conclusion statement (Coq `Main.parse_complete`); prefer the
equation-hypothesis primaries `parse_complete_parsed` / `parse_never_rejects` /
`parse_timeout_bound`. -/
theorem parse_complete (init : A.InitState) (hsafe : Safe A)
    (hcomplete : Complete A) (logNSteps : Nat) (word : List G.Token)
    (bufferEnd : Buffer G) (tree : ParseTree G (.NT (A.start_nt init)) word) :
    match parse init hsafe logNSteps (word ++ₛ bufferEnd) with
    | .Parsed sem buff =>
        sem = ptSem tree ∧ buff = bufferEnd ∧ ptSize tree ≤ 2 ^ logNSteps
    | .Timeout => 2 ^ logNSteps < ptSize tree
    | .Fail _ _ => False :=
  LeanMenhir.parse_complete init word bufferEnd hsafe hcomplete tree logNSteps

/-- **Soundness** (equation-hypothesis primary) — *if the parser accepts, the
input really is in the language and the value is its meaning*: `.Parsed sem rest`
implies some word derives from the start symbol, the buffer denotes exactly that
word followed by `rest`, and `sem` is the derivation's semantics. -/
theorem parse_sound (init : A.InitState) (hsafe : Safe A) {fuel : Nat}
    {buffer : Buffer G} {sem : G.symbol_semantic_type (.NT (A.start_nt init))}
    {rest : Buffer G}
    (h : parse init hsafe fuel buffer = .Parsed sem rest) :
    ∃ (word : List G.Token) (pt : ParseTree G (.NT (A.start_nt init)) word),
      buffer.get = (word ++ₛ rest).get ∧ ptSem pt = sem := by
  have H := parse_correct init hsafe fuel buffer
  rw [h] at H
  exact H

/-- **Completeness** (equation-hypothesis primary) — *every derivation is found*:
parsing a derivable word returns exactly the derivation's semantic value and the
untouched continuation, given fuel covering the derivation's size. -/
theorem parse_complete_parsed (init : A.InitState) (hsafe : Safe A)
    (hcomplete : Complete A) {word : List G.Token} {bufferEnd : Buffer G}
    (tree : ParseTree G (.NT (A.start_nt init)) word) {fuel : Nat}
    (hfuel : ptSize tree ≤ 2 ^ fuel) :
    parse init hsafe fuel (word ++ₛ bufferEnd) = .Parsed (ptSem tree) bufferEnd := by
  have H := parse_complete init hsafe hcomplete fuel word bufferEnd tree
  cases hp : parse init hsafe fuel (word ++ₛ bufferEnd) with
  | Parsed sem buff => rw [hp] at H; rw [H.1, H.2.1]
  | Timeout => rw [hp] at H; omega
  | Fail st tok => rw [hp] at H; exact H.elim

/-- **No spurious rejection** (equation-hypothesis primary): derivable input is
never `.Fail`ed, at any fuel. -/
theorem parse_never_rejects (init : A.InitState) (hsafe : Safe A)
    (hcomplete : Complete A) {word : List G.Token} {bufferEnd : Buffer G}
    (tree : ParseTree G (.NT (A.start_nt init)) word) (fuel : Nat)
    (st : A.State) (tok : G.Token) :
    parse init hsafe fuel (word ++ₛ bufferEnd) ≠ .Fail st tok := by
  intro hp
  have H := parse_complete init hsafe hcomplete fuel word bufferEnd tree
  rw [hp] at H
  exact H

/-- **Timeout bound** (equation-hypothesis primary): a timeout on derivable
input means the fuel really was smaller than the derivation. -/
theorem parse_timeout_bound (init : A.InitState) (hsafe : Safe A)
    (hcomplete : Complete A) {word : List G.Token} {bufferEnd : Buffer G}
    (tree : ParseTree G (.NT (A.start_nt init)) word) {fuel : Nat}
    (h : parse init hsafe fuel (word ++ₛ bufferEnd) = .Timeout) :
    2 ^ fuel < ptSize tree := by
  have H := parse_complete init hsafe hcomplete fuel word bufferEnd tree
  rw [h] at H
  exact H

/-- **Completeness, extensionally** : `parse_complete` for *any* input buffer
that denotes the same token stream as `word ++ₛ bufferEnd` — in particular the
array-backed buffers built by `Buf.ofListEof` that the runtime driver executes
(via `parse_congr`, since the parser observes the buffer only through
`head`/`tail`). The residual buffer is pinned up to denotation. -/
theorem parse_complete_ext (init : A.InitState) (hsafe : Safe A)
    (hcomplete : Complete A) (logNSteps : Nat) (word : List G.Token)
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
    parse_congr init hsafe hbuf logNSteps
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
theorem parse_correct_anchored (init : A.InitState) (hsafe : Safe A)
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
token type is inhabited (`[Nonempty G.Token]` — the honest rendering of Coq's
`inhabited token`; the witness is proof-only), any two parse trees of the same
word have the same semantic value. -/
theorem unambiguity [htok : Nonempty G.Token] (hsafe : Safe A) (hcomplete : Complete A)
    (init : A.InitState) (word : List G.Token)
    (tree1 tree2 : ParseTree G (.NT (A.start_nt init)) word) :
    ptSem tree1 = ptSem tree2 := by
  obtain ⟨tok⟩ := htok
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
