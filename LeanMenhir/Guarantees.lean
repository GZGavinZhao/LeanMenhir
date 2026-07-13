/-
★ THE REVIEW SURFACE ★

This file restates every end-to-end guarantee of LeanMenhir in the form a
reviewer should read: equation-hypothesis style ("if the parser returned
`Parsed …`, then …"), each with an informal reading, its precise caveats, and a
build-enforced axiom guard. Every proof here is a thin wrapper (`exact`/case
split) around an internal theorem — reviewing this file adds no proof risk and
requires no knowledge of the proof architecture.

# How to audit LeanMenhir (see also `docs/AUDIT.md`)

Read, in order:

1. `LeanMenhir/Spec/Grammar.lean` — what a grammar, a derivation (`ParseTree G`), and
   its semantic value (`ptSem`) are; `LeanMenhir/Spec/Language.lean` — the
   propositional form: `Derives` / `word ∈ language nt` ("a derivation exists").
   **These define "the language".**
2. `LeanMenhir/Spec/Buffer.lean` — what an input buffer denotes (`Buf.get`).
   **This defines "the input".**
3. `LeanMenhir/Machine/Interpreter.lean` — the signature and definition of `parse`
   (and `LeanMenhir/Runtime.lean` for the executable driver `parseList`).
   **This defines "what runs".**
4. This file. **This defines "what is guaranteed".**

Trusted base: the Lean kernel, the definitions in (1)–(3), the `Grammar0` you
wrote (the verified grammar is a definitional function of it — see §6), and
your lexer's EOF discipline (hypothesis `hlex` below). Everything else — the LR generator, the
table blobs, the validators' boolean kernels, the 2000 lines of ported proofs —
is *untrusted*: bugs there can only make certificates fail to check, never make
a theorem below claim something false.

Current caveats a reviewer must know (tracked in the idiomatic-refactor plan):
* The theorems are stated over an `Automaton`, whose grammar is the embedded
  `A.toGrammar` (Coq heritage). The grammar/automaton split (refactor phase P1)
  will make the grammar a separate, explicit binder.
* The validator hypotheses are the `Prop` structures `Safe A` / `Complete A`
  (named, documented fields); per-automaton they are discharged by the tuned
  boolean validators via `Safe.of_check (by decide)` etc. (genuine `Decidable`
  instances arrive with phase P5's reflection converses).

LGPL-3.0-or-later (derivative of coq-menhirlib).
-/
import LeanMenhir.Runtime
import LeanMenhir.Spec.Language

namespace LeanMenhir
namespace Guarantees

open LeanMenhir.Buf

variable {G : Grammar} {A : Automaton G}

/-! ## 1. Soundness -/

/-- **Soundness** — *if the parser accepts, the input really is in the language,
and the returned value is its meaning.*

If `parse` returns `.Parsed sem rest`, then there is a word `word` and a real
derivation (`ParseTree G`) of `word` from the start symbol such that (a) the input
buffer denotes exactly `word` followed by the residual buffer `rest`, and (b)
the returned semantic value `sem` is that derivation's semantics.

Caveats: `word` is *a prefix* of the input stream — "the whole input was
consumed" needs EOF anchoring, see `parser_consumes_exactly`. Nothing is claimed
about `.Fail`/`.Timeout` outcomes here; see `parser_never_rejects_valid`.

Wraps `Main.parse_correct` (Coq `Main.parse_correct`). -/
theorem parser_sound (init : A.InitState) (hsafe : Safe A)
    (fuel : Nat) (buffer : Buffer G) {sem : G.symbol_semantic_type (.NT (A.start_nt init))}
    {rest : Buffer G}
    (h : Main.parse init hsafe fuel buffer = .Parsed sem rest) :
    ∃ (word : List G.Token) (pt : ParseTree G (.NT (A.start_nt init)) word),
      buffer.get = (word ++ₛ rest).get ∧ ptSem pt = sem :=
  Main.parse_sound init hsafe h

/-- **Soundness, recognition face** — *if the parser accepts, the consumed
prefix is a word of the language.* The membership-only corollary of
`parser_sound` (the derivation is forgotten into `∈ language`). -/
theorem parser_sound_mem (init : A.InitState) (hsafe : Safe A)
    (fuel : Nat) (buffer : Buffer G) {sem : G.symbol_semantic_type (.NT (A.start_nt init))}
    {rest : Buffer G}
    (h : Main.parse init hsafe fuel buffer = .Parsed sem rest) :
    ∃ word ∈ G.language (A.start_nt init), buffer.get = (word ++ₛ rest).get := by
  obtain ⟨word, pt, hbuf, -⟩ := parser_sound init hsafe fuel buffer h
  exact ⟨word, ⟨pt⟩, hbuf⟩

/-! ## 2. Completeness -/

/-- **Completeness** — *every program in the language is parsed, to the right
value, consuming exactly its word.*

For **any** derivation `tree` of `word` from the start symbol, running the
parser on `word` (followed by anything) returns precisely that derivation's
semantic value and hands back the untouched continuation `bufferEnd` — provided
the fuel budget `2 ^ fuel` covers the derivation's size.

Caveats: the fuel hypothesis. The runtime driver discharges it up to physical
realisability (`runtime_complete`); for hand-picked fuel it is a real
obligation.

Wraps `Main.parse_complete` (Coq `Main.parse_complete`). -/
theorem parser_complete (init : A.InitState) (hsafe : Safe A)
    (hcomplete : Complete A)
    (word : List G.Token) (bufferEnd : Buffer G)
    (tree : ParseTree G (.NT (A.start_nt init)) word)
    (fuel : Nat) (hfuel : ptSize tree ≤ 2 ^ fuel) :
    Main.parse init hsafe fuel (word ++ₛ bufferEnd) = .Parsed (ptSem tree) bufferEnd :=
  Main.parse_complete_parsed init hsafe hcomplete tree hfuel

/-- **Completeness, recognition face** — *every word of the language is
accepted.*

If `word ∈ G.language (A.start_nt init)` — the hypothesis a reader expects — then
the parser, given enough fuel, accepts `word` (followed by anything) and hands
back the untouched continuation. Membership alone cannot reveal the size of a
derivation, hence the existential fuel threshold; `parser_complete` (the
semantic face, of which this is a corollary) pins value and fuel exactly, and
`runtime_complete` discharges the fuel up to physical realisability. -/
theorem parser_accepts (init : A.InitState) (hsafe : Safe A)
    (hcomplete : Complete A)
    {word : List G.Token} (hmem : word ∈ G.language (A.start_nt init))
    (bufferEnd : Buffer G) :
    ∃ fuel₀, ∀ fuel, fuel₀ ≤ fuel →
      ∃ sem, Main.parse init hsafe fuel (word ++ₛ bufferEnd) = .Parsed sem bufferEnd := by
  obtain ⟨tree⟩ := hmem
  refine ⟨ptSize tree, fun fuel hfuel => ⟨ptSem tree, ?_⟩⟩
  exact parser_complete init hsafe hcomplete word bufferEnd tree fuel
    (Nat.le_trans hfuel (Nat.le_of_lt Nat.lt_two_pow_self))

/-- **No spurious rejection** — *a word of the language is never `Fail`ed, with
any fuel.*

If `word ∈ G.language (A.start_nt init)`, the parser never answers `.Fail` on it —
even with too little fuel (it answers `.Timeout` instead). Together with
`parser_accepts` this is what makes `.Fail` a trustworthy "syntax error".

Wraps the `Fail → False` case of `Main.parse_complete`. -/
theorem parser_never_rejects_valid (init : A.InitState)
    (hsafe : Safe A) (hcomplete : Complete A)
    {word : List G.Token} (hmem : word ∈ G.language (A.start_nt init))
    (bufferEnd : Buffer G)
    (fuel : Nat) (st : A.State) (tok : G.Token) :
    Main.parse init hsafe fuel (word ++ₛ bufferEnd) ≠ .Fail st tok := by
  obtain ⟨tree⟩ := hmem
  exact Main.parse_never_rejects init hsafe hcomplete tree fuel st tok

/-! ## 3. Unambiguity -/

/-- **Unambiguity** — *any two derivations of the same word have the same
meaning.*

Caveat (important): this is **value-level** unambiguity — `ptSem tree1 = ptSem
tree2` — exactly as in the Coq original. Distinct derivation *trees* that your
semantic actions happen to collapse (e.g. identity coercion chains) are not
distinguished. To obtain tree-level (grammatical) unambiguity, instantiate the
semantic values with the syntax trees themselves.

Wraps `Main.unambiguity` (Coq `Main.unambiguity`; `[Nonempty G.Token]` is the
honest rendering of Coq's `inhabited token` — the witness is proof-only). -/
theorem grammar_unambiguous [Nonempty G.Token]
    (hsafe : Safe A) (hcomplete : Complete A)
    (init : A.InitState) (word : List G.Token)
    (tree1 tree2 : ParseTree G (.NT (A.start_nt init)) word) :
    ptSem tree1 = ptSem tree2 :=
  Main.unambiguity hsafe hcomplete init word tree1 tree2

/-! ## 4. Exact consumption (EOF anchoring) -/

/-- **Exact consumption** — *acceptance means the whole input was parsed, and
nothing but the input.*

Plain soundness only pins a *prefix* of the padded stream. If additionally the
grammar is EOF-anchored (`EofAnchored`, a decidable per-grammar check: every
start production ends in the EOF terminal, which occurs nowhere else) and the
lexer never emits the EOF terminal (`hlex`), then acceptance of the padded
input `Buf.ofListEof toks eofTok` means the recognised word is **exactly**
`toks ++ [eofTok]` — no trailing garbage accepted, EOF reached.

Wraps `Main.parse_correct_anchored` (no Coq counterpart; leak-3 fix). -/
theorem parser_consumes_exactly (init : A.InitState)
    (hsafe : Safe A) (fuel : Nat)
    (toks : List G.Token) (eofTok : G.Token)
    (hanch : EofAnchored (G.token_term eofTok) (A.start_nt init))
    (hlex : ∀ tok ∈ toks, G.token_term tok ≠ G.token_term eofTok)
    {sem : G.symbol_semantic_type (.NT (A.start_nt init))} {rest : Buffer G}
    (h : Main.parse init hsafe fuel (Buf.ofListEof toks eofTok) = .Parsed sem rest) :
    toks ++ [eofTok] ∈ G.language (A.start_nt init) ∧
      ∃ pt : ParseTree G (.NT (A.start_nt init)) (toks ++ [eofTok]), ptSem pt = sem :=
  have ⟨pt, hsem⟩ := Main.parse_correct_anchored init hsafe fuel toks eofTok hanch hlex h
  ⟨⟨pt⟩, pt, hsem⟩

/-! ## 5. The executable driver enjoys all of the above

`Runtime.parseList` is what applications actually run: it pads the finite token
list with an EOF filler into an array-backed buffer and projects the result into
`Except`. The theorems below transfer the guarantees to that exact code path
(via the interpreter-extensionality bridge `parse_congr` — the parser cannot
distinguish denotationally equal buffers). -/

/-- **Runtime soundness**: `parseList` returning `.ok v` means some prefix of
the padded input stream derives from the start symbol with value `v`.
(For "the whole input", see `runtime_consumes_exactly`.) -/
theorem runtime_sound {E : Type} (init : A.InitState)
    (hsafe : Safe A) (eof : G.Token) (toks : List G.Token)
    (onFail : A.State → G.Token → E) (onTimeout : E)
    {v : Runtime.ResultType A init}
    (h : Runtime.parseList init hsafe eof toks onFail onTimeout = .ok v) :
    ∃ (word : List G.Token) (rest : Buffer G)
      (pt : ParseTree G (.NT (A.start_nt init)) word),
      (Buf.ofListEof toks eof).get = (word ++ₛ rest).get ∧ ptSem pt = v := by
  unfold Runtime.parseList at h
  cases hp : Main.parse init hsafe (Runtime.fuelFor toks.length) (Buf.ofListEof toks eof) with
  | Parsed v' rest =>
    rw [hp] at h
    injection h with hv
    subst hv
    obtain ⟨word, pt, hbuf, hsem⟩ := parser_sound init hsafe _ _ hp
    exact ⟨word, rest, pt, hbuf, hsem⟩
  | Fail st tok => rw [hp] at h; exact absurd h (by simp)
  | Timeout => rw [hp] at h; exact absurd h (by simp)

/-- **Runtime completeness**: any derivation of `toks` followed by `k` EOF
sentinels (for EOF-anchored grammars, `k = 1`) with at most `2⁶⁴` nodes — i.e.
*any physically constructible derivation* — is found by the driver, which
returns exactly its semantic value.

Wraps `Runtime.parseList_complete_sized` (leak-1 + leak-4 fixes). -/
theorem runtime_complete {E : Type} (init : A.InitState)
    (hsafe : Safe A) (hcomplete : Complete A)
    (eof : G.Token) (toks : List G.Token)
    (onFail : A.State → G.Token → E) (onTimeout : E) (k : Nat)
    (tree : ParseTree G (.NT (A.start_nt init)) (toks ++ List.replicate k eof))
    (hsize : ptSize tree ≤ 2 ^ 64) :
    Runtime.parseList init hsafe eof toks onFail onTimeout = .ok (ptSem tree) :=
  Runtime.parseList_complete_sized init hsafe hcomplete eof toks onFail onTimeout k tree hsize

/-- **Runtime exact consumption**: for an EOF-anchored grammar and an EOF-free
lexer, `parseList` returning `.ok v` means the *entire* input (and nothing
else) was parsed, with `v` the semantics of one of its derivations.

Wraps `Runtime.parseList_sound_anchored` (leak-3 fix). -/
theorem runtime_consumes_exactly {E : Type} (init : A.InitState)
    (hsafe : Safe A) (eof : G.Token) (toks : List G.Token)
    (onFail : A.State → G.Token → E) (onTimeout : E)
    (hanch : EofAnchored (G.token_term eof) (A.start_nt init))
    (hlex : ∀ tok ∈ toks, G.token_term tok ≠ G.token_term eof)
    {v : Runtime.ResultType A init}
    (h : Runtime.parseList init hsafe eof toks onFail onTimeout = .ok v) :
    toks ++ [eof] ∈ G.language (A.start_nt init) ∧
      ∃ pt : ParseTree G (.NT (A.start_nt init)) (toks ++ [eof]), ptSem pt = v :=
  have ⟨pt, hsem⟩ :=
    Runtime.parseList_sound_anchored init hsafe eof toks onFail onTimeout hanch hlex h
  ⟨⟨pt⟩, pt, hsem⟩

/-! ## 6. The theorems are about *your* grammar

No theorem is needed here anymore — it holds **by construction** (D9): for
generated parsers, the grammar `G` above is `grammar.toGrammar(Typed) lk …`,
a definitional function of the `Grammar0` you wrote; the tables supply only the
untrusted automaton half, and the production lookups `lk : ProdLookup grammar`
carry intrinsic agreement proofs. On top,
`Gen.Grammar0.toGrammar_derives_iff` (and `…Typed…`) proves `G`'s *language*
equal to the 15-line textbook relation `Grammar0.Derives` on terminal strings —
see `Examples/MiniCalc.lean`'s `mini_language_eq` / `mini_accepts` for the
end-to-end shape. -/

/-! ## Axiom guards (build-enforced)

Every guarantee above depends on at most the three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) — no `sorry`, no custom axioms,
no compiler trust (`Lean.ofReduceBool` appears only in examples that opt into
`native_decide` and say so). `#guard_msgs` turns any regression into a build
failure. -/

/-- info: 'LeanMenhir.Guarantees.parser_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms parser_sound

/-- info: 'LeanMenhir.Guarantees.parser_sound_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms parser_sound_mem

/-- info: 'LeanMenhir.Guarantees.parser_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parser_complete

/-- info: 'LeanMenhir.Guarantees.parser_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parser_accepts

/-- info: 'LeanMenhir.Guarantees.parser_never_rejects_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parser_never_rejects_valid

/-- info: 'LeanMenhir.Guarantees.grammar_unambiguous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms grammar_unambiguous

/-- info: 'LeanMenhir.Guarantees.parser_consumes_exactly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms parser_consumes_exactly

/-- info: 'LeanMenhir.Guarantees.runtime_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms runtime_sound

/-- info: 'LeanMenhir.Guarantees.runtime_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms runtime_complete

/-- info: 'LeanMenhir.Guarantees.runtime_consumes_exactly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms runtime_consumes_exactly

end Guarantees
end LeanMenhir
