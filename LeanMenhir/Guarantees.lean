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

1. `LeanMenhir/Grammar.lean` — what a grammar, a derivation (`ParseTree`), and
   its semantic value (`ptSem`) are. **This defines "the language".**
2. `LeanMenhir/Buf.lean` — what an input buffer denotes (`Buf.get`).
   **This defines "the input".**
3. `LeanMenhir/Interpreter.lean` — the signature and definition of `parse`
   (and `LeanMenhir/Runtime.lean` for the executable driver `parseList`).
   **This defines "what runs".**
4. This file. **This defines "what is guaranteed".**

Trusted base: the Lean kernel, the definitions in (1)–(3), the `Grammar0` you
wrote (tied to the tables by `tables_grammar_faithful`), and your lexer's EOF
discipline (hypothesis `hlex` below). Everything else — the LR generator, the
table blobs, the validators' boolean kernels, the 2000 lines of ported proofs —
is *untrusted*: bugs there can only make certificates fail to check, never make
a theorem below claim something false.

Current caveats a reviewer must know (tracked in the idiomatic-refactor plan):
* The theorems are stated over an `Automaton`, whose grammar is the embedded
  `A.toGrammar` (Coq heritage). The grammar/automaton split (refactor phase P1)
  will make the grammar a separate, explicit binder.
* Hypotheses of the form `Main.safeValidator () = true` are boolean-reflection
  certificates (Coq heritage); phase P2 replaces them with `Prop`s (`Safe A`,
  `Complete A`) carrying named, documented content.

LGPL-3.0-or-later (derivative of coq-menhirlib).
-/
import LeanMenhir.Runtime
import LeanMenhir.Generator.GrammarCheck

namespace LeanMenhir
namespace Guarantees

open LeanMenhir.Buf

variable [A : Automaton]

/-! ## 1. Soundness -/

/-- **Soundness** — *if the parser accepts, the input really is in the language,
and the returned value is its meaning.*

If `parse` returns `.Parsed sem rest`, then there is a word `word` and a real
derivation (`ParseTree`) of `word` from the start symbol such that (a) the input
buffer denotes exactly `word` followed by the residual buffer `rest`, and (b)
the returned semantic value `sem` is that derivation's semantics.

Caveats: `word` is *a prefix* of the input stream — "the whole input was
consumed" needs EOF anchoring, see `parser_consumes_exactly`. Nothing is claimed
about `.Fail`/`.Timeout` outcomes here; see `parser_never_rejects_valid`.

Wraps `Main.parse_correct` (Coq `Main.parse_correct`). -/
theorem parser_sound (init : A.InitState) (hsafe : Main.safeValidator () = true)
    (fuel : Nat) (buffer : Buffer) {sem : A.symbol_semantic_type (.NT (A.start_nt init))}
    {rest : Buffer}
    (h : Main.parse init hsafe fuel buffer = .Parsed sem rest) :
    ∃ (word : List A.Token) (pt : ParseTree (.NT (A.start_nt init)) word),
      buffer.get = (word ++ₛ rest).get ∧ ptSem pt = sem := by
  have H := Main.parse_correct init hsafe fuel buffer
  rw [h] at H
  exact H

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
theorem parser_complete (init : A.InitState) (hsafe : Main.safeValidator () = true)
    (hcomplete : Main.completeValidator () = true)
    (word : List A.Token) (bufferEnd : Buffer)
    (tree : ParseTree (.NT (A.start_nt init)) word)
    (fuel : Nat) (hfuel : ptSize tree ≤ 2 ^ fuel) :
    Main.parse init hsafe fuel (word ++ₛ bufferEnd) = .Parsed (ptSem tree) bufferEnd := by
  have H := Main.parse_complete init hsafe hcomplete fuel word bufferEnd tree
  cases hp : Main.parse init hsafe fuel (word ++ₛ bufferEnd) with
  | Parsed sem buff =>
    rw [hp] at H
    obtain ⟨h1, h2, -⟩ := H
    rw [h1, h2]
  | Timeout => rw [hp] at H; omega
  | Fail st tok => rw [hp] at H; exact H.elim

/-- **No spurious rejection** — *valid input is never `Fail`ed, with any fuel.*

If `word` has a derivation, the parser never answers `.Fail` on it — even with
too little fuel (it answers `.Timeout` instead). Together with
`parser_complete` this is what makes `.Fail` a trustworthy "syntax error".

Wraps the `Fail → False` case of `Main.parse_complete`. -/
theorem parser_never_rejects_valid (init : A.InitState)
    (hsafe : Main.safeValidator () = true) (hcomplete : Main.completeValidator () = true)
    (word : List A.Token) (bufferEnd : Buffer)
    (tree : ParseTree (.NT (A.start_nt init)) word)
    (fuel : Nat) (st : A.State) (tok : A.Token) :
    Main.parse init hsafe fuel (word ++ₛ bufferEnd) ≠ .Fail st tok := by
  intro hp
  have H := Main.parse_complete init hsafe hcomplete fuel word bufferEnd tree
  rw [hp] at H
  exact H

/-! ## 3. Unambiguity -/

/-- **Unambiguity** — *any two derivations of the same word have the same
meaning.*

Caveat (important): this is **value-level** unambiguity — `ptSem tree1 = ptSem
tree2` — exactly as in the Coq original. Distinct derivation *trees* that your
semantic actions happen to collapse (e.g. identity coercion chains) are not
distinguished. To obtain tree-level (grammatical) unambiguity, instantiate the
semantic values with the syntax trees themselves.

Wraps `Main.unambiguity` (Coq `Main.unambiguity`; `[Nonempty A.Token]` is the
honest rendering of Coq's `inhabited token` — the witness is proof-only). -/
theorem grammar_unambiguous [Nonempty A.Token]
    (hsafe : Main.safeValidator () = true) (hcomplete : Main.completeValidator () = true)
    (init : A.InitState) (word : List A.Token)
    (tree1 tree2 : ParseTree (.NT (A.start_nt init)) word) :
    ptSem tree1 = ptSem tree2 := by
  obtain ⟨tok⟩ := ‹Nonempty A.Token›
  exact Main.unambiguity hsafe hcomplete tok init word tree1 tree2

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
    (hsafe : Main.safeValidator () = true) (fuel : Nat)
    (toks : List A.Token) (eofTok : A.Token)
    (hanch : EofAnchored (A.token_term eofTok) (A.start_nt init))
    (hlex : ∀ tok ∈ toks, A.token_term tok ≠ A.token_term eofTok)
    {sem : A.symbol_semantic_type (.NT (A.start_nt init))} {rest : Buffer}
    (h : Main.parse init hsafe fuel (Buf.ofListEof toks eofTok) = .Parsed sem rest) :
    ∃ pt : ParseTree (.NT (A.start_nt init)) (toks ++ [eofTok]), ptSem pt = sem :=
  Main.parse_correct_anchored init hsafe fuel toks eofTok hanch hlex h

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
    (hsafe : Main.safeValidator () = true) (eof : A.Token) (toks : List A.Token)
    (onFail : A.State → A.Token → E) (onTimeout : E)
    {v : Runtime.ResultType A init}
    (h : Runtime.parseList init hsafe eof toks onFail onTimeout = .ok v) :
    ∃ (word : List A.Token) (rest : Buffer)
      (pt : ParseTree (.NT (A.start_nt init)) word),
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
    (hsafe : Main.safeValidator () = true) (hcomplete : Main.completeValidator () = true)
    (eof : A.Token) (toks : List A.Token)
    (onFail : A.State → A.Token → E) (onTimeout : E) (k : Nat)
    (tree : ParseTree (.NT (A.start_nt init)) (toks ++ List.replicate k eof))
    (hsize : ptSize tree ≤ 2 ^ 64) :
    Runtime.parseList init hsafe eof toks onFail onTimeout = .ok (ptSem tree) :=
  Runtime.parseList_complete_sized init hsafe hcomplete eof toks onFail onTimeout k tree hsize

/-- **Runtime exact consumption**: for an EOF-anchored grammar and an EOF-free
lexer, `parseList` returning `.ok v` means the *entire* input (and nothing
else) was parsed, with `v` the semantics of one of its derivations.

Wraps `Runtime.parseList_sound_anchored` (leak-3 fix). -/
theorem runtime_consumes_exactly {E : Type} (init : A.InitState)
    (hsafe : Main.safeValidator () = true) (eof : A.Token) (toks : List A.Token)
    (onFail : A.State → A.Token → E) (onTimeout : E)
    (hanch : EofAnchored (A.token_term eof) (A.start_nt init))
    (hlex : ∀ tok ∈ toks, A.token_term tok ≠ A.token_term eof)
    {v : Runtime.ResultType A init}
    (h : Runtime.parseList init hsafe eof toks onFail onTimeout = .ok v) :
    ∃ pt : ParseTree (.NT (A.start_nt init)) (toks ++ [eof]), ptSem pt = v :=
  Runtime.parseList_sound_anchored init hsafe eof toks onFail onTimeout hanch hlex h

/-! ## 6. The theorems are about *your* grammar -/

omit A in
/-- **Grammar faithfulness** — *the grammar all theorems above quantify over is
exactly the `Grammar0` you wrote.*

The safety/completeness validators certify only the *automaton* half of a
generated table blob; a generator bug could produce a perfectly safe+complete
automaton **for the wrong grammar**. The decidable check `tablesMatchGrammar`
(certified per example by kernel `decide`/`rfl`) compares the production data
the verified bridges consume — jump-table fields *and* plain arrays — against
your `Grammar0`, with every index in range, so the `Fin` padding never clamps
and the dummy symbols stay unreachable. This proposition is what ties
`ParseTree` in the theorems above to the grammar a human reviews.

Wraps `Gen.tablesMatchGrammar_spec` (no Coq counterpart; leak-2 fix). See also
the faithfulness lemmas `TablesMatchGrammar.prodLhsOf_val`,
`TablesMatchGrammar.prodRhsRevOf_eq`, `TablesMatchGrammar.startNt_val`. -/
theorem tables_grammar_faithful {t : Gen.GenTables} {g : Gen.Grammar0}
    (h : Gen.tablesMatchGrammar t g = true) : Gen.TablesMatchGrammar t g :=
  Gen.tablesMatchGrammar_spec h

/-! ## Axiom guards (build-enforced)

Every guarantee above depends on at most the three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) — no `sorry`, no custom axioms,
no compiler trust (`Lean.ofReduceBool` appears only in examples that opt into
`native_decide` and say so). `#guard_msgs` turns any regression into a build
failure. -/

/-- info: 'LeanMenhir.Guarantees.parser_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms parser_sound

/-- info: 'LeanMenhir.Guarantees.parser_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parser_complete

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

/-- info: 'LeanMenhir.Guarantees.tables_grammar_faithful' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms tables_grammar_faithful

end Guarantees
end LeanMenhir
