/-
A small, **grammar-agnostic** runtime that drives the verified parser
(`Main.parse`) over a finite token list. A BNFC-style backend emits the
grammar-specific glue (grammar, tables via `build_tables%`, `ntType`/`termType`/
`actions`, the automaton, and a token adapter) and calls into here.

Nothing in this module is grammar-specific; it only:
  * computes a step budget from the token count,
  * pads the finite token list into the infinite `Buffer` the interpreter wants,
  * maps the `ParseResult` (`Parsed`/`Fail`/`Timeout`) into an `Except`.

Tokens built by `Gen.automatonOfTablesTyped` have the shape `Info × Σ t, termType t`;
`onFail` receives the failing lookahead token, so the caller can read a source
position out of its `Info` component (`.1`) for error messages.

LGPL-3.0-or-later (derivative of coq-menhirlib).
-/
import LeanMenhir.Main

namespace LeanMenhir.Runtime

open LeanMenhir
open LeanMenhir.Buf

variable {A : Automaton}

/-- A fuel **exponent** generous enough for an input of `n` tokens. `Main.parse`
runs with a budget of `2 ^ logNSteps` steps and a complete parse takes `O(n)`
steps, so any `logNSteps ≥ log₂ n + c` suffices; we add slack. Too-small fuel
only yields a `Timeout` error — never an unsound result — so over-provisioning is
safe (the loop stops as soon as the parse accepts or fails). -/
def fuelFor (n : Nat) : Nat := Nat.log2 (n + 1) + 6

/-- The semantic-value type produced by parsing from initial state `init`: the
value type of the start nonterminal. -/
abbrev ResultType (A : Automaton) (init : A.InitState) : Type :=
  A.symbol_semantic_type (.NT (A.start_nt init))

/-- Run the verified parser on the finite token list `toks`, padding the buffer
with the infinite `eof` filler, and project the `ParseResult` into `Except E`.
`onFail`/`onTimeout` build the caller's error type from the failure cases. -/
def parseList {E : Type}
    (init : A.InitState) (hsafe : Main.safeValidator () = true)
    (eof : A.Token) (toks : List A.Token)
    (onFail : A.State → A.Token → E) (onTimeout : E) :
    Except E (ResultType A init) :=
  match Main.parse init hsafe (fuelFor toks.length) (Buf.ofListEof toks eof) with
  | .Parsed v _ => .ok v
  | .Fail st tok => .error (onFail st tok)
  | .Timeout => .error onTimeout

/-- Convenience wrapper: convert each external token via `adapt` (which may fail —
e.g. an unlexable token), then `parseList`. The external token type `Tok` is
whatever the lexer produces (e.g. BNFC's `Token`). -/
def parseWith {Tok E : Type}
    (init : A.InitState) (hsafe : Main.safeValidator () = true)
    (eof : A.Token) (adapt : Tok → Except E A.Token)
    (onFail : A.State → A.Token → E) (onTimeout : E)
    (input : List Tok) :
    Except E (ResultType A init) := do
  parseList init hsafe eof (← input.mapM adapt) onFail onTimeout

/-- **Completeness of the runtime driver.** If `toks` followed by `k` copies of
the EOF filler is a word of the grammar — witnessed by a parse `tree` — and the
fuel heuristic covers the tree (`ptSize tree ≤ 2 ^ fuelFor toks.length`), then
`parseList` returns exactly that tree's semantic value.

For the usual EOF-anchored grammar (every start production ends in the EOF
terminal) instantiate `k := 1`: the recognised word is `toks ++ [eof]`, i.e.
the entire input is consumed and anchored at EOF. `k := 0` covers grammars that
do not read an end marker.

This is the end-to-end form of `Main.parse_complete`: the theorem there speaks
about push-list buffers `word ++ₛ bufferEnd`, while `parseList` executes on the
array-backed `Buf.ofListEof toks eof`; the two are connected by the interpreter
extensionality bridge (`parse_congr`), since both denote the same token stream
`toks ++ eof^ω`. -/
theorem parseList_complete {E : Type}
    (init : A.InitState) (hsafe : Main.safeValidator () = true)
    (hcomplete : Main.completeValidator () = true)
    (eof : A.Token) (toks : List A.Token)
    (onFail : A.State → A.Token → E) (onTimeout : E) (k : Nat)
    (tree : ParseTree (.NT (A.start_nt init)) (toks ++ List.replicate k eof))
    (hfuel : ptSize tree ≤ 2 ^ fuelFor toks.length) :
    parseList init hsafe eof toks onFail onTimeout = .ok (ptSem tree) := by
  have hbuf : (Buf.ofListEof toks eof).get
      = ((toks ++ List.replicate k eof) ++ₛ Buf.const eof).get := by
    rw [Buf.append_append_stream, Buf.get_ofListEof]
    exact (Buf.appendList_get_congr (Buf.get_replicate_const k eof) toks).symm
  have H := Main.parse_complete_ext init hsafe hcomplete (fuelFor toks.length)
    (toks ++ List.replicate k eof) (Buf.const eof) (Buf.ofListEof toks eof) hbuf tree
  unfold parseList
  cases hp : Main.parse init hsafe (fuelFor toks.length) (Buf.ofListEof toks eof) with
  | Parsed v rest => rw [hp] at H; rw [H.1]
  | Fail st tok => rw [hp] at H; exact H.elim
  | Timeout => rw [hp] at H; omega

/-- **Exact-consumption soundness of the runtime driver** for EOF-anchored
grammars: if the grammar is EOF-anchored (decidable via `isEofAnchored`) and the
lexer never emits the EOF terminal, then `parseList` returning `.ok v` means the
*entire* input was consumed, anchored at EOF — the recognised word is exactly
`toks ++ [eof]` — and `v` is the semantics of one of its parse trees. Without
the anchoring hypothesis, success only certifies that *some prefix* of the
padded stream was recognised (`Main.parse_correct`); this closes that gap. -/
theorem parseList_sound_anchored {E : Type}
    (init : A.InitState) (hsafe : Main.safeValidator () = true)
    (eof : A.Token) (toks : List A.Token)
    (onFail : A.State → A.Token → E) (onTimeout : E)
    (hanch : EofAnchored (A.token_term eof) (A.start_nt init))
    (hlex : ∀ tok ∈ toks, A.token_term tok ≠ A.token_term eof)
    {v : ResultType A init}
    (hok : parseList init hsafe eof toks onFail onTimeout = .ok v) :
    ∃ pt : ParseTree (.NT (A.start_nt init)) (toks ++ [eof]), ptSem pt = v := by
  unfold parseList at hok
  cases hp : Main.parse init hsafe (fuelFor toks.length) (Buf.ofListEof toks eof) with
  | Parsed v' rest =>
    rw [hp] at hok
    injection hok with hv
    subst hv
    exact Main.parse_correct_anchored init hsafe (fuelFor toks.length) toks eof hanch hlex hp
  | Fail st tok => rw [hp] at hok; exact absurd hok (by simp)
  | Timeout => rw [hp] at hok; exact absurd hok (by simp)

end LeanMenhir.Runtime
