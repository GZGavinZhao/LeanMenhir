# How to audit LeanMenhir in 30 minutes

LeanMenhir is a Lean 4 port of `coq-menhirlib` (the verified LR(1) interpreter
behind Menhir's `--coq` backend) plus an in-Lean, *untrusted* table generator
certified by the ported validators. This guide tells you **exactly what you must
read to trust it, and what you may ignore**.

## The review path

Read these, in order. Everything not listed is proof plumbing or untrusted
tooling — a bug there can make a build fail, never make a theorem lie.

| # | File | What to check | Defines |
|---|------|----------------|---------|
| 1 | `LeanMenhir/Grammar.lean` | `Grammar`, `Symbol`, `ParseTree`, `ptSem`, `ptSize`. A `ParseTree (.NT n) w` is a derivation of the token word `w` from nonterminal `n`; `ptSem` folds the semantic actions over it. Note the RHS-reversed convention (`prod_rhs_rev`) and that a `ParseTreeList`'s word is the concatenation in *grammar* order. Then `LeanMenhir/Language.lean` (30 lines): the propositional form — `Derives nt w := Nonempty (ParseTree (.NT nt) w)` and `w ∈ language nt` — i.e. **membership in the language is the existence of a derivation**. | **"the language"** |
| 2 | `LeanMenhir/Buf.lean` | `Buf` with `head`/`tail`/`cons`/`appendList` and the denotation `get : Buf α → Nat → α`. All statements compare buffers by `get` (the token stream they denote). | **"the input"** |
| 3 | `LeanMenhir/Interpreter.lean` | The signature and body of `parse` (fuelled LR driver; reads the input only via `head`/`tail`), and `ParseResult` (`Parsed`/`Timeout`/`Fail`). For applications, also `Runtime.parseList` (pads a finite token list with an EOF filler, projects into `Except`). | **"what runs"** |
| 4 | `LeanMenhir/Guarantees.lean` | The nine end-to-end theorems, each with an informal reading, its caveats, and a build-enforced `#print axioms` guard. | **"what is guaranteed"** |

## The guarantees, informally

All are stated in `Guarantees.lean`; names below are the ones to `#check`.
Most guarantees come in **two faces**: a *recognition-level* face phrased with
`word ∈ language nt` (the sentence a reader expects), and a *semantic-level*
face phrased with an explicit derivation `tree : ParseTree …` — strictly
stronger, since it also pins the returned value (`ptSem tree`) and the fuel
(`ptSize tree`). The derivation argument **is** the membership hypothesis, in
proof-relevant form; the recognition faces are corollaries.

| Theorem | Reading |
|---|---|
| `parser_sound` / `parser_sound_mem` | accepted ⇒ the consumed prefix really derives from the start symbol (`∈ language`), and the returned value is that derivation's semantics |
| `parser_complete` | every derivation is found: parsing its word returns exactly its semantic value and the untouched continuation (given fuel ≥ tree size) |
| `parser_accepts` | **every word of the language is accepted** (membership hypothesis; fuel threshold existential, since membership hides the derivation's size) |
| `parser_never_rejects_valid` | a word of the language is never `Fail`ed, with any fuel |
| `grammar_unambiguous` | any two derivations of a word have equal **semantic value** (value-level; instantiate values with syntax trees for tree-level uniqueness) |
| `parser_consumes_exactly` | EOF-anchored grammar + EOF-free lexer ⇒ acceptance means **the whole input and nothing else** was parsed (`toks ++ [eof] ∈ language …`) |
| `runtime_sound` / `runtime_complete` / `runtime_consumes_exactly` | all of the above transferred to the *executed* driver `Runtime.parseList` (the parser cannot distinguish denotationally equal buffers — `parse_congr`) |
| `tables_grammar_faithful` | the grammar those theorems quantify over is exactly the `Grammar0` you wrote — production by production, no index clamping |

## The trusted base

1. **The Lean kernel** (and, only where an example explicitly opts in with
   `native_decide`, the Lean compiler — grep for `ofReduceBool` in `#print
   axioms` output to see who opted in).
2. **The definitions in files 1–3 above** (~700 lines). If `ParseTree`/`ptSem`
   say what you mean by "derivation" and `parse`/`parseList` are what you run,
   the theorems mean what they say.
3. **Your `Grammar0`** — reviewed by eye; tied to the generated tables by the
   kernel-checked `tablesMatchGrammar` certificate (leak-2).
4. **Your lexer's EOF discipline** — the hypothesis `hlex : ∀ tok ∈ toks,
   token_term tok ≠ token_term eof` of the exact-consumption theorems.

## Explicitly *not* trusted

- The LR(1)/SLR generator (`Generator/LR1.lean`, `BuildTables.lean`) and the
  emitted `GenTables` blobs — certified after the fact by the validators and the
  grammar cross-check.
- The boolean validator kernels (`isSafe`, `isComplete`, `tablesMatchGrammar`,
  `isEofAnchored`) — they only *produce* certificates; their soundness lemmas
  (`safe_is_validator`, …) are proved.
- All proof files (`Interpreter/Correct.lean`, `Interpreter/Complete.lean`,
  `Interpreter/Congr.lean`, `Validator/*`, `Anchored.lean`) — 2000+ lines you
  never need to open: the kernel checked them.

## Per-example certificate stories

| Example | Certificates | Trust |
|---|---|---|
| `MiniCalc` | `decide` (safety, completeness, grammar match, EOF anchoring) | kernel only |
| `CalcTemplate`, `StmCalc`, `ScaleTest` | `rfl` (BTree-backed tables) | kernel only |
| `Arith` | `native_decide` (`buildTablesSLR` is a `partial def`, not kernel-reducible) | kernel + compiler |

Value-level acceptance tests (e.g. `parseExpr "1+2*3" = some …`) use
`native_decide`/`#eval` everywhere — they are tests of the compiled artifact,
not part of the proof.

## Known caveats

- **Fuel**: `parse` is fuelled; completeness requires `ptSize tree ≤ 2 ^ fuel`.
  The runtime driver's `fuelFor` makes this vacuous for any physically
  constructible tree (`runtime_complete`'s bound is `2⁶⁴` nodes).
- **Unambiguity is value-level** (same as the Coq original).
- **`Timeout`** with the runtime fuel can effectively only be produced by a
  non-terminating table set, not by a valid-but-deep parse.
- The `Automaton`-bundles-`Grammar` presentation and the `… = true` certificate
  hypotheses are Coq heritage; the in-progress idiomatic refactor (see the
  "LeanMenhir Idiomatic Refactor" plan) replaces them with an explicit
  `(G : Grammar)` / `(A : Automaton G)` split and `Prop`-valued `Safe A` /
  `Complete A`.

## Checking axiom hygiene yourself

Every theorem in `Guarantees.lean` is followed by

```lean
/-- info: '…' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms …
```

so any regression (a `sorry`, a new axiom, an accidental `native_decide`) turns
into a compile error. `lake build` is the audit.
