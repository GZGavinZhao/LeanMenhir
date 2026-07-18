# LeanMenhir

A formally verified LR(1) parser **interpreter + validator** for Lean 4,
ported from [`coq-menhirlib`](https://gitlab.inria.fr/fpottier/menhir) (the
verified parser library Menhir emits for Coq/CompCert), plus a self-contained,
**untrusted** native LR(1)/SLR(1) table generator.

## The key idea

The LR table *generator* is **untrusted**. Separate **verified validators**
(`isSafe` for soundness, `isComplete` for completeness) check that generated
tables are consistent with a grammar, and a **verified interpreter** runs
validated tables. Soundness, completeness, and unambiguity all hold whenever
the validators accept — regardless of bugs in the generator — so nobody has to
verify the large, fiddly LR table-construction algorithm itself.

## Guarantees

All stated and axiom-guarded in `LeanMenhir/Guarantees.lean` (see
`docs/AUDIT.md` for the full reviewer's guide):

* **Soundness** (`parser_sound`) — if `parse` returns `Parsed`, the consumed
  input really is a word of the language, and the returned value is the
  semantics of a real derivation.
* **Completeness** (`parser_complete`, `parser_accepts`,
  `parser_never_rejects_valid`) — every derivation of the grammar is found by
  the parser (given enough fuel), and a word of the language is never
  rejected.
* **Unambiguity** (`grammar_unambiguous`) — any two derivations of the same
  word have the same semantic value.
* **Exact consumption / EOF anchoring** (`parser_consumes_exactly`) — for an
  EOF-anchored grammar and an EOF-free lexer, acceptance means the *whole*
  input was parsed, nothing else.
* `runtime_sound` / `runtime_complete` / `runtime_consumes_exactly` transfer
  all of the above to the executable driver `Runtime.parseList`.

Every one of these theorems is followed by a `#guard_msgs`-checked
`#print axioms` call, so a `sorry` or a stray axiom is a build failure, not a
silent regression.

## Directory layout

```
LeanMenhir/
  Spec/          grammar/language/input definitions
    Alphabet.lean    Alphabet / Enumerable typeclasses (core `Ord` + `Std.TransOrd`/`Std.LawfulEqOrd`)
    Grammar.lean     symbols, the Grammar interface, dependently-typed ParseTree
    Language.lean    Derives / `word ∈ language nt` (existence of a derivation)
    Buffer.lean      O(1) head/tail token buffer and its denotation `get`
  Machine/       the LR automaton and interpreter
    Automaton.lean   the LR automaton table interface (states, actions, tables)
    Interpreter.lean pop / reduceStep / step / parse (fuel-based), no `sorry`
  Correctness/   the ported/extended proofs
    Classes.lean     validator boolean/Prop plumbing
    Safe.lean        safety validator `isSafe` + soundness lemma
    Complete.lean    completeness validator `isComplete` + soundness lemma
    Sound.lean       soundness proof of the interpreter
    CompleteProof.lean completeness proof of the interpreter
    Congr.lean       interpreter extensionality in the input buffer
    Anchored.lean    EOF-anchoring and exact-consumption
  Generator/     the untrusted native LR(1)/SLR(1) generator
    FinAlphabet.lean Alphabet instances for Fin n (generator index types)
    Tables.lean      bridge from untrusted GenTables to a genuine Automaton
    Grammar0.lean    the human-written grammar and its definitional Grammar
    Derives0.lean    the textbook Grammar0.Derives spec + transport theorem
    LR1.lean         canonical LR(1) / SLR(1) table construction
    BuildTables.lean the `build_tables%` elaborator (builds tables at elab time)
    BTree.lean       balanced BST for kernel-reducible O(log n) table lookups
  Examples/      end-to-end example grammars (see below)
  Main.lean      user-facing entry points: `parse`, `parse_correct`,
                 `parse_complete`, `unambiguity`
  Runtime.lean   grammar-agnostic executable driver: pads a token list into a
                 buffer, runs `Main.parse`, maps the result into `Except`
  Guarantees.lean  the review surface: every end-to-end theorem restated with
                   an informal reading, its caveats, and an axiom guard
```

## Building

```
lake build
```

Toolchain: `leanprover/lean4:v4.31.0` (see `lean-toolchain`).

## Examples

`LeanMenhir/Examples/` contains five end-to-end grammars, each generating its
own tables, certifying them with the validators, and running the verified
interpreter:

| Example | Grammar | Tables | Certificate |
|---|---|---|---|
| `Arith.lean` | left-recursive `E → E + num \| num` (gets PEG/recursive-descent backends wrong) | `buildTablesSLR`, fully in-Lean (`partial def`, not kernel-reducible) | `native_decide` (trusts the compiler) |
| `MiniCalc.lean` | full arithmetic with precedence, associativity, parens, a lexer, and an AST printer (ported from `coq-menhirlib`'s `rocq-minicalc` demo) | SLR(1), 18 states (vs. 33 for canonical LR(1)), emitted as a concrete literal via `Gen.emitTables` | kernel `decide` — no compiler-trust axiom |
| `StmCalc.lean` | two genuinely distinct AST categories (`Exp`/`Stm`), demonstrating the heterogeneous semantic-value bridge | `build_tables%` elaborator (SLR(1), built at elaboration time) | kernel `rfl` (BTree-backed tables) |
| `CalcTemplate.lean` | precedence-by-coercion arithmetic with a position-tracking lexer and `line:col` error reporting — the emission template for a planned BNFC backend | `build_tables%` | kernel `rfl` |
| `ScaleTest.lean` | a 21-production selector grammar, a regression test for the dependent-action-dispatcher scaling wall (`O(log n)` BTree lookups, the `Fin`-literal exhaustiveness workaround) | `build_tables%` | kernel `rfl` |

`MiniCalc` additionally proves that its verified language is exactly the
textbook `Grammar0.Derives` relation on the grammar you wrote
(`mini_language_eq`), and that the grammar is EOF-anchored
(`minicalcAnchored`/`mini_consumes_all`).

## Dependencies

Core Lean 4 and `Std` only — no Mathlib.

## Trust and axioms

The end-to-end guarantees depend on at most Lean's three standard axioms,
`propext`, `Classical.choice`, and `Quot.sound` — no `sorry`, no custom axioms.
Every theorem in `Guarantees.lean` carries a `#guard_msgs`-checked
`#print axioms` call enforcing this at build time.

A grammar's *own* safety/completeness certificates can be discharged either way:

* kernel `decide`/`rfl` on concrete tables — the Lean kernel is the only
  trusted component (see `MiniCalc`, `StmCalc`, `CalcTemplate`, `ScaleTest`);
* `native_decide` on tables produced by a `partial def` generator — scales to
  larger grammars, but adds `Lean.ofReduceBool` (trust in the compiler) to that
  certificate's axiom list (see `Arith`).

## License

LGPL-3.0-or-later (derivative of `coq-menhirlib`, © Inria/CNRS).
