/-
**Emission template** for the planned BNFC `--leanmenhir` backend.

This file is structured *exactly* as the backend will emit, so it doubles as the
spec for the Haskell emitter. It corresponds to this `.cf` fragment (a calculator
with precedence-by-coercion and parentheses):

    EAdd. Exp  ::= Exp "+" Exp1 ;
    ESub. Exp  ::= Exp "-" Exp1 ;
    _.    Exp  ::= Exp1 ;          -- coercion
    EMul. Exp1 ::= Exp1 "*" Exp2 ;
    _.    Exp1 ::= Exp2 ;          -- coercion
    EInt. Exp2 ::= Integer ;
    _.    Exp2 ::= "(" Exp ")" ;   -- coercion

The pieces a backend emits:
  1. `Position`/`TokenKind`/`LToken` — the lexer's output (in the real backend
     these come from BNFC's generated `ParserRuntime`/`Lex` modules; mocked here).
  2. `grammar : Grammar0` — numeric productions, a synthesized `eof`, and a fresh
     start production `Start → Exp EOF`. Precedence levels `Exp`/`Exp1`/`Exp2`
     become real nonterminals related by *identity* coercion actions (LR handles
     precedence via the grammar — no hand-rolled level loops).
  3. `tables := build_tables% grammar` — SLR(1) tables generated at elaboration
     time and certified by **kernel `decide`**.
  4. `ntType`/`termType`/`actions` — the heterogeneous semantic types and typed
     actions. `ntType` maps every `Exp`-level category to the AST type `Exp`; the
     coercion actions are `fun e => e`. No `Val`-union, no projection, no `Inhabited`.
  5. `automaton`, `adapt` (lexer token → grammar terminal), and a `parseString`
     driver returning `Except String Exp` with `line:col` errors — via the
     grammar-agnostic `LeanMenhir.Runtime`.

LGPL-3.0-or-later (derivative of coq-menhirlib).
-/
import LeanMenhir.Runtime
import LeanMenhir.Generator.BuildTables
import Mathlib.Data.Stream.Init

namespace LeanMenhir.Examples.CalcTemplate

open LeanMenhir LeanMenhir.Gen

/-! ### 1. Lexer output (stands in for BNFC's generated `ParserRuntime`) -/

structure Position where
  line : Nat := 1
  col : Nat := 1
deriving Repr, Inhabited

instance : ToString Position where toString p := s!"{p.line}:{p.col}"

inductive TokenKind
  | keyword : String → TokenKind
  | intLit : Int → TokenKind
deriving Repr, Inhabited

structure LToken where
  kind : TokenKind
  pos : Position
deriving Repr, Inhabited

/-! ### 2. Grammar

Terminals: PLUS=0 MINUS=1 TIMES=2 LPAREN=3 RPAREN=4 EOF=5 INT=6.
Nonterminals: Start=0 Exp=1 Exp1=2 Exp2=3. -/

def grammar : Grammar0 where
  numTerm := 7
  numNonterm := 4
  start := 0
  eof := 5
  prods := #[
    (0, #[.nonterm 1, .term 5]),                 -- Start → Exp EOF
    (1, #[.nonterm 1, .term 0, .nonterm 2]),     -- Exp → Exp "+" Exp1      (EAdd)
    (1, #[.nonterm 1, .term 1, .nonterm 2]),     -- Exp → Exp "-" Exp1      (ESub)
    (1, #[.nonterm 2]),                          -- Exp → Exp1              (coercion)
    (2, #[.nonterm 2, .term 2, .nonterm 3]),     -- Exp1 → Exp1 "*" Exp2    (EMul)
    (2, #[.nonterm 3]),                          -- Exp1 → Exp2             (coercion)
    (3, #[.term 6]),                             -- Exp2 → Integer          (EInt)
    (3, #[.term 3, .nonterm 1, .term 4])         -- Exp2 → "(" Exp ")"      (coercion)
  ]

/-! ### 3. Tables (strategy C: generated at elaboration time, kernel-`decide`-certified) -/

def tables : GenTables := build_tables% grammar

/-! ### 4. AST + heterogeneous semantic types + typed actions -/

inductive Exp
  | int : Int → Exp
  | add : Exp → Exp → Exp
  | sub : Exp → Exp → Exp
  | mul : Exp → Exp → Exp
deriving Repr, DecidableEq

/-- Every `Exp`-level category carries the AST type `Exp`; the dummy nonterminal
carries `Unit`. -/
def ntType : Fin (tables.numNonterm + 1) → Type
  | 4 => Unit
  | _ => Exp

/-- `Integer`=6 carries an `Int`; all keywords/punctuation/EOF carry `Unit`. -/
def termType : Fin (tables.numTerm + 1) → Type
  | 6 => Int
  | _ => Unit

/-- Typed semantic actions (arguments in reverse-RHS order). Coercions are
identities; `EInt` consumes an `Int` and builds an `Exp`.

The final `⟨_ + (numProd+1), h⟩` arm is an *exhaustiveness shim*: Lean's equation
compiler only proves a `Fin n` numeric-literal match complete (ruling out
`val ≥ n` via the `isLt` bound) for small `n`; past ~15 arms it reports the
out-of-range index as a "missing case". `elimOutOfRange` discharges that
impossible arm. BNFC's emitter appends this arm to every generated dispatcher. -/
def actions : (p : Fin (tables.numProd + 1)) →
    arrowsRight (symTypeOf tables ntType termType (.NT (prodLhsOf tables p)))
                ((prodRhsRevOf tables p).map (symTypeOf tables ntType termType))
  | 0 => fun (_ : Unit) (e : Exp) => e                            -- Start → Exp EOF
  | 1 => fun (r : Exp) (_ : Unit) (l : Exp) => Exp.add l r        -- EAdd
  | 2 => fun (r : Exp) (_ : Unit) (l : Exp) => Exp.sub l r        -- ESub
  | 3 => fun (e : Exp) => e                                       -- coercion
  | 4 => fun (r : Exp) (_ : Unit) (l : Exp) => Exp.mul l r        -- EMul
  | 5 => fun (e : Exp) => e                                       -- coercion
  | 6 => fun (n : Int) => Exp.int n                               -- EInt
  | 7 => fun (_ : Unit) (e : Exp) (_ : Unit) => e                 -- "(" Exp ")"
  | 8 => ()                                                       -- dummy production
  | ⟨_ + 9, h⟩ => elimOutOfRange h                                -- impossible (numProd+1 = 9)

/-! ### 5. Automaton, certificates, and the parse driver -/

/-- The verified automaton; tokens carry a `Position` for error reporting. -/
instance automaton : Automaton := automatonOfTablesTyped tables ntType termType Position actions

/-- Safety — kernel `decide` (no compiler-trust axiom). -/
theorem calcSafe : Main.safeValidator (A := automaton) () = true := by decide

/-- Completeness — kernel `decide`. -/
theorem calcComplete : Main.completeValidator (A := automaton) () = true := by decide

/-- The automaton's token type: `Position × Σ t, termType t`. -/
abbrev Tok : Type := automaton.Token

/-- Map a lexer token to a grammar terminal (attaching its position), or fail. -/
def adapt : LToken → Except String Tok
  | { kind := .intLit n, pos } => .ok (pos, ⟨6, n⟩)
  | { kind := .keyword "+", pos } => .ok (pos, ⟨0, ()⟩)
  | { kind := .keyword "-", pos } => .ok (pos, ⟨1, ()⟩)
  | { kind := .keyword "*", pos } => .ok (pos, ⟨2, ()⟩)
  | { kind := .keyword "(", pos } => .ok (pos, ⟨3, ()⟩)
  | { kind := .keyword ")", pos } => .ok (pos, ⟨4, ()⟩)
  | { kind := k, pos := pos } => .error s!"{pos}: unexpected token {repr k}"

/-- The EOF filler token at a given source position. -/
def eofAt (p : Position) : Tok := (p, ⟨5, ()⟩)

/-! A tiny lexer (mocking BNFC's `CFtoLeanLex` output): digits → `Integer`,
operators/parens → keywords, whitespace skipped, anything else is a lexical
error. Tracks `line`/`col` and returns the end position for the EOF token. -/

partial def lexAux : List Char → Position → List LToken → Except String (List LToken × Position)
  | [], p, acc => .ok (acc.reverse, p)
  | c :: rest, p, acc =>
    if c == ' ' || c == '\t' || c == '\r' then lexAux rest { p with col := p.col + 1 } acc
    else if c == '\n' then lexAux rest { line := p.line + 1, col := 1 } acc
    else if c.isDigit then
      let digs := (c :: rest).takeWhile Char.isDigit
      let n : Int := Int.ofNat (digs.foldl (fun a d => a * 10 + (d.toNat - 48)) 0)
      lexAux ((c :: rest).dropWhile Char.isDigit) { p with col := p.col + digs.length }
        ({ kind := .intLit n, pos := p } :: acc)
    else
      let kw (s : String) :=
        lexAux rest { p with col := p.col + 1 } ({ kind := .keyword s, pos := p } :: acc)
      match c with
      | '+' => kw "+"
      | '-' => kw "-"
      | '*' => kw "*"
      | '(' => kw "("
      | ')' => kw ")"
      | _   => .error s!"{p}: lexical error at '{c}'"

/-- Parse a string into an `Exp` (or a `line:col:` error). This is the analogue of
BNFC's generated `parseProgram`. -/
def parseString (s : String) : Except String Exp := do
  let (toks, endPos) ← lexAux s.toList {} []
  Runtime.parseWith (A := automaton) (0 : Fin 1) calcSafe (eofAt endPos) adapt
    (fun _ tok => s!"{(tok.1 : Position)}: syntax error") "input too large" toks

/-! ### Acceptance tests (run the compiled parser) -/

-- `*` binds tighter than `+`.
example : parseString "1+2*3" = .ok (.add (.int 1) (.mul (.int 2) (.int 3))) := by native_decide
-- Parentheses regroup.
example : parseString "(1+2)*3" = .ok (.mul (.add (.int 1) (.int 2)) (.int 3)) := by native_decide
-- `-` is left-associative.
example : parseString "1 - 2 - 3" = .ok (.sub (.sub (.int 1) (.int 2)) (.int 3)) := by native_decide
-- A syntax error is reported (with a position).
example : (parseString "1 +").toOption = none := by native_decide
-- A lexical error is reported.
example : (parseString "1 @ 2").toOption = none := by native_decide

end LeanMenhir.Examples.CalcTemplate
