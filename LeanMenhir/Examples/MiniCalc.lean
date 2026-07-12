/-
End-to-end MiniCalc example (ported from `refs/menhir/demos/rocq-minicalc`).

A real arithmetic grammar with precedence, associativity, and parentheses:

    parse_expr : p_expr EOF
    p_expr   : p_factor | p_expr ADD p_factor | p_expr SUB p_factor
    p_factor : p_atom   | p_factor MUL p_atom | p_factor DIV p_atom
    p_atom   : ID | NUM | LPAREN p_expr RPAREN

The LR(1) tables below were produced by our *untrusted* generator
(`Grammar0.buildTables`, emitted via `Gen.emitTables`) and are certified here by
the verified safety validator using **kernel `decide`** — so the certificate
carries no compiler-trust axiom (`Lean.ofReduceBool`), only the kernel.

LGPL-3.0-or-later (derivative of coq-menhirlib).
-/
import LeanMenhir.Generator.LR1

namespace LeanMenhir.Examples.MiniCalc

open LeanMenhir LeanMenhir.Gen LeanMenhir.Buf

/-- The AST (`MiniCalc.v`, `Ast.expr`). Used as the monomorphic semantic value. -/
inductive Expr where
  | num : Nat → Expr
  | var : String → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | div : Expr → Expr → Expr
deriving DecidableEq, Repr, Inhabited, BEq

/-- The source grammar (terminals ADD0 SUB1 MUL2 DIV3 LPAREN4 RPAREN5 EOF6 NUM7
ID8; nonterminals parse_expr0 p_expr1 p_factor2 p_atom3). The `miniTables` below
are `grammar.buildTablesSLR` (the SLR(1) generator — 18 states, vs 33 for
canonical LR(1)) emitted via `Gen.emitTables`; regenerate with:
`#eval IO.println (Gen.emitTables "miniTables" grammar.buildTablesSLR)`. -/
def grammar : Grammar0 where
  numTerm := 9
  numNonterm := 4
  start := 0
  eof := 6
  prods := #[
    (0, #[.nonterm 1, .term 6]),                 -- parse_expr → p_expr EOF
    (1, #[.nonterm 2]),                          -- p_expr → p_factor
    (1, #[.nonterm 1, .term 0, .nonterm 2]),     -- p_expr → p_expr ADD p_factor
    (1, #[.nonterm 1, .term 1, .nonterm 2]),     -- p_expr → p_expr SUB p_factor
    (2, #[.nonterm 3]),                          -- p_factor → p_atom
    (2, #[.nonterm 2, .term 2, .nonterm 3]),     -- p_factor → p_factor MUL p_atom
    (2, #[.nonterm 2, .term 3, .nonterm 3]),     -- p_factor → p_factor DIV p_atom
    (3, #[.term 8]),                             -- p_atom → ID
    (3, #[.term 7]),                             -- p_atom → NUM
    (3, #[.term 4, .nonterm 1, .term 5])         -- p_atom → LPAREN p_expr RPAREN
  ]

/-- Terminals: ADD=0 SUB=1 MUL=2 DIV=3 LPAREN=4 RPAREN=5 EOF=6 NUM=7 ID=8.
Nonterminals: parse_expr=0 p_expr=1 p_factor=2 p_atom=3. (Generated, untrusted.) -/
def miniTables : Gen.GenTables :=
  {
    numTerm := 9
    numNonterm := 4
    numProd := 10
    numStates := 18
    startNonterm := 0
    prodLhs := #[0, 1, 1, 1, 2, 2, 2, 3, 3, 3]
    prodRhsRev := #[#[.term 6, .nonterm 1], #[.nonterm 2], #[.nonterm 2, .term 0, .nonterm 1], #[.nonterm 2, .term 1, .nonterm 1], #[.nonterm 3], #[.nonterm 3, .term 2, .nonterm 2], #[.nonterm 3, .term 3, .nonterm 2], #[.term 8], #[.term 7], #[.term 5, .nonterm 1, .term 4]]
    incoming := #[none, (some (.nonterm 1)), (some (.nonterm 3)), (some (.nonterm 2)), (some (.term 8)), (some (.term 7)), (some (.term 4)), (some (.nonterm 1)), (some (.term 1)), (some (.term 0)), (some (.term 5)), (some (.nonterm 2)), (some (.term 3)), (some (.term 2)), (some (.nonterm 3)), (some (.nonterm 3)), (some (.nonterm 2)), (some (.term 6))]
    action := #[(.lookahead #[.fail, .fail, .fail, .fail, .shift 6, .fail, .fail, .shift 5, .shift 4]), (.lookahead #[.shift 9, .shift 8, .fail, .fail, .fail, .fail, .shift 17, .fail, .fail]), .defaultReduce 4, (.lookahead #[.reduce 1, .reduce 1, .shift 13, .shift 12, .fail, .reduce 1, .reduce 1, .fail, .fail]), .defaultReduce 7, .defaultReduce 8, (.lookahead #[.fail, .fail, .fail, .fail, .shift 6, .fail, .fail, .shift 5, .shift 4]), (.lookahead #[.shift 9, .shift 8, .fail, .fail, .fail, .shift 10, .fail, .fail, .fail]), (.lookahead #[.fail, .fail, .fail, .fail, .shift 6, .fail, .fail, .shift 5, .shift 4]), (.lookahead #[.fail, .fail, .fail, .fail, .shift 6, .fail, .fail, .shift 5, .shift 4]), .defaultReduce 9, (.lookahead #[.reduce 2, .reduce 2, .shift 13, .shift 12, .fail, .reduce 2, .reduce 2, .fail, .fail]), (.lookahead #[.fail, .fail, .fail, .fail, .shift 6, .fail, .fail, .shift 5, .shift 4]), (.lookahead #[.fail, .fail, .fail, .fail, .shift 6, .fail, .fail, .shift 5, .shift 4]), .defaultReduce 5, .defaultReduce 6, (.lookahead #[.reduce 3, .reduce 3, .shift 13, .shift 12, .fail, .reduce 3, .reduce 3, .fail, .fail]), .defaultReduce 0]
    goto := #[#[none, (some 1), (some 3), (some 2)], #[none, none, none, none], #[none, none, none, none], #[none, none, none, none], #[none, none, none, none], #[none, none, none, none], #[none, (some 7), (some 3), (some 2)], #[none, none, none, none], #[none, none, (some 16), (some 2)], #[none, none, (some 11), (some 2)], #[none, none, none, none], #[none, none, none, none], #[none, none, none, (some 15)], #[none, none, none, (some 14)], #[none, none, none, none], #[none, none, none, none], #[none, none, none, none], #[none, none, none, none]]
    pastSymb := #[#[], #[], #[], #[], #[], #[], #[], #[.term 4], #[.nonterm 1], #[.nonterm 1], #[.nonterm 1, .term 4], #[.term 0, .nonterm 1], #[.nonterm 2], #[.nonterm 2], #[.term 2, .nonterm 2], #[.term 3, .nonterm 2], #[.term 1, .nonterm 1], #[.nonterm 1]]
    pastStateSets := #[#[], #[#[0]], #[#[6, 9, 8, 0]], #[#[6, 0]], #[#[6, 9, 13, 12, 8, 0]], #[#[6, 9, 13, 12, 8, 0]], #[#[6, 9, 13, 12, 8, 0]], #[#[6], #[6, 9, 13, 12, 8, 0]], #[#[7, 1], #[6, 0]], #[#[7, 1], #[6, 0]], #[#[7], #[6], #[6, 9, 13, 12, 8, 0]], #[#[9], #[7, 1], #[6, 0]], #[#[11, 16, 3], #[9, 8, 6, 0]], #[#[11, 16, 3], #[9, 8, 6, 0]], #[#[13], #[11, 16, 3], #[9, 8, 6, 0]], #[#[12], #[11, 16, 3], #[9, 8, 6, 0]], #[#[8], #[7, 1], #[6, 0]], #[#[1], #[0]]]
    nullable := #[false, false, false, false]
    first := #[#[8, 7, 4], #[4, 7, 8], #[8, 7, 4], #[4, 7, 8]]
    items := #[#[(9, 0, 5), (9, 0, 3), (9, 0, 2), (9, 0, 6), (9, 0, 0), (9, 0, 1), (8, 0, 5), (8, 0, 3), (8, 0, 2), (8, 0, 6), (8, 0, 0), (8, 0, 1), (7, 0, 5), (7, 0, 3), (7, 0, 2), (7, 0, 6), (7, 0, 0), (7, 0, 1), (6, 0, 5), (6, 0, 3), (6, 0, 2), (6, 0, 1), (6, 0, 0), (6, 0, 6), (5, 0, 5), (5, 0, 3), (5, 0, 2), (5, 0, 1), (5, 0, 0), (5, 0, 6), (4, 0, 5), (4, 0, 3), (4, 0, 2), (4, 0, 1), (4, 0, 0), (4, 0, 6), (3, 0, 5), (3, 0, 1), (3, 0, 0), (3, 0, 6), (2, 0, 5), (2, 0, 1), (2, 0, 0), (2, 0, 6), (1, 0, 5), (1, 0, 1), (1, 0, 0), (1, 0, 6), (0, 0, 0), (0, 0, 1), (0, 0, 2), (0, 0, 3), (0, 0, 4), (0, 0, 5), (0, 0, 6), (0, 0, 7), (0, 0, 8), (0, 0, 9)], #[(0, 1, 0), (0, 1, 1), (0, 1, 2), (0, 1, 3), (0, 1, 4), (0, 1, 5), (0, 1, 6), (0, 1, 7), (0, 1, 8), (0, 1, 9), (2, 1, 5), (2, 1, 1), (2, 1, 0), (2, 1, 6), (3, 1, 5), (3, 1, 1), (3, 1, 0), (3, 1, 6)], #[(4, 1, 5), (4, 1, 3), (4, 1, 2), (4, 1, 1), (4, 1, 0), (4, 1, 6)], #[(1, 1, 5), (1, 1, 1), (1, 1, 0), (1, 1, 6), (5, 1, 5), (5, 1, 3), (5, 1, 2), (5, 1, 1), (5, 1, 0), (5, 1, 6), (6, 1, 5), (6, 1, 3), (6, 1, 2), (6, 1, 1), (6, 1, 0), (6, 1, 6)], #[(7, 1, 5), (7, 1, 3), (7, 1, 2), (7, 1, 6), (7, 1, 0), (7, 1, 1)], #[(8, 1, 5), (8, 1, 3), (8, 1, 2), (8, 1, 6), (8, 1, 0), (8, 1, 1)], #[(9, 0, 5), (9, 0, 3), (9, 0, 2), (9, 0, 6), (9, 0, 0), (9, 0, 1), (8, 0, 5), (8, 0, 3), (8, 0, 2), (8, 0, 6), (8, 0, 0), (8, 0, 1), (7, 0, 5), (7, 0, 3), (7, 0, 2), (7, 0, 6), (7, 0, 0), (7, 0, 1), (6, 0, 5), (6, 0, 3), (6, 0, 2), (6, 0, 1), (6, 0, 0), (6, 0, 6), (5, 0, 5), (5, 0, 3), (5, 0, 2), (5, 0, 1), (5, 0, 0), (5, 0, 6), (4, 0, 5), (4, 0, 3), (4, 0, 2), (4, 0, 1), (4, 0, 0), (4, 0, 6), (3, 0, 5), (3, 0, 1), (3, 0, 0), (3, 0, 6), (2, 0, 5), (2, 0, 1), (2, 0, 0), (2, 0, 6), (1, 0, 5), (1, 0, 1), (1, 0, 0), (1, 0, 6), (9, 1, 5), (9, 1, 3), (9, 1, 2), (9, 1, 6), (9, 1, 0), (9, 1, 1)], #[(9, 2, 5), (9, 2, 3), (9, 2, 2), (9, 2, 6), (9, 2, 0), (9, 2, 1), (2, 1, 5), (2, 1, 1), (2, 1, 0), (2, 1, 6), (3, 1, 5), (3, 1, 1), (3, 1, 0), (3, 1, 6)], #[(9, 0, 5), (9, 0, 3), (9, 0, 2), (9, 0, 6), (9, 0, 0), (9, 0, 1), (8, 0, 5), (8, 0, 3), (8, 0, 2), (8, 0, 6), (8, 0, 0), (8, 0, 1), (7, 0, 5), (7, 0, 3), (7, 0, 2), (7, 0, 6), (7, 0, 0), (7, 0, 1), (6, 0, 5), (6, 0, 3), (6, 0, 2), (6, 0, 1), (6, 0, 0), (6, 0, 6), (5, 0, 5), (5, 0, 3), (5, 0, 2), (5, 0, 1), (5, 0, 0), (5, 0, 6), (4, 0, 5), (4, 0, 3), (4, 0, 2), (4, 0, 1), (4, 0, 0), (4, 0, 6), (3, 2, 5), (3, 2, 1), (3, 2, 0), (3, 2, 6)], #[(9, 0, 5), (9, 0, 3), (9, 0, 2), (9, 0, 6), (9, 0, 0), (9, 0, 1), (8, 0, 5), (8, 0, 3), (8, 0, 2), (8, 0, 6), (8, 0, 0), (8, 0, 1), (7, 0, 5), (7, 0, 3), (7, 0, 2), (7, 0, 6), (7, 0, 0), (7, 0, 1), (6, 0, 5), (6, 0, 3), (6, 0, 2), (6, 0, 1), (6, 0, 0), (6, 0, 6), (5, 0, 5), (5, 0, 3), (5, 0, 2), (5, 0, 1), (5, 0, 0), (5, 0, 6), (4, 0, 5), (4, 0, 3), (4, 0, 2), (4, 0, 1), (4, 0, 0), (4, 0, 6), (2, 2, 5), (2, 2, 1), (2, 2, 0), (2, 2, 6)], #[(9, 3, 5), (9, 3, 3), (9, 3, 2), (9, 3, 6), (9, 3, 0), (9, 3, 1)], #[(2, 3, 5), (2, 3, 1), (2, 3, 0), (2, 3, 6), (5, 1, 5), (5, 1, 3), (5, 1, 2), (5, 1, 1), (5, 1, 0), (5, 1, 6), (6, 1, 5), (6, 1, 3), (6, 1, 2), (6, 1, 1), (6, 1, 0), (6, 1, 6)], #[(9, 0, 5), (9, 0, 3), (9, 0, 2), (9, 0, 6), (9, 0, 0), (9, 0, 1), (8, 0, 5), (8, 0, 3), (8, 0, 2), (8, 0, 6), (8, 0, 0), (8, 0, 1), (7, 0, 5), (7, 0, 3), (7, 0, 2), (7, 0, 6), (7, 0, 0), (7, 0, 1), (6, 2, 5), (6, 2, 3), (6, 2, 2), (6, 2, 1), (6, 2, 0), (6, 2, 6)], #[(9, 0, 5), (9, 0, 3), (9, 0, 2), (9, 0, 6), (9, 0, 0), (9, 0, 1), (8, 0, 5), (8, 0, 3), (8, 0, 2), (8, 0, 6), (8, 0, 0), (8, 0, 1), (7, 0, 5), (7, 0, 3), (7, 0, 2), (7, 0, 6), (7, 0, 0), (7, 0, 1), (5, 2, 5), (5, 2, 3), (5, 2, 2), (5, 2, 1), (5, 2, 0), (5, 2, 6)], #[(5, 3, 5), (5, 3, 3), (5, 3, 2), (5, 3, 1), (5, 3, 0), (5, 3, 6)], #[(6, 3, 5), (6, 3, 3), (6, 3, 2), (6, 3, 1), (6, 3, 0), (6, 3, 6)], #[(3, 3, 5), (3, 3, 1), (3, 3, 0), (3, 3, 6), (5, 1, 5), (5, 1, 3), (5, 1, 2), (5, 1, 1), (5, 1, 0), (5, 1, 6), (6, 1, 5), (6, 1, 3), (6, 1, 2), (6, 1, 1), (6, 1, 0), (6, 1, 6)], #[(0, 2, 0), (0, 2, 1), (0, 2, 2), (0, 2, 3), (0, 2, 4), (0, 2, 5), (0, 2, 6), (0, 2, 7), (0, 2, 8), (0, 2, 9)]]
  }

/-- Semantic actions (`collectArrows` supplies popped values in reverse-RHS
order: last symbol = index 0). -/
def actions : Nat → List Expr → Expr
  | 0, l => l.getD 1 (.num 0)                                -- parse_expr → p_expr EOF
  | 1, l => l.getD 0 (.num 0)                                -- p_expr → p_factor
  | 2, l => .add (l.getD 2 (.num 0)) (l.getD 0 (.num 0))     -- p_expr → p_expr + p_factor
  | 3, l => .sub (l.getD 2 (.num 0)) (l.getD 0 (.num 0))     -- p_expr → p_expr - p_factor
  | 4, l => l.getD 0 (.num 0)                                -- p_factor → p_atom
  | 5, l => .mul (l.getD 2 (.num 0)) (l.getD 0 (.num 0))     -- p_factor → p_factor * p_atom
  | 6, l => .div (l.getD 2 (.num 0)) (l.getD 0 (.num 0))     -- p_factor → p_factor / p_atom
  | 7, l => l.getD 0 (.num 0)                                -- p_atom → ID
  | 8, l => l.getD 0 (.num 0)                                -- p_atom → NUM
  | 9, l => l.getD 1 (.num 0)                                -- p_atom → ( p_expr )
  | _, _ => .num 0

/-- The verified automaton built from the generated tables. -/
instance automaton : Automaton := automatonOfTables miniTables Expr actions

/-- The generated tables are safe — certified by **kernel `decide`** (the only
trusted component is the Lean kernel; no `native_decide`/compiler-trust axiom). -/
theorem minicalcSafe : Main.safeValidator (A := automaton) () = true := by decide

/-! ### Lexer + end-to-end parsing -/

/-- A very small lexer: digits → `NUM`, letters → `ID`, and the operator/paren
characters; whitespace is skipped, anything else fails. Token values carry the
semantic `Expr` leaf (`Ast` value) for `NUM`/`ID`. -/
partial def lexAux : List Char → Option (List (Fin 10 × Expr))
  | [] => some []
  | c :: rest =>
    if c == ' ' || c == '\t' || c == '\n' then lexAux rest
    else if c.isDigit then
      let digs := (c :: rest).takeWhile Char.isDigit
      let n := digs.foldl (fun acc d => acc * 10 + (d.toNat - 48)) 0
      (lexAux ((c :: rest).dropWhile Char.isDigit)).map (((7 : Fin 10), Expr.num n) :: ·)
    else if c.isAlpha then
      let ids := (c :: rest).takeWhile Char.isAlpha
      (lexAux ((c :: rest).dropWhile Char.isAlpha)).map (((8 : Fin 10), Expr.var (String.ofList ids)) :: ·)
    else
      let single (i : Fin 10) := (lexAux rest).map (((i, Expr.num 0)) :: ·)
      match c with
      | '+' => single 0
      | '-' => single 1
      | '*' => single 2
      | '/' => single 3
      | '(' => single 4
      | ')' => single 5
      | _ => none

/-- Lex a string into a token buffer ending in an infinite `EOF` filler. -/
def lexString (s : String) : Option (Buffer (A := automaton)) :=
  (lexAux s.toList).map (fun toks => Buf.ofListEof toks ((6 : Fin 10), Expr.num 0))

/-- Parse a string into an `Expr` (`MiniCalc.v`, `string2expr`). -/
def parseExpr (s : String) : Option Expr :=
  match lexString s with
  | none => none
  | some buf =>
    match Main.parse (A := automaton) (0 : Fin 1) minicalcSafe 50 buf with
    | .Parsed e _ => some e
    | _ => none

/-- Re-linearize an expression (`MiniCalc.v`, `Print.pr_expr`). -/
def prExpr : Expr → String
  | .num n => toString n
  | .var x => x
  | .add a b => "(" ++ prExpr a ++ "+" ++ prExpr b ++ ")"
  | .sub a b => "(" ++ prExpr a ++ "-" ++ prExpr b ++ ")"
  | .mul a b => "(" ++ prExpr a ++ "*" ++ prExpr b ++ ")"
  | .div a b => "(" ++ prExpr a ++ "/" ++ prExpr b ++ ")"

/-! ### Acceptance tests

The safety certificate above (`minicalcSafe`) and soundness (`parse_correct`) are
kernel-checked. The value tests below run the *compiled* parser (via
`native_decide`/`#eval`) — the right tool for "does it compute the expected AST",
and how the parser is actually used. A clean build means each assertion holds. -/

-- Precedence: `*` binds tighter than `+`.
example : parseExpr "1+2*3" = some (.add (.num 1) (.mul (.num 2) (.num 3))) := by native_decide
-- Parentheses override precedence.
example : parseExpr "(1+2)*3" = some (.mul (.add (.num 1) (.num 2)) (.num 3)) := by native_decide
-- `-` is left-associative (LR handles left recursion).
example : parseExpr "1-2-3" = some (.sub (.sub (.num 1) (.num 2)) (.num 3)) := by native_decide
-- The Coq demo's example.
example : parseExpr "12 + 34*x / (48+y)"
    = some (.add (.num 12) (.div (.mul (.num 34) (.var "x")) (.add (.num 48) (.var "y")))) := by
  native_decide
-- Round-trip against the Coq demo's expected re-print.
example : (parseExpr "12 + 34*x / (48+y)").map prExpr = some "(12+((34*x)/(48+y)))" := by native_decide
-- Ill-formed inputs are rejected.
example : parseExpr "1+" = none := by native_decide
example : parseExpr "(1+2" = none := by native_decide

/- **Soundness** for this generated parser is the verified, kernel-checked
`Main.parse_correct (A := automaton) (0 : Fin 1) minicalcSafe` : whenever
`Main.parse` returns `Parsed sem _`, `sem` is the semantics of a real parse tree
of the consumed input. (We don't instantiate it inline: unfolding the large
kernel-`decide` proof `minicalcSafe` during elaboration is needlessly slow; the
generic theorem already applies.) -/

/-! ### Completeness and unambiguity

The completeness validator also accepts these tables. Combined with the verified
`Main.parse_complete`/`Main.unambiguity`, this certifies that the generated
parser recognises *every* parse tree of the MiniCalc grammar and that the grammar
is unambiguous (any two trees of a word have the same AST). -/

/-- The **completeness** validator accepts the generated tables — certified by
**kernel `decide`** (no `native_decide`/compiler-trust axiom). -/
theorem minicalcComplete : Main.completeValidator (A := automaton) () = true := by decide

/-- Every parse `tree`, given enough fuel, is parsed to its own AST, consuming
exactly `word`. -/
theorem mini_parses (logNSteps : Nat) (word : List automaton.Token)
    (bufEnd : Buffer (A := automaton))
    (tree : ParseTree (.NT (automaton.start_nt (0 : Fin 1))) word)
    (hfuel : ptSize tree ≤ 2 ^ logNSteps) :
    Main.parse (A := automaton) (0 : Fin 1) minicalcSafe logNSteps (word ++ₛ bufEnd)
      = .Parsed (ptSem tree) bufEnd := by
  have H := Main.parse_complete (A := automaton) (0 : Fin 1) minicalcSafe minicalcComplete
    logNSteps word bufEnd tree
  cases hp : Main.parse (A := automaton) (0 : Fin 1) minicalcSafe logNSteps (word ++ₛ bufEnd) with
  | Parsed sem buff => rw [hp] at H; obtain ⟨h1, h2, _⟩ := H; rw [h1, h2]
  | Timeout => rw [hp] at H; omega
  | Fail s t => rw [hp] at H; exact H.elim

/-- **Unambiguity**: any two parse trees of the same word have equal AST. -/
theorem mini_unambiguous (word : List automaton.Token)
    (tree1 tree2 : ParseTree (.NT (automaton.start_nt (0 : Fin 1))) word) :
    ptSem tree1 = ptSem tree2 :=
  Main.unambiguity (A := automaton) minicalcSafe minicalcComplete ((6 : Fin 10), .num 0)
    (0 : Fin 1) word tree1 tree2

/-- The EOF token that `lexString` pads with. -/
def eofTok : automaton.Token := ((6 : Fin 10), Expr.num 0)

/-- **Runtime-path completeness**: completeness on the *exact buffer shape
`parseExpr` executes* (`Buf.ofListEof toks EOF`, array-backed), not just on the
push-list buffers `word ++ₛ bufferEnd` of `mini_parses`. If the lexed tokens
followed by one EOF form a word of the grammar and the fuel covers the tree,
the parser returns that tree's AST. The two buffer shapes are connected by the
interpreter-extensionality bridge (`Main.parse_complete_ext` / `parse_congr`):
both denote the token stream `toks ++ EOF^ω`.

(`logNSteps` is universally quantified rather than fixed to `parseExpr`'s `50`:
elaborating these fuel-indexed theorems at a *fuel literal* forces the
elaborator's `whnf` through `parseFix`'s `2 ^ fuel` step cascade — exponential
in the literal — so, as with `mini_parses`, the fuel stays symbolic.) -/
theorem mini_parses_runtime (toks : List automaton.Token) (logNSteps : Nat)
    (tree : ParseTree (.NT (automaton.start_nt (0 : Fin 1))) (toks ++ [eofTok]))
    (hfuel : ptSize tree ≤ 2 ^ logNSteps) :
    ∃ rest, Main.parse (A := automaton) (0 : Fin 1) minicalcSafe logNSteps
        (Buf.ofListEof toks eofTok) = .Parsed (ptSem tree) rest := by
  have hbuf : (Buf.ofListEof toks eofTok).get
      = ((toks ++ [eofTok]) ++ₛ Buf.const eofTok).get := by
    rw [Buf.append_append_stream, Buf.get_ofListEof]
    exact (Buf.appendList_get_congr (Buf.get_replicate_const 1 eofTok) toks).symm
  have H := Main.parse_complete_ext (A := automaton) (0 : Fin 1) minicalcSafe minicalcComplete
    logNSteps _ (Buf.const eofTok) _ hbuf tree
  cases hp : Main.parse (A := automaton) (0 : Fin 1) minicalcSafe logNSteps
      (Buf.ofListEof toks eofTok) with
  | Parsed sem rest => rw [hp] at H; exact ⟨rest, by rw [H.1]⟩
  | Timeout => rw [hp] at H; omega
  | Fail st tok => rw [hp] at H; exact H.elim

end LeanMenhir.Examples.MiniCalc
