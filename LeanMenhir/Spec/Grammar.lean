/-
Port of `coq-menhirlib`'s `Grammar.v` to Lean 4.

Original: Copyright Inria and CNRS, LGPL-3.0-or-later.
This Lean port is a derivative work, distributed under LGPL-3.0-or-later.

The grammar interface (symbols, productions, semantic actions, tokens) together
with the dependently-typed `ParseTree` / `ParseTreeList` families that give the
semantics of a grammar.
-/
import LeanMenhir.Spec.Alphabet

namespace LeanMenhir

/-! ### Symbols -/

/-- The alphabet of grammar symbols: a terminal or a nonterminal. Mirrors Coq's
`symbol` from `Module Symbol`. -/
inductive Symbol (Terminal Nonterminal : Type) where
  | T : Terminal → Symbol Terminal Nonterminal
  | NT : Nonterminal → Symbol Terminal Nonterminal
deriving DecidableEq

namespace Symbol
variable {Terminal Nonterminal : Type}

/-- The comparison on symbols: terminals compare greater than nonterminals
(Coq `SymbolAlph`). Defined as a standalone function so its defining equations
are usable by `simp`. -/
def cmp [Comparable Terminal] [Comparable Nonterminal] :
    Symbol Terminal Nonterminal → Symbol Terminal Nonterminal → Ordering
  | T x, T y => Comparable.compare x y
  | NT x, NT y => Comparable.compare x y
  | T _, NT _ => Ordering.gt
  | NT _, T _ => Ordering.lt

instance instComparable [Comparable Terminal] [Comparable Nonterminal] :
    Comparable (Symbol Terminal Nonterminal) where
  compare := cmp
  compare_antisym x y := by
    cases x <;> cases y <;> simp only [cmp]
    · exact compare_antisym _ _
    · rfl
    · rfl
    · exact compare_antisym _ _
  compare_trans x y z c hxy hyz := by
    cases x <;> cases y <;> cases z <;> simp only [cmp] at hxy hyz ⊢
    · exact compare_trans _ _ _ _ hxy hyz
    · exact hyz
    · exact absurd (hxy.trans hyz.symm) (by decide)
    · exact hxy
    · exact hxy
    · exact absurd (hxy.trans hyz.symm) (by decide)
    · exact hyz
    · exact compare_trans _ _ _ _ hxy hyz

instance instComparableLeibnizEq [Comparable Terminal] [Comparable Nonterminal]
    [ComparableLeibnizEq Terminal] [ComparableLeibnizEq Nonterminal] :
    ComparableLeibnizEq (Symbol Terminal Nonterminal) where
  compare_eq x y h := by
    change cmp x y = Ordering.eq at h
    cases x <;> cases y <;> simp only [cmp] at h
    · exact congrArg T (compare_eq _ _ h)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact congrArg NT (compare_eq _ _ h)

instance instEnumerable [Enumerable Terminal] [Enumerable Nonterminal] :
    Enumerable (Symbol Terminal Nonterminal) where
  allList := (allList (α := Terminal)).map T ++ (allList (α := Nonterminal)).map NT
  allList_complete x := by
    rw [List.mem_append]
    cases x with
    | T t => exact Or.inl (List.mem_map.2 ⟨t, allList_complete t, rfl⟩)
    | NT n => exact Or.inr (List.mem_map.2 ⟨n, allList_complete n, rfl⟩)

instance instAlphabet [Alphabet Terminal] [Alphabet Nonterminal] :
    Alphabet (Symbol Terminal Nonterminal) := {}

end Symbol

/-! ### Curried action types -/

/-- `arrowsRight A [T₁, …, Tₙ] = T₁ → ⋯ → Tₙ → A`. Mirrors Coq `arrows_right`
(`fold_right (fun A B => A → B)`). -/
def arrowsRight (A : Type) : List Type → Type
  | [] => A
  | T :: rest => T → arrowsRight A rest

/-! ### The grammar interface -/

/-- The grammar: terminals, nonterminals, productions with typed semantic
actions, and tokens. This is a **structure** (not a class): a grammar is an
ordinary mathematical object that theorems bind explicitly — `(G : Grammar)` —
so that every statement visibly says *which grammar* it is about (Coq
`Grammar.T` bundled the same data as a module functor argument). -/
structure Grammar where
  Terminal : Type
  Nonterminal : Type
  terminalAlphabet : Alphabet Terminal
  nonterminalAlphabet : Alphabet Nonterminal
  /-- The type of semantic values associated with each symbol. -/
  symbol_semantic_type : Symbol Terminal Nonterminal → Type
  Production : Type
  productionAlphabet : Alphabet Production
  prod_lhs : Production → Nonterminal
  /-- The RHS of a production, in reversed order. -/
  prod_rhs_rev : Production → List (Symbol Terminal Nonterminal)
  /-- The semantic action of a production: a curried function taking the values
  of the RHS symbols (in reverse order) and producing the LHS value. -/
  prod_action : (p : Production) →
    arrowsRight (symbol_semantic_type (.NT (prod_lhs p)))
                ((prod_rhs_rev p).map symbol_semantic_type)
  Token : Type
  token_term : Token → Terminal
  token_sem : (tok : Token) → symbol_semantic_type (.T (token_term tok))

instance instTerminalAlphabet (G : Grammar) : Alphabet G.Terminal := G.terminalAlphabet
instance instNonterminalAlphabet (G : Grammar) : Alphabet G.Nonterminal :=
  G.nonterminalAlphabet
instance instProductionAlphabet (G : Grammar) : Alphabet G.Production := G.productionAlphabet

/-- Abbreviation for the symbol type of a grammar. -/
abbrev Grammar.symbol (G : Grammar) : Type := Symbol G.Terminal G.Nonterminal

/-! ### Parse trees -/

/- A parse tree recognises a `word` as a single head `symbol`; a `ParseTreeList`
recognises a `word` as a (reversed) list of head symbols. Semantic values are
stored at the leaves. The grammar `G` is an **explicit** parameter so that
statements read `G.ParseTree …` — a derivation *in G*. Mirrors Coq `parse_tree`
/ `parse_tree_list`. -/
mutual
inductive ParseTree (G : Grammar) :
    Symbol G.Terminal G.Nonterminal → List G.Token → Type where
  /-- Parse tree for a terminal symbol. -/
  | leaf : (tok : G.Token) → ParseTree G (.T (G.token_term tok)) [tok]
  /-- Parse tree for a non-terminal symbol. -/
  | node : (prod : G.Production) → {word : List G.Token} →
      ParseTreeList G (G.prod_rhs_rev prod) word →
      ParseTree G (.NT (G.prod_lhs prod)) word

inductive ParseTreeList (G : Grammar) :
    List (Symbol G.Terminal G.Nonterminal) → List G.Token → Type where
  | nil : ParseTreeList G [] []
  | cons : {head_symbolsq : List (Symbol G.Terminal G.Nonterminal)} →
      {wordq : List G.Token} → ParseTreeList G head_symbolsq wordq →
      {head_symbolt : Symbol G.Terminal G.Nonterminal} → {wordt : List G.Token} →
      ParseTree G head_symbolt wordt →
      ParseTreeList G (head_symbolt :: head_symbolsq) (wordq ++ wordt)
end

/-- Dot-notation alias so statements can say `G.ParseTree s w` — “a derivation
in `G`”. -/
protected abbrev Grammar.ParseTree := @LeanMenhir.ParseTree

@[inherit_doc Grammar.ParseTree]
protected abbrev Grammar.ParseTreeList := @LeanMenhir.ParseTreeList

variable {G : Grammar}

/- The semantic value associated with a parse tree (Coq `pt_sem` / `ptl_sem`). -/
mutual
def ptSem : {hs : Symbol G.Terminal G.Nonterminal} → {w : List G.Token} →
    ParseTree G hs w → G.symbol_semantic_type hs
  | _, _, .leaf tok => G.token_sem tok
  | _, _, .node prod ptl => ptlSem ptl (G.prod_action prod)

def ptlSem {A : Type} : {hs : List (Symbol G.Terminal G.Nonterminal)} →
    {w : List G.Token} → ParseTreeList G hs w →
    arrowsRight A (hs.map G.symbol_semantic_type) → A
  | _, _, .nil, act => act
  | _, _, .cons q t, act => ptlSem q (act (ptSem t))
end

/- The size of a parse tree (Coq `pt_size` / `ptl_size`). -/
mutual
def ptSize : {hs : Symbol G.Terminal G.Nonterminal} → {w : List G.Token} →
    ParseTree G hs w → Nat
  | _, _, .leaf _ => 1
  | _, _, .node _ l => ptlSize l + 1

def ptlSize : {hs : List (Symbol G.Terminal G.Nonterminal)} → {w : List G.Token} →
    ParseTreeList G hs w → Nat
  | _, _, .nil => 0
  | _, _, .cons q t => ptSize t + ptlSize q
end

end LeanMenhir
