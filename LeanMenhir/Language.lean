/-
Language membership: the *named* notion of "this word is in the language".

A derivation (`ParseTree`) is proof-relevant data: a value of type
`ParseTree (.NT nt) word` *is* a derivation of `word` from `nt`. The
propositional counterpart — "such a derivation exists" — is what a human means
by *membership in the language*, and it deserves a name so that theorem
statements can say it directly:

* `Derives nt word` — `word` is derivable from `nt`;
* `word ∈ language nt` — the same, in set-membership notation.

The guarantees in `LeanMenhir/Guarantees.lean` come in two faces: a
*recognition-level* face phrased with `∈ language` (what a reader expects:
"every word of the language is accepted"), and a *semantic-level* face phrased
with an explicit derivation (strictly stronger: it also pins the returned value
to `ptSem tree` and the needed fuel to `ptSize tree`). The recognition faces
are corollaries of the semantic ones.

Design note (D8): the language is over **token** words (terminal + semantic
payload) — the honest post-lexer notion, and what `ptSem` needs. Payloads never
affect *whether* a word derives (derivability constrains only `token_term`),
only the value produced; the classic terminal-string language is the image of
this one under `List.map token_term` and is provided at the `Grammar0` level
(`Grammar0.Derives`, phase P3b) together with a transport theorem.

LGPL-3.0-or-later (derivative of coq-menhirlib).
-/
import LeanMenhir.Grammar

namespace LeanMenhir

/-- A language over token type `α`: a predicate on token words. (Minimal stand-in
for Mathlib's `Language`; membership notation via the instance below.) -/
def Language (α : Type) : Type := List α → Prop

instance {α : Type} : Membership (List α) (Language α) := ⟨fun L w => L w⟩

variable {G : Grammar}

/-- `G.Derives nt word` : the token word `word` is derivable from nonterminal
`nt` **in grammar `G`** — i.e. "`word` is in the language of `nt`". This is the
propositional form of a `ParseTree`: the derivation itself is the
(proof-relevant) witness. -/
def Grammar.Derives (G : Grammar) (nt : G.Nonterminal) (word : List G.Token) : Prop :=
  Nonempty (ParseTree G (.NT nt) word)

/-- A derivation witnesses membership. -/
theorem Grammar.Derives.intro {nt : G.Nonterminal} {word : List G.Token}
    (pt : ParseTree G (.NT nt) word) : G.Derives nt word := ⟨pt⟩

/-- The language of nonterminal `nt` in grammar `G`: the set of token words
derivable from it. -/
def Grammar.language (G : Grammar) (nt : G.Nonterminal) : Language G.Token :=
  fun word => G.Derives nt word

@[simp] theorem Grammar.mem_language {nt : G.Nonterminal} {word : List G.Token} :
    word ∈ G.language nt ↔ G.Derives nt word := Iff.rfl

export Grammar (mem_language)

end LeanMenhir
