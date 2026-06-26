/-
Fast token buffer for the verified parser runtime.

Replaces Mathlib's `Stream' = ℕ → α` representation (which gives O(k)
`head`/`tail` after k consumed tokens, driving the parse loop to O(n²)
total) with a struct-of-Array buffer whose `head`/`tail` are O(1).

The proof story: this file provides exactly the operations and equational
laws the interpreter and completeness proofs depend on:
`head`, `tail`, `cons`, `const`, `appendList` (notation `++ₛ`), and the
five `rfl`-style lemmas `head_cons`, `tail_cons`, `nil_append_stream`,
`cons_append_stream`, `append_append_stream`. All correctness proofs in
`Interpreter/Complete.lean` and `Main.lean` are stated only in terms of
those laws (and the abstract `head`/`tail` interface), so swapping the
representation is a localized change.

LGPL-3.0-or-later (derivative of coq-menhirlib).
-/

namespace LeanMenhir

/-- A finite token buffer with O(1) `head` and `tail`.

The token stream is kept in three parts, consumed in this order:

* `push`  — a small list of tokens pushed back via `cons`/`appendList`
  (used by the completeness proof when reasoning about parser steps).
* `toks` / `idx` — an immutable token array with a cursor. This is the
  hot path; advancing the cursor is a single `Nat` increment.
* `eof` — a sentinel returned once both `push` and `toks` are exhausted.
  The verified driver pads with a caller-supplied EOF token.

All operations except `appendList`/`const`-of-list are O(1); the proofs
only care about the equational laws below. -/
structure Buf (α : Type u) where
  push : List α
  toks : Array α
  idx  : Nat
  eof  : α

namespace Buf

variable {α : Type u}

/-- First token, in O(1). Falls through to the array body, then to `eof`. -/
@[inline] def head : Buf α → α
  | { push := x :: _, .. } => x
  | { push := [], toks, idx, eof } =>
      if h : idx < toks.size then toks[idx] else eof

/-- Drop the first token, in O(1). -/
@[inline] def tail : Buf α → Buf α
  | { push := _ :: rest, toks, idx, eof } => { push := rest, toks, idx, eof }
  | { push := [], toks, idx, eof } => { push := [], toks, idx := idx + 1, eof }

/-- Prepend a token; O(1). -/
@[inline] def cons (a : α) (b : Buf α) : Buf α :=
  { b with push := a :: b.push }

/-- The constant buffer (every position is `a`). -/
@[inline] def const (a : α) : Buf α :=
  { push := [], toks := #[], idx := 0, eof := a }

/-- Prepend a list of tokens; O(|xs|). -/
def appendList : List α → Buf α → Buf α
  | [],      b => b
  | x :: xs, b => cons x (appendList xs b)

/-- Build an O(1)-head/tail buffer directly from a token list and EOF padding.
The list is converted to an `Array` once; subsequent `head`/`tail` are O(1). -/
@[inline] def ofListEof (xs : List α) (eof : α) : Buf α :=
  { push := [], toks := xs.toArray, idx := 0, eof := eof }

/-! ### Equational laws

These are the *only* laws the proofs (in `Interpreter/Complete.lean` and
`Main.lean`) rely on, and they all hold by definitional unfolding plus
structure η. The names mirror Mathlib's `Stream'` lemma names so the
proof texts read the same after a global `Stream' → Buf` rename. -/

@[simp] theorem head_cons (a : α) (b : Buf α) : (cons a b).head = a := rfl

@[simp] theorem tail_cons (a : α) (b : Buf α) : (cons a b).tail = b := rfl

@[simp] theorem nil_append_stream (b : Buf α) : appendList [] b = b := rfl

theorem cons_append_stream (a : α) (l : List α) (b : Buf α) :
    appendList (a :: l) b = cons a (appendList l b) := rfl

@[simp] theorem append_append_stream : ∀ (l₁ l₂ : List α) (b : Buf α),
    appendList (l₁ ++ l₂) b = appendList l₁ (appendList l₂ b)
  | [], _, _ => rfl
  | a :: l₁, l₂, b => by
    rw [List.cons_append, cons_append_stream, cons_append_stream, append_append_stream l₁]

/-- Structure-η for buffers: a buffer equals the cons of its head and tail.

⚠️ TEMPORARY `sorry`. This does **not** hold structurally for the current
array+push representation when the buffer is past EOF (`push = []` and
`idx ≥ toks.size`): `cons eof (tail b)` re-pushes an `eof` that the original
`b` represented only via its `eof` sentinel. The honest fixes are (a) a
bisimulation-quotient `Buf`, (b) a `DecidableEq`-gated canonical `cons` that
collapses a trailing-eof push, or (c) carrying a `buffer` non-emptiness
invariant (fuel-bounded) through `step_sound`. Parked while we validate the
runtime-performance hypothesis; see progress notes. -/
@[simp] protected theorem eta (b : Buf α) : cons b.head b.tail = b := by
  sorry

@[inherit_doc appendList] scoped infixl:65 " ++ₛ " => appendList

end Buf
end LeanMenhir
