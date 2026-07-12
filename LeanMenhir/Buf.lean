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

/-- Denotation: the `n`-th token of the buffer's stream.

Proof-only — the runtime parser uses `head`/`tail` directly and never calls
`get`, so the fact that `get` walks `n` tails is irrelevant to performance. The
soundness conservation law is phrased as equality of denotations (`a.get = b.get`),
the honest analogue of the `Stream'` equality used by the original Coq proof. -/
def get : Buf α → Nat → α
  | b, 0 => b.head
  | b, n + 1 => b.tail.get n

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

@[simp] theorem get_zero (b : Buf α) : b.get 0 = b.head := rfl

theorem get_succ (b : Buf α) (n : Nat) : b.get (n + 1) = b.tail.get n := rfl

/-- Denotational η: `cons b.head b.tail` denotes the same token stream as `b`.

This replaces the structurally **false** `cons b.head b.tail = b`. Structural
equality cannot hold for the array+cursor representation — `cons` records the
prepended token in `push` rather than rewinding the cursor — but the soundness
proof only ever needs the two buffers to *denote the same stream*. This is the
exact Lean analogue of the Coq proof, where the buffer is a coinductive `Stream`
and `destruct buffer as [tok buffer]` exposes `b = tok ::: tl b` definitionally;
here that definitional step becomes this one-line lemma. -/
protected theorem get_eta (b : Buf α) : (cons b.head b.tail).get = b.get := by
  funext n; cases n <;> rfl

/-- `cons` is a congruence for denotational equality. -/
theorem cons_get_congr {a b : Buf α} (x : α) (h : a.get = b.get) :
    (cons x a).get = (cons x b).get := by
  funext n
  cases n with
  | zero => rfl
  | succ n => exact congrFun h n

/-- `appendList` is a congruence for denotational equality (its `Buf` argument). -/
theorem appendList_get_congr {a b : Buf α} (h : a.get = b.get) :
    ∀ l : List α, (appendList l a).get = (appendList l b).get
  | [] => h
  | x :: l => cons_get_congr x (appendList_get_congr h l)

@[inherit_doc appendList] scoped infixl:65 " ++ₛ " => appendList

/-! ### Denotation of concrete buffers

The runtime driver feeds the parser an array-backed buffer (`ofListEof`), while
the completeness theorem speaks about push-list buffers (`word ++ₛ bufferEnd`).
These lemmas compute the denotation of both forms so the two can be compared:
`ofListEof xs eofv` denotes exactly `xs ++ₛ const eofv`. -/

/-- Denotation of an array-backed buffer with empty `push`: position `n` holds
the array element at `idx + n`, falling back to `eof` past the end. -/
theorem get_mk (a : Array α) (e : α) : ∀ (n i : Nat),
    Buf.get ⟨[], a, i, e⟩ n = a.toList.getD (i + n) e
  | 0, i => by
    show (if h : i < a.size then a[i] else e) = a.toList.getD (i + 0) e
    rw [Nat.add_zero, List.getD_eq_getElem?_getD]
    split
    · rename_i hlt
      rw [List.getElem?_eq_getElem (by simpa using hlt)]
      simp
    · rename_i hge
      rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hge)]
      rfl
  | n + 1, i => by
    show Buf.get ⟨[], a, i + 1, e⟩ n = a.toList.getD (i + (n + 1)) e
    rw [get_mk a e n (i + 1), Nat.add_assoc, Nat.add_comm 1 n]

/-- Every position of the constant buffer holds `a`. -/
theorem get_const (a : α) (n : Nat) : (const a).get n = a := by
  show Buf.get ⟨[], #[], 0, a⟩ n = a
  rw [get_mk]
  rfl

/-- Denotation of a push-list buffer over the constant buffer: position `n`
holds the `n`-th list element, falling back to `a` past the end. -/
theorem get_appendList_const (a : α) : ∀ (xs : List α) (n : Nat),
    (xs ++ₛ const a).get n = xs.getD n a
  | [], n => by rw [nil_append_stream, get_const]; exact (List.getD_nil).symm
  | x :: xs, 0 => by rw [cons_append_stream]; exact (List.getD_cons_zero).symm
  | x :: xs, n + 1 => by
    rw [cons_append_stream, List.getD_cons_succ]
    exact get_appendList_const a xs n

/-- Padding the constant buffer with copies of its own element is invisible in
the denotation. -/
theorem get_replicate_const (k : Nat) (a : α) :
    (List.replicate k a ++ₛ const a).get = (const a).get := by
  funext n
  rw [get_appendList_const, get_const, List.getD_eq_getElem?_getD]
  rcases Nat.lt_or_ge n k with hlt | hge
  · rw [List.getElem?_eq_getElem (by simpa using hlt), List.getElem_replicate]
    rfl
  · rw [List.getElem?_eq_none (by simpa using hge)]
    rfl

/-- The array-backed buffer `ofListEof xs eofv` denotes exactly the push-list
buffer `xs ++ₛ const eofv`. This is the bridge that lets theorems stated on the
canonical `++ₛ` form apply to the runtime's `ofListEof` input. -/
theorem get_ofListEof (xs : List α) (e : α) :
    (ofListEof xs e).get = (xs ++ₛ const e).get := by
  funext n
  show Buf.get ⟨[], xs.toArray, 0, e⟩ n = _
  rw [get_mk, get_appendList_const]
  simp

end Buf
end LeanMenhir
