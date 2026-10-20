-- Copyright (c) 2026 the proofbeta authors. All rights reserved. See LICENSE.
import StreamCore.Interface

/-!
# The recipes this layer copies, as written

`fold_memory` (the memory: the stream's own layer events), `records_codec` (its snapshot) and `j_beq` (reads compared
in the worked examples). Their usage examples are left out. URLs are opaque here (`opaqueUrl`, `Layer.lean`), so the
recipe `url_kind` is not used.
-/

namespace Work
open StreamCore StreamCore.Wire

/-! ## fold_memory: the rules read the state itself -/

/-- **A fold memory**: the rules read the fold of the stream's layer events (`read := foldl step init`, `view := id`),
so the obligation `fold_view` is `rfl`. The state needs a snapshot codec and its round trip (`records_codec`, or the
core's facts codec for a `List Fact`). -/
abbrev foldMemory {Ev St : Type} [DecidableEq St] (init : St) (step : St → Ev → St) (toJ : St → J)
    (ofJ : J → Except String St) (h : ∀ st, ofJ (toJ st) = .ok st) : Memory Ev where
  V := St
  read past := past.foldl step init
  St := St
  init := init
  step := step
  view st := st
  fold_view _ := rfl
  stateToJ := toJ
  stateFromJ := ofJ
  stateFromJ_toJ := h

section
variable {Ev St : Type} [DecidableEq St] {init : St} {step : St → Ev → St} {toJ : St → J}
  {ofJ : J → Except String St} {h : ∀ st, ofJ (toJ st) = .ok st}

@[simp] theorem fold_read (past : List Ev) : (foldMemory init step toJ ofJ h).read past = past.foldl step init := rfl

omit [DecidableEq St] in
/-- **A fold invariant**: a property of the state that every step keeps holds after any events. -/
theorem fold_keeps (P : St → Prop) (hs : ∀ st e, P st → P (step st e)) (es : List Ev) {st : St} (h0 : P st) :
    P (es.foldl step st) := by
  induction es generalizing st with
  | nil => exact h0
  | cons e es ih => exact ih (hs st e h0)

end

/-! ## records_codec: a snapshot codec for a state of records, over the wire's `J`, with its round trip -/

/-- An optional id: `null` or a string. -/
def optJ : Option String → J
  | none => .null
  | some x => .str x

def optOfJ : J → Except String (Option String)
  | .null => .ok none
  | .str x => .ok (some x)
  | _ => .error "expected a string or null"

def strOfJ : J → Except String String
  | .str s => .ok s
  | _ => .error "expected a string"

def boolOfJ : J → Except String Bool
  | .bool b => .ok b
  | _ => .error "expected a boolean"

/-- A list, each element read by `f`. -/
def listOfJ {α : Type} (f : J → Except String α) : List J → Except String (List α)
  | [] => .ok []
  | j :: js => match f j, listOfJ f js with
    | .ok x, .ok xs => .ok (x :: xs)
    | _, _ => .error "a list"

theorem optOfJ_toJ (o : Option String) : optOfJ (optJ o) = .ok o := by cases o <;> rfl

theorem listOfJ_map {α : Type} {f : J → Except String α} {g : α → J} (h : ∀ x, f (g x) = .ok x) (l : List α) :
    listOfJ f (l.map g) = .ok l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [listOfJ, h, ih]

/-! ## j_beq: structural equality on the wire's `J`, for `#guard` -/

mutual
/-- Two JSON values are the same value: same constructor, same contents, objects' keys in the same order. -/
def jBeq : J → J → Bool
  | .null, .null => true
  | .bool a, .bool b => a == b
  | .num a, .num b => a == b
  | .str a, .str b => a == b
  | .arr xs, .arr ys => jBeqList xs ys
  | .obj xs, .obj ys => jBeqObj xs ys
  | _, _ => false
def jBeqList : List J → List J → Bool
  | [], [] => true
  | x :: xs, y :: ys => jBeq x y && jBeqList xs ys
  | _, _ => false
def jBeqObj : List (String × J) → List (String × J) → Bool
  | [], [] => true
  | (k, x) :: xs, (l, y) :: ys => k == l && jBeq x y && jBeqObj xs ys
  | _, _ => false
end

instance : BEq J := ⟨jBeq⟩

end Work
