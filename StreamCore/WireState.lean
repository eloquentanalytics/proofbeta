-- Copyright (c) 2026 the proofbeta authors. All rights reserved. See LICENSE.
import StreamCore.StreamState
import StreamCore.WireTheorems

/-!
# The engine's fast path on the wire: catch-up, reads and snapshots from `StreamState`

Reads and snapshots from the per-stream state. Catch-up from stored rows through the state and the engine's
bookkeeping per stream (`Entry`) are the generic ones of `Service.lean` at the core (`Core.lean`).
-/

namespace StreamCore.Wire
open StreamCore

/-! ## Reads from the state -/

def membersS (st : StreamState) : List (Id × Bool × Bool) :=
  (st.joined.filter st.member).map fun p => (p, st.admin p, st.mayAct p)

/-- Reads from the state list exactly the current members, with the rules' own flags. -/
theorem mem_membersS {s : Id} {L : Log} {x : Id × Bool × Bool} :
    x ∈ membersS (fold s L) ↔
      Past.member L s x.1 = true ∧ x.2.1 = Past.admin L s x.1 ∧ x.2.2 = Past.mayAct L s x.1 := by
  obtain ⟨p, a, m⟩ := x
  simp only [membersS, List.mem_map, List.mem_filter, Prod.mk.injEq, fold_member, fold_admin, fold_mayAct]
  constructor
  · rintro ⟨q, ⟨-, hq⟩, rfl, rfl, rfl⟩; exact ⟨hq, rfl, rfl⟩
  · rintro ⟨hm, rfl, rfl⟩
    refine ⟨p, ⟨?_, hm⟩, rfl, rfl, rfl⟩
    have hj : Past.joined L s p = true := by simp only [Past.member, Bool.and_eq_true] at hm; exact hm.1
    rw [← fold_joined] at hj
    exact List.elem_iff.mp hj

/-- What a read of a stream answers, from its state. -/
def streamSJ (st : StreamState) : J :=
  if st.created then
    .obj [("stream", .str st.stream), ("creator", metaJ st.creator), ("proof_revision_url", metaJ st.url),
      ("ended", .bool st.ended),
      ("members", .arr ((membersS st).map memberJ)),
      ("banned", .arr (st.banned.map .str))]
  else .obj [("error", .str "unknown_stream")]

/-! ## Snapshots: a state on the wire -/

def stateToJ (st : StreamState) : J :=
  .obj [("stream", .str st.stream), ("created", .bool st.created), ("creator", metaJ st.creator),
    ("url", metaJ st.url), ("joined", .arr (st.joined.map .str)), ("banned", .arr (st.banned.map .str)),
    ("admins", .arr (st.admins.map .str)), ("ended", .bool st.ended)]

def strsFromJ : Option J → Except String (List String)
  | some j => strs "state" j
  | none => .error "state: expected an array"

def boolFromJ : Option J → Except String Bool
  | some (.bool b) => .ok b
  | _ => .error "state: expected a boolean"

def optFromJ : Option J → Except String (Option String)
  | some .null => .ok none
  | some (.str x) => .ok (some x)
  | _ => .error "state: expected a string or null"

def stateFromJ (j : J) : Except String StreamState := do
  let kvs ← fields "state" j
  let some (.str s) := get? kvs "stream" | throw "state.stream: missing"
  return { stream := s, created := ← boolFromJ (get? kvs "created"), creator := ← optFromJ (get? kvs "creator"),
           url := ← optFromJ (get? kvs "url"), joined := ← strsFromJ (get? kvs "joined"),
           banned := ← strsFromJ (get? kvs "banned"), admins := ← strsFromJ (get? kvs "admins"),
           ended := ← boolFromJ (get? kvs "ended") }

theorem optFromJ_toJ (o : Option String) : optFromJ (some (metaJ o)) = .ok o := by
  cases o <;> rfl

/-- **A snapshot decodes to the state it encodes.** -/
theorem stateFromJ_toJ (st : StreamState) : stateFromJ (stateToJ st) = .ok st := by
  obtain ⟨s, c, cr, u, j, b, a, e⟩ := st
  simp [stateFromJ, stateToJ, fields, get?, List.find?, boolFromJ, optFromJ_toJ, strsFromJ, strs_toJ, bind,
    Except.bind, pure, Except.pure]

end StreamCore.Wire
