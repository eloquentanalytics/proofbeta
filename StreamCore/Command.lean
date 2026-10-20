-- Copyright (c) 2026 the proofbeta authors. All rights reserved. See LICENSE.
import StreamCore.Stream

/-!
# Commands: what a caller sends, and the event it becomes

A caller does not write events. It sends a **command**, which carries only what the caller chooses: never an actor and
never a minted id. The service supplies the rest:

- the **caller**, a principal id, which the host derives from the bearer token;
- the **fresh** ids, which the host mints (UUIDv7) for this request, one per id the event mints.

`toEvent` turns caller, command and fresh ids into exactly one event, or refuses before any rule runs, and `toRequest`
inverts it (`toEvent_ok_iff`). `respond` (`toEvent` then the rules: the one answer to a request against a log),
`handle` and `run` are the generic ones of `Service.lean` at the core (`Core.lean`); `run` is the headline: these
commands, in this order, produce these events, which follow these rules (`CommandTheorems.lean`).

Core Lean only.
-/

namespace StreamCore

/-- What a caller sends: one constructor per command, carrying only caller-supplied fields. Each emits the event of
the same name. -/
inductive Command where
  | streamCreate (creation : Creation) («meta» : Meta)
  | principalInvite (stream : Id) (principal : Id) («meta» : Meta)
  | principalPromote (stream : Id) (principal : Id) («meta» : Meta)
  | principalDemote (stream : Id) (principal : Id) («meta» : Meta)
  | principalBan (stream : Id) (principal : Id) («meta» : Meta)
  | streamPanic (stream : Id) («meta» : Meta)
  deriving DecidableEq, Repr

/-- The ids the host minted for one request, which the event mints: `[stream]` for `stream.create`, `[]` otherwise.
(Principal ids are not minted by any event: the host issues them.) -/
abbrev Fresh := List Id

/-- Translate a command from caller `c` into its event; `c` is the event's actor. The one refusal here comes before
any rule: `fresh_ids`, the host supplied the wrong number of fresh ids. -/
def toEvent : Id → Command → Fresh → Except String Event
  | c, .streamCreate u m, [t] => .ok (.streamCreate c t u m)
  | c, .principalInvite t p m, [] => .ok (.principalInvite c t p m)
  | c, .principalPromote t p m, [] => .ok (.principalPromote c t p m)
  | c, .principalDemote t p m, [] => .ok (.principalDemote c t p m)
  | c, .principalBan t p m, [] => .ok (.principalBan c t p m)
  | c, .streamPanic t m, [] => .ok (.streamPanic c t m)
  | _, _, _ => .error "fresh_ids"

/-- One request as the engine receives it: the caller (a principal id, from the token), the command, the fresh ids
(from the host). -/
abbrev Request := Id × Command × Fresh

/-- The request that produces an event: its actor as caller, its caller-supplied fields as command, its minted ids
as fresh. The two directions of the bijection between commands and events (`toEvent_toRequest`, `toRequest_toEvent`). -/
def toRequest : Event → Request
  | .streamCreate c t u m => (c, .streamCreate u m, [t])
  | .principalInvite c t p m => (c, .principalInvite t p m, [])
  | .principalPromote c t p m => (c, .principalPromote t p m, [])
  | .principalDemote c t p m => (c, .principalDemote t p m, [])
  | .principalBan c t p m => (c, .principalBan t p m, [])
  | .streamPanic c t m => (c, .streamPanic t m, [])

/-- The stream a request is on: the id it would mint for a creation, else the stream it names. -/
def reqStream : Request → Id
  | (_, .streamCreate .., f) => f.headD ""
  | (_, .principalInvite t .., _) | (_, .principalPromote t .., _) | (_, .principalDemote t .., _)
  | (_, .principalBan t .., _) | (_, .streamPanic t .., _) => t

/-! ## Each command becomes exactly the event of its kind, field by field -/

/-- The translation, inverted: an event comes from a command exactly when that event's request (`toRequest`) is the
request sent. So each command becomes exactly the event of its name, from its caller, with its fresh ids, and no other
event comes out. -/
theorem toEvent_ok_iff {c : Id} {cmd : Command} {f : Fresh} {e : Event} :
    toEvent c cmd f = .ok e ↔ toRequest e = (c, cmd, f) := by
  constructor
  · intro h
    cases cmd <;>
      (rcases f with _ | ⟨x, _ | ⟨y, z⟩⟩ <;> simp [toEvent] at h <;> subst h <;> rfl)
  · intro h
    cases e <;> simp [toRequest] at h <;> obtain ⟨rfl, rfl, rfl⟩ := h <;> rfl

/-- Per event: translating the request an event came from gives the event back. (Instantiated, this is the six
equations `toEvent c (.streamCreate u m) [t] = .ok (.streamCreate c t u m)`, ..., each `rfl`.) -/
theorem toEvent_toRequest (e : Event) :
    toEvent (toRequest e).1 (toRequest e).2.1 (toRequest e).2.2 = .ok e := toEvent_ok_iff.mpr rfl

/-- Per request: the request recovered from an accepted request's event is that request, exactly (no normal form is
needed: `toEvent` accepts only the exact number of fresh ids). -/
theorem toRequest_toEvent {c : Id} {cmd : Command} {f : Fresh} {e : Event} (h : toEvent c cmd f = .ok e) :
    toRequest e = (c, cmd, f) := toEvent_ok_iff.mp h

/-- The caller of a request is the actor of its event. -/
theorem toEvent_actor {c : Id} {cmd : Command} {f : Fresh} {e : Event} (h : toEvent c cmd f = .ok e) :
    e.actor = c := by
  have := toEvent_ok_iff.mp h
  cases e <;> simp [toRequest] at this <;> obtain ⟨rfl, -, -⟩ := this <;> rfl

/-- A stream's first admin is the principal that created it: `stream.create` from `c` yields a stream event whose actor is
`c`, and nothing else yields a stream event. -/
theorem toEvent_stream_iff {c : Id} {cmd : Command} {f : Fresh} {a t : Id} {u : Creation} {m : Meta}
    (h : toEvent c cmd f = .ok (.streamCreate a t u m)) : a = c ∧ cmd = .streamCreate u m ∧ f = [t] := by
  have := toEvent_ok_iff.mp h
  simp [toRequest] at this
  exact ⟨this.1, this.2.1.symm, this.2.2.symm⟩

/-- The ids an event mints are exactly the fresh ids the host supplied, in order. So no caller-chosen value is ever
minted, and freshness rests on `id_taken` alone (see `minted_once`). -/
theorem toEvent_minted {c : Id} {cmd : Command} {f : Fresh} {e : Event} (h : toEvent c cmd f = .ok e) :
    e.mintedAll = f := by
  have := toEvent_ok_iff.mp h
  cases e <;> simp [toRequest] at this <;> obtain ⟨-, -, rfl⟩ := this <;> rfl

theorem toEvent_stream {c : Id} {cmd : Command} {f : Fresh} {e : Event} (h : toEvent c cmd f = .ok e) :
    e.stream = reqStream (c, cmd, f) := by
  have := toEvent_ok_iff.mp h
  cases e <;> simp [toRequest] at this <;> obtain ⟨rfl, rfl, rfl⟩ := this <;> rfl


end StreamCore
