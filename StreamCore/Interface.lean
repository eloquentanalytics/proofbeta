-- Copyright (c) 2026 the proofbeta authors. All rights reserved. See LICENSE.
import StreamCore.Theorems
import StreamCore.Layer

/-!
# The interface a layer builds on

A layer imports this module and nothing else of the core, and relies only on the declarations it writes against,
with their statements (a fact of the past by its signature and the lemmas below, not its body), and the guarantees
every layer gets, by name. Those change only with a major version
of the core. The engine for a layer, on the core or on a tower of layers, is `Engine.Layered.main`.

A layer on another layer imports that layer's modules too. `Work/` is one layer, written this way.
-/

namespace StreamCore

/-- The view's `mayAct`, as the layer above reads it: a member of a stream that has not ended. -/
def View.mayAct (v : View) (p : Id) : Bool := v.member p && !v.ended

/-! ## The view of a stream is its facts of the past -/

@[simp] theorem Past.view_created (past : Past) (t : Id) : (past.view t).created = past.hasStream t := rfl
@[simp] theorem Past.view_ended (past : Past) (t : Id) : (past.view t).ended = past.ended t := rfl
@[simp] theorem Past.view_member (past : Past) (t p : Id) : (past.view t).member p = past.member t p := rfl
@[simp] theorem Past.view_admin (past : Past) (t p : Id) : (past.view t).admin p = past.admin t p := rfl
@[simp] theorem Past.view_banned (past : Past) (t p : Id) : (past.view t).banned p = past.banned t p := rfl
@[simp] theorem Past.view_otherAdmin (past : Past) (t p : Id) : (past.view t).otherAdmin p = past.otherAdmin t p := rfl
@[simp] theorem View.mayAct_view (past : Past) (t p : Id) : (past.view t).mayAct p = past.mayAct t p := rfl

/-! ## The stream and the actor of an event, by its constructor -/

@[simp] theorem Event.stream_streamCreate (a t : Id) (u : Creation) (m : Meta) : (Event.streamCreate a t u m).stream = t := rfl
@[simp] theorem Event.stream_principalInvite (a t p : Id) (m : Meta) : (Event.principalInvite a t p m).stream = t := rfl
@[simp] theorem Event.stream_principalPromote (a t p : Id) (m : Meta) : (Event.principalPromote a t p m).stream = t := rfl
@[simp] theorem Event.stream_principalDemote (a t p : Id) (m : Meta) : (Event.principalDemote a t p m).stream = t := rfl
@[simp] theorem Event.stream_principalBan (a t p : Id) (m : Meta) : (Event.principalBan a t p m).stream = t := rfl
@[simp] theorem Event.stream_streamPanic (a t : Id) (m : Meta) : (Event.streamPanic a t m).stream = t := rfl
@[simp] theorem Event.actor_streamCreate (a t : Id) (u : Creation) (m : Meta) : (Event.streamCreate a t u m).actor = a := rfl
@[simp] theorem Event.actor_principalInvite (a t p : Id) (m : Meta) : (Event.principalInvite a t p m).actor = a := rfl
@[simp] theorem Event.actor_principalPromote (a t p : Id) (m : Meta) : (Event.principalPromote a t p m).actor = a := rfl
@[simp] theorem Event.actor_principalDemote (a t p : Id) (m : Meta) : (Event.principalDemote a t p m).actor = a := rfl
@[simp] theorem Event.actor_principalBan (a t p : Id) (m : Meta) : (Event.principalBan a t p m).actor = a := rfl
@[simp] theorem Event.actor_streamPanic (a t : Id) (m : Meta) : (Event.streamPanic a t m).actor = a := rfl

/-! ## Facts of the past -/

/-- An admin is a member. -/
theorem Past.admin_member {past : Past} {t p : Id} (h : past.admin t p = true) : past.member t p = true := by
  simp only [Past.admin, Bool.and_eq_true] at h; exact h.1

/-- A member is not banned. -/
theorem Past.member_banned {past : Past} {t p : Id} (h : past.member t p = true) : past.banned t p = false := by
  simp only [Past.member, Bool.and_eq_true, Bool.not_eq_true'] at h; exact h.2

end StreamCore
