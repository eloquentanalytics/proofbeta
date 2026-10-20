-- Copyright (c) 2026 the proofbeta authors. All rights reserved. See LICENSE.
import StreamCore.Rules

/-!
# The stream

A log is the list of accepted events, oldest first. A candidate is accepted when every rule holds against the log as it
stands; the first rule that fails is the rejection. Every rule reads only the candidate's own stream
(`rejection_local`). `Valid`, a log built by acceptances only, and `check`, which decides it, are the generic ones of
`Service.lean` at the core (`Core.lean`).
-/

namespace StreamCore

abbrev Log := List Event

def ok (past : Past) (e : Event) : Bool := (past.view e.stream).ok e

def rejection (past : Past) (e : Event) : Option String := (past.view e.stream).rejection e

/-- Accept a candidate: append it, or name the first rule it fails. -/
def accept (log : Log) (e : Event) : Except String Log :=
  match rejection log e with
  | some reason => .error reason
  | none => .ok (log ++ [e])

/-! ## `rejection` and `ok` agree -/

theorem rejection_none_iff (past : Past) (e : Event) : rejection past e = none ↔ ok past e = true :=
  View.rejection_none_iff _ e

/-- `accept` appends exactly when every rule holds. -/
theorem accept_ok_iff (log log' : Log) (e : Event) :
    accept log e = .ok log' ↔ ok log e = true ∧ log' = log ++ [e] := by
  unfold accept
  cases h : rejection log e with
  | none => simp [(rejection_none_iff log e).mp h, eq_comm]
  | some r =>
    have : ok log e ≠ true := fun hok => by simp [(rejection_none_iff log e).mpr hok] at h
    simp [this]

/-! ## Deciding is local to a stream -/

/-- The events of stream `s`, in order. -/
def onStream (L : Log) (s : Id) : Log := L.filter (·.stream == s)

/-! ## Every fact the rules read is a fact about one stream -/

theorem creates_stream {t : Id} {e : Event} (h : creates t e = true) : e.stream = t := by
  cases e <;> simp_all [creates, Event.stream]
theorem joins_stream {t p : Id} {e : Event} (h : joins t p e = true) : e.stream = t := by
  cases e <;> simp_all [joins, Event.stream]
theorem bans_stream {t p : Id} {e : Event} (h : bans t p e = true) : e.stream = t := by
  cases e <;> simp_all [bans, Event.stream]
theorem ends_stream {t : Id} {e : Event} (h : ends t e = true) : e.stream = t := by
  cases e <;> simp_all [ends, Event.stream]
theorem adminRel_stream {t p : Id} {e : Event} (h : adminRel t p e ≠ none) : e.stream = t := by
  cases e <;> simp only [adminRel] at h <;> (try split at h) <;> simp_all [Event.stream]

theorem any_onStream {L : Log} {s : Id} {f : Event → Bool} (hf : ∀ e, f e = true → e.stream = s) :
    (onStream L s).any f = L.any f := by
  induction L with
  | nil => rfl
  | cons e es ih =>
    simp only [onStream, List.filter_cons] at ih ⊢
    split
    · simp [ih]
    · rename_i hne
      rw [ih]
      simp only [List.any_cons]
      cases hfe : f e
      · simp
      · exact absurd (by simpa using hf e hfe) hne

theorem filterMap_onStream {L : Log} {s : Id} {rel : Event → Option Bool} (hr : ∀ e, rel e ≠ none → e.stream = s) :
    (onStream L s).filterMap rel = L.filterMap rel := by
  induction L with
  | nil => rfl
  | cons e es ih =>
    simp only [onStream, List.filter_cons] at ih ⊢
    split
    · simp [List.filterMap_cons, ih]
    · rename_i hne
      rw [ih, List.filterMap_cons]
      cases hre : rel e
      · rfl
      · exact absurd (by simpa using hr e (by simp [hre])) hne

theorem hasStream_onStream {L : Log} {s : Id} : Past.hasStream (onStream L s) s = Past.hasStream L s :=
  any_onStream fun _ => creates_stream
theorem ended_onStream {L : Log} {s : Id} : Past.ended (onStream L s) s = Past.ended L s :=
  any_onStream fun _ => ends_stream
theorem joined_onStream {L : Log} {s : Id} : Past.joined (onStream L s) s = Past.joined L s :=
  funext fun _ => any_onStream fun _ => joins_stream
theorem banned_onStream {L : Log} {s : Id} : Past.banned (onStream L s) s = Past.banned L s :=
  funext fun _ => any_onStream fun _ => bans_stream
theorem member_onStream {L : Log} {s : Id} : Past.member (onStream L s) s = Past.member L s :=
  funext fun _ => by simp [Past.member, joined_onStream, banned_onStream]
theorem latest_admin_onStream {L : Log} {s p : Id} :
    Past.latest (onStream L s) (adminRel s p) = Past.latest L (adminRel s p) := by
  unfold Past.latest; exact congrArg List.getLast? (filterMap_onStream fun _ => adminRel_stream)
theorem admin_onStream {L : Log} {s : Id} : Past.admin (onStream L s) s = Past.admin L s :=
  funext fun _ => by simp [Past.admin, member_onStream, latest_admin_onStream]
theorem otherAdmin_onStream {L : Log} {s : Id} : Past.otherAdmin (onStream L s) s = Past.otherAdmin L s :=
  funext fun p => by
    unfold Past.otherAdmin
    simp only [admin_onStream]
    apply any_onStream
    intro e h
    cases e <;> simp_all [Event.stream]

/-- **The view is local.** What the rules read about stream `s` from its own events is what they read from the whole
log. -/
theorem view_onStream (L : Log) (s : Id) : Past.view (onStream L s) s = Past.view L s := by
  simp only [Past.view, hasStream_onStream, ended_onStream, member_onStream, admin_onStream, banned_onStream,
    otherAdmin_onStream]

/-! ## So every rule, and the decision, is local -/

theorem ok_local (L : Log) (e : Event) : ok (onStream L e.stream) e = ok L e := by
  unfold ok; rw [view_onStream]

/-- **Deciding is local.** The first rule a candidate breaks, against the whole log, is the first it breaks against
its own stream's events. -/
theorem rejection_local (L : Log) (e : Event) : rejection (onStream L e.stream) e = rejection L e := by
  unfold rejection; rw [view_onStream]

end StreamCore
