-- Copyright (c) 2026 the proofbeta authors. All rights reserved. See LICENSE.
import StreamCore.Theorems

/-!
# Commands become events, and a sequence of commands becomes a valid log

The theorems about `respond`, `handle` and `run` (those about `toEvent` alone are in `Command.lean`). Those about
`respond` and `run` are `Service.lean`'s, at the core.
-/

namespace StreamCore

/-! ## One answer -/

/-- An answer is an acceptance exactly when the translation succeeds and every rule holds against the log before it. -/
theorem respond_accepted_iff {log : Log} {r : Request} {e : Event} :
    respond log r = .accepted e ↔ toEvent r.1 r.2.1 r.2.2 = .ok e ∧ ok log e = true :=
  Service.respond_accepted_iff (S := coreService)

/-- An answer is a refusal exactly with the translation's refusal, or the reason of the first rule that fails against
the log before it. -/
theorem respond_rejected_iff {log : Log} {r : Request} {x : String} :
    respond log r = .rejected x ↔
      toEvent r.1 r.2.1 r.2.2 = .error x ∨ ∃ e, toEvent r.1 r.2.1 r.2.2 = .ok e ∧ rejection log e = some x :=
  Service.respond_rejected_iff (S := coreService)

/-! ## `handle` appends exactly the translated event, or nothing -/

theorem handle_ok_iff {log log' : Log} {c : Id} {cmd : Command} {f : Fresh} {e : Event} :
    handle log c cmd f = .ok (e, log') ↔ toEvent c cmd f = .ok e ∧ ok log e = true ∧ log' = log ++ [e] := by
  unfold handle
  cases h : respond log (c, cmd, f) with
  | accepted e' =>
    simp only [Except.ok.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨(respond_accepted_iff.mp h).1, (respond_accepted_iff.mp h).2, rfl⟩
    · rintro ⟨ht, hok, rfl⟩
      have := (respond_accepted_iff (log := log) (r := (c, cmd, f))).mpr ⟨ht, hok⟩
      rw [h] at this; cases this; exact ⟨rfl, rfl⟩
  | rejected r =>
    constructor
    · intro h; cases h
    · rintro ⟨ht, hok, -⟩
      have := (respond_accepted_iff (log := log) (r := (c, cmd, f))).mpr ⟨ht, hok⟩
      rw [h] at this; cases this

/-- `handle` refuses with the translation's refusal, or else with the first rule that fails. -/
theorem handle_error_iff {log : Log} {c : Id} {cmd : Command} {f : Fresh} {r : String} :
    handle log c cmd f = .error r ↔
      toEvent c cmd f = .error r ∨ ∃ e, toEvent c cmd f = .ok e ∧ rejection log e = some r := by
  unfold handle
  cases h : respond log (c, cmd, f) with
  | accepted e' =>
    constructor
    · intro h; cases h
    · intro hr
      have := (respond_rejected_iff (log := log) (r := (c, cmd, f))).mpr hr
      rw [h] at this; cases this
  | rejected r' =>
    simp only [Except.error.injEq]
    constructor
    · rintro rfl; exact respond_rejected_iff.mp h
    · intro hr
      have := (respond_rejected_iff (log := log) (r := (c, cmd, f))).mpr hr
      rw [h] at this; cases this; rfl

/-! ## A sequence of commands -/

@[simp] theorem Response.event?_accepted (e : Event) : (Response.accepted e).event? = some e := rfl
@[simp] theorem Response.event?_rejected (r : String) : (Response.rejected r).event? = none := rfl

/-- One answer per request. -/
theorem runFrom_length (log : Log) (reqs : List Request) : (runFrom log reqs).2.length = reqs.length :=
  Service.runFrom_length (S := coreService) log reqs

/-- Running `reqs ++ more` is running `reqs`, then running `more` from the log `reqs` left. So a service that handles
requests one at a time, keeping the log in between, computes `run` over every request it ever received. -/
theorem runFrom_append (log : Log) (reqs more : List Request) :
    runFrom log (reqs ++ more) =
      ((runFrom (runFrom log reqs).1 more).1, (runFrom log reqs).2 ++ (runFrom (runFrom log reqs).1 more).2) :=
  Service.runFrom_append (S := coreService) log reqs more

theorem run_append (reqs more : List Request) :
    run (reqs ++ more) = ((runFrom (run reqs).1 more).1, (run reqs).2 ++ (runFrom (run reqs).1 more).2) :=
  Service.run_append (S := coreService) reqs more

/-- One request on top of a log: the log grows by the answer's event, if any. -/
theorem runFrom_one (log : Log) (r : Request) :
    runFrom log [r] = (log ++ (respond log r).event?.toList, [respond log r]) :=
  Service.runFrom_one (S := coreService) log r

/-- A refused request leaves the log exactly as it was. -/
theorem refused_keeps_log {log : Log} {c : Id} {cmd : Command} {f : Fresh} {r : String}
    (h : handle log c cmd f = .error r) : (runFrom log [(c, cmd, f)]).1 = log := by
  unfold handle at h
  rw [runFrom_one]
  cases hr : respond log (c, cmd, f) <;> rw [hr] at h
  · cases h
  · simp

/-- `handle` keeps a log valid. -/
theorem handle_valid {log log' : Log} {c : Id} {cmd : Command} {f : Fresh} {e : Event}
    (hv : Valid log) (h : handle log c cmd f = .ok (e, log')) : Valid log' := by
  obtain ⟨-, hok, rfl⟩ := handle_ok_iff.mp h
  exact .snoc hv hok

/-- **A repeated id is refused, never stored.** If any fresh id the host supplies was minted before, the request is
refused with `id_taken` (the first rule), whatever else it says. With `refused_keeps_log`, a UUID collision can cost a
refusal and never a change to the log. -/
theorem duplicate_refused {log : Log} {c : Id} {cmd : Command} {f : Fresh} {e : Event} {x : Id}
    (h : toEvent c cmd f = .ok e) (hx : x ∈ f) (hm : Past.minted log x = true) :
    handle log c cmd f = .error "id_taken" := by
  rw [← toEvent_minted h] at hx
  obtain ⟨c', u, m, rfl⟩ := minted_create hx
  rw [minted_eq_hasStream] at hm
  have hr : rejection log (.streamCreate c' x u m) = some "id_taken" := by
    simp [rejection, View.rejection, rules, idTaken, Past.view, Event.stream, hm]
  exact handle_error_iff.mpr (.inr ⟨_, h, hr⟩)

/-- **The log is the accepted requests' events, in request order.** The log `run` leaves from `log` is `log` followed
by the event of every accepted answer, in the order the requests came. -/
theorem runFrom_log_eq (log : Log) (reqs : List Request) :
    (runFrom log reqs).1 = log ++ (runFrom log reqs).2.filterMap Response.event? :=
  Service.runFrom_log_eq (S := coreService) log reqs

/-- **These commands, in this order, produce these events.** The log `run` produces is exactly the events of the
accepted answers, paired with the requests in order (`zip`), and every accepted event is the translation of its own
request. -/
theorem run_log_eq (reqs : List Request) :
    (run reqs).1 = (reqs.zip (run reqs).2).filterMap (fun rr => rr.2.event?) ∧
      ∀ r e, (r, Response.accepted e) ∈ reqs.zip (run reqs).2 → toEvent r.1 r.2.1 r.2.2 = .ok e :=
  Service.run_log_eq (S := coreService) reqs

/-- **Each answer is decided against the log of the requests before it.** For requests `pre ++ r :: post`, the answers
are those of `pre`, then `respond` for `r` against the log `pre` produced, then the rest; and that answer sits at
position `pre.length`. -/
theorem run_responses (pre : List Request) (r : Request) (post : List Request) :
    (run (pre ++ r :: post)).2 =
      (run pre).2 ++ respond (run pre).1 r :: (runFrom ((run pre).1 ++ (respond (run pre).1 r).event?.toList) post).2 ∧
    (run (pre ++ r :: post)).2[pre.length]? = some (respond (run pre).1 r) :=
  Service.run_responses (S := coreService) pre r post

/-- The log `run` produces from a valid log is valid; from the empty log, always. -/
theorem runFrom_valid {log : Log} (hv : Valid log) (reqs : List Request) : Valid (runFrom log reqs).1 :=
  Service.runFrom_valid hv reqs

theorem run_valid (reqs : List Request) : Valid (run reqs).1 := Service.run_valid (S := coreService) reqs

/-- **Completeness.** Every valid log is what `run` produces from some requests, every one of them accepted: one
command per event, by the event's actor, in the log's order. So the API can produce every valid log, and (by
`run_valid`) nothing else. -/
theorem run_complete {log : Log} (h : Valid log) :
    run (log.map toRequest) = (log, log.map Response.accepted) :=
  Service.run_complete h

/-! ## Events and commands determine each other -/

/-- **Events to commands to events.** Replaying the commands recovered from a valid log reproduces it exactly, and
every one of them is accepted. -/
theorem events_to_commands_to_events {log : Log} (h : Valid log) :
    (run (toRequests log)).1 = log ∧ AllAccepted (toRequests log) :=
  Service.events_to_commands_to_events h

theorem runFrom_all_accepted (log : Log) (rs : List Request)
    (h : ∀ x ∈ (runFrom log rs).2, ∃ e, x = .accepted e) :
    ∃ es, (runFrom log rs).1 = log ++ es ∧ toRequests es = rs :=
  Service.runFrom_all_accepted (S := coreService) log rs h

/-- **Commands to events to commands.** The commands recovered from the log of an all-accepted request list are
exactly those requests. -/
theorem commands_to_events_to_commands {reqs : List Request} (h : AllAccepted reqs) :
    toRequests (run reqs).1 = reqs :=
  Service.commands_to_events_to_commands h

/-- **A valid event log and the commands that produce it determine each other.** `run`, on request lists it accepts
in full, and `toRequests`, on valid logs, are mutually inverse: a bijection between all-accepted command logs and
valid event logs. -/
theorem commands_events_bijection :
    (∀ log, Valid log → AllAccepted (toRequests log) ∧ (run (toRequests log)).1 = log) ∧
    (∀ reqs, AllAccepted reqs → Valid (run reqs).1 ∧ toRequests (run reqs).1 = reqs) :=
  Service.commands_events_bijection (S := coreService)

end StreamCore
