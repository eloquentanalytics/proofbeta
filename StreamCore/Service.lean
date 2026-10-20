-- Copyright (c) 2026 the proofbeta authors. All rights reserved. See LICENSE.
import StreamCore.Wire

/-!
# A service: the machinery written and proved once

A `Service` is what the engine serves: its events, requests and per-stream states; commands becoming events and back;
its rules, with what they read (only the candidate's stream); a fast path; and its wire forms. Each field that is a
proposition is an obligation the service discharges once. Over any service this file defines, and proves once, what
the engine and the host rely on: the answer to a request and a sequence of requests (`respond`, `run`), the logs built
by acceptances only (`Valid`, decided by `check`), locality (`respond_local`, `run_project`), group commit and
compare-and-set appends (`batch_refines_run`, `cas_refines_run`), the fast path (`fold_sound`), stored rows and
startup replay (`rowFromJ_toJ`, `replayRows_sound`), and the engine's bookkeeping per stream (`entryRequest_spec`,
`entrySync_spec`).

Two kinds of service are built: the core (`coreService`, `Core.lean`), whose `run`, `Valid`, `respond`, ... are these
at it, and a layer with everything below it (`Layer.service`, `Layer.lean`: a layer on the core, on a layer, or two
layers side by side). The engine (`Engine/Step.lean`) serves any service.
-/

namespace StreamCore
open StreamCore.Wire

/-- What the engine serves, with the obligations its machinery is proved from. -/
structure Service where
  /-- The events, the requests (each carries its caller, command and fresh ids) and one stream's state. -/
  Ev : Type
  Req : Type
  St : Type
  [decEv : DecidableEq Ev]
  [decSt : DecidableEq St]
  -- Commands become events, and back.
  toEvent : Req → Except String Ev
  toRequest : Ev → Req
  toEvent_ok_iff : ∀ {r e}, toEvent r = .ok e ↔ toRequest e = r
  /-- The stream an event is on, and the stream a request is on. -/
  stream : Ev → Id
  reqStream : Req → Id
  toEvent_stream : ∀ {r e}, toEvent r = .ok e → stream e = reqStream r
  -- The rules: the first that fails against the past, and whether all hold.
  ok : List Ev → Ev → Bool
  rejection : List Ev → Ev → Option String
  rejection_none_iff : ∀ past e, rejection past e = none ↔ ok past e = true
  /-- Only the events of the candidate's own stream matter. -/
  rejection_local : ∀ past e, rejection (past.filter (stream · == stream e)) e = rejection past e
  -- The fast path: a per-stream state folded event by event, and the decision from it.
  init : Id → St
  step : St → Ev → St
  rejectionS : St → Ev → Option String
  /-- The fast path is the specification, for every past. -/
  rejectionS_fold : ∀ past e, rejectionS (past.foldl step (init (stream e))) e = rejection past e
  /-- The stream a state is of. -/
  stStream : St → Id
  stStream_init : ∀ s, stStream (init s) = s
  stStream_step : ∀ st e, stStream (step st e) = stStream st
  -- The wire.
  requestWf : Req → Bool
  eventWf : Ev → Bool
  eventWf_eq : ∀ e, eventWf e = requestWf (toRequest e)
  requestToJ : Req → J
  requestFromJ : J → Except String Req
  requestFromJ_toJ : ∀ r, requestWf r = true → requestFromJ (requestToJ r) = .ok r
  requestFromJ_wf : ∀ {j r}, requestFromJ j = .ok r → requestWf r = true
  eventToJ : Ev → J
  eventFromJ : J → Except String Ev
  eventFromJ_toJ : ∀ e, eventWf e = true → eventFromJ (eventToJ e) = .ok e
  eventFromJ_wf : ∀ {j e}, eventFromJ j = .ok e → eventWf e = true
  -- Snapshots and reads.
  stateToJ : St → J
  stateFromJ : J → Except String St
  stateFromJ_toJ : ∀ st, stateFromJ (stateToJ st) = .ok st
  /-- What a read of a stream answers, from its state. -/
  streamSJ : St → J

attribute [instance] Service.decEv Service.decSt

/-! ## The definitions -/

namespace Service
variable (S : Service)

abbrev Log := List S.Ev

/-- What a caller hears back. -/
inductive Response where
  | accepted (e : S.Ev)
  | rejected (reason : String)
  deriving DecidableEq

/-- The event of an accepted response. -/
def Response.event? {S : Service} : S.Response → Option S.Ev
  | .accepted e => some e
  | .rejected _ => none

/-- The answer to one request from a judge of events: the translation's refusal, or the judge's, or acceptance. -/
def answer (judge : S.Ev → Option String) (r : S.Req) : S.Response :=
  match S.toEvent r with
  | .error x => .rejected x
  | .ok e =>
    match judge e with
    | some x => .rejected x
    | none => .accepted e

/-- The answer to a request against a log. -/
def respond (log : S.Log) : S.Req → S.Response := S.answer (S.rejection log)

/-- A log built only by accepting candidates. -/
inductive Valid : S.Log → Prop
  | nil : Valid []
  | snoc {log : S.Log} {e : S.Ev} : Valid log → S.ok log e = true → Valid (log ++ [e])

/-- Run the rules over every prefix. -/
def checkFrom (past : S.Log) : S.Log → Bool
  | [] => true
  | e :: es => S.ok past e && checkFrom (past ++ [e]) es

def check (log : S.Log) : Bool := S.checkFrom [] log

/-- `respond` from a log over a sequence of requests, left to right, the log growing by each accepted event. -/
def runFrom : S.Log → List S.Req → S.Log × List S.Response
  | log, [] => (log, [])
  | log, r :: rs =>
    let x := S.respond log r
    let y := runFrom (log ++ x.event?.toList) rs
    (y.1, x :: y.2)

/-- Every request the service ever received, in order, run from the empty log. -/
def run (reqs : List S.Req) : S.Log × List S.Response := S.runFrom [] reqs

def toRequests (log : S.Log) : List S.Req := log.map S.toRequest

/-- Every response of `run reqs` is an acceptance. -/
def AllAccepted (reqs : List S.Req) : Prop := ∀ x ∈ (S.run reqs).2, ∃ e, x = .accepted e

/-- The events of stream `s`, in order. -/
def onStream (L : S.Log) (s : Id) : S.Log := L.filter (S.stream · == s)

/-- A store of per-stream logs. Each stream is a list, so its positions are contiguous from 0. -/
abbrev Store := Id → S.Log

def Store.empty : S.Store := fun _ => []

def Store.set {S : Service} (st : S.Store) (s : Id) (l : S.Log) : S.Store := fun x => if x = s then l else st x

/-- What a validator's batch comes to: committed with these answers, or a lost compare-and-set. -/
inductive Outcome where
  | committed (answers : List S.Response)
  | conflict
  deriving DecidableEq

/-- One validator's batch on stream `s`: it read the stream when it had `n` events, decided the requests one after
another from there, and appends every accepted event with one compare-and-set at `n`. Its answers, refusals
included, are delivered only if that append commits. -/
def attemptBatch (st : S.Store) (s : Id) (reqs : List S.Req) (n : Nat) : S.Store × S.Outcome :=
  let decided := S.runFrom ((st s).take n) reqs
  if (st s).length = n then (Store.set st s decided.1, .committed decided.2) else (st, .conflict)

/-- Any interleaving of validators: batches in commit order, each with its stream and the length it read at. -/
def execB : S.Store → List (Id × List S.Req × Nat) → S.Store × List (Id × List S.Req × S.Outcome)
  | st, [] => (st, [])
  | st, (s, reqs, n) :: rest =>
    let (st', o) := S.attemptBatch st s reqs n
    let x := execB st' rest
    (x.1, (s, reqs, o) :: x.2)

/-- The requests of the batches that committed on stream `s`, in commit order. -/
def committedReqs : List (Id × List S.Req × S.Outcome) → Id → List S.Req
  | [], _ => []
  | (s', reqs, .committed _) :: rest, s => (if s' = s then reqs else []) ++ committedReqs rest s
  | (_, _, .conflict) :: rest, s => committedReqs rest s

/-- The answers delivered on stream `s`, in commit order. -/
def deliveredAnswers : List (Id × List S.Req × S.Outcome) → Id → List S.Response
  | [], _ => []
  | (s', _, .committed as) :: rest, s => (if s' = s then as else []) ++ deliveredAnswers rest s
  | (_, _, .conflict) :: rest, s => deliveredAnswers rest s

/-- The state of stream `s` after a log. -/
def fold (s : Id) (L : S.Log) : S.St := L.foldl S.step (S.init s)

/-- The answer to a request, from the state. -/
def respondS (st : S.St) : S.Req → S.Response := S.answer (S.rejectionS st)

/-- One request: the answer and the next state. -/
def stepS (st : S.St) (r : S.Req) : S.St × S.Response :=
  let resp := S.respondS st r
  match resp with
  | .accepted e => (S.step st e, resp)
  | .rejected _ => (st, resp)

def runS : S.St → List S.Req → S.St × List S.Response
  | st, [] => (st, [])
  | st, r :: rs => let (st', x) := S.stepS st r; let y := runS st' rs; (y.1, x :: y.2)

/-- The engine's answer to one line. -/
def responseToJ : S.Response → J
  | .accepted e => .obj [("accept", .bool true), ("event", S.eventToJ e)]
  | .rejected r => .obj [("accept", .bool false), ("reason", .str r)]

/-- A stored row: the request the engine accepted and the event it returned. -/
def rowFromJ (j : J) : Except String (S.Req × S.Ev) := do
  let kvs ← fields "stored" j
  onlyKeys "stored" kvs ["request", "event"]
  let some r := get? kvs "request" | throw "stored.request: missing"
  let some e := get? kvs "event" | throw "stored.event: missing"
  return (← S.requestFromJ r, ← S.eventFromJ e)

def rowToJ : S.Req × S.Ev → J
  | (r, e) => .obj [("request", S.requestToJ r), ("event", S.eventToJ e)]

/-- One parsed line against the log: decode, `respond`, encode; the log grows by the accepted event (`runFrom` on one
request). A line that does not decode changes nothing. -/
def stepJ (log : S.Log) (j : J) : S.Log × J :=
  match S.requestFromJ j with
  | .error d => (log, malformedJ d)
  | .ok r => let x := S.respond log r; (log ++ x.event?.toList, S.responseToJ x)

/-- Replay stored rows from a log, one at a time: each stored request must be accepted and give exactly the stored
event. -/
def replayFrom (log : S.Log) : List (S.Req × S.Ev) → Except String S.Log
  | [] => .ok log
  | (r, e) :: rows =>
    match S.respond log r with
    | .accepted e' => if e' = e then replayFrom (log ++ [e']) rows
                      else .error notTranslation
    | .rejected reason => .error s!"a stored request is refused ({reason}): the stored log is not Valid"

def replayRows (rows : List (S.Req × S.Ev)) : Except String S.Log := S.replayFrom [] rows

/-- Catch-up from stored rows, through the state. -/
def replaySFrom (st : S.St) : List (S.Req × S.Ev) → Except String S.St
  | [] => .ok st
  | (r, e) :: rows =>
    if S.reqStream r = S.stStream st then
      match S.stepS st r with
      | (st', .accepted e') =>
        if e' = e then replaySFrom st' rows else .error notTranslation
      | (_, .rejected reason) => .error s!"a stored request is refused ({reason}): the stored stream is not Valid"
    else .error "a stored row is on another stream"

def replaySRows (s : Id) (rows : List (S.Req × S.Ev)) : Except String S.St := S.replaySFrom (S.init s) rows

/-- What the engine keeps for a stream: a state and the number of events it folds. The specification of an entry
for stream `s` after log `L` is `Entry.ofLog s L`. -/
structure Entry where
  st : S.St
  len : Nat
  deriving DecidableEq

def Entry.ofLog (s : Id) (L : S.Log) : S.Entry := ⟨S.fold s L, L.length⟩

/-- A stream the engine has never seen: the entry of the empty log. -/
def Entry.empty (s : Id) : S.Entry := ⟨S.init s, 0⟩

/-- Decide one request: the new entry, the answer, and the position it was decided at. -/
def entryRequest (en : S.Entry) (r : S.Req) : S.Entry × S.Response × Nat :=
  let (st', resp) := S.stepS en.st r
  (⟨st', match resp with | .accepted _ => en.len + 1 | .rejected _ => en.len⟩, resp, en.len)

/-- Fold stored rows onto an entry that must fold exactly `k` events. -/
def entrySync (en : S.Entry) (k : Nat) (rows : List (S.Req × S.Ev)) : Except String S.Entry :=
  if en.len = k then (S.replaySFrom en.st rows).map fun st' => ⟨st', en.len + rows.length⟩
  else .error "out_of_sync"

end Service

/-! ## The theorems, once for every service -/

namespace Service
variable {S : Service}

@[simp] theorem Response.event?_accepted (e : S.Ev) : (Response.accepted e : S.Response).event? = some e := rfl
@[simp] theorem Response.event?_rejected (r : String) : (Response.rejected r : S.Response).event? = none := rfl

theorem except_map_ok {α β ε} {x : Except ε α} {f : α → β} {y : β} :
    x.map f = .ok y ↔ ∃ a, x = .ok a ∧ f a = y := by
  cases x <;> simp [Except.map]

/-! ### `Valid` and `check` -/

theorem Valid.inv {log : S.Log} {e : S.Ev} (h : S.Valid (log ++ [e])) : S.Valid log ∧ S.ok log e = true := by
  suffices ∀ l, S.Valid l → l = log ++ [e] → S.Valid log ∧ S.ok log e = true from this _ h rfl
  intro l hl heq
  cases hl with
  | nil => simp at heq
  | snoc hv hok =>
    obtain ⟨rfl, h2⟩ := List.append_inj' heq rfl
    cases h2
    exact ⟨hv, hok⟩

/-- Every prefix of a valid log is valid. -/
theorem Valid.prefix {log : S.Log} (h : S.Valid log) : ∀ a b, log = a ++ b → S.Valid a := by
  induction h with
  | nil => intro a b hab; simp at hab; simp [hab.1]; exact .nil
  | @snoc log e hv hok ih =>
    intro a b hab
    rcases List.eq_nil_or_concat b with rfl | ⟨b', z, rfl⟩
    · simp at hab; subst hab; exact .snoc hv hok
    · have := List.append_inj' (by simpa [List.append_assoc] using hab : log ++ [e] = (a ++ b') ++ [z]) rfl
      exact ih a b' this.1

/-- The rules held for every event at the moment it was accepted. -/
theorem Valid.okAt {pre post : S.Log} {e : S.Ev} (h : S.Valid (pre ++ e :: post)) : S.ok pre e = true :=
  (Valid.inv (h.prefix (pre ++ [e]) post (by simp))).2

theorem checkFrom_iff (past : S.Log) (hp : S.Valid past) :
    ∀ es, S.checkFrom past es = true ↔ S.Valid (past ++ es) := by
  intro es
  induction es generalizing past with
  | nil => simp [checkFrom, hp]
  | cons e es ih =>
    simp only [checkFrom, Bool.and_eq_true]
    constructor
    · rintro ⟨hok, hrest⟩
      have := (ih (past ++ [e]) (.snoc hp hok)).mp hrest
      simpa [List.append_assoc] using this
    · intro hv
      have hv' : S.Valid (past ++ e :: es) := by simpa using hv
      have hok := hv'.okAt
      refine ⟨hok, (ih (past ++ [e]) (.snoc hp hok)).mpr ?_⟩
      simpa [List.append_assoc] using hv

/-- `check` decides `Valid`. -/
theorem check_iff_valid (log : S.Log) : S.check log = true ↔ S.Valid log := by
  simpa [check] using checkFrom_iff [] .nil log

/-! ### One answer -/

theorem toEvent_toRequest (e : S.Ev) : S.toEvent (S.toRequest e) = .ok e := S.toEvent_ok_iff.mpr rfl

theorem answer_accepted_iff {judge : S.Ev → Option String} {r : S.Req} {e : S.Ev} :
    S.answer judge r = .accepted e ↔ S.toEvent r = .ok e ∧ judge e = none := by
  unfold answer
  cases S.toEvent r with
  | error x => simp
  | ok e0 => cases h : judge e0 <;> simp [h] <;> (try constructor) <;> (try rintro rfl) <;> simp_all

/-- An answer is an acceptance exactly when the translation succeeds and every rule holds against the log before it. -/
theorem respond_accepted_iff {log : S.Log} {r : S.Req} {e : S.Ev} :
    S.respond log r = .accepted e ↔ S.toEvent r = .ok e ∧ S.ok log e = true := by
  rw [respond, answer_accepted_iff, S.rejection_none_iff]

/-- An answer is a refusal exactly with the translation's refusal, or the reason of the first rule that fails. -/
theorem respond_rejected_iff {log : S.Log} {r : S.Req} {x : String} :
    S.respond log r = .rejected x ↔
      S.toEvent r = .error x ∨ ∃ e, S.toEvent r = .ok e ∧ S.rejection log e = some x := by
  simp only [respond, answer]
  cases S.toEvent r with
  | error x' => simp
  | ok e0 => cases hr : S.rejection log e0 <;> simp [hr]

/-! ### A sequence of requests -/

/-- One answer per request. -/
theorem runFrom_length (log : S.Log) (reqs : List S.Req) : (S.runFrom log reqs).2.length = reqs.length := by
  induction reqs generalizing log with
  | nil => rfl
  | cons r rs ih => simp [runFrom, ih]

/-- Running `reqs ++ more` is running `reqs`, then running `more` from the log `reqs` left. -/
theorem runFrom_append (log : S.Log) (reqs more : List S.Req) :
    S.runFrom log (reqs ++ more) =
      ((S.runFrom (S.runFrom log reqs).1 more).1,
        (S.runFrom log reqs).2 ++ (S.runFrom (S.runFrom log reqs).1 more).2) := by
  induction reqs generalizing log with
  | nil => rfl
  | cons r rs ih => simp [runFrom, ih]

theorem run_append (reqs more : List S.Req) :
    S.run (reqs ++ more) =
      ((S.runFrom (S.run reqs).1 more).1, (S.run reqs).2 ++ (S.runFrom (S.run reqs).1 more).2) :=
  runFrom_append [] reqs more

/-- One request on top of a log: the log grows by the answer's event, if any. -/
theorem runFrom_one (log : S.Log) (r : S.Req) :
    S.runFrom log [r] = (log ++ (S.respond log r).event?.toList, [S.respond log r]) := by
  simp [runFrom]

/-- The log `runFrom` leaves is the log followed by the event of every accepted answer, in request order. -/
theorem runFrom_log_eq (log : S.Log) (reqs : List S.Req) :
    (S.runFrom log reqs).1 = log ++ (S.runFrom log reqs).2.filterMap Response.event? := by
  induction reqs generalizing log with
  | nil => simp [runFrom]
  | cons r rs ih =>
    simp only [runFrom]
    rw [ih, List.filterMap_cons]
    cases S.respond log r <;> simp [Response.event?]

/-- These requests, in this order, produce these events: the accepted answers' events, each the translation of its
own request. -/
theorem run_log_eq (reqs : List S.Req) :
    (S.run reqs).1 = (reqs.zip (S.run reqs).2).filterMap (fun rr => rr.2.event?) ∧
      ∀ r e, (r, Response.accepted e) ∈ reqs.zip (S.run reqs).2 → S.toEvent r = .ok e := by
  have key : ∀ log (rs : List S.Req),
      (rs.zip (S.runFrom log rs).2).filterMap (fun rr => rr.2.event?) =
        (S.runFrom log rs).2.filterMap Response.event? ∧
      ∀ r e, (r, Response.accepted e) ∈ rs.zip (S.runFrom log rs).2 → S.toEvent r = .ok e := by
    intro log rs
    induction rs generalizing log with
    | nil => simp [runFrom]
    | cons r rs ih =>
      obtain ⟨ih1, ih2⟩ := ih (log ++ (S.respond log r).event?.toList)
      constructor
      · simp only [runFrom, List.zip_cons_cons, List.filterMap_cons, ih1]
      · intro r' e' hm
        simp only [runFrom, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, hh⟩ | hm
        · exact (respond_accepted_iff.mp hh.symm).1
        · exact ih2 r' e' hm
  obtain ⟨k1, k2⟩ := key [] reqs
  refine ⟨?_, k2⟩
  show (S.runFrom [] reqs).1 = List.filterMap _ (reqs.zip (S.runFrom [] reqs).2)
  rw [k1, runFrom_log_eq]; simp

/-- Each answer is decided against the log of the requests before it. -/
theorem run_responses (pre : List S.Req) (r : S.Req) (post : List S.Req) :
    (S.run (pre ++ r :: post)).2 =
      (S.run pre).2 ++ S.respond (S.run pre).1 r ::
        (S.runFrom ((S.run pre).1 ++ (S.respond (S.run pre).1 r).event?.toList) post).2 ∧
    (S.run (pre ++ r :: post)).2[pre.length]? = some (S.respond (S.run pre).1 r) := by
  have h1 : (S.run (pre ++ r :: post)).2 =
      (S.run pre).2 ++ S.respond (S.run pre).1 r ::
        (S.runFrom ((S.run pre).1 ++ (S.respond (S.run pre).1 r).event?.toList) post).2 := by
    rw [run_append]; simp [runFrom]
  refine ⟨h1, ?_⟩
  rw [h1, List.getElem?_append_right (by simp [run, runFrom_length])]
  simp [run, runFrom_length]

/-- The log `runFrom` produces from a valid log is valid. -/
theorem runFrom_valid {log : S.Log} (hv : S.Valid log) (reqs : List S.Req) : S.Valid (S.runFrom log reqs).1 := by
  induction reqs generalizing log with
  | nil => exact hv
  | cons r rs ih =>
    simp only [runFrom]
    cases h : S.respond log r with
    | accepted e => exact ih (.snoc hv (respond_accepted_iff.mp h).2)
    | rejected x => exact ih (by simpa using hv)

/-- The requests produce only valid logs. -/
theorem run_valid (reqs : List S.Req) : S.Valid (S.run reqs).1 := runFrom_valid .nil reqs

/-- **Completeness.** Every valid log is what `run` produces from one request per event, all accepted. -/
theorem run_complete {log : S.Log} (h : S.Valid log) :
    S.run (log.map S.toRequest) = (log, log.map Response.accepted) := by
  induction h with
  | nil => rfl
  | @snoc l e hv hok ih =>
    rw [List.map_append, run_append, ih, List.map_singleton, runFrom_one]
    have : S.respond l (S.toRequest e) = .accepted e := respond_accepted_iff.mpr ⟨toEvent_toRequest e, hok⟩
    simp [this, Response.event?]

/-! ### Events and requests determine each other -/

/-- Replaying the requests recovered from a valid log reproduces it exactly, and every one of them is accepted. -/
theorem events_to_commands_to_events {log : S.Log} (h : S.Valid log) :
    (S.run (S.toRequests log)).1 = log ∧ S.AllAccepted (S.toRequests log) := by
  have := run_complete h
  refine ⟨by rw [toRequests, this], ?_⟩
  intro x hx
  rw [toRequests, this] at hx
  simp only [List.mem_map] at hx
  obtain ⟨e, -, rfl⟩ := hx
  exact ⟨e, rfl⟩

theorem runFrom_all_accepted (log : S.Log) (rs : List S.Req)
    (h : ∀ x ∈ (S.runFrom log rs).2, ∃ e, x = .accepted e) :
    ∃ es, (S.runFrom log rs).1 = log ++ es ∧ S.toRequests es = rs := by
  induction rs generalizing log with
  | nil => exact ⟨[], by simp [runFrom], rfl⟩
  | cons r rs ih =>
    simp only [runFrom] at h ⊢
    cases hr : S.respond log r with
    | accepted e =>
      rw [hr] at h
      obtain ⟨es, h1, h2⟩ := ih (log ++ [e]) (fun x hx => h x (List.mem_cons_of_mem _ hx))
      refine ⟨e :: es, by simp [h1], ?_⟩
      simp only [toRequests, List.map_cons] at h2 ⊢
      rw [h2, S.toEvent_ok_iff.mp (respond_accepted_iff.mp hr).1]
    | rejected reason =>
      rw [hr] at h
      obtain ⟨e, he⟩ := h (.rejected reason) List.mem_cons_self
      cases he

/-- The requests recovered from the log of an all-accepted request list are exactly those requests. -/
theorem commands_to_events_to_commands {reqs : List S.Req} (h : S.AllAccepted reqs) :
    S.toRequests (S.run reqs).1 = reqs := by
  obtain ⟨es, h1, h2⟩ := runFrom_all_accepted [] reqs h
  unfold run; rw [h1]; simpa using h2

/-- A valid log and the requests that produce it determine each other. -/
theorem commands_events_bijection :
    (∀ log, S.Valid log → S.AllAccepted (S.toRequests log) ∧ (S.run (S.toRequests log)).1 = log) ∧
    (∀ reqs, S.AllAccepted reqs → S.Valid (S.run reqs).1 ∧ S.toRequests (S.run reqs).1 = reqs) :=
  ⟨fun _ h => ⟨(events_to_commands_to_events h).2, (events_to_commands_to_events h).1⟩,
   fun reqs h => ⟨run_valid reqs, commands_to_events_to_commands h⟩⟩

/-! ### Deciding is local to a stream -/

theorem rejection_onStream (L : S.Log) (e : S.Ev) : S.rejection (S.onStream L (S.stream e)) e = S.rejection L e :=
  S.rejection_local L e

/-- The answer to a request against the whole log is its answer against its stream's events. -/
theorem respond_local (L : S.Log) (r : S.Req) : S.respond (S.onStream L (S.reqStream r)) r = S.respond L r := by
  simp only [respond, answer]
  cases h : S.toEvent r with
  | error x => rfl
  | ok e => simp only []; rw [← S.toEvent_stream h, rejection_onStream]

theorem onStream_append_other {L : S.Log} {e : S.Ev} {s : Id} (h : S.stream e ≠ s) :
    S.onStream (L ++ [e]) s = S.onStream L s := by
  simp [onStream, List.filter_append, h]

theorem onStream_append_same {L : S.Log} {e : S.Ev} {s : Id} (h : S.stream e = s) :
    S.onStream (L ++ [e]) s = S.onStream L s ++ [e] := by
  simp [onStream, List.filter_append, h]

theorem respond_event_stream {L : S.Log} {r : S.Req} {e : S.Ev} (h : S.respond L r = .accepted e) :
    S.stream e = S.reqStream r :=
  S.toEvent_stream (respond_accepted_iff.mp h).1

theorem runFrom_project (L : S.Log) (reqs : List S.Req) (s : Id) :
    S.onStream (S.runFrom L reqs).1 s = (S.runFrom (S.onStream L s) (reqs.filter (S.reqStream · == s))).1 ∧
    ((reqs.zip (S.runFrom L reqs).2).filter (S.reqStream ·.1 == s)).map (·.2) =
      (S.runFrom (S.onStream L s) (reqs.filter (S.reqStream · == s))).2 := by
  induction reqs generalizing L with
  | nil => simp [runFrom]
  | cons r rs ih =>
    simp only [runFrom]
    obtain ⟨ih1, ih2⟩ := ih (L ++ (S.respond L r).event?.toList)
    by_cases hs : S.reqStream r = s
    · have hfil : (r :: rs).filter (S.reqStream · == s) = r :: rs.filter (S.reqStream · == s) := by simp [hs]
      rw [hfil]
      simp only [runFrom]
      have hloc : S.respond (S.onStream L s) r = S.respond L r := by rw [← hs]; exact respond_local L r
      rw [hloc]
      have hlog : S.onStream (L ++ (S.respond L r).event?.toList) s =
          S.onStream L s ++ (S.respond L r).event?.toList := by
        cases hr : S.respond L r with
        | accepted e => simp [Response.event?, onStream_append_same (hs ▸ respond_event_stream hr)]
        | rejected x => simp [Response.event?]
      rw [hlog] at ih1 ih2
      refine ⟨ih1, ?_⟩
      simp [List.zip_cons_cons, hs, ih2]
    · have hfil : (r :: rs).filter (S.reqStream · == s) = rs.filter (S.reqStream · == s) := by simp [hs]
      rw [hfil]
      have hlog : S.onStream (L ++ (S.respond L r).event?.toList) s = S.onStream L s := by
        cases hr : S.respond L r with
        | accepted e =>
          simp only [Response.event?, Option.toList_some]
          exact onStream_append_other (by rw [respond_event_stream hr]; exact hs)
        | rejected x => simp [Response.event?]
      rw [hlog] at ih1 ih2
      refine ⟨ih1, ?_⟩
      simp [List.zip_cons_cons, hs, ih2]

/-- **A stream's log is `run` of its own requests**, with the same answers. -/
theorem run_project (reqs : List S.Req) (s : Id) :
    S.onStream (S.run reqs).1 s = (S.run (reqs.filter (S.reqStream · == s))).1 ∧
    ((reqs.zip (S.run reqs).2).filter (S.reqStream ·.1 == s)).map (·.2) =
      (S.run (reqs.filter (S.reqStream · == s))).2 := by
  have := runFrom_project [] reqs s
  simpa [run, onStream] using this

/-! ### Group commit and compare-and-set appends refine `run` -/

/-- **Group commit.** Deciding a batch in order from `(run before).1` and appending the accepted events at once is
`run (before ++ reqs)`. -/
theorem batch_refines_run (before reqs : List S.Req) :
    (S.run before).1 ++ (S.runFrom (S.run before).1 reqs).2.filterMap Response.event? = (S.run (before ++ reqs)).1 ∧
    (S.run (before ++ reqs)).2 = (S.run before).2 ++ (S.runFrom (S.run before).1 reqs).2 := by
  rw [run_append]
  exact ⟨(runFrom_log_eq _ reqs).symm, rfl⟩

/-- A lost compare-and-set changes nothing and answers nothing. -/
theorem attemptBatch_conflict {st : S.Store} {s : Id} {reqs : List S.Req} {n : Nat} {st' : S.Store}
    (h : S.attemptBatch st s reqs n = (st', .conflict)) : st' = st := by
  unfold attemptBatch at h
  split at h <;> simp_all

theorem committedReqs_append (l₁ l₂ : List (Id × List S.Req × S.Outcome)) (s : Id) :
    S.committedReqs (l₁ ++ l₂) s = S.committedReqs l₁ s ++ S.committedReqs l₂ s := by
  induction l₁ with
  | nil => rfl
  | cons x xs ih => obtain ⟨s', r, o⟩ := x; cases o <;> simp [committedReqs, ih]

theorem deliveredAnswers_append (l₁ l₂ : List (Id × List S.Req × S.Outcome)) (s : Id) :
    S.deliveredAnswers (l₁ ++ l₂) s = S.deliveredAnswers l₁ s ++ S.deliveredAnswers l₂ s := by
  induction l₁ with
  | nil => rfl
  | cons x xs ih => obtain ⟨s', r, o⟩ := x; cases o <;> simp [deliveredAnswers, ih]

theorem execB_spec (st : S.Store) (atts : List (Id × List S.Req × Nat)) (pre : List (Id × List S.Req × S.Outcome))
    (hinv : ∀ s, st s = (S.run (S.committedReqs pre s)).1 ∧
      S.deliveredAnswers pre s = (S.run (S.committedReqs pre s)).2) :
    ∀ s, (S.execB st atts).1 s = (S.run (S.committedReqs (pre ++ (S.execB st atts).2) s)).1 ∧
      S.deliveredAnswers (pre ++ (S.execB st atts).2) s = (S.run (S.committedReqs (pre ++ (S.execB st atts).2) s)).2 := by
  induction atts generalizing st pre with
  | nil => simpa [execB] using hinv
  | cons a rest ih =>
    obtain ⟨s0, reqs, n⟩ := a
    simp only [execB]
    cases hat : S.attemptBatch st s0 reqs n with
    | mk st' o =>
      simp only []
      have key : ∀ s, st' s = (S.run (S.committedReqs (pre ++ [(s0, reqs, o)]) s)).1 ∧
          S.deliveredAnswers (pre ++ [(s0, reqs, o)]) s = (S.run (S.committedReqs (pre ++ [(s0, reqs, o)]) s)).2 := by
        intro s
        unfold attemptBatch at hat
        split at hat
        · rename_i hlen
          simp only [Prod.mk.injEq] at hat
          obtain ⟨rfl, rfl⟩ := hat
          rw [← hlen, List.take_length]
          rw [committedReqs_append, deliveredAnswers_append]
          by_cases hs : s0 = s
          · subst hs
            obtain ⟨h1, h2⟩ := hinv s0
            simp only [committedReqs, deliveredAnswers, ite_true, List.append_nil, Store.set]
            obtain ⟨b1, b2⟩ := batch_refines_run (S.committedReqs pre s0) reqs
            rw [← h1] at b1 b2
            refine ⟨?_, ?_⟩
            · rw [← b1]; exact runFrom_log_eq (st s0) reqs
            · rw [h2, b2]
          · simp only [committedReqs, deliveredAnswers, hs, ite_false, List.append_nil, Store.set]
            simpa [Ne.symm hs] using hinv s
        · simp only [Prod.mk.injEq] at hat
          obtain ⟨rfl, rfl⟩ := hat
          rw [committedReqs_append, deliveredAnswers_append]
          simpa [committedReqs, deliveredAnswers] using hinv s
      have := ih st' (pre ++ [(s0, reqs, o)]) key
      simpa [List.append_assoc] using this

/-- **Compare-and-set batch appends refine `run`.** Starting from empty streams, under any interleaving of validators
(each reads a stream at some length, decides a batch of requests one after another from what it read, and appends the
accepted events with one compare-and-set at that length), every stream holds exactly `run` of the requests of the
batches that committed on it, in commit order, and the answers delivered on it, refusals included, are exactly
`run`'s answers to those requests. A lost compare-and-set changes nothing and answers nothing
(`attemptBatch_conflict`). A single request is a batch of one. -/
theorem cas_refines_run (atts : List (Id × List S.Req × Nat)) (s : Id) :
    (S.execB (Store.empty S) atts).1 s = (S.run (S.committedReqs (S.execB (Store.empty S) atts).2 s)).1 ∧
    S.deliveredAnswers (S.execB (Store.empty S) atts).2 s =
      (S.run (S.committedReqs (S.execB (Store.empty S) atts).2 s)).2 := by
  have := execB_spec (Store.empty S) atts [] (fun s => ⟨rfl, rfl⟩) s
  simpa using this

/-- **Each delivered answer is `respond` on the stream as it stood**: the committed prefix the validator read plus the
events accepted earlier in the batch. -/
theorem batch_answer (L : S.Log) (pre : List S.Req) (r : S.Req) (post : List S.Req) :
    (S.runFrom L (pre ++ r :: post)).2[pre.length]? = some (S.respond (S.runFrom L pre).1 r) := by
  rw [runFrom_append L pre (r :: post), List.getElem?_append_right (by simp [runFrom_length]), runFrom_length,
    Nat.sub_self]
  simp [runFrom]

/-! ### The fast path is the specification -/

theorem fold_snoc (s : Id) (L : S.Log) (e : S.Ev) : S.fold s (L ++ [e]) = S.step (S.fold s L) e := by
  simp [fold, List.foldl_append]

/-- **Snapshots.** Folding the rest of a log onto the fold of its first part is folding the whole log. -/
theorem snapshot_equiv (s : Id) (L₁ L₂ : S.Log) : S.fold s (L₁ ++ L₂) = L₂.foldl S.step (S.fold s L₁) := by
  simp [fold, List.foldl_append]

theorem fold_stStream (s : Id) (L : S.Log) : S.stStream (S.fold s L) = s := by
  unfold fold
  suffices ∀ st : S.St, S.stStream (L.foldl S.step st) = S.stStream st by rw [this, S.stStream_init]
  induction L with
  | nil => intro; rfl
  | cons e es ih => intro st; simp [List.foldl_cons, ih, S.stStream_step]

theorem rejectionS_fold' (L : S.Log) (e : S.Ev) : S.rejectionS (S.fold (S.stream e) L) e = S.rejection L e :=
  S.rejectionS_fold L e

/-- **The fast path is the specification.** For every log and every request, deciding from the fold of the log onto
the request's stream gives exactly the answer against the log. No hypothesis. -/
theorem fold_sound (L : S.Log) (r : S.Req) : S.respondS (S.fold (S.reqStream r) L) r = S.respond L r := by
  simp only [respondS, respond, answer]
  cases h : S.toEvent r with
  | error x => rfl
  | ok e => simp only []; rw [← S.toEvent_stream h, rejectionS_fold']

/-- So a decision from a snapshot and the events after it is the decision from the whole log. -/
theorem snapshot_sound (L₁ L₂ : S.Log) (r : S.Req) :
    S.respondS (L₂.foldl S.step (S.fold (S.reqStream r) L₁)) r = S.respond (L₁ ++ L₂) r := by
  rw [← snapshot_equiv, fold_sound]

theorem stepS_eq (s : Id) (L : S.Log) (r : S.Req) (hr : S.reqStream r = s) :
    S.stepS (S.fold s L) r = (S.fold s (L ++ (S.respond L r).event?.toList), S.respond L r) := by
  have hresp : S.respondS (S.fold s L) r = S.respond L r := by rw [← hr]; exact fold_sound L r
  simp only [stepS, hresp]
  cases S.respond L r with
  | accepted e => simp [Response.event?, fold_snoc]
  | rejected x => simp [Response.event?]

/-- **The fast path runs the same service.** For requests all on stream `s`, running them through the state from the
fold of a log gives `runFrom`'s answers, and ends in the fold of the log `runFrom` ends in. -/
theorem runS_eq_run (s : Id) (L : S.Log) (reqs : List S.Req) (hs : ∀ r ∈ reqs, S.reqStream r = s) :
    S.runS (S.fold s L) reqs = (S.fold s (S.runFrom L reqs).1, (S.runFrom L reqs).2) := by
  induction reqs generalizing L with
  | nil => rfl
  | cons r rs ih =>
    have ih' := ih (L ++ (S.respond L r).event?.toList) (fun x hx => hs x (List.mem_cons_of_mem _ hx))
    simp only [runS, runFrom, stepS_eq s L r (hs r List.mem_cons_self), ih']

/-! ### Stored rows and startup replay -/

/-- A stored row of a well-formed request and event survives encoding and decoding unchanged. -/
theorem rowFromJ_toJ (r : S.Req) (e : S.Ev) (hr : S.requestWf r = true) (he : S.eventWf e = true) :
    S.rowFromJ (S.rowToJ (r, e)) = .ok (r, e) := by
  simp [rowFromJ, rowToJ, fields, onlyKeys, get?, List.find?, S.requestFromJ_toJ r hr, S.eventFromJ_toJ e he, bind,
    Except.bind, pure, Except.pure]

/-- A well-formed request translates to a well-formed event. -/
theorem toEvent_wf {r : S.Req} {e : S.Ev} (hr : S.requestWf r = true) (h : S.toEvent r = .ok e) :
    S.eventWf e = true := by
  rw [S.eventWf_eq, S.toEvent_ok_iff.mp h]; exact hr

/-- **Forms hold for every event kept.** If every request is well formed, every event of the log `runFrom` produces
from a well-formed log is well formed. -/
theorem runFrom_wf {log : S.Log} (hl : ∀ e ∈ log, S.eventWf e = true) (reqs : List S.Req)
    (hr : ∀ r ∈ reqs, S.requestWf r = true) : ∀ e ∈ (S.runFrom log reqs).1, S.eventWf e = true := by
  induction reqs generalizing log with
  | nil => simpa [runFrom] using hl
  | cons r rs ih =>
    simp only [runFrom]
    cases h : S.respond log r with
    | accepted e =>
      apply ih _ (fun r hm => hr r (List.mem_cons_of_mem _ hm))
      intro e' he'
      simp only [Response.event?, Option.toList_some, List.mem_append, List.mem_singleton] at he'
      rcases he' with he' | rfl
      · exact hl e' he'
      · exact toEvent_wf (hr _ List.mem_cons_self) (respond_accepted_iff.mp h).1
    | rejected x => exact ih (by simpa using hl) (fun r hm => hr r (List.mem_cons_of_mem _ hm))

theorem run_wf (reqs : List S.Req) (hr : ∀ r ∈ reqs, S.requestWf r = true) :
    ∀ e ∈ (S.run reqs).1, S.eventWf e = true :=
  runFrom_wf (by simp) reqs hr

/-- **Replaying stored rows** succeeds exactly when every stored request is accepted, in order, from the log so far,
and gives exactly the stored event; the result is then the stored events after the starting log, and `runFrom` of
the stored requests answers each with acceptance of its stored event. -/
theorem replayFrom_ok {log log' : S.Log} {rows : List (S.Req × S.Ev)} (h : S.replayFrom log rows = .ok log') :
    log' = log ++ rows.map (·.2) ∧
      S.runFrom log (rows.map (·.1)) = (log', (rows.map (·.2)).map Response.accepted) := by
  induction rows generalizing log with
  | nil => simp [replayFrom] at h; subst h; simp [runFrom]
  | cons row rs ih =>
    obtain ⟨r, e⟩ := row
    simp only [replayFrom] at h
    split at h
    · rename_i e' hs
      split at h
      · rename_i heq; subst heq
        obtain ⟨ih1, ih2⟩ := ih h
        refine ⟨by rw [ih1]; simp, ?_⟩
        simp only [List.map_cons, runFrom, hs, Response.event?, Option.toList_some, ih2]
      · cases h
    · cases h

/-- **Startup replay is sound.** If the stored rows replay, the log is exactly the stored events, it is `Valid`, and
it is `run` of the stored requests with every one accepted. -/
theorem replayRows_sound {rows : List (S.Req × S.Ev)} {log : S.Log} (h : S.replayRows rows = .ok log) :
    log = rows.map (·.2) ∧ S.Valid log ∧ S.run (rows.map (·.1)) = (log, log.map Response.accepted) := by
  obtain ⟨h1, h2⟩ := replayFrom_ok h
  simp only [List.nil_append] at h1
  subst h1
  refine ⟨rfl, ?_, h2⟩
  have := run_valid (S := S) (rows.map (·.1))
  unfold run at this
  rw [h2] at this
  exact this

/-- **Startup replay is complete.** Storing `(r, e)` exactly when the engine accepted `r` with `e` makes a list that
`replayRows` accepts. -/
theorem replayRows_complete (reqs : List S.Req) (hacc : ∀ x ∈ (S.run reqs).2, ∃ e, x = .accepted e) :
    S.replayRows (reqs.zip ((S.run reqs).1)) = .ok (S.run reqs).1 := by
  have key : ∀ (log : S.Log) (rs : List S.Req), (∀ x ∈ (S.runFrom log rs).2, ∃ e, x = .accepted e) →
      S.replayFrom log (rs.zip ((S.runFrom log rs).1.drop log.length)) = .ok (S.runFrom log rs).1 := by
    intro log rs
    induction rs generalizing log with
    | nil => intro _; simp [runFrom, replayFrom]
    | cons r rs ih =>
      intro hall
      simp only [runFrom] at hall ⊢
      cases hr : S.respond log r with
      | accepted e =>
        rw [hr] at hall
        simp only [Response.event?, Option.toList_some] at hall ⊢
        have hall' : ∀ x ∈ (S.runFrom (log ++ [e]) rs).2, ∃ e, x = .accepted e :=
          fun x hx => hall x (List.mem_cons_of_mem _ hx)
        have hdrop : ((S.runFrom (log ++ [e]) rs).1.drop log.length) =
            e :: ((S.runFrom (log ++ [e]) rs).1.drop (log ++ [e]).length) := by
          rw [runFrom_log_eq (log ++ [e]) rs]; simp
        rw [hdrop, List.zip_cons_cons]
        simp only [replayFrom, hr, ite_true]
        exact ih (log ++ [e]) hall'
      | rejected reason =>
        rw [hr] at hall
        obtain ⟨e, he⟩ := hall (.rejected reason) List.mem_cons_self
        cases he
  have := key [] reqs hacc
  simpa [replayRows, run] using this

/-- **Catch-up through the state is catch-up through the log.** If the state-based replay of stored rows succeeds
from the fold of a log, the log-based replay succeeds too, and the state it ends in is the fold of the log that one
ends in. -/
theorem replaySFrom_ok {s : Id} {L : S.Log} {rows : List (S.Req × S.Ev)} {st' : S.St}
    (h : S.replaySFrom (S.fold s L) rows = .ok st') : ∃ L', S.replayFrom L rows = .ok L' ∧ st' = S.fold s L' := by
  induction rows generalizing L with
  | nil => exact ⟨L, rfl, by simpa [replaySFrom] using h.symm⟩
  | cons row rs ih =>
    obtain ⟨r, e⟩ := row
    simp only [replaySFrom, fold_stStream] at h
    split at h
    · rename_i hs
      rw [stepS_eq s L r hs] at h
      cases hx : S.respond L r with
      | rejected x => rw [hx] at h; simp at h
      | accepted e0 =>
        rw [hx] at h
        simp only [Response.event?, Option.toList_some] at h
        split at h
        · rename_i heq; subst heq
          obtain ⟨L', h1, h2⟩ := ih h
          exact ⟨L', by simp [replayFrom, hx, h1], h2⟩
        · cases h
    · cases h

/-- From the empty stream: the rows replay as `replayRows` does, and the state is the fold of the stored events. -/
theorem replaySRows_sound {s : Id} {rows : List (S.Req × S.Ev)} {st : S.St}
    (h : S.replaySRows s rows = .ok st) :
    S.replayRows rows = .ok (rows.map (·.2)) ∧ st = S.fold s (rows.map (·.2)) := by
  have h0 : S.replaySFrom (S.fold s []) rows = .ok st := h
  obtain ⟨L', h1, h2⟩ := replaySFrom_ok h0
  have := (replayFrom_ok h1).1
  simp only [List.nil_append] at this
  subst this
  exact ⟨h1, h2⟩

/-! ### The engine's bookkeeping per stream -/

theorem Entry.empty_eq (s : Id) : Entry.empty S s = Entry.ofLog S s [] := rfl

/-- **The engine's step on a request is `respond`, `runFrom` and the stream's length.** -/
theorem entryRequest_spec (s : Id) (L : S.Log) (r : S.Req) (hr : S.reqStream r = s) :
    S.entryRequest (Entry.ofLog S s L) r = (Entry.ofLog S s (S.runFrom L [r]).1, S.respond L r, L.length) := by
  simp only [entryRequest, Entry.ofLog, stepS_eq s L r hr, runFrom_one]
  cases S.respond L r <;> simp [Response.event?]

/-- **Syncing keeps the specification.** If syncing rows onto the entry of `L` succeeds, the host had the right
count, the rows replay against `L`, and the new entry is the entry of the log that replay ends in. -/
theorem entrySync_spec {s : Id} {L : S.Log} {k : Nat} {rows : List (S.Req × S.Ev)} {en' : S.Entry}
    (h : S.entrySync (Entry.ofLog S s L) k rows = .ok en') :
    k = L.length ∧ ∃ L', S.replayFrom L rows = .ok L' ∧ en' = Entry.ofLog S s L' := by
  unfold entrySync at h
  split at h
  · rename_i hk
    refine ⟨hk.symm, ?_⟩
    cases hr : S.replaySFrom (Entry.ofLog S s L).st rows with
    | error d => rw [hr] at h; cases h
    | ok st' =>
      rw [hr] at h
      simp only [Except.map, Except.ok.injEq] at h
      obtain ⟨L', h1, h2⟩ := replaySFrom_ok (L := L) (s := s) hr
      refine ⟨L', h1, ?_⟩
      have hl := (replayFrom_ok h1).1
      subst h
      simp only [Entry.ofLog] at h2 ⊢
      rw [h2, hl]; simp
  · cases h

end Service
end StreamCore
