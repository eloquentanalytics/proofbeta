-- Copyright (c) 2026 the proofbeta authors. All rights reserved. See LICENSE.
import StreamCore.Service
import StreamCore.WireState

/-!
# The core, as a service

`coreService` is this core's events, requests, rules, fast path and wire forms, with their obligations discharged by
the lemmas of `Command.lean`, `Stream.lean`, `StreamState.lean`, `WireTheorems.lean` and `WireState.lean`. The core's
`Response`, `respond`, `run`, `Valid`, `check`, `Store`, `execB`, `respondS`, `stepS`, `replayFrom`, `Entry`,
`entryRequest`, `entrySync`, ... are `Service.lean`'s at `coreService`, and the theorems below (and in
`CommandTheorems.lean` and `Streams.lean`) are `Service.lean`'s theorems at it, under the names and statements the
core has always had.
-/

namespace StreamCore
open StreamCore.Wire

/-- The core: `Event`, `Request`, `StreamState`, the rules, and the wire. -/
abbrev coreService : Service where
  Ev := Event
  Req := Request
  St := StreamState
  toEvent r := toEvent r.1 r.2.1 r.2.2
  toRequest := toRequest
  toEvent_ok_iff := fun {r _} => by obtain ⟨c, cmd, f⟩ := r; exact toEvent_ok_iff
  stream := Event.stream
  reqStream := reqStream
  toEvent_stream := fun {r _} h => by obtain ⟨c, cmd, f⟩ := r; exact toEvent_stream h
  ok := ok
  rejection := rejection
  rejection_none_iff := rejection_none_iff
  rejection_local := fun past e => rejection_local past e
  init := StreamState.init
  step := StreamState.step
  rejectionS := rejectionS
  rejectionS_fold := fun past e => rejectionS_eq past e
  stStream := StreamState.stream
  stStream_init := fun _ => rfl
  stStream_step := step_stream
  requestWf := requestWf
  eventWf := eventWf
  eventWf_eq := fun _ => rfl
  requestToJ := requestToJ
  requestFromJ := requestFromJ
  requestFromJ_toJ := requestFromJ_toJ
  requestFromJ_wf := requestFromJ_wf
  eventToJ := eventToJ
  eventFromJ := eventFromJ
  eventFromJ_toJ := eventFromJ_toJ
  eventFromJ_wf := eventFromJ_wf
  stateToJ := stateToJ
  stateFromJ := stateFromJ
  stateFromJ_toJ := stateFromJ_toJ
  streamSJ := streamSJ

/-! ## Answers and sequences -/

/-- What a caller hears back. -/
abbrev Response : Type := coreService.Response

@[match_pattern] abbrev Response.accepted (e : Event) : Response := Service.Response.accepted e
@[match_pattern] abbrev Response.rejected (reason : String) : Response := Service.Response.rejected reason

/-- The event of an accepted response. -/
abbrev Response.event? : Response → Option Event := Service.Response.event?

/-- The answer to one request from a judge of events: the translation's refusal, or the first rule that fails, or
acceptance. Every other decision function is this one: `respond` judges against the log, and the fast path
(`respondS`) judges from the stream's state. -/
abbrev answer (judge : Event → Option String) : Request → Response := coreService.answer judge

abbrev respond (log : Log) : Request → Response := coreService.respond log

/-- Translate, then accept: the new log and the event appended, or the reason for refusing. -/
def handle (log : Log) (c : Id) (cmd : Command) (f : Fresh) : Except String (Event × Log) :=
  match respond log (c, cmd, f) with
  | .accepted e => .ok (e, log ++ [e])
  | .rejected r => .error r

/-- `respond` from a log over a sequence of requests, left to right, the log growing by each accepted event. The
engine's loop is this, one request at a time. -/
abbrev runFrom : Log → List Request → Log × List Response := coreService.runFrom

/-- Every request the service ever received, in the order it received them, run from the empty log. -/
abbrev run (reqs : List Request) : Log × List Response := coreService.run reqs

/-- A log built only by accepting candidates (`Service.Valid`: `nil`, and `snoc` of an event `ok` against the log). -/
abbrev Valid : Log → Prop := coreService.Valid

/-- Run the rules over every prefix. -/
abbrev checkFrom (past : Past) : List Event → Bool := coreService.checkFrom past

abbrev check (log : Log) : Bool := coreService.check log

abbrev toRequests (log : Log) : List Request := coreService.toRequests log

/-- Every response of `run reqs` is an acceptance. -/
abbrev AllAccepted (reqs : List Request) : Prop := coreService.AllAccepted reqs

/-! ## The fast path -/

/-- The answer to a request, from the state. -/
abbrev respondS (st : StreamState) : Request → Response := coreService.respondS st

/-- One request: the answer and the next state. -/
abbrev stepS (st : StreamState) (r : Request) : StreamState × Response := coreService.stepS st r

abbrev runS : StreamState → List Request → StreamState × List Response := coreService.runS

/-! ## Compare-and-set appends -/

/-- A store of per-stream logs. Each stream is a list, so its positions are contiguous from 0. -/
abbrev Store := coreService.Store

abbrev Store.empty : Store := Service.Store.empty coreService

abbrev Store.set (st : Store) (s : Id) (l : Log) : Store := Service.Store.set st s l

/-- What a validator's batch comes to: committed with these answers, or a lost compare-and-set. -/
abbrev Outcome := coreService.Outcome

@[match_pattern] abbrev Outcome.committed (answers : List Response) : Outcome := Service.Outcome.committed answers
@[match_pattern] abbrev Outcome.conflict : Outcome := Service.Outcome.conflict

/-- One validator's batch on stream `s`: it read the stream when it had `n` events, decided the requests one after
another from there, and appends every accepted event with one compare-and-set at `n`. -/
abbrev attemptBatch (st : Store) (s : Id) (reqs : List Request) (n : Nat) : Store × Outcome :=
  coreService.attemptBatch st s reqs n

/-- Any interleaving of validators: batches in commit order, each with its stream and the length it read at. -/
abbrev execB : Store → List (Id × List Request × Nat) → Store × List (Id × List Request × Outcome) :=
  coreService.execB

/-- The requests of the batches that committed on stream `s`, in commit order. -/
abbrev committedReqs : List (Id × List Request × Outcome) → Id → List Request := coreService.committedReqs

/-- The answers delivered on stream `s`, in commit order. -/
abbrev deliveredAnswers : List (Id × List Request × Outcome) → Id → List Response := coreService.deliveredAnswers

/-! ## The wire: stored rows, the engine's step and startup replay, catch-up through the state, and entries -/

namespace Wire

/-- A stored row: the request the engine accepted and the event it returned. -/
abbrev rowFromJ (j : J) : Except String (Request × Event) := coreService.rowFromJ j

abbrev rowToJ : Request × Event → J := coreService.rowToJ

/-- The engine's answer to one line. -/
abbrev responseToJ : Response → J := coreService.responseToJ

/-- One parsed line against the log: decode, `respond`, encode; the log grows by the accepted event (`runFrom` on one
request). A line that does not decode changes nothing. -/
abbrev stepJ (log : Log) (j : J) : Log × J := coreService.stepJ log j

/-- Replay stored rows from a log, one at a time: each stored request must be accepted and give exactly the stored
event. -/
abbrev replayFrom (log : Log) : List (Request × Event) → Except String Log := coreService.replayFrom log

abbrev replayRows (rows : List (Request × Event)) : Except String Log := coreService.replayRows rows

/-- One parsed line: a read (`{"query": "stream", "stream": <id>}`), which never changes the log, or a request,
handled by `stepJ`. -/
def lineJ (log : Log) (j : J) : Log × J :=
  match j with
  | .obj [("query", .str "stream"), ("stream", .str t)] => (log, streamJ log t)
  | _ => stepJ log j

abbrev replaySFrom (st : StreamState) : List (Request × Event) → Except String StreamState := coreService.replaySFrom st

abbrev replaySRows (s : Id) (rows : List (Request × Event)) : Except String StreamState :=
  coreService.replaySRows s rows

/-- What the engine keeps for a stream: a state and the number of events it folds. The specification of an entry
for stream `s` after log `L` is `Entry.ofLog s L = ⟨fold s L, L.length⟩`. Every operation the engine performs on an
entry is one of the functions below, and each has a theorem saying it keeps that specification. -/
abbrev Entry := coreService.Entry

abbrev Entry.ofLog (s : Id) (L : Log) : Entry := Service.Entry.ofLog coreService s L

/-- A stream the engine has never seen: the entry of the empty log. -/
abbrev Entry.empty (s : Id) : Entry := Service.Entry.empty coreService s

/-- Decide one request: the new entry, the answer, and the position it was decided at. -/
abbrev entryRequest (en : Entry) (r : Request) : Entry × Response × Nat := coreService.entryRequest en r

/-- Fold stored rows onto an entry that must fold exactly `k` events. -/
abbrev entrySync (en : Entry) (k : Nat) (rows : List (Request × Event)) : Except String Entry :=
  coreService.entrySync en k rows

end Wire

/-! ## `Valid` and `check` (`Service.lean`, at the core) -/

theorem Valid.inv {log : Log} {e : Event} (h : Valid (log ++ [e])) : Valid log ∧ ok log e = true :=
  Service.Valid.inv h

/-- Every prefix of a valid log is valid. -/
theorem Valid.prefix {log : Log} (h : Valid log) : ∀ a b, log = a ++ b → Valid a := Service.Valid.prefix h

/-- The rules held for every event at the moment it was accepted. -/
theorem Valid.okAt {pre post : Log} {e : Event} (h : Valid (pre ++ e :: post)) : ok pre e = true :=
  Service.Valid.okAt h

theorem checkFrom_iff (past : Past) (hp : Valid past) :
    ∀ es, checkFrom past es = true ↔ Valid (past ++ es) := Service.checkFrom_iff (S := coreService) past hp

/-- `check` decides `Valid`. -/
theorem check_iff_valid (log : Log) : check log = true ↔ Valid log := Service.check_iff_valid (S := coreService) log

/-- Induction on a valid log of the core, stated over `Log` (`induction h using Valid.induction`). -/
@[elab_as_elim] theorem Valid.induction {motive : (log : Log) → Valid log → Prop} (nil : motive [] .nil)
    (snoc : ∀ {log : Log} {e : Event} (hv : Valid log) (hok : ok log e = true), motive log hv →
      motive (log ++ [e]) (.snoc hv hok))
    {log : Log} (h : Valid log) : motive log h :=
  Service.Valid.rec (motive := fun l h => motive l h) nil (fun hv hok ih => snoc hv hok ih) h

/-! ## The fast path is the specification (`Service.lean`, at the core) -/

/-- **The fast path is the specification.** For every log and every request, deciding from the fold of the log onto
the request's stream gives exactly the answer the rules give against the log. No hypothesis. -/
theorem fold_sound (L : Log) (r : Request) : respondS (fold (reqStream r) L) r = respond L r :=
  Service.fold_sound (S := coreService) L r

/-- So a decision from a snapshot and the events after it is the decision from the whole log. -/
theorem snapshot_sound (L₁ L₂ : Log) (r : Request) :
    respondS (L₂.foldl StreamState.step (fold (reqStream r) L₁)) r = respond (L₁ ++ L₂) r :=
  Service.snapshot_sound (S := coreService) L₁ L₂ r

/-- **The fast path runs the same service.** For requests all on stream `s`, running them through the state from the
fold of a log gives the same answers as `runFrom` on the log, and ends in the fold of the log `runFrom` ends in. -/
theorem runS_eq_run (s : Id) (L : Log) (reqs : List Request) (hs : ∀ r ∈ reqs, reqStream r = s) :
    runS (fold s L) reqs = (fold s (runFrom L reqs).1, (runFrom L reqs).2) :=
  Service.runS_eq_run (S := coreService) s L reqs hs

namespace Wire

/-! ## Stored rows and startup replay (`Service.lean`, at the core) -/

/-- A stored row of a well-formed request and event survives encoding and decoding unchanged. -/
theorem rowFromJ_toJ (r : Request) (e : Event) (hr : requestWf r = true) (he : eventWf e = true) :
    rowFromJ (rowToJ (r, e)) = .ok (r, e) := Service.rowFromJ_toJ (S := coreService) r e hr he

/-- **Forms hold for every event the engine keeps.** If every request is well formed (as every decoded request is,
`requestFromJ_wf`), every event of the log `run` produces from a well-formed log is well formed. -/
theorem runFrom_wf {log : Log} (hl : ∀ e ∈ log, eventWf e = true) (reqs : List Request)
    (hr : ∀ r ∈ reqs, requestWf r = true) : ∀ e ∈ (runFrom log reqs).1, eventWf e = true :=
  Service.runFrom_wf (S := coreService) hl reqs hr

theorem run_wf (reqs : List Request) (hr : ∀ r ∈ reqs, requestWf r = true) :
    ∀ e ∈ (run reqs).1, eventWf e = true :=
  Service.run_wf (S := coreService) reqs hr

/-- **Replaying stored rows** succeeds exactly when every stored request is accepted, in order, from the log so far,
and gives exactly the stored event; the result is then the stored events after the starting log, and `run` of the
stored requests answers each with acceptance of its stored event. -/
theorem replayFrom_ok {log log' : Log} {rows : List (Request × Event)} (h : replayFrom log rows = .ok log') :
    log' = log ++ rows.map (·.2) ∧ runFrom log (rows.map (·.1)) = (log', (rows.map (·.2)).map Response.accepted) :=
  Service.replayFrom_ok h

/-- **Startup replay is sound.** If the stored rows replay, the engine's log is exactly the stored events, it is
`Valid`, and it is `run` of the stored requests with every one accepted. -/
theorem replayRows_sound {rows : List (Request × Event)} {log : Log} (h : replayRows rows = .ok log) :
    log = rows.map (·.2) ∧ Valid log ∧ run (rows.map (·.1)) = (log, log.map Response.accepted) :=
  Service.replayRows_sound h

/-- **Startup replay is complete.** The rows the service stores (each accepted request with the event it returned)
always replay: storing `(r, e)` exactly when the engine accepted `r` with `e` makes a list that `replayRows` accepts. -/
theorem replayRows_complete (reqs : List Request) (hacc : ∀ x ∈ (run reqs).2, ∃ e, x = .accepted e) :
    replayRows (reqs.zip ((run reqs).1)) = .ok (run reqs).1 :=
  Service.replayRows_complete (S := coreService) reqs hacc

/-! ## Catch-up through the state and the engine's bookkeeping per stream (`Service.lean`, at the core) -/

/-- **Catch-up through the state is catch-up through the log.** If the state-based replay of stored rows succeeds from
the fold of a log, the log-based replay succeeds too (so `replayFrom_ok` applies: the rows are accepted requests with
exactly their events, `Valid`), and the state it ends in is the fold of the log that one ends in. -/
theorem replaySFrom_ok {s : Id} {L : Log} {rows : List (Request × Event)} {st' : StreamState}
    (h : replaySFrom (fold s L) rows = .ok st') : ∃ L', replayFrom L rows = .ok L' ∧ st' = fold s L' :=
  Service.replaySFrom_ok (S := coreService) h

/-- From the empty stream: the rows replay as `replayRows` does, and the state is the fold of the stored events. -/
theorem replaySRows_sound {s : Id} {rows : List (Request × Event)} {st : StreamState}
    (h : replaySRows s rows = .ok st) :
    replayRows rows = .ok (rows.map (·.2)) ∧ st = fold s (rows.map (·.2)) :=
  Service.replaySRows_sound (S := coreService) h

theorem Entry.empty_eq (s : Id) : Entry.empty s = Entry.ofLog s [] := rfl

/-- **The engine's step on a request is `respond`, `run` and the stream's length.** From the entry of log `L`, deciding
a request on that stream gives the entry of the log `run` leaves, the answer `respond L r`, and the position
`L.length` it was decided at. -/
theorem entryRequest_spec (s : Id) (L : Log) (r : Request) (hr : reqStream r = s) :
    entryRequest (Entry.ofLog s L) r = (Entry.ofLog s (runFrom L [r]).1, respond L r, L.length) :=
  Service.entryRequest_spec (S := coreService) s L r hr

/-- **Syncing keeps the specification.** If syncing rows onto the entry of `L` succeeds, the host had the right count,
the rows replay against `L` (so they are accepted requests with exactly their events: `replayFrom_ok`), and the new
entry is the entry of the log that replay ends in. -/
theorem entrySync_spec {s : Id} {L : Log} {k : Nat} {rows : List (Request × Event)} {en' : Entry}
    (h : entrySync (Entry.ofLog s L) k rows = .ok en') :
    k = L.length ∧ ∃ L', replayFrom L rows = .ok L' ∧ en' = Entry.ofLog s L' :=
  Service.entrySync_spec (S := coreService) h

end Wire

end StreamCore
