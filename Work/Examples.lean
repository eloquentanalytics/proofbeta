-- Copyright (c) 2026 the proofbeta authors. All rights reserved. See LICENSE.
import Work.Theorems

/-!
# Worked examples: one person's stream of work items

A story of requests through the specification, each with the answer it gets, checked at build time (`#guard`) and
compiled into the engine's `--self-test` (`allOk`). alice (a person: her creation records `actor_kind` person) creates
the stream `S`, binds the agents agent-1 and agent-2, creates the work items `W1` and `W2`, names agent-1 and agent-2
on `W1` and agent-2 on `W2`; they submit their preparations; alice completes `W1` with her own answer; then she binds
agent-3, names it on `W1`, and agent-3 submits after the completion, accepted. Along the way: an unnamed agent
submitting, a double submit, preparing an unbound principal, an agent completing, a double complete, re-creating `W1`,
an agent creating a stream and the actor binding itself are refused, and every rule and guard of the layer refuses
something. Last, alice's second stream `S2` is ended by a panic, after which nothing is accepted on it.
-/

namespace Work.Examples
open StreamCore StreamCore.Layer Work

def url : String := "https://example.org/proofbeta/commit/0123456789abcdef0123456789abcdef01234567"

/-! Ids are opaque UUIDs: nothing in them says person or agent. -/
def alice : Id := "9e111900-0000-7000-8000-000000000001"
def agent1 : Id := "a6e47000-0000-7000-8000-000000000001"
def agent2 : Id := "a6e47000-0000-7000-8000-000000000002"
def agent3 : Id := "a6e47000-0000-7000-8000-000000000003"
def S : Id := "5e000000-0000-7000-8000-000000000001"
def S2 : Id := "5e000000-0000-7000-8000-000000000002"
def W1 : Id := "3e000000-0000-7000-8000-000000000001"
def W2 : Id := "3e000000-0000-7000-8000-000000000002"
def W9 : Id := "3e000000-0000-7000-8000-000000000009"

#guard [alice, agent1, agent2, agent3, S, S2, W1, W2, W9].all validUuid

/-- The SHA-256 of the empty string, standing in for every ciphertext's hash. -/
def sha : String := "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"

def blob (n : String) : Meta := some (encode [("blob_sha256", sha), ("blob_url", "https://blobs.example.org/w/" ++ n)])
def prep (n : String) : Meta :=
  some (encode [("preparation_sha256", sha), ("preparation_url", "https://blobs.example.org/p/" ++ n)])
def completion (n : String) : Meta := some (encode [("completion_sha256", sha), ("completion_url", "https://blobs.example.org/a/" ++ n)])

#guard isSha256 sha && !isSha256 sha.toUpper && !isSha256 (sha.drop 1).copy
#guard opaqueUrl "https://blobs.example.org/w/1" && opaqueUrl "not a URL at all, and that is fine" && opaqueUrl "s3:x"
#guard !opaqueUrl "" && !opaqueUrl "https://x\n" && !opaqueUrl (String.ofList (List.replicate 2049 'a'))
#guard (decodeMeta (blob "1")).map (conforms blobSchema) == some true
#guard (decodeMeta (prep "1")).map (conforms preparationSchema) == some true
#guard (decodeMeta (completion "1")).map (conforms completionSchema) == some true
-- URLs are never compared: an answer naming the very URL of a preparation conforms all the same
#guard (decodeMeta (some (encode [("completion_sha256", sha), ("completion_url", "https://blobs.example.org/p/1-1")]))).map
  (conforms completionSchema) == some true
#guard agentsForm (agent1 ++ "," ++ agent2) && agentList (agent1 ++ "," ++ agent2) == [agent1, agent2]
#guard !agentsForm "" && !agentsForm (agent1 ++ ",") && !agentsForm (agent1 ++ ", " ++ agent2)

abbrev Sv := work.service

def core (c : Id) (cmd : Command) (f : Fresh := []) : Sv.Req := .inl (c, cmd, f)
def cmd (c : Id) (cmd : WorkCommand) (f : Fresh := []) : Sv.Req := .inr (c, cmd, f)

/-- The creation the host sends for a principal it records as a person: `actor_kind` person. -/
def asPerson : Creation := ⟨url, some .person⟩
/-- And for one it records as an agent. -/
def asAgent : Creation := ⟨url, some .agent⟩

/-- Requests, each with the answer it gets: `none` accepted, `some r` refused with `r`. -/
def story : List (Sv.Req × Option String) :=
  [ (cmd alice (.create S W1 (blob "1")), some "unknown_stream"),
    (core agent1 (.streamCreate asAgent none) [S], some "creator_not_person"),            -- an agent creates no stream
    (core alice (.streamCreate url none) [S], some "actor_kind_unattested"),             -- the kind must be stated
    (core alice (.streamCreate asPerson none) [S], none),                                 -- alice is the actor
    (core alice (.principalInvite S agent1 none), some "single_member"),
    (core alice (.principalPromote S agent1 none), some "not_member"),                   -- the core's rules first
    (cmd alice (.agent S alice none), some "agent_is_actor"),                            -- the actor binds itself
    (cmd agent1 (.agent S agent2 none), some "not_actor"),
    (cmd alice (.agent S agent1 none) [W9], some "fresh_ids"),
    (cmd alice (.agent S agent1 none), none),
    (cmd alice (.agent S agent2 none), none),
    (cmd alice (.agent S agent1 none), some "already_agent"),
    (cmd alice (.create S W1 none), some "meta_invalid"),
    (cmd alice (.create S W1 (some (encode [("blob_url", "https://b.example.org/x")]))), some "meta_missing_field"),
    (cmd alice (.create S W1 (some (encode [("blob_sha256", "abc"), ("blob_url", "https://b.example.org/x")]))),
      some "meta_bad_field"),
    (cmd agent1 (.create S W1 (blob "1")), some "not_actor"),
    (cmd alice (.create S W1 (blob "1")), none),
    (cmd alice (.create S W2 (blob "2")), none),
    (cmd alice (.create S W1 (blob "1b")), some "work_id_taken"),                       -- re-creating W1
    (cmd alice (.prepare S W9 agent1 none), some "unknown_work"),
    (cmd alice (.prepare S W1 agent3 none), some "not_an_agent"),                       -- an unbound principal
    (cmd alice (.prepare S W1 (agent1 ++ "," ++ agent1) none), some "already_named"),
    (cmd agent1 (.prepare S W1 agent1 none), some "not_actor"),
    (cmd alice (.prepare S W1 (agent1 ++ "," ++ agent2) none), none),
    (cmd alice (.prepare S W2 agent2 none), none),
    (cmd alice (.prepare S W2 agent2 none), some "already_named"),
    (cmd agent1 (.submit S W2 (prep "2-1")), some "not_named"),                          -- an unnamed agent submits
    (cmd alice (.submit S W1 (prep "1-0")), some "not_named"),                           -- the actor never submits
    (cmd agent1 (.submit S W1 none), some "meta_invalid"),
    (cmd agent1 (.submit S W1 (some (encode [("preparation_url", "https://b.example.org/p")]))),
      some "meta_missing_field"),
    (cmd agent1 (.submit S W1 (blob "x")), some "meta_missing_field"),                   -- a blob is no preparation
    (cmd agent1 (.submit S W1 (some (encode [("preparation_sha256", "abc"), ("preparation_url", "https://b.example.org/p")]))),
      some "meta_bad_field"),
    (cmd agent1 (.submit S W1 (prep "1-1")), none),
    (cmd agent2 (.submit S W1 (prep "1-2")), none),
    (cmd agent2 (.submit S W2 (prep "2-2")), none),
    (cmd agent1 (.submit S W1 (prep "1-1b")), some "already_submitted"),                 -- a double submit
    (cmd agent1 (.complete S W1 (completion "1")), some "not_actor"),                        -- an agent completes
    (cmd alice (.complete S W1 none), some "meta_invalid"),                              -- the answer is required
    (cmd alice (.complete S W9 (completion "9")), some "unknown_work"),
    (cmd alice (.complete S W1 (completion "1")), none),
    (cmd alice (.complete S W1 (completion "1b")), some "already_completed"),                -- a double complete
    (cmd alice (.agent S agent3 none), none),
    (cmd alice (.prepare S W1 agent3 none), none),                                      -- after completion
    (cmd agent3 (.submit S W1 (prep "1-3")), none),                                      -- after completion
    (core alice (.streamCreate asPerson none) [S2], none),                               -- alice's second stream
    (cmd agent1 (.submit S2 W1 (prep "x")), some "unknown_work"),                        -- work items are per stream
    (core alice (.streamPanic S2 none), none),
    (cmd alice (.create S2 W1 (blob "1")), some "stream_ended"),
    (core agent1 (.streamPanic S none), some "not_stream_admin") ]

def reason : Sv.Response → Option String
  | .accepted _ => none
  | .rejected r => some r

def eventOf : Sv.Response → List Sv.Ev
  | .accepted e => [e]
  | .rejected _ => []

def log : Sv.Log := (Sv.run (story.map (·.1))).1

/-- Every prefix of the log, the empty one and the whole one included. -/
def prefixes : List Sv.Log := (List.range (log.length + 1)).map log.take

/-- Every request gets the answer the story says. -/
def answersOk : Bool := (Sv.run (story.map (·.1))).2.map reason == story.map (·.2)

/-- The log is valid, and replaying its events' requests gives it back. -/
def replayOk : Bool := Sv.check log && (Sv.run (log.map Sv.toRequest)).1 == log

/-- The fast path answers every request as the specification does. -/
def fastOk : Bool := (story.map (·.1)).foldl (fun (acc : Sv.Log × Bool) r =>
    let x := Sv.respond acc.1 r
    (acc.1 ++ eventOf x, acc.2 && Sv.respondS (Sv.fold (Sv.reqStream r) acc.1) r == x)) ([], true) |>.2

/-- Every event survives the wire. -/
def wireOk : Bool := log.all fun e => match Sv.eventFromJ (Sv.eventToJ e) with | .ok e' => e' == e | _ => false

/-- Every request of the story survives the wire, the refused ones included. -/
def requestsOk : Bool :=
  (story.map (·.1)).all fun r => match Sv.requestFromJ (Sv.requestToJ r) with | .ok r' => r' == r | _ => false

/-- Each stream's state after every prefix survives its snapshot. -/
def snapshotsOk : Bool :=
  prefixes.all fun l => [S, S2].all fun t =>
    let st := Sv.fold t l
    match Sv.stateFromJ (Sv.stateToJ st) with
    | .ok st' => st' == st
    | .error _ => false

/-- The core's events of every prefix form a valid core log (`ValidX.cores`, run). -/
def coresOk : Bool := prefixes.all fun l => coreService.check (cores l)

/-- What the theorems state, at every layer event: binds, creates, prepares and completes by the actor (`by_actor`),
every submit by an agent bound and named before it (`submit_after_prepare`); alice the only admin of `S`
(`admin_iff_actor`); the creation recording a person (`actor_is_person`). -/
def theoremsOk : Bool :=
  (List.range log.length).all (fun i =>
    let pre := log.take i
    match log[i]? with
    | some (.inr x) =>
      let t := work.evStream x
      let es := evs pre t
      match x with
      | .submit a _ w _ => isAgent es a && named es w a
      | _ => Past.admin (cores pre) t x.actor
    | _ => true)
  && [alice, agent1, agent2, agent3].all (fun p => Past.admin (cores log) S p == (p == alice))
  && [alice, agent1, agent2, agent3].all (fun p => Past.member (cores log) S p == (p == alice))
  && (cores log).all (fun | .streamCreate _ _ c _ => c.actorKind == some .person | _ => true)

/-- The records at the end of `S`. -/
def recordsOk : Bool :=
  let es := evs log S
  agents es == [agent1, agent2, agent3] && works es == [(W1, blob "1"), (W2, blob "2")] &&
    namedOn es W1 == [agent1, agent2, agent3] && namedOn es W2 == [agent2] &&
    submitsOn es W1 == [(agent1, prep "1-1"), (agent2, prep "1-2"), (agent3, prep "1-3")] &&
    submitsOn es W2 == [(agent2, prep "2-2")] && completed es W1 && !completed es W2 &&
    blobOf es W1 == some (blob "1") && completionOf es W1 == some (completion "1") && completionOf es W2 == none

/-- The read at the end, as JSON. -/
def readOk : Bool :=
  readFields (evs log S) ==
    [("agents", .arr [.str agent1, .str agent2, .str agent3]),
     ("works", .arr [
       .obj [("work_id", .str W1), ("meta", optJ (blob "1")), ("agents", .arr [.str agent1, .str agent2, .str agent3]),
         ("submissions", .arr [.obj [("agent", .str agent1), ("meta", optJ (prep "1-1"))],
           .obj [("agent", .str agent2), ("meta", optJ (prep "1-2"))],
           .obj [("agent", .str agent3), ("meta", optJ (prep "1-3"))]]),
         ("completion", optJ (completion "1"))],
       .obj [("work_id", .str W2), ("meta", optJ (blob "2")), ("agents", .arr [.str agent2]),
         ("submissions", .arr [.obj [("agent", .str agent2), ("meta", optJ (prep "2-2"))]]),
         ("completion", .null)]])]

/-- Every rule and guard of the layer refuses something in the story. -/
def everyRuleOk : Bool :=
  (work.rules.map (·.reason) ++ work.guards.map (·.reason)).all fun r => story.any (·.2 == some r)

#guard answersOk
#guard replayOk
#guard fastOk
#guard wireOk
#guard requestsOk
#guard snapshotsOk
#guard coresOk
#guard theoremsOk
#guard recordsOk
#guard readOk
#guard everyRuleOk

/-- The engine's self-test: the checks above, compiled. -/
def allOk : Bool := answersOk && replayOk && fastOk && wireOk && requestsOk && snapshotsOk && coresOk &&
  theoremsOk && recordsOk && readOk && everyRuleOk

end Work.Examples
