-- Copyright (c) 2026 the proofbeta authors. All rights reserved. See LICENSE.
import Work.Recipes
import Work.Meta

/-!
# Work: one stream, many work items, one person and the agents it binds

A layer on the core (`Layer`, on `coreBase`). A stream of this service belongs to **the actor**, the person who created
it: its creation records the creator's kind as the host attests it (`actor_kind`), which must be a person (the core's
`creator_not_person`) and must be stated (the guard `actor_kind_unattested`). The actor is the stream's only member and
only admin for life: the guard `single_member` refuses every invite, promote, demote and ban. A `stream.panic` by the
actor ends the stream. Every theorem about a stream follows from that stream's own events: who is an agent there is
what the stream's own `principal.agent` events say, never a registry outside it.

Five commands, on the actor's stream, which holds many work items:

- `principal.agent {stream, principal}`: the actor binds `principal` into the stream as an agent, for good; never itself,
  and once per principal.
- `work.create {stream, work_id, meta}`: the actor creates a work item, its id new on the stream (the host fills one in
  when the caller leaves it out); its `meta` (`structured_meta`) carries exactly `blob_url` and `blob_sha256`, where
  the encrypted work is, outside the stream, and the hash of its ciphertext (`blobSchema`). Fixed for good.
- `work.prepare {stream, work_id, agents}`: the actor names agents to prepare a work item: each already bound by
  `principal.agent`, each named at most once per work item (over all its prepares). Issued again later to name more,
  also after the work item is completed. `agents` is the agents' ids joined by `,` (the host takes a JSON array).
- `work.submit {stream, work_id, meta}`: an agent named by an earlier prepare on that work item submits its
  preparation, once per agent per work item, at any time (also after completion); its `meta` carries exactly
  `preparation_url` and `preparation_sha256` (`preparationSchema`).
- `work.complete {stream, work_id, meta}`: the actor completes a work item, once, with its own official answer: `meta`
  carries exactly `completion_url` and `completion_sha256` (`completionSchema`). Completion marks when the work is considered
  finished, and nothing else depends on it: prepare and submit are accepted after it as before.

URLs are opaque: the engine never interprets or compares them (`opaqueUrl`: a non-empty string of at most 2048
characters, none of them a control character); hashes are exactly 64 lowercase hex digits (`isSha256`).

Its memory is the stream's layer events themselves (the recipe `fold_memory`, each step appending the event), so a rule
reads off them who is bound as an agent, which work items exist, who was named and who submitted on each, and which
are completed; its snapshot is the events (`records_codec`'s pieces).
-/

namespace Work
open StreamCore StreamCore.Layer StreamCore.Wire

/-! ## The encrypted work, preparations and answers, in meta -/

/-- A SHA-256 as hex: exactly 64 lowercase hex digits. -/
def isSha256 (s : String) : Bool :=
  s.length == 64 && s.all fun c => ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')

/-- **An opaque URL**: non-empty, at most 2048 characters, no control character (U+0000 to U+001F, U+007F, U+0080 to
U+009F). Nothing else is read of it: no scheme, no form, and it is never compared with another. -/
def opaqueUrl (s : String) : Bool :=
  !s.isEmpty && decide (s.length ≤ 2048) &&
    s.all fun c => 32 ≤ c.toNat && c.toNat != 127 && !(128 ≤ c.toNat && c.toNat ≤ 159)

/-- The work, on `work.create`: `blob_url` and `blob_sha256`, both required, nothing else. -/
def blobSchema : Schema :=
  [⟨"blob_sha256", .str isSha256, true⟩, ⟨"blob_url", .str opaqueUrl, true⟩]

/-- A preparation, on `work.submit`: `preparation_url` and `preparation_sha256`, both required, nothing else. -/
def preparationSchema : Schema :=
  [⟨"preparation_sha256", .str isSha256, true⟩, ⟨"preparation_url", .str opaqueUrl, true⟩]

/-- The actor's answer, on `work.complete`: `completion_url` and `completion_sha256`, both required, nothing else. -/
def completionSchema : Schema :=
  [⟨"completion_sha256", .str isSha256, true⟩, ⟨"completion_url", .str opaqueUrl, true⟩]

/-! ## The agents a prepare names -/

/-- The agents of a prepare's `agents` field: its ids, split at `,`. -/
def agentList (s : String) : List Id := s.splitOn ","

/-- The form of `agents`: one or more canonical UUIDs joined by `,` (an empty field is one empty id, refused). -/
def agentsForm (s : String) : Bool := (agentList s).all validUuid

/-! ## Commands and events -/

/-- The layer's events: the actor, then the command's fields. -/
inductive WorkEvent where
  | agent (actor stream principal : Id) («meta» : Meta)
  | create (actor stream work : Id) («meta» : Meta)
  | prepare (actor stream work : Id) (agents : String) («meta» : Meta)
  | submit (actor stream work : Id) («meta» : Meta)
  | complete (actor stream work : Id) («meta» : Meta)
  deriving DecidableEq

/-- The layer's commands, as the caller sends them. -/
inductive WorkCommand where
  | agent (stream principal : Id) («meta» : Meta)
  | create (stream work : Id) («meta» : Meta)
  | prepare (stream work : Id) (agents : String) («meta» : Meta)
  | submit (stream work : Id) («meta» : Meta)
  | complete (stream work : Id) («meta» : Meta)
  deriving DecidableEq

namespace WorkEvent

/-- Who sent a layer event. -/
def actor : WorkEvent → Id
  | .agent a .. | .create a .. | .prepare a .. | .submit a .. | .complete a .. => a

/-- The meta a layer event carries. -/
def «meta» : WorkEvent → Meta
  | .agent _ _ _ m | .create _ _ _ m | .prepare _ _ _ _ m | .submit _ _ _ m | .complete _ _ _ m => m

/-- The event binds `p` as an agent. -/
def binds (p : Id) : WorkEvent → Bool
  | .agent _ _ q _ => q == p
  | _ => false

/-- The event creates work item `w`. -/
def creates (w : Id) : WorkEvent → Bool
  | .create _ _ w' _ => w' == w
  | _ => false

/-- The event names `p` to prepare work item `w`. -/
def names (w p : Id) : WorkEvent → Bool
  | .prepare _ _ w' as _ => w' == w && (agentList as).contains p
  | _ => false

/-- The event is `p`'s submit on work item `w`. -/
def submits (w p : Id) : WorkEvent → Bool
  | .submit a _ w' _ => w' == w && a == p
  | _ => false

/-- The event completes work item `w`. -/
def completes (w : Id) : WorkEvent → Bool
  | .complete _ _ w' _ => w' == w
  | _ => false

end WorkEvent

/-- The meta a command carries. -/
def WorkCommand.meta : WorkCommand → Meta
  | .agent _ _ m | .create _ _ m | .prepare _ _ _ m | .submit _ _ m | .complete _ _ m => m

/-! ## What the rules read of the stream's events -/

/-- `p` is bound as an agent on the stream. -/
def isAgent (es : List WorkEvent) (p : Id) : Bool := es.any (·.binds p)

/-- Work item `w` was created. -/
def workExists (es : List WorkEvent) (w : Id) : Bool := es.any (·.creates w)

/-- `p` was named to prepare work item `w`. -/
def named (es : List WorkEvent) (w p : Id) : Bool := es.any (·.names w p)

/-- `p` submitted on work item `w`. -/
def submitted (es : List WorkEvent) (w p : Id) : Bool := es.any (·.submits w p)

/-- Work item `w` was completed. -/
def completed (es : List WorkEvent) (w : Id) : Bool := es.any (·.completes w)

/-- **The work** of item `w`: its creation's meta, as the actor sent it. -/
def blobOf (es : List WorkEvent) (w : Id) : Option Meta :=
  es.findSome? fun | .create _ _ w' m => if w' == w then some m else none | _ => none

/-- **The answer** of item `w`: its completion's meta, as the actor sent it. -/
def completionOf (es : List WorkEvent) (w : Id) : Option Meta :=
  es.findSome? fun | .complete _ _ w' m => if w' == w then some m else none | _ => none

/-- The agents bound, in order. -/
def agents (es : List WorkEvent) : List Id := es.filterMap fun | .agent _ _ p _ => some p | _ => none

/-- The work items created, in order: id and meta. -/
def works (es : List WorkEvent) : List (Id × Meta) := es.filterMap fun | .create _ _ w m => some (w, m) | _ => none

/-- The agents named on work item `w`, in order. -/
def namedOn (es : List WorkEvent) (w : Id) : List Id :=
  es.flatMap fun | .prepare _ _ w' as _ => if w' == w then agentList as else [] | _ => []

/-- The submits on work item `w`, in order: the agent and its preparation's meta. -/
def submitsOn (es : List WorkEvent) (w : Id) : List (Id × Meta) :=
  es.filterMap fun | .submit a _ w' m => if w' == w then some (a, m) else none | _ => none

/-! ## The memory: the stream's layer events, and their snapshot -/

/-- One event as JSON: its kind, then its fields in order. -/
def evJ : WorkEvent → J
  | .agent a t p m => .arr [.str "agent", .str a, .str t, .str p, optJ m]
  | .create a t w m => .arr [.str "create", .str a, .str t, .str w, optJ m]
  | .prepare a t w as m => .arr [.str "prepare", .str a, .str t, .str w, .str as, optJ m]
  | .submit a t w m => .arr [.str "submit", .str a, .str t, .str w, optJ m]
  | .complete a t w m => .arr [.str "complete", .str a, .str t, .str w, optJ m]

def evOfJ : J → Except String WorkEvent
  | .arr [.str "agent", .str a, .str t, .str p, m] => (optOfJ m).map (.agent a t p)
  | .arr [.str "create", .str a, .str t, .str w, m] => (optOfJ m).map (.create a t w)
  | .arr [.str "prepare", .str a, .str t, .str w, .str as, m] => (optOfJ m).map (.prepare a t w as)
  | .arr [.str "submit", .str a, .str t, .str w, m] => (optOfJ m).map (.submit a t w)
  | .arr [.str "complete", .str a, .str t, .str w, m] => (optOfJ m).map (.complete a t w)
  | _ => .error "state: expected an event"

theorem evOfJ_toJ (e : WorkEvent) : evOfJ (evJ e) = .ok e := by
  cases e <;> simp [evJ, evOfJ, optOfJ_toJ, Except.map]

/-- The state's codec: the events, as an array. -/
def logToJ (st : List WorkEvent) : J := .arr (st.map evJ)

def logOfJ : J → Except String (List WorkEvent)
  | .arr js => listOfJ evOfJ js
  | _ => .error "state: expected events"

theorem logOfJ_toJ (st : List WorkEvent) : logOfJ (logToJ st) = .ok st := listOfJ_map evOfJ_toJ st

/-- **The memory**: the rules read the stream's layer events before the candidate, in order (`fold_memory`, each step
appending the event). -/
abbrev eventsMemory : Memory WorkEvent :=
  foldMemory [] (fun st e => st ++ [e]) logToJ logOfJ logOfJ_toJ

/-- Folding by appending gives the events back. -/
@[simp] theorem foldl_snoc (acc l : List WorkEvent) : l.foldl (fun st e => st ++ [e]) acc = acc ++ l := by
  induction l generalizing acc with
  | nil => simp
  | cons e l ih => simp [ih]

/-- What a read of the stream adds: `agents` (the ids bound, in order) and `works`, each
`{"work_id", "meta", "agents", "submissions", "completion"}`: the work's meta (its blob), the agents named on it, each
submit `{"agent", "meta"}`, and the completion's meta or `null`. -/
def readFields (st : List WorkEvent) : Fields :=
  [("agents", .arr ((agents st).map .str)),
   ("works", .arr ((works st).map fun (w, m) =>
     .obj [("work_id", .str w), ("meta", optJ m), ("agents", .arr ((namedOn st w).map .str)),
       ("submissions", .arr ((submitsOn st w).map fun (a, m') => .obj [("agent", .str a), ("meta", optJ m')])),
       ("completion", match completionOf st w with | some m' => optJ m' | none => .null)]))]

/-! ## The layer -/

/-- **The layer.** Rules, tried in order: `unknown_stream`, `stream_ended`, `meta_invalid`, `meta_missing_field`,
`meta_bad_field` (the work's meta under `blobSchema` on create, the preparation's under `preparationSchema` on submit,
the answer's under `completionSchema` on complete), `not_actor` (every command but submit: the actor, the stream's only
admin), `agent_is_actor` (principal.agent: not the actor itself), `already_agent` (principal.agent), `work_id_taken`
(create), `unknown_work` (prepare, submit, complete), `not_an_agent` (prepare: every named principal bound),
`already_named` (prepare: no agent named twice on the work item), `not_named` (submit: the caller named on the work
item), `already_submitted` (submit), `already_completed` (complete). Guards on the core's commands:
`actor_kind_unattested` on `stream.create` (the creation states its creator a person), `single_member` on
`principal.invite`, `principal.promote`, `principal.demote` and `principal.ban`. A read adds `agents` and `works`. -/
abbrev work : Layer where
  Cmd := WorkCommand
  Ev := WorkEvent
  toRequest
    | .agent a t p m => (a, .agent t p m)
    | .create a t w m => (a, .create t w m)
    | .prepare a t w as m => (a, .prepare t w as m)
    | .submit a t w m => (a, .submit t w m)
    | .complete a t w m => (a, .complete t w m)
  ofRequest
    | (a, .agent t p m) => .agent a t p m
    | (a, .create t w m) => .create a t w m
    | (a, .prepare t w as m) => .prepare a t w as m
    | (a, .submit t w m) => .submit a t w m
    | (a, .complete t w m) => .complete a t w m
  stream | .agent t .. | .create t .. | .prepare t .. | .submit t .. | .complete t .. => t
  schema := [⟨"principal.agent", [("stream", .uuid), ("principal", .uuid), ("meta", .metaOpt)]⟩,
             ⟨"work.create", [("stream", .uuid), ("work_id", .uuid), ("meta", .metaOpt)]⟩,
             ⟨"work.prepare", [("stream", .uuid), ("work_id", .uuid), ("agents", .str agentsForm),
               ("meta", .metaOpt)]⟩,
             ⟨"work.submit", [("stream", .uuid), ("work_id", .uuid), ("meta", .metaOpt)]⟩,
             ⟨"work.complete", [("stream", .uuid), ("work_id", .uuid), ("meta", .metaOpt)]⟩]
  toVals
    | .agent t p m => ("principal.agent", [.s t, .s p, .m m])
    | .create t w m => ("work.create", [.s t, .s w, .m m])
    | .prepare t w as m => ("work.prepare", [.s t, .s w, .s as, .m m])
    | .submit t w m => ("work.submit", [.s t, .s w, .m m])
    | .complete t w m => ("work.complete", [.s t, .s w, .m m])
  ofVals
    | "principal.agent", [.s t, .s p, .m m] => some (.agent t p m)
    | "work.create", [.s t, .s w, .m m] => some (.create t w m)
    | "work.prepare", [.s t, .s w, .s as, .m m] => some (.prepare t w as m)
    | "work.submit", [.s t, .s w, .m m] => some (.submit t w m)
    | "work.complete", [.s t, .s w, .m m] => some (.complete t w m)
    | _, _ => none
  memory := eventsMemory
  rules := [⟨"unknown_stream", fun v _ _ => v.created⟩,
            ⟨"stream_ended", fun v _ _ => !v.ended⟩,
            ⟨"meta_invalid", fun _ _ e => match e with
              | .create _ _ _ m | .submit _ _ _ m | .complete _ _ _ m => metaOk m
              | _ => true⟩,
            ⟨"meta_missing_field", fun _ _ e => match e with
              | .create _ _ _ m => metaRequired blobSchema m
              | .submit _ _ _ m => metaRequired preparationSchema m
              | .complete _ _ _ m => metaRequired completionSchema m
              | _ => true⟩,
            ⟨"meta_bad_field", fun _ _ e => match e with
              | .create _ _ _ m => metaFields blobSchema m
              | .submit _ _ _ m => metaFields preparationSchema m
              | .complete _ _ _ m => metaFields completionSchema m
              | _ => true⟩,
            ⟨"not_actor", fun v _ e => match e with
              | .submit .. => true
              | _ => v.admin e.actor⟩,
            ⟨"agent_is_actor", fun _ _ e => match e with
              | .agent a _ p _ => p != a
              | _ => true⟩,
            ⟨"already_agent", fun _ es e => match e with
              | .agent _ _ p _ => !isAgent es p
              | _ => true⟩,
            ⟨"work_id_taken", fun _ es e => match e with
              | .create _ _ w _ => !workExists es w
              | _ => true⟩,
            ⟨"unknown_work", fun _ es e => match e with
              | .prepare _ _ w _ _ | .submit _ _ w _ | .complete _ _ w _ => workExists es w
              | _ => true⟩,
            ⟨"not_an_agent", fun _ es e => match e with
              | .prepare _ _ _ as _ => (agentList as).all (isAgent es)
              | _ => true⟩,
            ⟨"already_named", fun _ es e => match e with
              | .prepare _ _ w as _ => decide (agentList as).Nodup && (agentList as).all (!named es w ·)
              | _ => true⟩,
            ⟨"not_named", fun _ es e => match e with
              | .submit a _ w _ => named es w a
              | _ => true⟩,
            ⟨"already_submitted", fun _ es e => match e with
              | .submit a _ w _ => !submitted es w a
              | _ => true⟩,
            ⟨"already_completed", fun _ es e => match e with
              | .complete _ _ w _ => !completed es w
              | _ => true⟩]
  guards := [⟨"actor_kind_unattested", fun _ _ e => match e with
               | .streamCreate _ _ c _ => c.actorKind == some .person
               | _ => true⟩,
             ⟨"single_member", fun _ _ e => match e with
               | .principalInvite .. | .principalPromote .. | .principalDemote .. | .principalBan .. => false
               | _ => true⟩]
  readJ := readFields

end Work
