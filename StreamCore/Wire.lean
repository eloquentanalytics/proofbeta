-- Copyright (c) 2026 the proofbeta authors. All rights reserved. See LICENSE.
import StreamCore.Command

/-!
# The wire: JSON values in, JSON values out, and the engine's step

Decoding JSON values into commands, requests and events, encoding them and reads; their proofs are in
`WireTheorems.lean`. Stored rows, answers, the engine's step and its startup replay are the generic ones of
`Service.lean` at the core (`Core.lean`).

`J` is a JSON value with objects as lists of pairs, so a decoder can be stated and proved without a map type; bytes to
`J` and back is `Engine/Json.lean`. Numbers and booleans never occur in this protocol's input and are kept only so output can say
`"accept": true`.
-/

namespace StreamCore.Wire
open StreamCore

/-- A JSON value. -/
inductive J where
  | null
  | bool (b : Bool)
  | num (n : Nat)
  | str (s : String)
  | arr (xs : List J)
  | obj (kvs : List (String × J))

abbrev Fields := List (String × J)

/-! ## Forms -/

/-- No U+0000 (why: `Engine/Json.lean`). -/
def noNul (s : String) : Bool := !s.any (· == '\x00')

/-- A well-formed `meta`: absent, or `ewm1.<base64url>` of at most 4096 bytes without U+0000. -/
def wfMeta : Meta → Bool
  | none => true
  | some s => noNul s && validMeta s

/-- A well-formed command: every id a canonical UUID (`validUuid`), the proof URL without U+0000, `meta` well formed. -/
def commandWf : Command → Bool
  | .streamCreate u m => noNul u.url && wfMeta m
  | .principalInvite t p m | .principalPromote t p m | .principalDemote t p m | .principalBan t p m =>
    validUuid t && validUuid p && wfMeta m
  | .streamPanic t m => validUuid t && wfMeta m

def requestWf : Request → Bool
  | (c, cmd, f) => validUuid c && commandWf cmd && f.all validUuid

/-- A well-formed event: the same forms, through the request it came from. -/
def eventWf (e : Event) : Bool := requestWf (toRequest e)

/-! ## Decoding -/

def fields (what : String) : J → Except String Fields
  | .obj kvs => .ok kvs
  | _ => .error s!"{what}: expected an object"

def onlyKeys (what : String) (kvs : Fields) (allowed : List String) : Except String Unit :=
  match kvs.find? (fun kv => !allowed.contains kv.1) with
  | some (k, _) => .error s!"{what}: unknown key {k}"
  | none => .ok ()

def get? (kvs : Fields) (k : String) : Option J := (kvs.find? (·.1 == k)).map (·.2)

/-- A string field, as it is. Forms are checked once the whole value is decoded (`commandWf`, `eventWf`, ...). -/
def str (what : String) (kvs : Fields) (k : String) : Except String String :=
  match get? kvs k with
  | some (.str s) => .ok s
  | some _ => .error s!"{what}.{k}: expected a string"
  | none => .error s!"{what}.{k}: missing"

/-- The optional `meta` field: absent or null is `none`. -/
def metaOf (what : String) (kvs : Fields) : Except String Meta :=
  match get? kvs "meta" with
  | none | some .null => .ok none
  | some (.str s) => .ok (some s)
  | some _ => .error s!"{what}.meta: expected a string or null"

/-- A principal kind on the wire. -/
def kindJ : PrincipalKind → String
  | .person => "person"
  | .agent => "agent"

/-- The optional `actor_kind` of a creation: absent is `none` (no attestation: a person, `Creation.kind`). -/
def actorKindOf (what : String) (kvs : Fields) : Except String (Option PrincipalKind) :=
  match get? kvs "actor_kind" with
  | none => .ok none
  | some (.str "person") => .ok (some .person)
  | some (.str "agent") => .ok (some .agent)
  | some _ => .error s!"{what}.actor_kind: expected \"person\" or \"agent\""

/-- Accept a decoded value only if it is well formed. -/
def checked {α} (what : String) (wf : α → Bool) (x : α) : Except String α :=
  if wf x then .ok x
  else .error s!"{what}: an id is not a canonical lowercase UUID, a string holds U+0000 (or an escaped surrogate), or meta is not ewm1.<base64url> of at most 4096 bytes"

/-- The four membership changes share one shape: a stream and the principal it names. -/
def changeCommand : String → Option (Id → Id → Meta → Command)
  | "principal.invite" => some .principalInvite
  | "principal.promote" => some .principalPromote
  | "principal.demote" => some .principalDemote
  | "principal.ban" => some .principalBan
  | _ => none

def commandFromJ (j : J) : Except String Command := do
  let w := "command"
  let kvs ← fields w j
  let t ← str w kvs "command"
  let cmd ← match t, changeCommand t with
    | "stream.create", _ => do
      onlyKeys w kvs ["command", "meta", "proof_revision_url", "actor_kind"]
      pure (.streamCreate ⟨← str w kvs "proof_revision_url", ← actorKindOf w kvs⟩ (← metaOf w kvs))
    | "stream.panic", _ => do
      onlyKeys w kvs ["command", "meta", "stream"]
      pure (.streamPanic (← str w kvs "stream") (← metaOf w kvs))
    | _, some mk => do
      onlyKeys w kvs ["command", "meta", "stream", "principal"]
      pure (mk (← str w kvs "stream") (← str w kvs "principal") (← metaOf w kvs))
    | t, none => throw s!"command: unknown command {t}"
  checked w commandWf cmd

def callerFromJ (j : J) : Except String Id := do
  let kvs ← fields "caller" j
  onlyKeys "caller" kvs ["principal"]
  str "caller" kvs "principal"

/-- An array of strings. -/
def strs (what : String) : J → Except String (List String)
  | .arr xs => xs.mapM fun
    | .str s => .ok s
    | _ => .error s!"{what}: expected strings"
  | _ => .error s!"{what}: expected an array"

def freshFromJ : J → Except String Fresh := strs "fresh"

def requestFromJ (j : J) : Except String Request := do
  let kvs ← fields "request" j
  onlyKeys "request" kvs ["caller", "command", "fresh"]
  let some c := get? kvs "caller" | throw "request.caller: missing"
  let some cmd := get? kvs "command" | throw "request.command: missing"
  let some f := get? kvs "fresh" | throw "request.fresh: missing"
  checked "request" requestWf (← callerFromJ c, ← commandFromJ cmd, ← freshFromJ f)

def changeEvent : String → Option (Id → Id → Id → Meta → Event)
  | "principal.invite" => some .principalInvite
  | "principal.promote" => some .principalPromote
  | "principal.demote" => some .principalDemote
  | "principal.ban" => some .principalBan
  | _ => none

def eventFromJ (j : J) : Except String Event := do
  let w := "event"
  let kvs ← fields w j
  let t ← str w kvs "event"
  let e ← match t, changeEvent t with
    | "stream.create", _ => do
      onlyKeys w kvs ["event", "meta", "actor", "actor_kind", "stream", "proof_revision_url"]
      pure (.streamCreate (← str w kvs "actor") (← str w kvs "stream")
        ⟨← str w kvs "proof_revision_url", ← actorKindOf w kvs⟩ (← metaOf w kvs))
    | "stream.panic", _ => do
      onlyKeys w kvs ["event", "meta", "actor", "stream"]
      pure (.streamPanic (← str w kvs "actor") (← str w kvs "stream") (← metaOf w kvs))
    | _, some mk => do
      onlyKeys w kvs ["event", "meta", "actor", "stream", "principal"]
      pure (mk (← str w kvs "actor") (← str w kvs "stream") (← str w kvs "principal") (← metaOf w kvs))
    | t, none => throw s!"event: unknown event {t}"
  checked w eventWf e

/-! ## Encoding -/

def metaJ : Meta → J
  | none => .null
  | some s => .str s

/-- The four membership changes, as commands and as events, share one shape. -/
def changeCommandJ (name : String) (t p : Id) (m : Meta) : J :=
  .obj [("command", .str name), ("stream", .str t), ("principal", .str p), ("meta", metaJ m)]

def changeEventJ (name : String) (a t p : Id) (m : Meta) : J :=
  .obj [("event", .str name), ("actor", .str a), ("stream", .str t), ("principal", .str p), ("meta", metaJ m)]

/-- A creation's `actor_kind`, when it has one: absent when none is attested, so a creation written before kinds
existed is written as it was. -/
def actorKindJ : Option PrincipalKind → Fields
  | none => []
  | some k => [("actor_kind", .str (kindJ k))]

def commandToJ : Command → J
  | .streamCreate u m => .obj ([("command", .str "stream.create"), ("proof_revision_url", .str u.url)] ++
      actorKindJ u.actorKind ++ [("meta", metaJ m)])
  | .principalInvite t p m => changeCommandJ "principal.invite" t p m
  | .principalPromote t p m => changeCommandJ "principal.promote" t p m
  | .principalDemote t p m => changeCommandJ "principal.demote" t p m
  | .principalBan t p m => changeCommandJ "principal.ban" t p m
  | .streamPanic t m => .obj [("command", .str "stream.panic"), ("stream", .str t), ("meta", metaJ m)]

def requestToJ : Request → J
  | (c, cmd, f) => .obj [("caller", .obj [("principal", .str c)]), ("command", commandToJ cmd),
      ("fresh", .arr (f.map .str))]

def eventToJ : Event → J
  | .streamCreate a t u m => .obj ([("event", .str "stream.create"), ("actor", .str a)] ++ actorKindJ u.actorKind ++
      [("stream", .str t), ("proof_revision_url", .str u.url), ("meta", metaJ m)])
  | .principalInvite a t p m => changeEventJ "principal.invite" a t p m
  | .principalPromote a t p m => changeEventJ "principal.promote" a t p m
  | .principalDemote a t p m => changeEventJ "principal.demote" a t p m
  | .principalBan a t p m => changeEventJ "principal.ban" a t p m
  | .streamPanic a t m => .obj [("event", .str "stream.panic"), ("actor", .str a), ("stream", .str t), ("meta", metaJ m)]

def malformedJ (detail : String) : J := .obj [("error", .str "malformed"), ("detail", .str detail)]

def notTranslation : String := "a stored event is not the translation of its stored request"

/-! ## Reads: the same predicates the rules use, answered by the engine

Reads are answered here, from `Past.member`, `Past.admin`, `Past.mayAct` and `Past.banned`, so no other program
recomputes what the rules decide (`mem_members` in `WireTheorems.lean` says the member list is exactly the members). -/

/-- Remove repeats, keeping first occurrences. -/
def dedup : List Id → List Id
  | [] => []
  | x :: xs => if xs.contains x then x :: (dedup xs).filter (· != x) else x :: dedup xs

/-- The principal an event of stream `t` names: its creator, or the principal it invites, promotes, demotes or bans. -/
def named (t : Id) : Event → Option Id
  | .streamCreate a t' .. | .principalInvite _ t' a .. | .principalPromote _ t' a .. | .principalDemote _ t' a ..
  | .principalBan _ t' a .. => if t' == t then some a else none
  | .streamPanic .. => none

/-- The stream's current members, each with whether it is an admin and whether it may act, in order of first mention. -/
def members (log : Log) (t : Id) : List (Id × Bool × Bool) :=
  ((dedup (log.filterMap (named t))).filter (Past.member log t)).map fun p =>
    (p, Past.admin log t p, Past.mayAct log t p)

def bannedList (log : Log) (t : Id) : List Id :=
  dedup (log.filterMap fun | .principalBan _ t' p .. => if t' == t then some p else none | _ => none)

def creation (log : Log) (t : Id) : Option (Id × String) :=
  log.findSome? fun | .streamCreate a t' u .. => if t' == t then some (a, u.url) else none | _ => none

/-- A member as reads show it: the principal, whether it is an admin, whether it may act. -/
def memberJ : Id × Bool × Bool → J
  | (p, ad, ma) => .obj [("principal", .str p), ("admin", .bool ad), ("may_act", .bool ma)]

/-- What a read of stream `t` answers. -/
def streamJ (log : Log) (t : Id) : J :=
  match creation log t with
  | none => .obj [("error", .str "unknown_stream")]
  | some (a, u) => .obj [("stream", .str t), ("creator", .str a), ("proof_revision_url", .str u),
      ("ended", .bool (Past.ended log t)),
      ("members", .arr ((members log t).map memberJ)),
      ("banned", .arr ((bannedList log t).map .str))]

end StreamCore.Wire
