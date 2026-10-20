-- Copyright (c) 2026 the proofbeta authors. All rights reserved. See LICENSE.
import StreamCore.Event

/-!
# The rules

A rule is a named check on a candidate event against the facts about its stream (`View`). Its name is the
`rejection_reason` a caller sees when it fails. The facts are read from the whole past here (`Past.view`), and the
rules are tried in the order of `rules`, the first that fails being the answer (README.md, "The rules, in the order
they are tried").
-/

namespace StreamCore

abbrev Past := List Event

/-! ## What one event says -/

/-- The event created stream `t`. -/
def creates (t : Id) : Event → Bool
  | .streamCreate _ t' .. => t' == t
  | _ => false

/-- The event put `p` on stream `t`: it created the stream as `p`, or invited `p`. -/
def joins (t p : Id) : Event → Bool
  | .streamCreate a t' .. => t' == t && a == p
  | .principalInvite _ t' p' .. => t' == t && p' == p
  | _ => false

/-- The event banned `p` from stream `t`. -/
def bans (t p : Id) : Event → Bool
  | .principalBan _ t' p' .. => t' == t && p' == p
  | _ => false

/-- The event ended stream `t`. -/
def ends (t : Id) : Event → Bool
  | .streamPanic _ t' .. => t' == t
  | _ => false

/-- What an event says about principal `p` being an admin of stream `t`: creating the stream or being promoted makes it
one; being demoted or banned stops it being one. -/
def adminRel (t p : Id) : Event → Option Bool
  | .streamCreate a t' .. => if t' == t && a == p then some true else none
  | .principalPromote _ t' p' .. => if t' == t && p' == p then some true else none
  | .principalDemote _ t' p' .. | .principalBan _ t' p' .. => if t' == t && p' == p then some false else none
  | _ => none

/-! ## Facts about the past: flat statements, no index and no derived state -/

/-- Stream `t` was created. -/
def Past.hasStream (past : Past) (t : Id) : Bool := past.any (creates t)

/-- `p` joined stream `t`: it created the stream or was invited. -/
def Past.joined (past : Past) (t p : Id) : Bool := past.any (joins t p)

/-- `p` was banned from stream `t`. -/
def Past.banned (past : Past) (t p : Id) : Bool := past.any (bans t p)

/-- Stream `t` was ended by a panic. -/
def Past.ended (past : Past) (t : Id) : Bool := past.any (ends t)

/-- `p` is on stream `t` now: it joined, and was not banned. -/
def Past.member (past : Past) (t p : Id) : Bool := past.joined t p && !past.banned t p

/-- What the latest event of `past` that `rel` speaks about says: `some true`, `some false`, or `none` if no event
does. ("The latest earlier event about this says ...".) -/
def Past.latest (past : Past) (rel : Event → Option Bool) : Option Bool := (past.filterMap rel).getLast?

/-- `p` is an admin of stream `t` now: it is on the stream, and the latest event that makes it an admin or stops it being
one makes it one. -/
def Past.admin (past : Past) (t p : Id) : Bool := past.member t p && (past.latest (adminRel t p)).getD false

/-- Stream `t` has a current admin other than `p`: some creation or promotion names a principal `q ≠ p` that is an admin
now. -/
def Past.otherAdmin (past : Past) (t p : Id) : Bool :=
  past.any fun
    | .streamCreate q t' .. | .principalPromote _ t' q .. => t' == t && q != p && past.admin t q
    | _ => false

/-- `p` may act on stream `t` now (the contract with the layer above: README.md). -/
def Past.mayAct (past : Past) (t p : Id) : Bool := past.member t p && !past.ended t

/-- Some earlier event minted `x`. A stream's id is minted by its creation and by nothing else, so this is
`Past.hasStream` (`minted_eq_hasStream`); it is the vocabulary of `minted_once` and `duplicate_refused`. -/
def Past.minted (past : Past) (x : Id) : Bool := past.any fun p => p.mintedAll.contains x

/-! ## The facts a rule reads, about one stream -/

structure View where
  created : Bool
  ended : Bool
  member : Id → Bool
  admin : Id → Bool
  banned : Id → Bool
  otherAdmin : Id → Bool

/-- The specification's view of stream `t`: the flat statements above. -/
def Past.view (past : Past) (t : Id) : View :=
  ⟨past.hasStream t, past.ended t, past.member t, past.admin t, past.banned t, past.otherAdmin t⟩

structure Rule where
  reason : String
  holds  : View → Event → Bool

/-! ## Rules, in the order they are tried -/

def idTaken : Rule := ⟨"id_taken", fun v e => match e with | .streamCreate .. => !v.created | _ => true⟩

def invalidRevisionUrl : Rule := ⟨"invalid_revision_url", fun _ e =>
  match e with | .streamCreate _ _ c .. => validRevisionUrl c.url | _ => true⟩

/-- Only a person creates a stream: a creation whose attested creator kind (`actor_kind`) is an agent is refused. The
creator becomes the stream's first admin. -/
def creatorNotPerson : Rule := ⟨"creator_not_person", fun _ e =>
  match e with | .streamCreate _ _ c _ => c.kind == .person | _ => true⟩

def unknownStream : Rule := ⟨"unknown_stream", fun v e => match e with | .streamCreate .. => true | _ => v.created⟩

def streamEnded : Rule := ⟨"stream_ended", fun v _ => !v.ended⟩

def notStreamAdmin : Rule := ⟨"not_stream_admin", fun v e =>
  match e with | .streamCreate .. => true | _ => v.admin e.actor⟩

def bannedRule : Rule := ⟨"banned", fun v e =>
  match e with | .principalInvite _ _ p _ | .principalPromote _ _ p _ => !v.banned p | _ => true⟩

def alreadyMember : Rule := ⟨"already_member", fun v e =>
  match e with | .principalInvite _ _ p _ => !v.member p | _ => true⟩

def notMember : Rule := ⟨"not_member", fun v e =>
  match e with | .principalPromote _ _ p _ | .principalDemote _ _ p _ => v.member p | _ => true⟩

def alreadyAdmin : Rule := ⟨"already_admin", fun v e =>
  match e with | .principalPromote _ _ p _ => !v.admin p | _ => true⟩

def notAnAdmin : Rule := ⟨"not_an_admin", fun v e =>
  match e with | .principalDemote _ _ p _ => v.admin p | _ => true⟩

def alreadyBanned : Rule := ⟨"already_banned", fun v e =>
  match e with | .principalBan _ _ p _ => !v.banned p | _ => true⟩

def lastAdmin : Rule := ⟨"last_admin", fun v e =>
  match e with
  | .principalDemote _ _ p _ | .principalBan _ _ p _ => !v.admin p || v.otherAdmin p
  | _ => true⟩

def rules : List Rule :=
  [idTaken, invalidRevisionUrl, creatorNotPerson, unknownStream, streamEnded, notStreamAdmin, bannedRule,
   alreadyMember, notMember, alreadyAdmin, notAnAdmin, alreadyBanned, lastAdmin]

/-- Every rule holds for `e` against the view. -/
def View.ok (v : View) (e : Event) : Bool := rules.all fun r => r.holds v e

/-- The first rule that fails, if any: the answer a caller sees. -/
def View.rejection (v : View) (e : Event) : Option String := (rules.find? fun r => !r.holds v e).map (·.reason)

theorem View.rejection_none_iff (v : View) (e : Event) : v.rejection e = none ↔ v.ok e = true := by
  simp [View.rejection, View.ok, List.find?_eq_none, List.all_eq_true]

end StreamCore
