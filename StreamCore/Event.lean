-- Copyright (c) 2026 the proofbeta authors. All rights reserved. See LICENSE.
/-!
# The event

The six events of the model (README.md), one constructor each, carrying exactly that event's fields, so a malformed
row cannot be written down. Everything non-standard rides in `meta`, which no rule reads. An event's position in the
log is its sequence number. Stream ids are minted by the service; the model needs only that a minted id is fresh,
which is a rule (`id_taken`).

Core Lean only, no Mathlib.
-/

namespace StreamCore

abbrev Id := String

/-- Its form (`validMeta`) is checked when it is parsed. -/
abbrev Meta := Option String

/-- A principal's kind: a person or an agent. On the wire, `"person"` and `"agent"`. -/
inductive PrincipalKind where
  | person
  | agent
  deriving DecidableEq, Repr

/-- **What a creation states besides its creator, its stream and its meta**: the proof revision URL whose rules judge
the stream, and the kind of its creator as the host attests it (`actor_kind` on the wire; absent, as in every creation
written before kinds existed, it is a person: `Creation.kind`). The kind is recorded in the creation event itself, so
whatever a theorem says of the creator's kind follows from the stream's own events; that the attestation is true is the
host's (gap_kind_issuance). A plain URL is a creation with no attested kind (the coercion), so a layer that writes
`.streamCreate url m` means what it always meant. -/
structure Creation where
  url : String
  actorKind : Option PrincipalKind := none
  deriving DecidableEq, Repr

instance : Coe String Creation := ⟨fun u => ⟨u, none⟩⟩

/-- The creator's kind a creation records: the attested one, a person when none is attested. -/
def Creation.kind (c : Creation) : PrincipalKind := c.actorKind.getD .person

inductive Event where
  | streamCreate (actor : Id) (stream : Id) (creation : Creation) («meta» : Meta)
  | principalInvite (actor : Id) (stream : Id) (principal : Id) («meta» : Meta)
  | principalPromote (actor : Id) (stream : Id) (principal : Id) («meta» : Meta)
  | principalDemote (actor : Id) (stream : Id) (principal : Id) («meta» : Meta)
  | principalBan (actor : Id) (stream : Id) (principal : Id) («meta» : Meta)
  | streamPanic (actor : Id) (stream : Id) («meta» : Meta)
  deriving DecidableEq, Repr

/-- Who sent the event: every event has an actor. -/
def Event.actor : Event → Id
  | .streamCreate a .. | .principalInvite a .. | .principalPromote a .. | .principalDemote a .. | .principalBan a ..
  | .streamPanic a .. => a

/-- The stream an event belongs to: every event names one (a creation, the stream it mints). -/
def Event.stream : Event → Id
  | .streamCreate _ t .. | .principalInvite _ t .. | .principalPromote _ t .. | .principalDemote _ t ..
  | .principalBan _ t .. | .streamPanic _ t .. => t

/-- Every id an event mints. -/
def Event.mintedAll : Event → List Id
  | .streamCreate _ t .. => [t]
  | _ => []

/-! ## Forms, checked when an event is parsed -/

def isLowerHex (c : Char) : Bool := c.isDigit || ('a' ≤ c && c ≤ 'f')

def isBase64Url (c : Char) : Bool := c.isAlphanum || c == '-' || c == '_'

/-- An id (a stream, a principal): a canonical lowercase UUID, the form README.md's model states. -/
def validUuid (s : String) : Bool :=
  match s.splitOn "-" with
  | [a, b, c, d, e] =>
    a.length == 8 && b.length == 4 && c.length == 4 && d.length == 4 && e.length == 12 &&
    a.all isLowerHex && b.all isLowerHex && c.all isLowerHex && d.all isLowerHex && e.all isLowerHex
  | _ => false

/-- `ewm1.` then base64url (at least one character, then at most two `=`), at most 4096 bytes. -/
def validMeta (s : String) : Bool :=
  let body := (s.drop 5).copy
  let core := (body.toList.reverse.dropWhile (· == '=')).reverse
  s.utf8ByteSize ≤ 4096 && "ewm1.".toList.isPrefixOf s.toList && body.length - core.length ≤ 2 && 1 ≤ core.length &&
    core.all isBase64Url

/-- An immutable revision id: 40 (SHA-1) or 64 (SHA-256) lowercase hex digits. A prefix is refused, since it could
name a revision of another repository. -/
def validRevision (s : String) : Bool := (s.length == 40 || s.length == 64) && s.all isLowerHex

/-- A revision URL: `<scheme>://<host>/<path>` naming a repository, then `/commit/`, `#` or `@`, then a full revision
id; no whitespace or control characters, at most 2048 characters. It names the revision whose rules judge the stream. -/
def validRevisionUrl (s : String) : Bool :=
  s.length ≤ 2048 && s.all (fun (c : Char) => 32 < c.val && c.val != 127) &&
  let repoOk (repo : String) : Bool :=
    match repo.splitOn "://" with
    | [scheme, rest] =>
      !scheme.isEmpty && scheme.all (fun (c : Char) => c.isAlphanum || c == '+' || c == '-' || c == '.') &&
      (rest.splitOn "/").length ≥ 2 && (rest.splitOn "/").all (!·.isEmpty)
    | _ => false
  let split (sep : String) : Bool :=
    match s.splitOn sep with
    | [repo, rev] => repoOk repo && validRevision rev
    | _ => false
  split "/commit/" || split "#" || split "@"

end StreamCore
