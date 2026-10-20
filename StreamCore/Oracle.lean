-- Copyright (c) 2026 the proofbeta authors. All rights reserved. See LICENSE.
import StreamCore.Streams

/-!
# The rules, run

A happy path, and for every rule a candidate that only that rule refuses ("every rule bites"). `#guard` fails the
build if any answer changes. The cases are data (`cases`, `validLogs`, `commandsProduceEvents`), so the compiled
engine runs them too (`stream-engine --self-test`).
-/

namespace StreamCore.Examples
open StreamCore

def url := "https://example.org/proofbeta/commit/0123456789abcdef0123456789abcdef01234567"

/-! Ids are canonical lowercase UUIDs; these are named for reading. -/
def alice : Id := "a11ce000-0000-4000-8000-000000000001"
def bob : Id := "b0b00000-0000-4000-8000-000000000002"
def carol : Id := "ca401000-0000-4000-8000-000000000003"
def dave : Id := "da7e0000-0000-4000-8000-000000000004"
def erin : Id := "e0140000-0000-4000-8000-000000000005"
/-- An agent: no id says so (ids are opaque); a creation records its creator's kind (`actor_kind`). -/
def ada : Id := "ada00000-0000-7000-8000-000000000006"
def stream : Id := "7ea30000-0000-7000-8000-000000000001"
def stream2 : Id := "7ea30000-0000-7000-8000-000000000002"
def stream3 : Id := "7ea30000-0000-7000-8000-000000000003"
def stream9 : Id := "7ea30000-0000-7000-8000-000000000009"

#guard [alice, bob, carol, dave, erin, ada, stream, stream2, stream3, stream9].all validUuid
#guard !validUuid "A11CE000-0000-4000-8000-000000000001"        -- uppercase
#guard !validUuid "a11ce000-0000-4000-8000-00000000001"         -- 35 characters
#guard !validUuid "a11ce000000040008000000000000001"            -- no hyphens
#guard !validUuid "a11ce000-0000-4000-8000-00000000000\u00a0"   -- a look-alike space
#guard !validUuid "alice"

/-- Alice creates `stream`, invites bob and promotes him, invites carol; bob creates `stream2` and is its only admin. -/
def happy : Log :=
  [ .streamCreate alice stream url none,
    .principalInvite alice stream bob none,
    .principalPromote alice stream bob none,
    .principalInvite alice stream carol none,
    .streamCreate bob stream2 url none ]

/-- Alice bans carol from `stream`. -/
def withBan : Log := happy ++ [.principalBan alice stream carol none]

/-- Bob ends `stream`'s stream. -/
def ended : Log := happy ++ [.streamPanic bob stream (some "ewm1.c3RvcA==")]

#guard check happy
#guard check withBan
#guard check ended
#guard validRevisionUrl "https://git.example.org/repo#0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
#guard validRevisionUrl "https://example.org/x/y@0123456789abcdef0123456789abcdef01234567"
#guard !validRevisionUrl "https://example.org/x/y/commit/0123456789ABCDEF0123456789abcdef01234567"

/-- Every example: the log, the candidate, and the answer. -/
def cases : List (Log × Event × Option String) :=
  [ (happy, .streamCreate dave stream url none, some "id_taken"),
    (happy, .streamCreate dave stream3 "https://example.org/x/y/commit/0123456" none, some "invalid_revision_url"),
    (happy, .streamCreate ada stream3 ⟨url, some .agent⟩ none, some "creator_not_person"),  -- an agent creates none
    (happy, .principalInvite alice stream9 dave none, some "unknown_stream"),
    (ended, .principalInvite alice stream dave none, some "stream_ended"),
    (ended, .streamPanic carol stream none, some "stream_ended"),            -- after a panic, whoever sends it
    (ended, .streamPanic bob stream none, some "stream_ended"),              -- a stream panics once
    (happy, .principalInvite carol stream dave none, some "not_stream_admin"),  -- a member is not an admin
    (happy, .principalInvite dave stream erin none, some "not_stream_admin"),
    (happy, .streamPanic alice stream2 none, some "not_stream_admin"),         -- admin-ness is per stream
    (withBan, .principalInvite alice stream carol none, some "banned"),
    (withBan, .principalPromote alice stream carol none, some "banned"),
    (happy, .principalInvite alice stream carol none, some "already_member"),
    (happy, .principalPromote alice stream dave none, some "not_member"),
    (happy, .principalDemote alice stream dave none, some "not_member"),
    (happy, .principalPromote alice stream bob none, some "already_admin"),
    (happy, .principalDemote alice stream carol none, some "not_an_admin"),
    (withBan, .principalBan alice stream carol none, some "already_banned"),
    (happy, .principalDemote bob stream2 bob none, some "last_admin"),
    (happy, .principalBan bob stream2 bob none, some "last_admin"),
    (happy ++ [.principalDemote alice stream bob none], .principalDemote alice stream alice none, some "last_admin"),
    -- acceptances
    (happy, .principalBan alice stream dave none, none),                    -- a ban can come before any invite
    (happy, .principalDemote alice stream bob none, none),
    (happy, .principalBan alice stream bob none, none),                     -- an admin is banned while another remains
    (happy, .principalDemote alice stream alice none, none),                -- an admin may step down if one remains
    (happy, .principalInvite bob stream2 alice none, none),                 -- the same principal on two streams
    (happy, .principalInvite alice stream ada none, none),                  -- any principal joins as a member
    (happy, .streamCreate erin stream3 ⟨url, some .person⟩ none, none),    -- an attested person creates
    (ended, .streamPanic bob stream2 none, none),                          -- other streams carry on
    (ended, .streamCreate alice stream3 url none, none) ]

#guard cases.all fun c => rejection c.1 c.2.1 == c.2.2

-- the fast path answers every case the same (`fold_sound`, run on the examples)
def fastPathAgrees : Bool := cases.all fun c => rejectionS (fold c.2.1.stream c.1) c.2.1 == c.2.2

#guard fastPathAgrees

-- Every rule's reason appears among the cases: every rule bites.
#guard rules.all fun r => cases.any fun c => c.2.2 == some r.reason

/-! ## Who may act (the contract with the layer above) -/

#guard Past.mayAct happy stream carol                                  -- invited: may act, need not
#guard !(Past.mayAct happy stream dave)
#guard Past.mayAct (happy ++ [.principalDemote alice stream bob none]) stream bob   -- demoted, still a member
#guard !(Past.mayAct withBan stream carol)
#guard !(Past.mayAct ended stream alice) && Past.mayAct ended stream2 bob

def validLogs : List Log :=
  [happy, withBan, ended, ended ++ [.streamPanic bob stream2 none],
   happy ++ [.principalPromote bob stream carol none, .principalDemote carol stream alice none,
             .principalBan carol stream alice none, .principalBan carol stream dave none]]

#guard validLogs.all check

/-! ## Commands, in order, produce the events -/

def happyCommands : List Request :=
  [ (alice, .streamCreate url none, [stream]),
    (alice, .principalInvite stream bob none, []),
    (alice, .principalPromote stream bob none, []),
    (alice, .principalInvite stream carol none, []),
    (bob, .streamCreate url none, [stream2]),
    (bob, .streamPanic stream (some "ewm1.c3RvcA=="), []) ]

/-- Refusals before any rule and by the rules; a refused request leaves the log as it was. -/
def mixedCommands : List Request :=
  happyCommands ++
  [ (carol, .streamCreate url none, [stream]),
    (alice, .streamPanic stream2 none, ["x"]),
    (alice, .streamCreate url none, []),
    (alice, .principalInvite stream dave none, []),
    (alice, .streamPanic stream2 none, []),
    (bob, .principalDemote stream2 bob none, []),
    (bob, .principalInvite stream2 alice none, []) ]

def commandsProduceEvents : Bool :=
  run happyCommands == (ended, ended.map Response.accepted) &&
  run mixedCommands == (ended ++ [.principalInvite bob stream2 alice none],
    ended.map Response.accepted ++
      [.rejected "id_taken", .rejected "fresh_ids", .rejected "fresh_ids", .rejected "stream_ended",
       .rejected "not_stream_admin", .rejected "last_admin", .accepted (.principalInvite bob stream2 alice none)])

#guard commandsProduceEvents

end StreamCore.Examples
