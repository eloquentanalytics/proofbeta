# The line protocol

Both engines speak the same protocol: one JSON value per line on stdin, one JSON value per line on stdout, in order,
one answer per non-empty line. The engine prints `{"ready":true}` first. It holds no storage: it starts empty, and
everything it knows about a stream it was told on this connection.

```
stream-engine                 serve the core (streams, members, admins, bans, panics)
work-engine                   serve the core with the work layer (agents and work items)
<engine> --self-test          run the worked examples through the compiled code; exit 0 when they pass
<engine> --revision           print {"revision": <commit>, "repo": <url>}
```

`spec-engine` is the specification path for differential testing only (one global log, every request decided against
the whole log; `{"reset":true}` empties it). It is not part of the protocol below.

## Encoding

- UTF-8, one value per line, terminated by a line feed. Empty lines (after trailing whitespace is trimmed) get no answer.
- Answers have no whitespace, and an object's keys are printed in descending order. Parse them as JSON; byte equality
  is only promised between two runs of the same engine (the corpus relies on it).
- Numbers in input are natural numbers only (`from`, `k`). A repeated key keeps its last value. A `\u` escape of a
  UTF-16 surrogate decodes to U+0000, which no field accepts.
- Every id (principal, stream, work item) is a canonical lowercase UUID: `8-4-4-4-12` lowercase hex digits.
- `meta`, wherever it appears, is absent, `null`, or `ewm1.` followed by base64url (at most two `=`), at most 4096 bytes.
  The core never reads it; the work layer reads a structured form of it (below).

## Requests

```json
{"caller": {"principal": "<id>"}, "command": {"command": "<name>", ...}, "fresh": ["<id>", ...]}
```

The answer names the stream and the length of the stream the request was decided at (`at`):

```json
{"accept": true,  "event": {...}, "stream": "<id>", "at": 3}
{"accept": false, "reason": "<rule>", "stream": "<id>", "at": 3}
```

An accepted request's `event` is the event to append at position `at`. The engine has already applied it to its own
state; a caller that stores events appends it at `at` only if the stream still has `at` events (compare and set), and
otherwise drops the stream (`drop`), syncs it again and resends.

### The core's commands (both engines)

| command | fields | fresh |
|---|---|---|
| `stream.create` | `proof_revision_url`, optional `actor_kind` (`"person"` or `"agent"`), `meta` | exactly one: the new stream's id |
| `principal.invite` | `stream`, `principal`, `meta` | none |
| `principal.promote` | `stream`, `principal`, `meta` | none |
| `principal.demote` | `stream`, `principal`, `meta` | none |
| `principal.ban` | `stream`, `principal`, `meta` | none |
| `stream.panic` | `stream`, `meta` | none |

`proof_revision_url` is `<scheme>://<host>/<path>` followed by `/commit/`, `#` or `@` and a full 40 or 64 digit
lowercase hex revision. Its stream is judged by the engine built from that revision, for good.

The rules, in the order they are tried; the first that fails is the `reason`:

| reason | refuses |
|---|---|
| `fresh_ids` | the wrong number of fresh ids for the command (tried before every rule) |
| `id_taken` | a creation whose fresh id names an existing stream |
| `invalid_revision_url` | a creation whose URL is not of the form above |
| `creator_not_person` | a creation whose `actor_kind` is `agent` |
| `unknown_stream` | any other command on a stream that was not created |
| `stream_ended` | anything on a stream that panicked |
| `not_stream_admin` | a change or a panic by a principal that is not an admin of the stream now |
| `banned` | inviting or promoting a banned principal |
| `already_member` | inviting a member |
| `not_member` | promoting or demoting a principal that is not a member |
| `already_admin` | promoting an admin |
| `not_an_admin` | demoting a principal that is not an admin |
| `already_banned` | banning a banned principal |
| `last_admin` | demoting or banning the stream's only admin |

### The work layer's commands (`work-engine` only)

| command | fields |
|---|---|
| `principal.agent` | `stream`, `principal`, `meta`: bind `principal` into the stream as an agent |
| `work.create` | `stream`, `work_id`, `meta` = `blob_url`, `blob_sha256` |
| `work.prepare` | `stream`, `work_id`, `agents` (ids joined by `,`, no spaces), `meta` |
| `work.submit` | `stream`, `work_id`, `meta` = `preparation_url`, `preparation_sha256` |
| `work.complete` | `stream`, `work_id`, `meta` = `completion_url`, `completion_sha256` |

None takes fresh ids. A work stream belongs to its creator, the actor, who must be attested a person
(`actor_kind: "person"`) and stays its only member and admin. The structured `meta` is `ewm1.` then the unpadded
base64url of the bytes `0x01`, then each field as key and value, each a two-byte big-endian length and that many bytes
of UTF-8, keys strictly ascending. A URL is any 1 to 2048 characters without control characters; a hash is 64
lowercase hex digits.

Rules, in order, after the core's (on the layer's commands): `unknown_stream`, `stream_ended`, `meta_invalid`,
`meta_missing_field`, `meta_bad_field`, `not_actor` (every command but submit is the actor's), `agent_is_actor`,
`already_agent`, `work_id_taken`, `unknown_work`, `not_an_agent`, `already_named`, `not_named` (only a named agent
submits), `already_submitted`, `already_completed`. Guards on the core's commands, after the core's rules:
`actor_kind_unattested` (a creation must state `actor_kind`), `single_member` (no invite, promote, demote or ban).

## Queries

```json
{"query": "stream", "stream": "<id>"}
```

answers the stream as the rules see it: `{"stream", "creator", "proof_revision_url", "ended", "members": [{"principal",
"admin", "may_act"}...], "banned": [...]}`, and on `work-engine` also `"agents"` and `"works": [{"work_id", "meta",
"agents", "submissions": [{"agent", "meta"}...], "completion"}...]`. A stream it does not hold:
`{"error":"unknown_stream"}`.

```json
{"query": "revision"}
```

answers `{"revision": "<commit>", "repo": "<url>"}`: the commit the engine was built from (`-dirty` appended for an
uncommitted tree, `unknown` when unstamped) and the repository URL recorded at build time (`unknown` when none). It
depends on the build, so the corpus does not record it.

## Host-cache messages (optional)

A caller that keeps the events in its own store uses these to hand the engine a stream's stored past instead of
resending its requests. A row is `{"request": <request>, "event": <event>}`, exactly as the engine accepted them.

| message | answer |
|---|---|
| `{"sync": {"stream": s, "from": k, "rows": [row...]}}` | fold the rows onto `s`, whose state must hold exactly `k` events: `{"synced": s, "length": n}`; `{"error": "out_of_sync", "length": n}` when it holds `n ≠ k`; `{"error": "refused", "detail"}` when a row is refused or its event is not its request's |
| `{"load": {"stream": s, "k": k, "state": state}}` | set `s` from a snapshot: `{"loaded": s, "length": k}`. The state is taken as given: verify it first (with `check`) |
| `{"snapshot": s}` | `{"stream": s, "k": n, "state": state}` |
| `{"drop": s}` | forget `s`: `{"dropped": s}` |
| `{"check": {"stream": s, "rows": [row...]}}` | replay the rows from empty through the specification, without touching the cache: `{"checked": s, "length": n, "state": state}`, or `{"error": "refused", "detail"}` |

An empty `sync` of a stream the engine does not hold creates nothing, and neither does a refused request on one.

## What the engine trusts from its caller

The engine decides; it does not authenticate, mint or keep time. It takes as given:

- **`caller.principal`**: who is acting. The caller derives it from its own credentials (gap_token_is_caller).
- **`fresh`**: new ids, unused anywhere. A repeated id is always refused (`id_taken`), never stored, so a bad id costs
  availability, not correctness (gap_id_collisions).
- **`actor_kind`**: whether the creator is a person or an agent (gap_kind_issuance).
- **`at`**: the engine reports the length it decided at; that the caller appends only at that length (compare and set)
  is the caller's, and so is storing what it appends (gap_store_compare_and_set, gap_storage_durability).
- **`load`** states and the rows of `sync`: `sync` re-decides every row, `load` does not.

## Errors

| class | shape | meaning |
|---|---|---|
| malformed | `{"error": "malformed", "detail": "..."}` | the line is not JSON, not a message, or a field is missing, unknown, of the wrong type or of the wrong form. Nothing changes |
| refused request | `{"accept": false, "reason": "<rule>", ...}` | a well-formed request a rule refuses. Nothing changes |
| refused rows | `{"error": "refused", "detail": "..."}` | `sync` or `check` rows that do not replay. Nothing changes |
| out of sync | `{"error": "out_of_sync", "length": n}` | `sync` from a length the engine does not hold. Nothing changes |
| unknown stream | `{"error": "unknown_stream"}` | a read of a stream the engine does not hold |

`detail` texts are for people; they are stable within one revision.
