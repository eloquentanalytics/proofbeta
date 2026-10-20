# proofbeta

A Lean 4 model of an append-only event stream with members, admins, bans and panics, a work layer on top of it
(agents, work items, preparations, completions), the proofs of what they guarantee, and the engines compiled from the
proved functions. Each engine is a process that reads one JSON value per line on stdin and answers one per line on
stdout ([PROTOCOL.md](PROTOCOL.md)). Core Lean only: no Mathlib, no Lean JSON library.

Source-available, all rights reserved: see [LICENSE](LICENSE). You may read the source, and build and run it locally
to verify streams and proofs.

## Three commands

```sh
docker build --build-arg REVISION="$(git rev-parse HEAD)" --build-arg REPO_URL="$(git remote get-url origin)" -t proofbeta .
docker run -i --rm proofbeta < corpus/sessions/work-rules.in.jsonl
corpus/replay "docker run -i --rm --entrypoint /stream-engine proofbeta" "docker run -i --rm proofbeta"
```

The build compiles the proofs and both engines, runs their self-tests and replays the corpus. The image's entry point
is the work engine; the core engine is `--entrypoint /stream-engine`.

Without Docker, with [elan](https://github.com/leanprover/elan) installed (it fetches the toolchain `lean-toolchain`
names):

```sh
scripts/stamp_revision && lake build      # .lake/build/bin/{stream-engine,work-engine,spec-engine}
scripts/check.sh                           # every check below
corpus/replay                              # the corpus against the engines just built
```

## Layout

| path | what |
|---|---|
| `StreamCore/` | the core: events, rules, log, commands, wire, the generic service and layers, theorems, worked examples |
| `Work/` | the work layer: it imports `StreamCore.Interface` and nothing else of the core |
| `Engine/` | unproved: the JSON parser and printer, the per-stream map and message dispatch |
| `StreamMain.lean`, `WorkMain.lean` | the two engines; `SpecMain.lean`, the specification path for differential testing |
| `scripts/` | `stamp_revision`, `check.sh`, `Axioms.lean`, `Audit.lean`, `strip_lean_comments.py` |
| `corpus/` | recorded sessions (`*.in.jsonl` sent, `*.out.jsonl` answered), their seal `SHA256SUMS`, and `replay` |

## The checks (`scripts/check.sh`)

1. `lake build`: the model, every theorem, the worked examples (`#guard`) and the engines, with no warning and no
   `sorry`.
2. Axioms: every declaration under `StreamCore` and `Work` depends on `propext`, `Quot.sound` and `Classical.choice`
   at most.
3. No `sorry`, `admit`, `axiom`, `partial`, `unsafe`, `implemented_by`, `extern` or `native_decide` in the Lean
   sources (comments and strings stripped); the work layer imports only the core's interface.
4. `scripts/Audit.lean`: the dependency tree of the decision, wire and engine functions reaches no `unsafe`, `partial`,
   `implemented_by` or `extern` constant of ours, no panic, and only the pinned list of core primitives.
5. The engines' self-tests: the worked examples, through the compiled code.
6. Every gap stated in `StreamCore/Theorems.lean` is in the table below, and every row is stated there.
7. The corpus replays byte for byte.

## The model

Six events: `stream.create`, `principal.invite`, `principal.promote`, `principal.demote`, `principal.ban`,
`stream.panic`. Ids are canonical lowercase UUIDs. A stream's creator is its first admin; a stream names, at its
creation, the revision whose engine judges it, and that never changes.

### The rules, in the order they are tried

`id_taken`, `invalid_revision_url`, `creator_not_person`, `unknown_stream`, `stream_ended`, `not_stream_admin`,
`banned`, `already_member`, `not_member`, `already_admin`, `not_an_admin`, `already_banned`, `last_admin`; before them
all, `fresh_ids`. The first that fails is the answer ([PROTOCOL.md](PROTOCOL.md) says what each refuses). A principal
may act on a stream (`Past.mayAct`, the contract with a layer above) when it is a member of a stream that has not
ended.

### One revision per stream

A stream is judged by the engine built from the revision its creation names. The engine reports the revision it was
built from (`--revision`, `{"query":"revision"}`): `scripts/stamp_revision` writes it into the build from the
`PROOFBETA_REVISION` environment variable or git, and the repository URL from `PROOFBETA_REPO_URL` or the git remote
`origin`. A caller sends a stream only to the engine of that stream's revision.

## What is proved

Among others (`StreamCore/Theorems.lean`, `CommandTheorems.lean`, `Streams.lean`, `Core.lean`, `Layer.lean`,
`Work/Theorems.lean`):

- the log is the accepted requests' events in request order, each decided against the log before it, and a refusal
  never changes the log (`run_log_eq`, `refused_keeps_log`); a repeated id is refused, never stored
  (`duplicate_refused`);
- every event's actor is the caller (`toEvent_actor`); a creation recording an agent is refused (`creator_is_person`);
  a ban revokes acting for good (`ban_revokes_mayAct_forever`); a panic ends a stream for good (`panic_ends_stream`);
  a stream's revision never changes, whatever any layer appends (`proof_revision_fixed`, `proof_revision_fixedX`);
- deciding on one stream is deciding on the whole log (`respond_local`); the fast path, from a stream's folded state,
  gives exactly the specification's answer (`fold_sound`); the engine's step is `respond`, `run` and the stream's
  length (`entryRequest_spec`), and syncing keeps that (`entrySync_spec`);
- stored rows replay soundly and completely (`replayRows_sound`, `replayRows_complete`); snapshots decide as the
  whole stream does (`snapshot_equiv`); compare-and-set batch appends under any interleaving refine `run`
  (`cas_refines_run`);
- decoding inverts encoding for commands, requests, events, rows and states (`WireTheorems.lean`, `WireState.lean`);
- a layer keeps every guarantee of the base it sits on, and two layers side by side keep each one's (`Layer.lean`);
- the work layer: the actor is the stream's only member and admin for life (`admin_iff_actor`, `actor_for_life`);
  only named agents submit, once each (`submit_after_prepare`, `submit_once`); a work item is created once and
  completed at most once, its blob and its answer fixed (`create_once`, `complete_once`, `blob_fixed`,
  `completion_fixed`); the structured `meta` round-trips and is canonical (`Work/Meta.lean`).

## What is trusted, not proved

Each gap is stated in full at the end of `StreamCore/Theorems.lean`.

| gap | what is trusted |
|---|---|
| gap_wire_bytes | our JSON parser and printer (`Engine/Json.lean`), and the caller's JSON |
| gap_token_is_caller | the caller's principal is whoever the caller authenticated |
| gap_id_collisions | fresh ids are fresh in practice (a repeat is refused, so this is availability only) |
| gap_storage_durability | the caller's store keeps what it reports appended |
| gap_store_compare_and_set | the caller's append is a compare-and-set at the length the engine reports |
| gap_read_decide_append | the caller's glue syncs, decides and appends as `attemptBatch` does |
| gap_compiled_engine | the Lean compiler, the C compiler, the runtime and the pinned primitives |
| gap_runtime_failures | the parser, the runtime (memory, stack) and the IO loop do not fail mid-answer |
| gap_concurrency | concurrent callers serialise each stream through compare-and-set |
| gap_read_visibility | who may read what is outside the model |
| gap_no_unsafe_declarations | checked by `scripts/Audit.lean` and the word scan, not a theorem |
| gap_principal_issuance | principal ids belong to whom the caller says |
| gap_kind_issuance | the attested `actor_kind` is true |
| gap_after_panic | continuing after a panic is out of scope: a new stream |
| gap_layer_above_contract | a layer above the core acts only when `mayAct` holds (proved for `Work/`) |
| gap_unproved_edge | the compiled code is the kernel's code, and the edge (`Engine/`) does what it says |
| gap_engine_is_revision | the binary that judges a stream is built from the stream's revision |
| gap_snapshot_fold | a stored snapshot is the fold of the rows it names (`check` verifies one) |

## The corpus

`corpus/sessions/` holds six sessions, three per engine: `*-rules` (every rule and guard refusing and every command
accepted), `*-cache` (`sync`, `load`, `snapshot`, `drop`, `check`, reads, and every outcome of each) and `*-malformed`
(lines that are not JSON, not messages, or of the wrong form). Every `.in.jsonl` line is sent to a fresh engine and
the `.out.jsonl` file is what it printed, its ready line first. `corpus/replay` checks the seal, then replays every
session and compares byte for byte. `{"query":"revision"}` is not recorded: its answer depends on the build.
