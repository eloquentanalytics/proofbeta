-- Copyright (c) 2026 the proofbeta authors. All rights reserved. See LICENSE.
import Work.Layer

/-!
# What Work guarantees

Every theorem is about a valid combined log (`ValidX`: the core's events and the work layer's, each accepted against
the events before it) and follows from the rules and guards that held when its events were accepted, and from the
core's theorems through `h.cores`. Every rule reads one stream's own events (`evs log t`, the core's view of `t`), so
every theorem about a stream follows from that stream's events alone: no registry outside the stream is consulted, in
the rules or in the proofs. None has a hypothesis beyond validity, except where a statement is about one event's
position.
-/

namespace Work
open StreamCore StreamCore.Layer StreamCore.Wire

/-! ## Reading the stream's events -/

@[simp] theorem read_evs (log : work.XLog) (t : Id) : work.memory.read (evs log t) = evs log t := by
  show (evs log t).foldl (fun st e => st ++ [e]) [] = _
  rw [foldl_snoc, List.nil_append]

/-- What `simp` makes of the memory's read: the events, as they are. -/
@[simp] theorem flatten_singletons (l : List WorkEvent) : (l.map fun x => [x]).flatten = l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [ih]

@[simp] theorem isAgent_nil (p : Id) : isAgent [] p = false := rfl
@[simp] theorem isAgent_cons (e : WorkEvent) (es : List WorkEvent) (p : Id) :
    isAgent (e :: es) p = (e.binds p || isAgent es p) := by simp [isAgent]
@[simp] theorem isAgent_append (a b : List WorkEvent) (p : Id) :
    isAgent (a ++ b) p = (isAgent a p || isAgent b p) := by simp [isAgent, List.any_append]

@[simp] theorem workExists_nil (w : Id) : workExists [] w = false := rfl
@[simp] theorem workExists_cons (e : WorkEvent) (es : List WorkEvent) (w : Id) :
    workExists (e :: es) w = (e.creates w || workExists es w) := by simp [workExists]
@[simp] theorem workExists_append (a b : List WorkEvent) (w : Id) :
    workExists (a ++ b) w = (workExists a w || workExists b w) := by simp [workExists, List.any_append]

@[simp] theorem named_nil (w p : Id) : named [] w p = false := rfl
@[simp] theorem named_cons (e : WorkEvent) (es : List WorkEvent) (w p : Id) :
    named (e :: es) w p = (e.names w p || named es w p) := by simp [named]
@[simp] theorem named_append (a b : List WorkEvent) (w p : Id) :
    named (a ++ b) w p = (named a w p || named b w p) := by simp [named, List.any_append]

@[simp] theorem submitted_nil (w p : Id) : submitted [] w p = false := rfl
@[simp] theorem submitted_cons (e : WorkEvent) (es : List WorkEvent) (w p : Id) :
    submitted (e :: es) w p = (e.submits w p || submitted es w p) := by simp [submitted]
@[simp] theorem submitted_append (a b : List WorkEvent) (w p : Id) :
    submitted (a ++ b) w p = (submitted a w p || submitted b w p) := by simp [submitted, List.any_append]

@[simp] theorem completed_nil (w : Id) : completed [] w = false := rfl
@[simp] theorem completed_cons (e : WorkEvent) (es : List WorkEvent) (w : Id) :
    completed (e :: es) w = (e.completes w || completed es w) := by simp [completed]
@[simp] theorem completed_append (a b : List WorkEvent) (w : Id) :
    completed (a ++ b) w = (completed a w || completed b w) := by simp [completed, List.any_append]

/-- A bound agent was bound by an `agent` event of the events. -/
theorem isAgent_mem {es : List WorkEvent} {p : Id} (h : isAgent es p = true) :
    ∃ a t m, WorkEvent.agent a t p m ∈ es := by
  obtain ⟨x, hx, hb⟩ := List.any_eq_true.mp h
  cases x with
  | agent a t q m => simp [WorkEvent.binds] at hb; subst hb; exact ⟨a, t, m, hx⟩
  | _ => simp [WorkEvent.binds] at hb

/-- A named agent was named by a `prepare` of the events, on that work item. -/
theorem named_mem {es : List WorkEvent} {w p : Id} (h : named es w p = true) :
    ∃ a t as m, WorkEvent.prepare a t w as m ∈ es ∧ p ∈ agentList as := by
  obtain ⟨x, hx, hb⟩ := List.any_eq_true.mp h
  cases x with
  | prepare a t w' as m =>
    simp [WorkEvent.names] at hb; obtain ⟨rfl, hp⟩ := hb; exact ⟨a, t, as, m, hx, hp⟩
  | _ => simp [WorkEvent.names] at hb

/-! ## The core's events: one member, the actor, a person -/

/-- `a` is **the actor** of stream `t` in `log`: it created the stream (a log has at most one creator per stream:
`stream_fixed`). -/
def IsActor (log : work.XLog) (t a : Id) : Prop := ∃ u m, Event.streamCreate a t u m ∈ cores log

/-- No invite is ever accepted (the guard `single_member`). -/
theorem no_invite {log : work.XLog} (h : ValidX log) {a t p : Id} {m : Meta} :
    (.inl (.principalInvite a t p m) : work.XEv) ∉ log := by
  intro hm
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hm
  have := h.guardHoldsNamed "single_member"
  simp at this

/-- No promote is ever accepted (the guard `single_member`). -/
theorem no_promote {log : work.XLog} (h : ValidX log) {a t p : Id} {m : Meta} :
    (.inl (.principalPromote a t p m) : work.XEv) ∉ log := by
  intro hm
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hm
  have := h.guardHoldsNamed "single_member"
  simp at this

/-- No demote is ever accepted (the guard `single_member`). -/
theorem no_demote {log : work.XLog} (h : ValidX log) {a t p : Id} {m : Meta} :
    (.inl (.principalDemote a t p m) : work.XEv) ∉ log := by
  intro hm
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hm
  have := h.guardHoldsNamed "single_member"
  simp at this

/-- No ban is ever accepted (the guard `single_member`). -/
theorem no_ban {log : work.XLog} (h : ValidX log) {a t p : Id} {m : Meta} :
    (.inl (.principalBan a t p m) : work.XEv) ∉ log := by
  intro hm
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hm
  have := h.guardHoldsNamed "single_member"
  simp at this

/-- **The actor is the only admin**: in a valid log, a principal is a current admin of a stream iff it created it. -/
theorem admin_iff_actor {log : work.XLog} (h : ValidX log) {t p : Id} :
    Past.admin (cores log) t p = true ↔ IsActor log t p := by
  constructor
  · intro hp
    rcases (admin_chain h.cores hp).2 with hc | ⟨pre, post, a, m, he, -⟩
    · exact hc
    · have : Event.principalPromote a t p m ∈ cores log := by rw [he]; simp
      exact absurd (mem_bases.mp this) (no_promote h)
  · rintro ⟨u, m, hc⟩
    have hs : Past.hasStream (cores log) t = true := (hasStream_iff _ _).mpr ⟨p, u, m, hc⟩
    obtain ⟨a, ha⟩ := always_an_admin h.cores t hs
    rcases (admin_chain h.cores ha).2 with ⟨u', m', hc'⟩ | ⟨pre, post, b, m', he, -⟩
    · rw [(stream_fixed h.cores hc hc').1]; exact ha
    · have : Event.principalPromote b t a m' ∈ cores log := by rw [he]; simp
      exact absurd (mem_bases.mp this) (no_promote h)

/-- **The actor is the only member**: in a valid log, a principal is on a stream iff it created it. -/
theorem member_iff_actor {log : work.XLog} (h : ValidX log) {t p : Id} :
    Past.member (cores log) t p = true ↔ IsActor log t p := by
  constructor
  · intro hp
    rcases members_by_admin h.cores hp with hc | ⟨pre, post, a, m, he, -⟩
    · exact hc
    · have : Event.principalInvite a t p m ∈ cores log := by rw [he]; simp
      exact absurd (mem_bases.mp this) (no_invite h)
  · intro hp
    exact Past.admin_member ((admin_iff_actor h).mpr hp)

/-- A stream has one actor. -/
theorem actor_unique {log : work.XLog} (h : ValidX log) {t a b : Id} (ha : IsActor log t a) (hb : IsActor log t b) :
    a = b := by
  obtain ⟨u, m, hu⟩ := ha
  obtain ⟨u', m', hu'⟩ := hb
  exact (stream_fixed h.cores hu hu').1

/-- The actor of a prefix is the actor of the whole log. -/
theorem IsActor.append {log : work.XLog} {t a : Id} (h : IsActor log t a) (post : work.XLog) :
    IsActor (log ++ post) t a := by
  obtain ⟨u, m, hc⟩ := h
  exact ⟨u, m, by simp [hc]⟩

/-- **The creator is a person, as its own creation records**: in a valid log, every creation states its creator's kind
(`actor_kind`, attested by the host: the guard `actor_kind_unattested`) and that kind is a person (the core's
`creator_not_person`, lifted: `creations_by_persons`). -/
theorem actor_is_person {log : work.XLog} (h : ValidX log) {a t : Id} {c : Creation} {m : Meta}
    (hc : .inl (Event.streamCreate a t c m) ∈ log) : c.actorKind = some .person ∧ c.kind = .person := by
  refine ⟨?_, creations_by_persons h.cores (mem_bases.mpr hc)⟩
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hc
  have := h.guardHoldsNamed "actor_kind_unattested"
  simpa using this

/-- **The actor is a person**: the creation that makes `a` the actor of `t` records `a` a person. -/
theorem actor_person {log : work.XLog} (h : ValidX log) {t a : Id} (ha : IsActor log t a) :
    ∃ c m, Event.streamCreate a t c m ∈ cores log ∧ c.actorKind = some .person := by
  obtain ⟨c, m, hc⟩ := ha
  exact ⟨c, m, hc, (actor_is_person h (mem_bases.mp hc)).1⟩

/-- **Every core event is the actor's**: a stream's creation, or its panic by its actor. -/
theorem core_events_by_actor {log : work.XLog} (h : ValidX log) {e : Event} (he : .inl e ∈ log) :
    (∃ a t u m, e = .streamCreate a t u m) ∨ ∃ a t m, e = .streamPanic a t m ∧ IsActor log t a := by
  cases e with
  | streamCreate a t u m => exact .inl ⟨a, t, u, m, rfl⟩
  | streamPanic a t m =>
    obtain ⟨pre, post, rfl⟩ := List.append_of_mem he
    have hv : ValidX (pre ++ [.inl (.streamPanic a t m)]) :=
      Service.Valid.prefix h (pre ++ [.inl (.streamPanic a t m)]) post (by simp)
    have hc : Valid (cores pre ++ Event.streamPanic a t m :: []) := by simpa using hv.cores
    have hadm := (acts_by_admin hc rfl (by intros; simp)).2.2
    have := (admin_iff_actor (Service.Valid.prefix h pre _ rfl)).mp (by simpa using hadm)
    exact .inr ⟨a, t, m, rfl, this.append _⟩
  | principalInvite => exact absurd he (no_invite h)
  | principalPromote => exact absurd he (no_promote h)
  | principalDemote => exact absurd he (no_demote h)
  | principalBan => exact absurd he (no_ban h)

/-! ## Only the actor binds agents, creates work, prepares and completes -/

/-- The event is not a submit. -/
def notSubmit : WorkEvent → Prop
  | .submit .. => False
  | _ => True

/-- The rule `not_actor`, read: every layer event but a submit is the actor's (the stream's only admin). -/
theorem by_actor {pre post : work.XLog} {x : WorkEvent} (h : ValidX (pre ++ .inr x :: post)) (hx : notSubmit x) :
    IsActor pre (work.evStream x) x.actor := by
  have hv : ValidX pre := Service.Valid.prefix h pre _ rfl
  have h1 := h.holdsNamed "not_actor"
  cases x <;> simp [notSubmit] at hx <;> simp at h1 <;> exact (admin_iff_actor hv).mp h1

/-- **Only the actor binds an agent.** -/
theorem agent_by_actor {pre post : work.XLog} {a t p : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.agent a t p m) :: post)) : IsActor pre t a := by_actor h trivial

/-- **Only the actor creates a work item.** -/
theorem create_by_actor {pre post : work.XLog} {a t w : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.create a t w m) :: post)) : IsActor pre t a := by_actor h trivial

/-- **Only the actor prepares** (names agents on a work item). -/
theorem prepare_by_actor {pre post : work.XLog} {a t w : Id} {as : String} {m : Meta}
    (h : ValidX (pre ++ .inr (.prepare a t w as m) :: post)) : IsActor pre t a := by_actor h trivial

/-- **Only the actor completes a work item.** -/
theorem complete_by_actor {pre post : work.XLog} {a t w : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.complete a t w m) :: post)) : IsActor pre t a := by_actor h trivial

/-- Every layer event is on a stream that exists and has not ended (`unknown_stream`, `stream_ended`). -/
theorem acts_on_live_stream {pre post : work.XLog} {x : WorkEvent} (h : ValidX (pre ++ .inr x :: post)) :
    Past.hasStream (cores pre) (work.evStream x) = true ∧ Past.ended (cores pre) (work.evStream x) = false := by
  have h1 := h.holdsNamed "unknown_stream"
  have h2 := h.holdsNamed "stream_ended"
  simp at h1 h2
  exact ⟨h1, h2⟩

/-! ## Agents: bound by the actor, for good, never the actor -/

/-- **A principal is bound as an agent at most once per stream** (`already_agent`). -/
theorem bind_once {pre mid post : work.XLog} {a a' t p : Id} {m m' : Meta}
    (h : ValidX (pre ++ .inr (.agent a t p m) :: mid ++ .inr (.agent a' t p m') :: post)) : False := by
  have h1 := h.holdsNamed "already_agent"
  simp [evs_cons, WorkEvent.binds] at h1

/-- **An agent stays an agent**: once `p` is bound on stream `t`, it is bound after anything appended (no hypothesis:
no event unbinds). -/
theorem agent_stays {log : work.XLog} {t p : Id} (h : isAgent (evs log t) p = true) (post : work.XLog) :
    isAgent (evs (log ++ post) t) p = true := by
  simp [h]

/-- **A principal bound as an agent is never the actor** of its stream (`agent_is_actor`, with `not_actor`: the binder
is the actor, and a stream has one). -/
theorem agent_not_actor {log : work.XLog} (h : ValidX log) {t p : Id} (hb : isAgent (evs log t) p = true) :
    ¬ IsActor log t p := by
  intro hp
  obtain ⟨a, t', m, hm⟩ := isAgent_mem hb
  obtain ⟨hm', ht⟩ := mem_evs.mp hm
  simp at ht; subst ht
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hm'
  have h1 := h.holdsNamed "agent_is_actor"
  simp at h1
  have ha := (agent_by_actor h).append (.inr (.agent a t' p m) :: post)
  exact h1 (actor_unique h hp ha)

/-! ## Submits: by an agent bound and named earlier, once per work item -/

/-- **Every submit is by an agent bound earlier and named by an earlier prepare on that work item** (`not_named`, and
`not_an_agent` at that prepare): before the submit, the stream has a binding of its sender as an agent and a prepare
on the same work item naming it, and the binding came before that prepare. -/
theorem submit_after_prepare {pre post : work.XLog} {a t w : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.submit a t w m) :: post)) :
    ∃ pre₁ pre₂ b as m', pre = pre₁ ++ .inr (.prepare b t w as m') :: pre₂ ∧ a ∈ agentList as ∧
      ∃ b' m'', .inr (WorkEvent.agent b' t a m'') ∈ pre₁ := by
  have h1 := h.holdsNamed "not_named"
  simp at h1
  obtain ⟨b, t', as, m', hm, ha⟩ := named_mem h1
  obtain ⟨hm', ht⟩ := mem_evs.mp hm
  simp at ht; subst ht
  obtain ⟨pre₁, pre₂, rfl⟩ := List.append_of_mem hm'
  have hv : ValidX (pre₁ ++ .inr (.prepare b t' w as m') :: pre₂) := Service.Valid.prefix h _ _ rfl
  have h2 := hv.holdsNamed "not_an_agent" (post := pre₂)
  simp at h2
  obtain ⟨b', t'', m'', hb⟩ := isAgent_mem (h2 a ha)
  obtain ⟨hb', ht⟩ := mem_evs.mp hb
  simp at ht; subst ht
  have hb := hb'
  exact ⟨pre₁, pre₂, b, as, m', rfl, ha, b', m'', hb⟩

/-- **Every submitter is an agent of the stream, and never its actor.** -/
theorem submit_by_agent {pre post : work.XLog} {a t w : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.submit a t w m) :: post)) : isAgent (evs pre t) a = true ∧ ¬ IsActor pre t a := by
  obtain ⟨pre₁, pre₂, b, as, m', rfl, -, b', m'', hb⟩ := submit_after_prepare h
  have hi : isAgent (evs (pre₁ ++ .inr (WorkEvent.prepare b t w as m') :: pre₂) t) a = true := by
    simp only [isAgent, List.any_eq_true]
    exact ⟨WorkEvent.agent b' t a m'', mem_evs.mpr ⟨List.mem_append_left _ hb, rfl⟩, by simp [WorkEvent.binds]⟩
  exact ⟨hi, agent_not_actor (Service.Valid.prefix h _ _ rfl) hi⟩

/-- **Each agent submits at most once per work item** (`already_submitted`). -/
theorem submit_once {pre mid post : work.XLog} {a t w : Id} {m m' : Meta}
    (h : ValidX (pre ++ .inr (.submit a t w m) :: mid ++ .inr (.submit a t w m') :: post)) : False := by
  have h1 := h.holdsNamed "already_submitted"
  simp [evs_cons, WorkEvent.submits] at h1

/-- **Every preparation submitted is a structured meta with `preparation_url` and `preparation_sha256`**. -/
theorem submit_preparation {pre post : work.XLog} {a t w : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.submit a t w m) :: post)) :
    ∃ v, decodeMeta m = some v ∧ conforms preparationSchema v = true := by
  have h1 := h.holdsNamed "meta_invalid"
  have h2 := h.holdsNamed "meta_missing_field"
  have h3 := h.holdsNamed "meta_bad_field"
  exact (meta_rules_iff preparationSchema m).mp (by simp_all)

/-- **An agent is named at most once per work item** (`already_named`): no two prepares on it name the same agent. -/
theorem named_once {pre mid post : work.XLog} {a a' t w p : Id} {as as' : String} {m m' : Meta}
    (h : ValidX (pre ++ .inr (.prepare a t w as m) :: mid ++ .inr (.prepare a' t w as' m') :: post))
    (hp : p ∈ agentList as) (hp' : p ∈ agentList as') : False := by
  have h1 := h.holdsNamed "already_named"
  simp [evs_cons, WorkEvent.names] at h1
  have := h1.2 p hp'
  simp_all

/-! ## Work items: created once, completed at most once, the blob and the answer fixed -/

/-- **A work item is created once per stream** (`work_id_taken`). -/
theorem create_once {pre mid post : work.XLog} {a a' t w : Id} {m m' : Meta}
    (h : ValidX (pre ++ .inr (.create a t w m) :: mid ++ .inr (.create a' t w m') :: post)) : False := by
  have h1 := h.holdsNamed "work_id_taken"
  simp [evs_cons, WorkEvent.creates] at h1

/-- **A work item is completed at most once** (`already_completed`). -/
theorem complete_once {pre mid post : work.XLog} {a a' t w : Id} {m m' : Meta}
    (h : ValidX (pre ++ .inr (.complete a t w m) :: mid ++ .inr (.complete a' t w m') :: post)) : False := by
  have h1 := h.holdsNamed "already_completed"
  simp [evs_cons, WorkEvent.completes] at h1

theorem blobOf_isSome (es : List WorkEvent) (w : Id) : (blobOf es w).isSome = workExists es w := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [blobOf, List.findSome?_cons, workExists_cons] at ih ⊢
    cases e with
    | create a t w' m => cases hw : w' == w <;> simp_all [WorkEvent.creates]
    | _ => simpa [WorkEvent.creates] using ih

theorem completionOf_isSome (es : List WorkEvent) (w : Id) : (completionOf es w).isSome = completed es w := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [completionOf, List.findSome?_cons, completed_cons] at ih ⊢
    cases e with
    | complete a t w' m => cases hw : w' == w <;> simp_all [WorkEvent.completes]
    | _ => simpa [WorkEvent.completes] using ih

/-- **Once a work item has a blob, appending anything keeps it** (no hypothesis: no event updates it). -/
theorem blob_fixed {log : work.XLog} {t w : Id} {m : Meta} (h : blobOf (evs log t) w = some m) (post : work.XLog) :
    blobOf (evs (log ++ post) t) w = some m := by
  unfold blobOf at *
  rw [evs_append, List.findSome?_append, h]; rfl

/-- **Once a work item has an answer, appending anything keeps it** (no hypothesis). -/
theorem completion_fixed {log : work.XLog} {t w : Id} {m : Meta} (h : completionOf (evs log t) w = some m)
    (post : work.XLog) : completionOf (evs (log ++ post) t) w = some m := by
  unfold completionOf at *
  rw [evs_append, List.findSome?_append, h]; rfl

/-- The fields of a value conforming to a two-field schema of a URL and a hash. -/
theorem url_sha_fields {v : MetaValue} {ku ks : String}
    (h : conforms [⟨ks, .str isSha256, true⟩, ⟨ku, .str opaqueUrl, true⟩] v = true) (hne : ks ≠ ku) :
    ∃ url sha, v.get ku = some url ∧ opaqueUrl url = true ∧ v.get ks = some sha ∧ isSha256 sha = true := by
  obtain ⟨url, hu⟩ := conforms_required h (f := ⟨ku, .str opaqueUrl, true⟩) (by simp) rfl
  obtain ⟨sha, hs⟩ := conforms_required h (f := ⟨ks, .str isSha256, true⟩) (by simp) rfl
  obtain ⟨fu, hfu, hku⟩ := conforms_kind h hu
  obtain ⟨fs, hfs, hks⟩ := conforms_kind h hs
  have h1 : (ks == ku) = false := by simpa using hne
  simp [List.find?, h1] at hfu hfs
  subst hfu hfs
  exact ⟨url, sha, hu, hku, hs, hks⟩

/-- **A work item's blob is exactly its creator's, the actor's, and never changes.** In a valid log, the creation of
work item `w` on stream `t` is the actor's, and fixes `w`'s blob: at that point and after anything appended, it is the
creation's meta, which decodes to a `blob_url` (opaque) and a `blob_sha256` (64 lowercase hex digits), as the actor
sent it (`event_meta_is_sent`). -/
theorem work_blob {pre post : work.XLog} {a t w : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.create a t w m) :: post)) (more : work.XLog) :
    IsActor pre t a ∧ blobOf (evs (pre ++ .inr (.create a t w m) :: post ++ more) t) w = some m ∧
      ∃ v, decodeMeta m = some v ∧ ∃ url sha, v.get "blob_url" = some url ∧ opaqueUrl url = true ∧
        v.get "blob_sha256" = some sha ∧ isSha256 sha = true := by
  refine ⟨create_by_actor h, ?_, ?_⟩
  · have h1 := h.holdsNamed "work_id_taken"
    simp at h1
    have hn : blobOf (evs pre t) w = none := by
      have := blobOf_isSome (evs pre t) w
      rw [h1] at this; exact Option.not_isSome_iff_eq_none.mp (by simp [this])
    have he : evs (pre ++ .inr (.create a t w m) :: post ++ more) t =
        evs pre t ++ .create a t w m :: (evs post t ++ evs more t) := by simp
    rw [he]
    unfold blobOf at hn ⊢
    rw [List.findSome?_append, hn]
    simp
  · have h1 := h.holdsNamed "meta_invalid"
    have h2 := h.holdsNamed "meta_missing_field"
    have h3 := h.holdsNamed "meta_bad_field"
    obtain ⟨v, hd, hc⟩ := (meta_rules_iff blobSchema m).mp (by simp_all)
    exact ⟨v, hd, url_sha_fields hc (by decide)⟩

/-- **A work item's answer is the actor's and fixed once recorded.** In a valid log, the completion of `w` is the
actor's, and from it on, whatever is appended, `w`'s answer is the completion's meta: a `completion_url` (opaque) and a
`completion_sha256`, as the actor sent it. Nothing is checked of how it relates to any other URL. -/
theorem work_completion {pre post : work.XLog} {a t w : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.complete a t w m) :: post)) (more : work.XLog) :
    IsActor pre t a ∧ completionOf (evs (pre ++ .inr (.complete a t w m) :: post ++ more) t) w = some m ∧
      ∃ v, decodeMeta m = some v ∧ ∃ url sha, v.get "completion_url" = some url ∧ opaqueUrl url = true ∧
        v.get "completion_sha256" = some sha ∧ isSha256 sha = true := by
  refine ⟨complete_by_actor h, ?_, ?_⟩
  · have h1 := h.holdsNamed "already_completed"
    simp at h1
    have hn : completionOf (evs pre t) w = none := by
      have := completionOf_isSome (evs pre t) w
      rw [h1] at this; exact Option.not_isSome_iff_eq_none.mp (by simp [this])
    have he : evs (pre ++ .inr (.complete a t w m) :: post ++ more) t =
        evs pre t ++ .complete a t w m :: (evs post t ++ evs more t) := by simp
    rw [he]
    unfold completionOf at hn ⊢
    rw [List.findSome?_append, hn]
    simp
  · have h1 := h.holdsNamed "meta_invalid"
    have h2 := h.holdsNamed "meta_missing_field"
    have h3 := h.holdsNamed "meta_bad_field"
    obtain ⟨v, hd, hc⟩ := (meta_rules_iff completionSchema m).mp (by simp_all)
    exact ⟨v, hd, url_sha_fields hc (by decide)⟩

/-- **A complete, prepare or submit names a work item that exists** (`unknown_work`). -/
theorem acts_on_existing_work {pre post : work.XLog} {x : WorkEvent} {w : Id}
    (h : ValidX (pre ++ .inr x :: post))
    (hx : (∃ a t as m, x = .prepare a t w as m) ∨ (∃ a t m, x = .submit a t w m) ∨ ∃ a t m, x = .complete a t w m) :
    workExists (evs pre (work.evStream x)) w = true := by
  have h1 := h.holdsNamed "unknown_work"
  rcases hx with ⟨a, t, as, m, rfl⟩ | ⟨a, t, m, rfl⟩ | ⟨a, t, m, rfl⟩ <;> simpa using h1

/-! ## When each command is accepted -/

/-- **`principal.agent` is accepted** iff the stream exists and has not ended, the caller is its actor, the principal
is not the actor, and it is not bound already. -/
theorem agent_ok_iff {pre : work.XLog} (h : ValidX pre) {a t p : Id} {m : Meta} :
    ValidX (pre ++ [.inr (.agent a t p m)]) ↔
      Past.hasStream (cores pre) t = true ∧ Past.ended (cores pre) t = false ∧ IsActor pre t a ∧ p ≠ a ∧
      isAgent (evs pre t) p = false := by
  rw [h.snoc_inr_iff]
  simp [WorkEvent.actor, ← admin_iff_actor h]

/-- **`work.create` is accepted** iff the stream exists and has not ended, the meta is a work (`blobSchema`), the
caller is the actor, and the work id is new on the stream. -/
theorem create_ok_iff {pre : work.XLog} (h : ValidX pre) {a t w : Id} {m : Meta} :
    ValidX (pre ++ [.inr (.create a t w m)]) ↔
      Past.hasStream (cores pre) t = true ∧ Past.ended (cores pre) t = false ∧
      (∃ v, decodeMeta m = some v ∧ conforms blobSchema v = true) ∧ IsActor pre t a ∧
      workExists (evs pre t) w = false := by
  rw [h.snoc_inr_iff, ← meta_rules_iff]
  simp [WorkEvent.actor, ← admin_iff_actor h, and_assoc]

/-- **`work.prepare` is accepted** iff the stream exists and has not ended, the caller is the actor, the work item
exists, every agent named is bound on the stream, and none is named twice on the work item, in this prepare or an
earlier one. Whether the work item is completed is not among the conditions: **a prepare is accepted after
completion** as before it. -/
theorem prepare_ok_iff {pre : work.XLog} (h : ValidX pre) {a t w : Id} {as : String} {m : Meta} :
    ValidX (pre ++ [.inr (.prepare a t w as m)]) ↔
      Past.hasStream (cores pre) t = true ∧ Past.ended (cores pre) t = false ∧ IsActor pre t a ∧
      workExists (evs pre t) w = true ∧ (∀ p ∈ agentList as, isAgent (evs pre t) p = true) ∧
      (agentList as).Nodup ∧ ∀ p ∈ agentList as, named (evs pre t) w p = false := by
  rw [h.snoc_inr_iff]
  simp [WorkEvent.actor, ← admin_iff_actor h]

/-- **`work.submit` is accepted** iff the stream exists and has not ended, the meta is a preparation
(`preparationSchema`), the work item exists, the caller was named on it by an earlier prepare, and it has not submitted
on it. Whether the work item is completed is not among the conditions: **a submit is accepted after completion**. -/
theorem submit_ok_iff {pre : work.XLog} (h : ValidX pre) {a t w : Id} {m : Meta} :
    ValidX (pre ++ [.inr (.submit a t w m)]) ↔
      Past.hasStream (cores pre) t = true ∧ Past.ended (cores pre) t = false ∧
      (∃ v, decodeMeta m = some v ∧ conforms preparationSchema v = true) ∧
      workExists (evs pre t) w = true ∧ named (evs pre t) w a = true ∧ submitted (evs pre t) w a = false := by
  rw [h.snoc_inr_iff, ← meta_rules_iff]
  simp [and_assoc]

/-- **`work.complete` is accepted** iff the stream exists and has not ended, the meta is an answer (`completionSchema`),
the caller is the actor, the work item exists, and it is not completed. -/
theorem complete_ok_iff {pre : work.XLog} (h : ValidX pre) {a t w : Id} {m : Meta} :
    ValidX (pre ++ [.inr (.complete a t w m)]) ↔
      Past.hasStream (cores pre) t = true ∧ Past.ended (cores pre) t = false ∧
      (∃ v, decodeMeta m = some v ∧ conforms completionSchema v = true) ∧ IsActor pre t a ∧
      workExists (evs pre t) w = true ∧ completed (evs pre t) w = false := by
  rw [h.snoc_inr_iff, ← meta_rules_iff]
  simp [WorkEvent.actor, ← admin_iff_actor h, and_assoc]

/-! ## Completion changes nothing about prepare and submit -/

@[simp] theorem completes_names (a t w w' p : Id) (m : Meta) :
    (WorkEvent.complete a t w' m).names w p = false := rfl
@[simp] theorem completes_binds (a t w' p : Id) (m : Meta) : (WorkEvent.complete a t w' m).binds p = false := rfl
@[simp] theorem completes_creates (a t w w' : Id) (m : Meta) : (WorkEvent.complete a t w' m).creates w = false := rfl
@[simp] theorem completes_submits (a t w w' p : Id) (m : Meta) :
    (WorkEvent.complete a t w' m).submits w p = false := rfl

/-- **A completion has no effect on whether a prepare is accepted**: after any accepted completion, a prepare is
accepted exactly when it would have been without it. -/
theorem prepare_ignores_complete {pre : work.XLog} (h : ValidX pre) {c t w w' : Id} {mc : Meta}
    (hc : ValidX (pre ++ [.inr (.complete c t w' mc)])) {a : Id} {as : String} {m : Meta} :
    ValidX (pre ++ [.inr (.complete c t w' mc)] ++ [.inr (.prepare a t w as m)]) ↔
      ValidX (pre ++ [.inr (.prepare a t w as m)]) := by
  rw [prepare_ok_iff hc, prepare_ok_iff h]
  simp [IsActor]

/-- **A completion has no effect on whether a submit is accepted**: after any accepted completion, a submit is accepted
exactly when it would have been without it. -/
theorem submit_ignores_complete {pre : work.XLog} (h : ValidX pre) {c t w w' : Id} {mc : Meta}
    (hc : ValidX (pre ++ [.inr (.complete c t w' mc)])) {a : Id} {m : Meta} :
    ValidX (pre ++ [.inr (.complete c t w' mc)] ++ [.inr (.submit a t w m)]) ↔
      ValidX (pre ++ [.inr (.submit a t w m)]) := by
  rw [submit_ok_iff hc, submit_ok_iff h]
  simp

/-! ## Meta: what an event records is what its caller sent -/

/-- The meta of a combined event: the core's (`eventMeta`) or the layer's. -/
def xEvMeta : work.XEv → Meta
  | .inl e => eventMeta e
  | .inr x => x.meta

/-- The meta of a combined request: the core command's (`commandMeta`) or the layer command's. -/
def xReqMeta : work.XReq → Meta
  | .inl (_, c, _) => commandMeta c
  | .inr (_, c, _) => c.meta

theorem toRequest_meta (e : work.XEv) : xReqMeta (work.service.toRequest e) = xEvMeta e := by
  cases e with
  | inl e => cases e <;> rfl
  | inr x => cases x <;> rfl

/-- **An event's meta is exactly its request's** (the recipe's `toEvent_meta_of`): the blob a create records, the
preparation a submit records and the answer a complete records are what the caller sent, byte for byte. -/
theorem event_meta_is_sent {r : work.XReq} {e : work.XEv} (h : work.service.toEvent r = .ok e) :
    xEvMeta e = xReqMeta r :=
  toEvent_meta_of xEvMeta xReqMeta toRequest_meta h

/-! ## The proof revision of a stream never changes (the core's, lifted) -/

/-- **A stream's proof revision never changes**, whatever is appended (no hypothesis). -/
theorem revision_fixed {log : work.XLog} {t : Id} {u : String} (h : proofRevision (cores log) t = some u)
    (post : work.XLog) : proofRevision (cores (log ++ post)) t = some u :=
  proof_revision_fixedX h post

/-- **Every creation of a stream carries its revision.** -/
theorem revision_unique {log : work.XLog} (h : ValidX log) {a t : Id} {u : Creation} {m : Meta}
    (hc : .inl (Event.streamCreate a t u m) ∈ log) : proofRevision (cores log) t = some u.url :=
  h.proof_revision_unique hc

/-- **To change the rules, start a new stream**: a creation accepted after stream `t` has a revision names another
stream (the core's `new_proof_new_stream`). -/
theorem new_revision_new_stream {pre post : work.XLog} {a t t' : Id} {u : String} {u' : Creation} {m : Meta}
    (h : ValidX (pre ++ .inl (.streamCreate a t' u' m) :: post)) (hu : proofRevision (cores pre) t = some u) :
    t' ≠ t :=
  new_proof_new_stream (by simpa using h.cores) hu

/-- **The actor keeps its rights for life**: once `a` created stream `t`, it is the actor after anything appended
(while the stream lasts: `stream_ended` refuses everyone after a panic). -/
theorem actor_for_life {log : work.XLog} {t a : Id} (h : IsActor log t a) (post : work.XLog) :
    IsActor (log ++ post) t a := h.append post

end Work
