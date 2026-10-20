-- Copyright (c) 2026 the proofbeta authors. All rights reserved. See LICENSE.
import StreamCore.CommandTheorems

/-!
# One log per stream

Why the service may keep one log per stream, decide a request against that stream's log alone, and coordinate only by
a compare-and-set append (`attemptBatch`). Every rule reads only its own stream (`rejection_local`, `Stream.lean`);
the rest is `Service.lean`'s, at the core.
-/

namespace StreamCore

/-- The answer to a request against the whole log is its answer against its stream's events. -/
theorem respond_local (L : Log) (r : Request) : respond (onStream L (reqStream r)) r = respond L r :=
  Service.respond_local (S := coreService) L r

/-! ## Projection of `run` onto a stream -/

theorem onStream_append_other {L : Log} {e : Event} {s : Id} (h : e.stream ≠ s) :
    onStream (L ++ [e]) s = onStream L s :=
  Service.onStream_append_other (S := coreService) h

theorem onStream_append_same {L : Log} {e : Event} {s : Id} (h : e.stream = s) :
    onStream (L ++ [e]) s = onStream L s ++ [e] :=
  Service.onStream_append_same (S := coreService) h

theorem respond_event_stream {L : Log} {r : Request} {e : Event} (h : respond L r = .accepted e) :
    e.stream = reqStream r :=
  Service.respond_event_stream h

theorem runFrom_project (L : Log) (reqs : List Request) (s : Id) :
    onStream (runFrom L reqs).1 s = (runFrom (onStream L s) (reqs.filter (reqStream · == s))).1 ∧
    ((reqs.zip (runFrom L reqs).2).filter (reqStream ·.1 == s)).map (·.2) =
      (runFrom (onStream L s) (reqs.filter (reqStream · == s))).2 :=
  Service.runFrom_project (S := coreService) L reqs s

/-- **A stream's log is `run` of its own requests.** The events of stream `s` in `run reqs` are `run` of the requests
on `s`, in order, and those requests get the same answers in both. -/
theorem run_project (reqs : List Request) (s : Id) :
    onStream (run reqs).1 s = (run (reqs.filter (reqStream · == s))).1 ∧
    ((reqs.zip (run reqs).2).filter (reqStream ·.1 == s)).map (·.2) = (run (reqs.filter (reqStream · == s))).2 :=
  Service.run_project (S := coreService) reqs s

/-! ## Freshness is local -/

/-- **A creation's id is fresh exactly when its stream is empty.** In a valid log, `id_taken` holds for a creation of
stream `t` exactly when the log has no event on `t`: the only event that mints `t` is `t`'s creation, and every other
event on `t` needs the creation first. -/
theorem idTaken_iff_stream_empty {L : Log} (hv : Valid L) {c t : Id} {u : Creation} {m : Meta} :
    idTaken.holds (Past.view L t) (.streamCreate c t u m) = true ↔ onStream L t = [] := by
  simp only [idTaken, Past.view, Bool.not_eq_true']
  constructor
  · intro hm
    unfold onStream; rw [List.filter_eq_nil_iff]
    intro e he hs
    simp only [beq_iff_eq] at hs
    cases e with
    | streamCreate a t' u' m' =>
      simp [Event.stream] at hs; subst hs
      have : Past.hasStream L t' = true := List.any_eq_true.mpr ⟨_, he, by simp [creates]⟩
      simp [this] at hm
    | _ =>
      obtain ⟨pre, post, rfl⟩ := List.append_of_mem he
      have := (acts_by_admin hv hs (by intros; simp)).1
      simp only [Past.hasStream, List.any_append, Bool.or_eq_false_iff] at hm
      simp only [Past.hasStream] at this
      rw [hm.1] at this; cases this
  · intro he
    cases hm : Past.hasStream L t
    · rfl
    · obtain ⟨e, hmem, hx⟩ := List.any_eq_true.mp hm
      have : e ∈ onStream L t := List.mem_filter.mpr ⟨hmem, by simp [creates_stream hx]⟩
      rw [he] at this; cases this

/-! ## A batch decided in order and appended at once is `run` -/

/-- **Group commit.** Deciding requests one after another from a stream's log `(run before).1` (each against the log
including the events accepted earlier in the batch) and appending the accepted events at once gives exactly the log
and the answers `run` gives for `before ++ reqs`. -/
theorem batch_refines_run (before reqs : List Request) :
    (run before).1 ++ (runFrom (run before).1 reqs).2.filterMap Response.event? = (run (before ++ reqs)).1 ∧
    (run (before ++ reqs)).2 = (run before).2 ++ (runFrom (run before).1 reqs).2 :=
  Service.batch_refines_run (S := coreService) before reqs

/-! ## Compare-and-set batch appends refine `run` -/

/-- A lost compare-and-set changes nothing and answers nothing. -/
theorem attemptBatch_conflict {st : Store} {s : Id} {reqs : List Request} {n : Nat} {st' : Store}
    (h : attemptBatch st s reqs n = (st', .conflict)) : st' = st :=
  Service.attemptBatch_conflict h

theorem committedReqs_append (l₁ l₂ : List (Id × List Request × Outcome)) (s : Id) :
    committedReqs (l₁ ++ l₂) s = committedReqs l₁ s ++ committedReqs l₂ s :=
  Service.committedReqs_append (S := coreService) l₁ l₂ s

theorem deliveredAnswers_append (l₁ l₂ : List (Id × List Request × Outcome)) (s : Id) :
    deliveredAnswers (l₁ ++ l₂) s = deliveredAnswers l₁ s ++ deliveredAnswers l₂ s :=
  Service.deliveredAnswers_append (S := coreService) l₁ l₂ s

theorem execB_spec (st : Store) (atts : List (Id × List Request × Nat)) (pre : List (Id × List Request × Outcome))
    (hinv : ∀ s, st s = (run (committedReqs pre s)).1 ∧ deliveredAnswers pre s = (run (committedReqs pre s)).2) :
    ∀ s, (execB st atts).1 s = (run (committedReqs (pre ++ (execB st atts).2) s)).1 ∧
      deliveredAnswers (pre ++ (execB st atts).2) s = (run (committedReqs (pre ++ (execB st atts).2) s)).2 :=
  Service.execB_spec (S := coreService) st atts pre hinv

/-- **Compare-and-set batch appends refine `run`.** Starting from empty streams, under any interleaving of validators
(each reads a stream at some length, decides a batch of requests one after another from what it read, and appends the
accepted events with one compare-and-set at that length), every stream holds exactly `run` of the requests of the
batches that committed on it, in commit order, and the answers delivered on it, refusals included, are exactly
`run`'s answers to those requests. A lost compare-and-set changes nothing and answers nothing
(`attemptBatch_conflict`). A single request is a batch of one. -/
theorem cas_refines_run (atts : List (Id × List Request × Nat)) (s : Id) :
    (execB Store.empty atts).1 s = (run (committedReqs (execB Store.empty atts).2 s)).1 ∧
    deliveredAnswers (execB Store.empty atts).2 s = (run (committedReqs (execB Store.empty atts).2 s)).2 :=
  Service.cas_refines_run (S := coreService) atts s

/-- **Each delivered answer is `respond` on the stream as it stood.** In a committed batch, the answer to its `i`-th
request is `respond` against the stream's events at that point: the committed prefix the validator read plus the
events accepted earlier in the batch. (`run_responses`, applied to the batch.) -/
theorem batch_answer (L : Log) (pre : List Request) (r : Request) (post : List Request) :
    (runFrom L (pre ++ r :: post)).2[pre.length]? = some (respond (runFrom L pre).1 r) :=
  Service.batch_answer (S := coreService) L pre r post

end StreamCore
