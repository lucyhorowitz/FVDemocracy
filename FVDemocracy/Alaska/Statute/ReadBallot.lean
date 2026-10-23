import FVDemocracy.Alaska.Statute.StatuteDefs

/-!
# Reading a ballot ranking by ranking

AS 15.15.350 describes how a ballot counts in two ways. Subsection (g)(2) describes properties of
the whole ballot: a ballot is inactive if it "does not rank any continuing candidate, contains an
overvote at the highest continuing ranking, or contains two or more sequential skipped rankings
before its highest continuing ranking". `MeetsInactivityCondition` and `resultOf` follow this
description.
Subsections (d), (e)(1) and (e)(2) describe reading the rankings in order:

* (d): the ballot counts "as one vote for the highest-ranked continuing candidate on that ballot
  or as an inactive ballot";
* (e)(1): "a ballot containing an overvote shall be considered an inactive ballot once the
  overvote is encountered at the highest ranking for a continuing candidate";
* (e)(2): "if a ballot skips a ranking, then the election board shall count the next ranking. If
  the next ranking is another skipped ranking, the ballot shall be considered an inactive ballot
  once the second skipped ranking is encountered".

`readRankings` reads the rankings in order following (d), (e)(1) and (e)(2), and
`readRankings_eq_resultOf` proves that it gives every ballot the same result as `resultOf`.
-/

namespace Alaska

/-- AS 15.15.350(d), (e)(1), (e)(2): the result of the rankings `rs`, read from the highest
ranking down, when `cont` are the continuing candidates. `skipped` is whether the ranking read
just before `rs` was a skipped ranking. A ballot `b` is read from its first ranking with `skipped`
false: `readRankings cont false b.ranks` (`readRankings_eq_resultOf`).

* The rankings are read one at a time, and reading stops at the first ranking that marks a
  continuing candidate. No ranking above it ranks a continuing candidate, so it is the highest
  ranking for a continuing candidate. If it is an overvote, the ballot is inactive (e)(1);
  otherwise the ballot counts for the first continuing candidate it marks (d).
* A skipped ranking (g)(6) makes the ballot inactive if the ranking before it was also skipped,
  and otherwise the next ranking is read (e)(2).
* A ranking that marks no continuing candidate and is not a skipped ranking is passed over, and
  the next ranking is read. Such a ranking either marks only defeated candidates or is blank
  (`Ballot.IsBlankAt`) with no candidate ranked after it; a blank ranking is a skipped ranking
  only on "a ballot on which a voter has ranked another candidate at a subsequent ranking" (g)(6).
  It is not a skipped ranking, so the ranking after it is not a second skipped ranking.
* When the reading reaches a ranking that marks a candidate again (a duplicate ranking,
  6 AAC 25.072), that candidate is defeated, since the reading stops at the first ranking that
  marks a continuing candidate. So the reading never counts the lower ranking for that candidate.
  A ranking that marks only such candidates marks only defeated candidates, and the reading
  passes over it.
* If every ranking is read without reaching a ranking that marks a continuing candidate, the
  ballot does not rank any continuing candidate, so it is inactive (g)(2). -/
def readRankings (cont : List Cand) (skipped : Bool) : List (List Cand) → BallotResult
  | [] => .inactive
  | r :: rs =>
    match r.find? (· ∈ cont) with
    | some c => if 2 ≤ r.eraseDups.length then .inactive else .voteFor c
    | none =>
      if r = [] ∧ ∃ r' ∈ rs, r' ≠ [] then
        if skipped then .inactive else readRankings cont true rs
      else readRankings cont false rs

namespace Ballot

theorem candsAt_cons_zero (i : Nat) (r : List Cand) (rs : List (List Cand)) :
    (⟨i, r :: rs⟩ : Ballot).candsAt 0 = r := by
  simp [candsAt]

theorem candsAt_cons_succ (i : Nat) (r : List Cand) (rs : List (List Cand)) (k : Nat) :
    (⟨i, r :: rs⟩ : Ballot).candsAt (k + 1) = (⟨i, rs⟩ : Ballot).candsAt k := by
  simp [candsAt]

end Ballot

theorem highestContinuingRank_cons (cont : List Cand) (i : Nat) (r : List Cand)
    (rs : List (List Cand)) :
    highestContinuingRank cont ⟨i, r :: rs⟩ =
      if ∃ c ∈ r, c ∈ cont then some 0
      else (highestContinuingRank cont ⟨i, rs⟩).map (· + 1) := by
  simp [highestContinuingRank, List.findIdx?_cons]

section NoContinuing

variable {cont : List Cand} {i : Nat} {r : List Cand} {rs : List (List Cand)}

theorem highestContinuingCand_cons_of_forall (hr : ∀ c ∈ r, c ∉ cont) :
    highestContinuingCand cont ⟨i, r :: rs⟩ = highestContinuingCand cont ⟨i, rs⟩ := by
  unfold highestContinuingCand
  rw [highestContinuingRank_cons, if_neg (by simpa using hr)]
  cases highestContinuingRank cont ⟨i, rs⟩ <;> simp [Ballot.candsAt_cons_succ]

theorem exhausted_cons_iff_of_forall (hr : ∀ c ∈ r, c ∉ cont) :
    Exhausted cont ⟨i, r :: rs⟩ ↔ Exhausted cont ⟨i, rs⟩ := by
  simp only [exhausted_iff_highest_cont_rank_none, highestContinuingRank_cons,
    if_neg (show ¬ ∃ c ∈ r, c ∈ cont by simpa using hr), Option.map_eq_none_iff]

theorem isOvervoteAtHighestCont_cons_iff_of_forall (hr : ∀ c ∈ r, c ∉ cont) :
    IsOvervoteAtHighestCont cont ⟨i, r :: rs⟩ ↔ IsOvervoteAtHighestCont cont ⟨i, rs⟩ := by
  unfold IsOvervoteAtHighestCont
  rw [exists_isHighestContinuingRank_and_iff, exists_isHighestContinuingRank_and_iff,
    highestContinuingRank_cons, if_neg (by simpa using hr)]
  cases highestContinuingRank cont ⟨i, rs⟩ <;>
    simp [Ballot.IsOvervoteAt, Ballot.candsAt_cons_succ]

end NoContinuing

/-- The ranking at the highest continuing rank is not blank. -/
theorem candsAt_ne_nil_of_highestContinuingRank {cont : List Cand} {b : Ballot} {k : Nat}
    (hk : highestContinuingRank cont b = some k) : k < b.ranks.length ∧ b.candsAt k ≠ [] := by
  obtain ⟨⟨c, hc, -⟩, -⟩ := (highestContinuingRank_eq_some_iff cont b k).mp hk
  have hne : b.candsAt k ≠ [] := List.ne_nil_of_mem hc
  exact ⟨Ballot.lt_length_of_candsAt_ne_nil hne, hne⟩

/-- AS 15.15.350(g)(2), (g)(6): a ballot has two sequential skipped rankings before its highest
continuing ranking exactly when it has two sequential blank rankings (`Ballot.IsBlankAt`) before
it. A blank ranking before the highest continuing ranking is a skipped ranking, since a candidate
is ranked at the highest continuing ranking. -/
theorem twoSkips_iff (cont : List Cand) (b : Ballot) :
    TwoSkips cont b ↔ ∃ k, IsHighestContinuingRank cont b k ∧
      ∃ j, j + 1 < k ∧ b.candsAt j = [] ∧ b.candsAt (j + 1) = [] := by
  unfold TwoSkips
  refine exists_congr fun k => and_congr_right fun hk => ?_
  obtain ⟨hlt, hne⟩ :=
    candsAt_ne_nil_of_highestContinuingRank ((highestContinuingRank_eq_some_iff cont b k).mpr hk)
  constructor
  · rintro ⟨j, -, hj, hs, hs1⟩
    exact ⟨j, hj, hs.1, hs1.1⟩
  · rintro ⟨j, hj, h, h1⟩
    exact ⟨j, by omega, hj, ⟨h, k, hlt, by omega, hne⟩, ⟨h1, k, hlt, hj, hne⟩⟩

/-- A ballot whose first ranking marks no continuing candidate has two sequential skipped
rankings before its highest continuing ranking iff the rest of the ballot does, or when its
first two rankings are blank and it ranks a continuing candidate. -/
theorem twoSkips_cons_iff_of_forall {cont : List Cand} {i : Nat} {r : List Cand}
    {rs : List (List Cand)} (hr : ∀ c ∈ r, c ∉ cont) :
    TwoSkips cont ⟨i, r :: rs⟩ ↔
      TwoSkips cont ⟨i, rs⟩ ∨
        (r = [] ∧ (⟨i, rs⟩ : Ballot).candsAt 0 = [] ∧ ¬ Exhausted cont ⟨i, rs⟩) := by
  rw [twoSkips_iff, twoSkips_iff, exists_isHighestContinuingRank_and_iff,
    exists_isHighestContinuingRank_and_iff, highestContinuingRank_cons,
    if_neg (show ¬ ∃ c ∈ r, c ∈ cont by simpa using hr), exhausted_iff_highest_cont_rank_none]
  cases hk : highestContinuingRank cont ⟨i, rs⟩ with
  | none => simp
  | some k =>
    have hne := (candsAt_ne_nil_of_highestContinuingRank hk).2
    simp only [Option.map_some, Option.some.injEq, exists_eq_left', reduceCtorEq,
      not_false_eq_true, and_true]
    constructor
    · rintro ⟨_ | j, hj, h, h1⟩
      · rw [Ballot.candsAt_cons_zero] at h
        rw [Ballot.candsAt_cons_succ] at h1
        exact Or.inr ⟨h, h1⟩
      · rw [Ballot.candsAt_cons_succ] at h h1
        exact Or.inl ⟨j, by omega, h, h1⟩
    · rintro (⟨j, hj, h, h1⟩ | ⟨h, h1⟩)
      · refine ⟨j + 1, by omega, ?_, ?_⟩ <;> rwa [Ballot.candsAt_cons_succ]
      · have hk0 : k ≠ 0 := by
          rintro rfl
          exact hne h1
        refine ⟨0, by omega, ?_, ?_⟩
        · rwa [Ballot.candsAt_cons_zero]
        · rwa [Ballot.candsAt_cons_succ]

theorem resultOf_of_exhausted {cont : List Cand} {b : Ballot} (h : Exhausted cont b) :
    resultOf cont b = .inactive := by
  simp [resultOf, MeetsInactivityCondition, h]

/-- A ballot whose first ranking marks a continuing candidate `c` first is inactive if that
ranking is an overvote, and otherwise counts for `c`. -/
theorem resultOf_cons_of_find?_eq_some {cont : List Cand} {i : Nat} {r : List Cand}
    {rs : List (List Cand)} {c : Cand} (hc : r.find? (· ∈ cont) = some c) :
    resultOf cont ⟨i, r :: rs⟩ = if 2 ≤ r.eraseDups.length then .inactive else .voteFor c := by
  have hex : ∃ c ∈ r, c ∈ cont :=
    ⟨c, List.mem_of_find?_eq_some hc, by simpa using List.find?_some hc⟩
  have hk : highestContinuingRank cont ⟨i, r :: rs⟩ = some 0 := by
    rw [highestContinuingRank_cons, if_pos hex]
  have hcand : highestContinuingCand cont ⟨i, r :: rs⟩ = some c := by
    simp [highestContinuingCand, hk, Ballot.candsAt_cons_zero, hc]
  have hnex : ¬ Exhausted cont ⟨i, r :: rs⟩ := by
    rw [exhausted_iff_highest_cont_rank_none, hk]
    simp
  have hov : IsOvervoteAtHighestCont cont ⟨i, r :: rs⟩ ↔ 2 ≤ r.eraseDups.length := by
    rw [IsOvervoteAtHighestCont, exists_isHighestContinuingRank_and_iff, hk]
    simp [Ballot.isOvervoteAt_iff, Ballot.candsAt_cons_zero]
  have hskip : ¬ TwoSkips cont ⟨i, r :: rs⟩ := by
    rw [TwoSkips, exists_isHighestContinuingRank_and_iff, hk]
    simp
  unfold resultOf MeetsInactivityCondition
  by_cases h2 : 2 ≤ r.eraseDups.length
  · simp [h2, hov]
  · simp [h2, hov, hnex, hskip, hcand]

/-- A ballot whose first ranking marks no continuing candidate has the result of the rest of the
ballot, unless its first two rankings are blank and it ranks a continuing candidate, in which
case it is inactive. -/
theorem resultOf_cons_of_forall {cont : List Cand} {i : Nat} {r : List Cand}
    {rs : List (List Cand)} (hr : ∀ c ∈ r, c ∉ cont) :
    resultOf cont ⟨i, r :: rs⟩ =
      if r = [] ∧ (⟨i, rs⟩ : Ballot).candsAt 0 = [] ∧ ¬ Exhausted cont ⟨i, rs⟩ then .inactive
      else resultOf cont ⟨i, rs⟩ := by
  unfold resultOf MeetsInactivityCondition
  simp only [exhausted_cons_iff_of_forall hr, isOvervoteAtHighestCont_cons_iff_of_forall hr,
    twoSkips_cons_iff_of_forall hr, highestContinuingCand_cons_of_forall hr]
  by_cases h : r = [] ∧ (⟨i, rs⟩ : Ballot).candsAt 0 = [] ∧ ¬ Exhausted cont ⟨i, rs⟩
  · simp [h]
  · simp only [h, or_false, if_false]

/-- Reading the rankings `rs` gives the result `resultOf` gives a ballot with rankings `rs`.
Reading them just after a skipped ranking gives the result of a ballot with a blank ranking
followed by `rs`. -/
theorem readRankings_eq_resultOf_aux (cont : List Cand) (i : Nat) (rs : List (List Cand)) :
    readRankings cont false rs = resultOf cont ⟨i, rs⟩ ∧
      readRankings cont true rs = resultOf cont ⟨i, [] :: rs⟩ := by
  induction rs with
  | nil =>
    refine ⟨?_, ?_⟩ <;> rw [readRankings, resultOf_of_exhausted (by simp [Exhausted])]
  | cons r rs ih =>
    have hblank : resultOf cont ⟨i, [] :: r :: rs⟩ =
        if r = [] ∧ ¬ Exhausted cont ⟨i, r :: rs⟩ then .inactive
        else resultOf cont ⟨i, r :: rs⟩ := by
      rw [resultOf_cons_of_forall (by simp), Ballot.candsAt_cons_zero]
      simp
    rw [hblank]
    cases hc : r.find? (· ∈ cont) with
    | some c =>
      have hr : r ≠ [] := by
        rintro rfl
        simp at hc
      simp only [readRankings, hc, hr, false_and, if_false]
      rw [resultOf_cons_of_find?_eq_some hc]
      exact ⟨rfl, rfl⟩
    | none =>
      have hr : ∀ c ∈ r, c ∉ cont := by simpa [List.find?_eq_none] using hc
      have hread : ∀ skipped : Bool, readRankings cont skipped (r :: rs) =
          if r = [] ∧ ∃ r' ∈ rs, r' ≠ [] then
            (if skipped then .inactive else readRankings cont true rs)
          else readRankings cont false rs := by
        intro skipped
        simp only [readRankings, hc]
      rw [hread, hread]
      by_cases hskip : r = [] ∧ ∃ r' ∈ rs, r' ≠ []
      · obtain ⟨rfl, hne⟩ := hskip
        refine ⟨?_, ?_⟩
        · rw [if_pos ⟨rfl, hne⟩, if_neg Bool.false_ne_true]
          exact ih.2
        · rw [if_pos ⟨rfl, hne⟩, if_pos rfl]
          by_cases hex : Exhausted cont ⟨i, [] :: rs⟩
          · rw [if_neg (fun h => h.2 hex), resultOf_of_exhausted hex]
          · rw [if_pos ⟨rfl, hex⟩]
      · have hrest : ¬ (r = [] ∧ (⟨i, rs⟩ : Ballot).candsAt 0 = [] ∧
            ¬ Exhausted cont ⟨i, rs⟩) := by
          rintro ⟨rfl, -, hex⟩
          apply hex
          rintro ⟨r', hr', c, hc', -⟩
          exact hskip ⟨rfl, r', hr', List.ne_nil_of_mem hc'⟩
        rw [if_neg hskip, if_neg hskip]
        refine ⟨?_, ?_⟩
        · rw [ih.1, resultOf_cons_of_forall hr, if_neg hrest]
        · by_cases hr0 : r = []
          · subst hr0
            have hex : Exhausted cont ⟨i, [] :: rs⟩ := by
              rintro ⟨r', hr', c, hc', -⟩
              rcases List.mem_cons.mp hr' with rfl | hr'
              · simp at hc'
              · exact hskip ⟨rfl, r', hr', List.ne_nil_of_mem hc'⟩
            rw [if_neg (fun h => h.2 hex), resultOf_of_exhausted hex, ih.1,
              resultOf_of_exhausted ((exhausted_cons_iff_of_forall hr).mp hex)]
          · rw [if_neg (fun h => hr0 h.1), ih.1, resultOf_cons_of_forall hr, if_neg hrest]

/-- AS 15.15.350(d), (e)(1), (e)(2) and (g)(2) agree: reading a ballot's rankings in order
gives the ballot the result `resultOf` gives it. -/
theorem readRankings_eq_resultOf (cont : List Cand) (b : Ballot) :
    readRankings cont false b.ranks = resultOf cont b :=
  (readRankings_eq_resultOf_aux cont b.ballotIndex b.ranks).1

/-- Reading a ballot's rankings in order gives the result `o` exactly when `o` is the ballot's
result under AS 15.15.350(g)(2): `IsBallotResult cont b (.voteFor c)` is `IsVoteFor cont b c`, and
`IsBallotResult cont b .inactive` is `MeetsInactivityCondition cont b`. -/
theorem readRankings_eq_iff (cont : List Cand) (b : Ballot) (o : BallotResult) :
    readRankings cont false b.ranks = o ↔ IsBallotResult cont b o := by
  rw [readRankings_eq_resultOf]
  obtain ⟨o', -, huniq⟩ := exists_unique_ballot_result cont b
  have h := resultOf_eq_result cont b
  constructor
  · rintro rfl
    exact h
  · intro ho
    rw [huniq _ h, huniq _ ho]

end Alaska
