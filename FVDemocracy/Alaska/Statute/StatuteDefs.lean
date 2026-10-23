import FVDemocracy.Util.List

namespace Alaska

inductive Cand where
  | writeIn (c : Nat)
  | regular (c : Nat)
deriving Repr, DecidableEq

def IsWriteIn (c : Cand) : Prop :=
  match c with
  | .writeIn _ => True
  | .regular _ => False

instance : DecidablePred IsWriteIn := by
  intro c
  cases c <;> simp [IsWriteIn]
  exact instDecidableTrue
  exact instDecidableFalse

structure Ballot where
  ballotIndex : Nat
  ranks : List (List Cand)
deriving Repr, DecidableEq

structure Election where
  ballots : List Ballot
  cands : List Cand
  cands_unique : cands.Nodup
deriving Repr

namespace Ballot

/-- Candidates ranked at rank `k`. Empty list at indices after the length of the
list of rankings. -/
def candsAt (b : Ballot) (k : Nat) : List Cand :=
  b.ranks.getD k []

/-- AS 15.15.350(g)(3): “overvote” means an instance where a voter has assigned the same
ranking to more than one candidate;

Logical English: An overvote is a property of a ballot at a given rank.

A candidate also marked at a higher ranking (a duplicate ranking, 6 AAC 25.072) counts toward the
overvote. -/
def IsOvervoteAt (b : Ballot) (k : Nat) : Prop :=
  ∃ c ∈ b.candsAt k, ∃ c' ∈ b.candsAt k, c ≠ c'

instance (b : Ballot) : DecidablePred (IsOvervoteAt b) := by
  intro k
  unfold IsOvervoteAt
  infer_instance

/-- `IsOvervoteAt` in terms of `List.eraseDups`, which `readRankings` computes. -/
theorem isOvervoteAt_iff (b : Ballot) (k : Nat) :
    b.IsOvervoteAt k ↔ 2 ≤ (b.candsAt k).eraseDups.length :=
  List.exists_ne_iff_two_le_length_eraseDups

def HasOvervote (b : Ballot) : Prop :=
  ∃ k < b.ranks.length, IsOvervoteAt b k

instance : DecidablePred HasOvervote := by
  unfold HasOvervote
  infer_instance

/-- 6 AAC 25.072: "a duplicate ranking occurs when a voter marks more than one ranking for the
same candidate". -/
def HasDuplicateRanking (b : Ballot) : Prop :=
  ¬ b.ranks.Pairwise fun r r' => ∀ c ∈ r, c ∉ r'

instance : DecidablePred HasDuplicateRanking := by
  unfold HasDuplicateRanking
  infer_instance

/-- A blank ranking (AS 15.15.350(g)(6)): rank `k` of `b` marks no candidate. Every rank after the
last ranking of `b` is blank. A ranking that marks only defeated candidates, or only candidates
also marked at a higher ranking (duplicate rankings, 6 AAC 25.072), is not blank. -/
def IsBlankAt (b : Ballot) (k : Nat) : Prop :=
  b.candsAt k = []

instance (b : Ballot) : DecidablePred (IsBlankAt b) := by
  intro k
  unfold IsBlankAt
  infer_instance

/-- AS 15.15.350(g)(6): “skipped ranking” means a blank ranking on a ballot on which a voter
has ranked another candidate at a subsequent ranking.

A ranking that marks only candidates also marked at a higher ranking (duplicate rankings,
6 AAC 25.072) is not blank. -/
def SkippedRankingAt (b : Ballot) (k : Nat) : Prop :=
  b.IsBlankAt k ∧ ∃ k' < b.ranks.length, k < k' ∧ ¬ b.IsBlankAt k'

instance (b : Ballot) : DecidablePred (b.SkippedRankingAt) := by
  intro k
  unfold SkippedRankingAt
  infer_instance

end Ballot

/-- AS 15.15.350(g)(2) "highest continuing ranking", AS 15.15.350(e)(1) "highest ranking for a
continuing candidate": rank `k` of `b` marks a continuing candidate, and no rank above it does.
Ranks are numbered from 0, so rank `k` is the ranking "`k + 1`" of AS 15.15.350(g)(4). -/
def IsHighestContinuingRank (cont : List Cand) (b : Ballot) (k : Nat) : Prop :=
  (∃ c ∈ b.candsAt k, c ∈ cont) ∧ ∀ j < k, ∀ c ∈ b.candsAt j, c ∉ cont

instance (cont : List Cand) (b : Ballot) : DecidablePred (IsHighestContinuingRank cont b) := by
  intro k
  unfold IsHighestContinuingRank
  infer_instance

/-- The highest continuing rank of `b`, if `b` ranks a continuing candidate
(`highestContinuingRank_eq_some_iff`). -/
def highestContinuingRank (cont : List Cand) (b : Ballot) : Option Nat :=
  (b.ranks.findIdx? (fun r => r.any (· ∈ cont)))

theorem highestContinuingRank_eq_some_iff (cont : List Cand) (b : Ballot) (k : Nat) :
    highestContinuingRank cont b = some k ↔ IsHighestContinuingRank cont b k := by
  obtain ⟨i, rs⟩ := b
  unfold highestContinuingRank IsHighestContinuingRank Ballot.candsAt
  dsimp only
  induction rs generalizing k with
  | nil =>
    rw [List.findIdx?_nil]
    constructor
    · intro h
      cases h
    · rintro ⟨⟨c, hc, -⟩, -⟩
      exact absurd (by simpa only [List.getD_nil] using hc) List.not_mem_nil
  | cons r rs ih =>
    rw [List.findIdx?_cons]
    cases k with
    | zero =>
      simp only [List.getD_cons_zero]
      constructor
      · intro h
        refine ⟨?_, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
        cases hany : r.any fun x => decide (x ∈ cont)
        · rw [hany, if_neg Bool.false_ne_true] at h
          obtain ⟨k', -, hk'⟩ := Option.map_eq_some_iff.mp h
          exact absurd hk' (Nat.succ_ne_zero k')
        · obtain ⟨c, hc, hcont⟩ := List.any_eq_true.mp hany
          exact ⟨c, hc, of_decide_eq_true hcont⟩
      · rintro ⟨⟨c, hc, hcont⟩, -⟩
        rw [if_pos (List.any_eq_true.mpr ⟨c, hc, decide_eq_true hcont⟩)]
    | succ k =>
      simp only [List.getD_cons_succ]
      by_cases hr : ∃ c ∈ r, c ∈ cont
      · obtain ⟨c, hc, hcont⟩ := hr
        rw [if_pos (List.any_eq_true.mpr ⟨c, hc, decide_eq_true hcont⟩)]
        constructor
        · intro h
          exact absurd (Option.some.inj h) (Nat.succ_ne_zero k).symm
        · rintro ⟨-, h⟩
          exact absurd hcont (h 0 (Nat.succ_pos k) c (by simpa only [List.getD_cons_zero] using hc))
      · have hany : (r.any fun x => decide (x ∈ cont)) = false :=
          List.any_eq_false.mpr fun c hc hcont => hr ⟨c, hc, of_decide_eq_true hcont⟩
        rw [hany, if_neg Bool.false_ne_true, Option.map_eq_some_iff]
        constructor
        · rintro ⟨k', hk', hk⟩
          obtain rfl : k' = k := Nat.succ.inj hk
          obtain ⟨hex, hbefore⟩ := (ih k').mp hk'
          refine ⟨hex, fun j hj c hc hcont => ?_⟩
          cases j with
          | zero => exact hr ⟨c, by simpa only [List.getD_cons_zero] using hc, hcont⟩
          | succ j =>
            exact hbefore j (Nat.lt_of_succ_lt_succ hj) c
              (by simpa only [List.getD_cons_succ] using hc) hcont
        · rintro ⟨hex, hbefore⟩
          refine ⟨k, (ih k).mpr ⟨hex, fun j hj c hc => ?_⟩, rfl⟩
          exact hbefore (j + 1) (Nat.succ_lt_succ hj) c
            (by simpa only [List.getD_cons_succ] using hc)

theorem isHighestContinuingRank_unique {cont : List Cand} {b : Ballot} {k k' : Nat}
    (hk : IsHighestContinuingRank cont b k) (hk' : IsHighestContinuingRank cont b k') : k = k' := by
  obtain ⟨⟨c, hc, hcont⟩, hbefore⟩ := hk
  obtain ⟨⟨c', hc', hcont'⟩, hbefore'⟩ := hk'
  rcases Nat.lt_trichotomy k k' with h | h | h
  · exact absurd hcont (hbefore' k h c hc)
  · exact h
  · exact absurd hcont' (hbefore k' h c' hc')

/-- A property of the highest continuing rank holds exactly when it holds of the rank
`highestContinuingRank` computes. -/
theorem exists_isHighestContinuingRank_and_iff (cont : List Cand) (b : Ballot) (p : Nat → Prop) :
    (∃ k, IsHighestContinuingRank cont b k ∧ p k) ↔
      ∃ k, highestContinuingRank cont b = some k ∧ p k := by
  simp only [highestContinuingRank_eq_some_iff]

/-- AS 15.15.350(d): `c` is "the highest-ranked continuing candidate on that ballot": `c` is a
continuing candidate marked at the highest continuing rank. If that rank is an overvote, this holds
of every continuing candidate marked there. -/
def IsHighestContinuingCand (cont : List Cand) (b : Ballot) (c : Cand) : Prop :=
  c ∈ cont ∧ ∃ k, IsHighestContinuingRank cont b k ∧ c ∈ b.candsAt k

instance (cont : List Cand) (b : Ballot) : DecidablePred (IsHighestContinuingCand cont b) :=
  fun c =>
    decidable_of_iff (c ∈ cont ∧ ∃ k, highestContinuingRank cont b = some k ∧ c ∈ b.candsAt k)
      (and_congr_right fun _ => (exists_isHighestContinuingRank_and_iff cont b _).symm)

/-- The first continuing candidate listed at the highest continuing rank, if any exist. It is a
highest-ranked continuing candidate (`isHighestContinuingCand_of_highestContinuingCand_eq_some`),
and the only one if the ballot has no overvote at that rank (`isVoteFor_iff`). -/
def highestContinuingCand (cont : List Cand) (b : Ballot) : Option Cand :=
  match highestContinuingRank cont b with
  | none => none
  | some k => (b.candsAt k).find? (· ∈ cont)

theorem isHighestContinuingCand_of_highestContinuingCand_eq_some {cont : List Cand} {b : Ballot}
    {c : Cand} (h : highestContinuingCand cont b = some c) : IsHighestContinuingCand cont b c := by
  unfold highestContinuingCand at h
  split at h
  · contradiction
  · next k hk =>
    exact ⟨by simpa using List.find?_some h, k, (highestContinuingRank_eq_some_iff cont b k).mp hk,
      List.mem_of_find?_eq_some h⟩

/-- AS 15.15.350(g)(2): the ballot "does not rank any continuing candidate". AS 15.15.350(g)(1):
a continuing candidate is "a candidate who has not been defeated". -/
def Exhausted (cont : List Cand) (b : Ballot) : Prop :=
  ¬ ∃ r ∈ b.ranks, ∃ c ∈ r, c ∈ cont

instance (cont : List Cand) : DecidablePred (Exhausted cont) := by
  intro b
  unfold Exhausted
  infer_instance

/-- AS 15.15.350(g)(2): the ballot "contains an overvote at the highest continuing ranking".
-/
def IsOvervoteAtHighestCont (cont : List Cand) (b : Ballot) : Prop :=
  ∃ k, IsHighestContinuingRank cont b k ∧ b.IsOvervoteAt k

instance (cont : List Cand) : DecidablePred (IsOvervoteAtHighestCont cont) :=
  fun b => decidable_of_iff _ (exists_isHighestContinuingRank_and_iff cont b b.IsOvervoteAt).symm

/-- AS 15.15.350(g)(2): the ballot "contains two or more sequential skipped rankings before its
highest continuing ranking". -/
def TwoSkips (cont : List Cand) (b : Ballot) : Prop :=
  ∃ k, IsHighestContinuingRank cont b k ∧
    ∃ i < k, i + 1 < k ∧ b.SkippedRankingAt i ∧ b.SkippedRankingAt (i + 1)

instance (cont : List Cand) : DecidablePred (TwoSkips cont) :=
  fun b => decidable_of_iff _ (exists_isHighestContinuingRank_and_iff cont b
    fun k => ∃ i < k, i + 1 < k ∧ b.SkippedRankingAt i ∧ b.SkippedRankingAt (i + 1)).symm

/-- AS 15.15.350(g)(2): “inactive ballot” means a ballot that is no longer tabulated, either in
whole or in part, by the division because it does not rank any continuing candidate, contains an
overvote at the highest continuing ranking, or contains two or more sequential skipped rankings
before its highest continuing ranking;

`b` meets one of these three conditions when `cont` are the continuing candidates. An inactive
ballot is one that is no longer tabulated because it met one of them: `Round.next` stops
tabulating a ballot once it meets one, so a ballot that met one in an earlier round is inactive
even if it meets none now. -/
def MeetsInactivityCondition (cont : List Cand) (b : Ballot) : Prop :=
  Exhausted cont b ∨ IsOvervoteAtHighestCont cont b ∨ TwoSkips cont b

instance (cont : List Cand) : DecidablePred (MeetsInactivityCondition cont) := by
  intro b
  unfold MeetsInactivityCondition
  infer_instance

/-- A ballot without an overvote at its highest continuing rank has at most one highest-ranked
continuing candidate. -/
theorem isHighestContinuingCand_unique {cont : List Cand} {b : Ballot} {c c' : Cand}
    (hov : ¬ IsOvervoteAtHighestCont cont b) (hc : IsHighestContinuingCand cont b c)
    (hc' : IsHighestContinuingCand cont b c') : c = c' := by
  obtain ⟨-, k, hk, hck⟩ := hc
  obtain ⟨-, k', hk', hck'⟩ := hc'
  obtain rfl := isHighestContinuingRank_unique hk hk'
  by_cases h : c = c'
  · exact h
  · exact absurd ⟨k, hk, c, hck, c', hck', h⟩ hov

/-- AS 15.15.350(d): in each round a ballot is tabulated "as one vote for the highest-ranked
continuing candidate on that ballot or as an inactive ballot". -/
inductive BallotResult where
  | voteFor (c : Cand)
  | inactive
deriving Repr, DecidableEq

/-- The result of the ballot `b` when `cont` are the continuing candidates, under
AS 15.15.350(d) and (g)(2): a ballot that meets an inactivity condition is tabulated as inactive,
and any other ballot as a vote for its highest-ranked continuing candidate. -/
def IsBallotResult (cont : List Cand) (b : Ballot) : BallotResult → Prop
  | .voteFor c => ¬ MeetsInactivityCondition cont b ∧ IsHighestContinuingCand cont b c
  | .inactive => MeetsInactivityCondition cont b

instance (cont : List Cand) (b : Ballot) : DecidablePred (IsBallotResult cont b) := by
  intro b
  unfold IsBallotResult
  split <;> infer_instance

theorem highestContinuingRank_eq_none_iff_cand (cont : List Cand) (b : Ballot) :
    highestContinuingRank cont b = none ↔ highestContinuingCand cont b = none := by
  unfold highestContinuingCand
  constructor
  · intro h
    rw [h]
  · intro h
    cases hk : highestContinuingRank cont b with
    | none => rfl
    | some k =>
      rw [hk] at h
      obtain ⟨⟨c, hc, hcont⟩, -⟩ := (highestContinuingRank_eq_some_iff cont b k).mp hk
      exact absurd (decide_eq_true hcont) (List.find?_eq_none.mp h c hc)

theorem exhausted_iff_highest_cont_rank_none (cont : List Cand) (b : Ballot) :
    Exhausted cont b ↔ highestContinuingRank cont b = none := by
  unfold Exhausted highestContinuingRank
  simp

theorem exhausted_iff_highest_cont_cand_none (cont : List Cand) (b : Ballot) :
    Exhausted cont b ↔ highestContinuingCand cont b = none := by
  simp [exhausted_iff_highest_cont_rank_none]
  exact highestContinuingRank_eq_none_iff_cand cont b

/-- A ballot that ranks no continuing candidate still ranks none when the continuing candidates
are reduced to `cont'`. -/
theorem exhausted_of_subset {cont cont' : List Cand} {b : Ballot} (hsub : cont' ⊆ cont)
    (h : Exhausted cont b) : Exhausted cont' b := by
  rintro ⟨r, hr, c, hc, hc'⟩
  exact h ⟨r, hr, c, hc, hsub hc'⟩

/-- Reducing the continuing candidates to `cont'` does not move the highest continuing rank
up the ballot. -/
theorem highestContinuingRank_le_of_subset {cont cont' : List Cand} {b : Ballot} {k k' : Nat}
    (hsub : cont' ⊆ cont) (hk : highestContinuingRank cont b = some k)
    (hk' : highestContinuingRank cont' b = some k') : k ≤ k' := by
  obtain ⟨-, hbefore⟩ := (highestContinuingRank_eq_some_iff cont b k).mp hk
  obtain ⟨⟨c, hc, hc'⟩, -⟩ := (highestContinuingRank_eq_some_iff cont' b k').mp hk'
  exact Nat.le_of_not_lt fun hlt => hbefore k' hlt c hc (hsub hc')

/-- A ballot with two sequential skipped rankings before its highest continuing ranking still
has them when the continuing candidates are reduced to `cont'`, unless it no longer ranks any
continuing candidate. -/
theorem twoSkips_or_exhausted_of_subset {cont cont' : List Cand} {b : Ballot} (hsub : cont' ⊆ cont)
    (h : TwoSkips cont b) : TwoSkips cont' b ∨ Exhausted cont' b := by
  cases hk' : highestContinuingRank cont' b with
  | none => exact Or.inr ((exhausted_iff_highest_cont_rank_none cont' b).mpr hk')
  | some k' =>
    left
    obtain ⟨k, hk, i, hi, hi1, hs, hs1⟩ := h
    have hle := highestContinuingRank_le_of_subset hsub
      ((highestContinuingRank_eq_some_iff cont b k).mpr hk) hk'
    exact ⟨k', (highestContinuingRank_eq_some_iff cont' b k').mp hk', i, by omega, by omega, hs,
      hs1⟩


/-- The main well-definedness theorem of the BallotResult. At each round, each ballot has a unique
interpretation as either inactive in this round or counting as a vote for a candidate. -/
theorem exists_unique_ballot_result (cont : List Cand) (b : Ballot) :
    ∃ o, IsBallotResult cont b o ∧ ∀ o', IsBallotResult cont b o' → o' = o := by
  by_cases hi : MeetsInactivityCondition cont b
  · refine ⟨.inactive, hi, ?_⟩
    intro o' ho'
    cases o' with
    | inactive => rfl
    | voteFor c => exact absurd hi ho'.1
  · cases hc : highestContinuingCand cont b with
    | none => exact absurd (Or.inl ((exhausted_iff_highest_cont_cand_none cont b).mpr hc)) hi
    | some c =>
      have hc' := isHighestContinuingCand_of_highestContinuingCand_eq_some hc
      refine ⟨.voteFor c, ⟨hi, hc'⟩, ?_⟩
      intro o' ho'
      cases o' with
      | inactive => exact absurd ho' hi
      | voteFor c' =>
        rw [isHighestContinuingCand_unique (fun h => hi (Or.inr (Or.inl h))) ho'.2 hc']

/-- The unique result `o` with `IsBallotResult cont b o` (`resultOf_eq_result`). -/
def resultOf (cont : List Cand) (b : Ballot) : BallotResult :=
  if MeetsInactivityCondition cont b then BallotResult.inactive else
    match highestContinuingCand cont b with
    | none   => .inactive
    | some c => .voteFor c

theorem resultOf_eq_result (cont : List Cand) (b : Ballot) : IsBallotResult cont b (resultOf cont b) := by
  unfold resultOf
  by_cases hi : MeetsInactivityCondition cont b
  · rw [if_pos hi]
    exact hi
  · rw [if_neg hi]
    cases hc : highestContinuingCand cont b with
    | none => exact absurd (Or.inl ((exhausted_iff_highest_cont_cand_none cont b).mpr hc)) hi
    | some c => exact ⟨hi, isHighestContinuingCand_of_highestContinuingCand_eq_some hc⟩

/-- AS 15.15.350(d): the ballot `b` is tabulated as one vote for `c`. -/
def IsVoteFor (cont : List Cand) (b : Ballot) : Cand → Prop :=
  fun (c : Cand) => IsBallotResult cont b (BallotResult.voteFor c)

instance (cont : List Cand) (b : Ballot) : DecidablePred (IsVoteFor cont b) := by
  unfold IsVoteFor
  infer_instance

/-- `IsVoteFor` in terms of `highestContinuingCand`, which `resultOf` computes. -/
theorem isVoteFor_iff (cont : List Cand) (b : Ballot) (c : Cand) :
    IsVoteFor cont b c ↔
      ¬ MeetsInactivityCondition cont b ∧ highestContinuingCand cont b = some c := by
  constructor
  · rintro ⟨hi, hc⟩
    refine ⟨hi, ?_⟩
    cases hd : highestContinuingCand cont b with
    | none => exact absurd (Or.inl ((exhausted_iff_highest_cont_cand_none cont b).mpr hd)) hi
    | some d =>
      rw [isHighestContinuingCand_unique (fun h => hi (Or.inr (Or.inl h)))
        (isHighestContinuingCand_of_highestContinuingCand_eq_some hd) hc]
  · rintro ⟨hi, hc⟩
    exact ⟨hi, isHighestContinuingCand_of_highestContinuingCand_eq_some hc⟩

/-- 6 AAC 25.072: "The election board shall count a duplicate ranking as the highest ranking
marked for the candidate and disregard the remaining rankings for that candidate." A ballot that
counts for `c` counts at the highest ranking that marks `c`: rank `k` is the highest continuing
rank exactly when it marks `c` and no rank above it does. -/
theorem isHighestContinuingRank_iff_of_isVoteFor {cont : List Cand} {b : Ballot} {c : Cand}
    (h : IsVoteFor cont b c) (k : Nat) :
    IsHighestContinuingRank cont b k ↔ c ∈ b.candsAt k ∧ ∀ j < k, c ∉ b.candsAt j := by
  obtain ⟨-, hcont, k₀, hk₀, hck₀⟩ := h
  constructor
  · intro hk
    obtain rfl := isHighestContinuingRank_unique hk₀ hk
    exact ⟨hck₀, fun j hj hcj => hk₀.2 j hj c hcj hcont⟩
  · rintro ⟨hck, hbefore⟩
    rcases Nat.lt_trichotomy k k₀ with hlt | rfl | hlt
    · exact absurd hcont (hk₀.2 k hlt c hck)
    · exact hk₀
    · exact absurd hck₀ (hbefore k₀ hlt)

theorem Ballot.lt_length_of_candsAt_ne_nil {b : Ballot} {k : Nat} (h : b.candsAt k ≠ []) :
    k < b.ranks.length := by
  refine Nat.lt_of_not_le fun hle => h ?_
  simp [Ballot.candsAt, List.getD_eq_getElem?_getD, hle]

theorem exhausted_iff_not_exists_isHighestContinuingRank (cont : List Cand) (b : Ballot) :
    Exhausted cont b ↔ ¬ ∃ k, IsHighestContinuingRank cont b k := by
  rw [exhausted_iff_highest_cont_rank_none]
  cases h : highestContinuingRank cont b with
  | none => simp [← highestContinuingRank_eq_some_iff, h]
  | some k => simp [← highestContinuingRank_eq_some_iff, h]

/-- A ballot tabulated as a vote for `c` is still tabulated as a vote for `c` when the continuing
candidates are reduced to `cont'`, if `c` is one of them: the rank that marks `c` stays the
highest continuing rank. -/
theorem isVoteFor_of_subset {cont cont' : List Cand} {b : Ballot} {c : Cand} (hsub : cont' ⊆ cont)
    (hc : c ∈ cont') (h : IsVoteFor cont b c) : IsVoteFor cont' b c := by
  obtain ⟨hi, -, k, hk, hck⟩ := h
  have hk' : IsHighestContinuingRank cont' b k :=
    ⟨⟨c, hck, hc⟩, fun j hj c' hc' hcont' => hk.2 j hj c' hc' (hsub hcont')⟩
  refine ⟨fun hin => hi ?_, hc, k, hk', hck⟩
  rcases hin with hex | ⟨k', hk'', hov⟩ | ⟨k', hk'', hs⟩
  · exact absurd ⟨k, hk'⟩ ((exhausted_iff_not_exists_isHighestContinuingRank cont' b).mp hex)
  · obtain rfl := isHighestContinuingRank_unique hk' hk''
    exact Or.inr (Or.inl ⟨k, hk, hov⟩)
  · obtain rfl := isHighestContinuingRank_unique hk' hk''
    exact Or.inr (Or.inr ⟨k, hk, hs⟩)

section SameCands

variable {cont : List Cand} {b b' : Ballot} (h : ∀ k c, c ∈ b.candsAt k ↔ c ∈ b'.candsAt k)
include h

theorem candsAt_eq_nil_iff_of_mem_iff (k : Nat) : b.candsAt k = [] ↔ b'.candsAt k = [] := by
  have hnil : ∀ l l' : List Cand, (∀ c, c ∈ l ↔ c ∈ l') → l = [] → l' = [] := by
    intro l l' hl hnil
    cases l' with
    | nil => rfl
    | cons c _ => exact absurd ((hl c).mpr List.mem_cons_self) (hnil ▸ List.not_mem_nil)
  exact ⟨hnil _ _ (h k), hnil _ _ fun c => (h k c).symm⟩

theorem skippedRankingAt_iff_of_mem_iff (k : Nat) :
    b.SkippedRankingAt k ↔ b'.SkippedRankingAt k := by
  have hn := candsAt_eq_nil_iff_of_mem_iff h
  unfold Ballot.SkippedRankingAt Ballot.IsBlankAt
  constructor
  · rintro ⟨hk, k', -, hkk', hne⟩
    exact ⟨(hn k).mp hk, k', Ballot.lt_length_of_candsAt_ne_nil (mt (hn k').mpr hne), hkk',
      mt (hn k').mpr hne⟩
  · rintro ⟨hk, k', -, hkk', hne⟩
    exact ⟨(hn k).mpr hk, k', Ballot.lt_length_of_candsAt_ne_nil (mt (hn k').mp hne), hkk',
      mt (hn k').mp hne⟩

theorem isHighestContinuingRank_iff_of_mem_iff (k : Nat) :
    IsHighestContinuingRank cont b k ↔ IsHighestContinuingRank cont b' k := by
  simp only [IsHighestContinuingRank, h]

theorem meetsInactivityCondition_iff_of_mem_iff :
    MeetsInactivityCondition cont b ↔ MeetsInactivityCondition cont b' := by
  simp only [MeetsInactivityCondition, exhausted_iff_not_exists_isHighestContinuingRank,
    IsOvervoteAtHighestCont, TwoSkips, Ballot.IsOvervoteAt,
    isHighestContinuingRank_iff_of_mem_iff h, skippedRankingAt_iff_of_mem_iff h, h]

/-- Two ballots that mark the same candidates at each ranking have the same results. -/
theorem isBallotResult_iff_of_mem_iff (o : BallotResult) :
    IsBallotResult cont b o ↔ IsBallotResult cont b' o := by
  cases o with
  | inactive => exact meetsInactivityCondition_iff_of_mem_iff h
  | voteFor c =>
    simp only [IsBallotResult, IsHighestContinuingCand, meetsInactivityCondition_iff_of_mem_iff h,
      isHighestContinuingRank_iff_of_mem_iff h, h]

end SameCands

/-- No result depends on the order in which a ballot lists the candidates at a ranking: two
ballots that list the same candidates at each ranking, in any order, have the same results. -/
theorem isBallotResult_iff_of_perm {cont : List Cand} {b b' : Ballot}
    (h : ∀ k, (b.candsAt k).Perm (b'.candsAt k)) (o : BallotResult) :
    IsBallotResult cont b o ↔ IsBallotResult cont b' o :=
  isBallotResult_iff_of_mem_iff (fun k _ => (h k).mem_iff) o

/-- `resultOf` does not depend on the order in which a ballot lists the candidates at a ranking,
although `highestContinuingCand` takes the first continuing candidate listed. -/
theorem resultOf_eq_of_perm {cont : List Cand} {b b' : Ballot}
    (h : ∀ k, (b.candsAt k).Perm (b'.candsAt k)) : resultOf cont b = resultOf cont b' := by
  obtain ⟨o, -, huniq⟩ := exists_unique_ballot_result cont b'
  rw [huniq _ ((isBallotResult_iff_of_perm h _).mp (resultOf_eq_result cont b)),
    huniq _ (resultOf_eq_result cont b')]

end Alaska
