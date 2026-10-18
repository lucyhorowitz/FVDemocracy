import FVDemocracy.Alaska.Statute.Spec

/-!
# An overvote at the highest continuing ranking

The ballot `exampleBallot` ranks A first, B and C together second, D third and E fourth.
Starting from the round `firstRound`, with continuing candidates A, B, C, D and E:

* Defeating B, C and then A, rank 2 is never the highest continuing ranking, so the overvote is
  never encountered: the ballot is still tabulated and counts for D (`defeat_B_C_A`).
* Defeating A, rank 2 is the highest continuing ranking and holds two continuing candidates, so
  the ballot is no longer tabulated (`defeat_A`).
* Defeating A, B and then C, the ballot meets no inactivity condition for the continuing
  candidates D and E, and it is still not tabulated (`defeat_A_B_C`).

The election `exampleElection` adds ballots that tie A, B and C, so that the tabulation can defeat
either B, C and then A or A, B and then C. Both leave D and E continuing, and only the second makes
`exampleBallot` an inactive ballot. So under Stop, whether a ballot is inactive is not determined
by the election, the ballot and the continuing candidates (`stop_not_stateless`). After A, B and C
are defeated, `exampleBallot` is inactive, although `IsBallotResult` for the continuing candidates
D and E alone would count it for D (`exampleElection_A_B_C_isBallotResultAfter`).
-/

namespace Alaska.OvervoteExample

def A : Cand := .regular 0
def B : Cand := .regular 1
def C : Cand := .regular 2
def D : Cand := .regular 3
def E : Cand := .regular 4

/-- 1: A, 2: B and C, 3: D, 4: E. -/
def exampleBallot : Ballot := ⟨0, [[A], [B, C], [D], [E]]⟩

/-- The round with continuing candidates A, B, C, D and E, tabulating `exampleBallot`. -/
def firstRound : Round := ⟨[A, B, C, D, E], [exampleBallot]⟩

/-- After defeating B, C and then A, the ballot is tabulated and counts for D. -/
theorem defeat_B_C_A :
    (firstRound.nextAll [B, C, A]).ballots = [exampleBallot] ∧
      resultOf (firstRound.nextAll [B, C, A]).continuing exampleBallot = .voteFor D := by
  decide

/-- After defeating A, the ballot is no longer tabulated. -/
theorem defeat_A : (firstRound.nextAll [A]).ballots = [] := by
  decide

/-- After defeating A, B and then C, the ballot is not tabulated, although it meets no inactivity
condition for the continuing candidates of that round. -/
theorem defeat_A_B_C :
    (firstRound.nextAll [A, B, C]).ballots = [] ∧
      ¬ MeetsInactivityCondition (firstRound.nextAll [A, B, C]).continuing exampleBallot := by
  decide

/-- `exampleBallot`, one ballot each ranking only B and only C, and two ballots each ranking only
D and only E. A, B and C each have one vote in the initial tabulation, and D and E two. -/
def exampleElection : Election where
  ballots := [exampleBallot, ⟨1, [[B]]⟩, ⟨2, [[C]]⟩, ⟨3, [[D]]⟩, ⟨4, [[D]]⟩, ⟨5, [[E]]⟩,
    ⟨6, [[E]]⟩]
  cands := [A, B, C, D, E]
  cands_unique := by decide

theorem noMajority_exampleElection : NoMajority exampleElection :=
  (noMajority_iff _).mpr ((majorityWinner_eq_none_iff _ _).mp (by decide))

/-- The tabulation can defeat B, C and then A, leaving D and E continuing, and `exampleBallot` is
still tabulated. -/
theorem exampleElection_B_C_A :
    (initialRound exampleElection).ValidDefeats [B, C, A] ∧
      (roundAfter exampleElection [B, C, A]).continuing = [D, E] ∧
      exampleBallot ∈ (roundAfter exampleElection [B, C, A]).ballots := by
  simp only [Round.ValidDefeats, Round.CanDefeat, roundAfter, List.foldl]
  decide

/-- The tabulation can defeat A, B and then C, leaving D and E continuing, and `exampleBallot` is
no longer tabulated. -/
theorem exampleElection_A_B_C :
    (initialRound exampleElection).ValidDefeats [A, B, C] ∧
      (roundAfter exampleElection [A, B, C]).continuing = [D, E] ∧
      exampleBallot ∉ (roundAfter exampleElection [A, B, C]).ballots := by
  simp only [Round.ValidDefeats, Round.CanDefeat, roundAfter, List.foldl]
  decide

/-- After A, B and C are defeated, `exampleBallot` is an inactive ballot, so the round tabulates it
as inactive. For the continuing candidates D and E alone, `IsBallotResult` would count it for D. -/
theorem exampleElection_A_B_C_isBallotResultAfter :
    IsBallotResultAfter exampleElection [A, B, C] exampleBallot .inactive ∧
      IsBallotResult (roundAfter exampleElection [A, B, C]).continuing exampleBallot
        (.voteFor D) := by
  obtain ⟨-, hc, hb⟩ := exampleElection_A_B_C
  refine ⟨(isInactive_iff_not_mem_roundAfter _ _ _).mpr ⟨by decide, hb⟩, ?_⟩
  rw [hc]
  decide

/-- Under Stop, whether a ballot is inactive in a round of the tabulation is not a function of the
election, the ballot and the continuing candidates of that round: it depends on the order in which
the candidates were defeated. -/
theorem stop_not_stateless :
    ¬ ∃ g : Election → Ballot → List Cand → Prop,
      ∀ (e : Election) (defeated : List Cand), NoMajority e →
        (initialRound e).ValidDefeats defeated → ∀ b ∈ e.ballots,
          (IsInactive e defeated b ↔ g e b (roundAfter e defeated).continuing) := by
  rintro ⟨g, hg⟩
  obtain ⟨hv₁, hc₁, hb₁⟩ := exampleElection_B_C_A
  obtain ⟨hv₂, hc₂, hb₂⟩ := exampleElection_A_B_C
  have hmem : exampleBallot ∈ exampleElection.ballots := by decide
  have h := (hg _ _ noMajority_exampleElection hv₂ _ hmem).mp
    ((isInactive_iff_not_mem_roundAfter _ _ _).mpr ⟨hmem, hb₂⟩)
  rw [hc₂, ← hc₁] at h
  exact ((isInactive_iff_not_mem_roundAfter _ _ _).mp
    ((hg _ _ noMajority_exampleElection hv₁ _ hmem).mpr h)).2 hb₁

end Alaska.OvervoteExample
