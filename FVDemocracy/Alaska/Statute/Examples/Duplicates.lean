import FVDemocracy.Alaska.Duplicates

/-!
# Duplicate rankings under three readings

Each example puts one ballot in an election, defeats a fixed list of candidates, and gives whether
the ballot is still tabulated in the round after, under `tabulate` (`resultOf`, which keeps every
mark), under `tabulate` after `Election.dropDuplicates` (`resultOf` after `Ballot.dropDuplicates`,
which removes each candidate from the rankings below its highest one), and under the reproduction
`reproductionTabulate` (`resultOf` after `Ballot.toReproduction`). In all three a ballot that is
inactive in some round is not tabulated in any later round. Each ballot is tabulated in the
initial round under all three readings, so a ballot that is not tabulated after the defeats became
inactive in a round after the initial one.

* `skip`: the ballot marks A again at rank 3 between two blank rankings, and A is defeated.
  `resultOf` passes over rank 3 because it marks only defeated candidates, and counts the ballot
  for B. With duplicates removed, rank 3 is blank, so ranks 2 and 3 are two sequential skipped
  rankings and the ballot is inactive. The reproduction treats rank 3 the same way and exhausts the
  ballot.
* `overvote`: the ballot marks A again at rank 2 together with B, and A is defeated. `resultOf`
  and the reproduction count A toward an overvote at rank 2, and the ballot is inactive. With
  duplicates removed, rank 2 marks only B, and the ballot counts for B.
* `truncate`: the ballot ranks A first and B and C together second, and has no duplicate ranking.
  B, C and then A are defeated. Rank 2 is never the highest continuing ranking: while A is
  continuing the ballot counts for A, and once A is defeated B and C have been defeated too. So
  `resultOf`, with or without duplicates removed, passes over rank 2 and counts the ballot for D,
  and the reproduction stops at the overvote. So `reproductionResultOf_eq_resultOf_dropDuplicates`
  needs its hypothesis that the ballot has no overvote.

The final lemmas compare Hybrid, Truncate + Retain, and Truncate + Remove with the fixed
continuing list `[B]`. `skipBallot` separates Retain from both other methods, and
`overvoteBallot` separates Remove from both other methods. Thus Hybrid's counted-ballot
class is properly included in each Truncate class, and the two Truncate classes are
incomparable. These statements do not compare final totals along different defeat sequences.
-/

namespace Alaska.DuplicatesExample

def A : Cand := .regular 0
def B : Cand := .regular 1
def C : Cand := .regular 2
def D : Cand := .regular 3
def E : Cand := .regular 4

/-- 1: A, 2: blank, 3: A, 4: blank, 5: B. -/
def skipBallot : Ballot := ⟨0, [[A], [], [A], [], [B]]⟩

/-- 1: A, 2: A and B. -/
def overvoteBallot : Ballot := ⟨1, [[A], [A, B]]⟩

/-- 1: A, 2: B and C, 3: D. -/
def truncateBallot : Ballot := ⟨2, [[A], [B, C], [D]]⟩

/-- `skipBallot`, with candidates A, B and C. -/
def skipElection : Election := ⟨[skipBallot], [A, B, C], by decide⟩

/-- `overvoteBallot`, with candidates A, B and C. -/
def overvoteElection : Election := ⟨[overvoteBallot], [A, B, C], by decide⟩

/-- `truncateBallot`, with candidates A, B, C, D and E. -/
def truncateElection : Election := ⟨[truncateBallot], [A, B, C, D, E], by decide⟩

/-- After A is defeated, `tabulate` counts `skipBallot` for B, and the other two readings no longer
tabulate it, although they tabulate it in the initial round. -/
theorem skip :
    skipBallot.HasDuplicateRanking ∧
      skipBallot ∈ (roundAfter skipElection [A]).ballots ∧
      resultOf (roundAfter skipElection [A]).continuing skipBallot = .voteFor B ∧
      skipBallot.dropDuplicates ∈ (roundAfter skipElection.dropDuplicates []).ballots ∧
      skipBallot.dropDuplicates ∉ (roundAfter skipElection.dropDuplicates [A]).ballots ∧
      skipBallot.toReproduction ∈ (roundAfter
        { skipElection with ballots := skipElection.ballots.map Ballot.toReproduction } []).ballots ∧
      skipBallot.toReproduction ∉ (roundAfter
        { skipElection with ballots := skipElection.ballots.map Ballot.toReproduction } [A]).ballots ∧
      reproductionResultOf (roundAfter skipElection [A]).continuing skipBallot = .exhausted := by
  decide

/-- After A is defeated, the duplicate ranking of A makes rank 2 of `overvoteBallot` an overvote
under `tabulate` and the reproduction, which no longer tabulate it, although they tabulate it in
the initial round. With duplicates removed, the ballot counts for B. -/
theorem overvote :
    overvoteBallot.HasDuplicateRanking ∧
      overvoteBallot ∈ (roundAfter overvoteElection []).ballots ∧
      overvoteBallot ∉ (roundAfter overvoteElection [A]).ballots ∧
      overvoteBallot.dropDuplicates ∈ (roundAfter overvoteElection.dropDuplicates [A]).ballots ∧
      resultOf (roundAfter overvoteElection [A]).continuing overvoteBallot.dropDuplicates =
        .voteFor B ∧
      overvoteBallot.toReproduction ∈ (roundAfter
        { overvoteElection with
          ballots := overvoteElection.ballots.map Ballot.toReproduction } []).ballots ∧
      overvoteBallot.toReproduction ∉ (roundAfter
        { overvoteElection with
          ballots := overvoteElection.ballots.map Ballot.toReproduction } [A]).ballots ∧
      reproductionResultOf (roundAfter overvoteElection [A]).continuing overvoteBallot =
        .overvote := by
  decide

/-- After B, C and then A are defeated, `tabulate` counts `truncateBallot` for D with or without
duplicates removed, and the reproduction no longer tabulates it, although it tabulates it in the
initial round. -/
theorem truncate :
    ¬ truncateBallot.HasDuplicateRanking ∧ truncateBallot.HasOvervote ∧
      truncateBallot ∈ (roundAfter truncateElection [B, C, A]).ballots ∧
      resultOf (roundAfter truncateElection [B, C, A]).continuing truncateBallot = .voteFor D ∧
      truncateBallot.dropDuplicates ∈
        (roundAfter truncateElection.dropDuplicates [B, C, A]).ballots ∧
      resultOf (roundAfter truncateElection [B, C, A]).continuing truncateBallot.dropDuplicates =
        .voteFor D ∧
      truncateBallot.toReproduction ∈ (roundAfter
        { truncateElection with
          ballots := truncateElection.ballots.map Ballot.toReproduction } []).ballots ∧
      truncateBallot.toReproduction ∉ (roundAfter
        { truncateElection with
          ballots := truncateElection.ballots.map Ballot.toReproduction } [B, C, A]).ballots ∧
      reproductionResultOf (roundAfter truncateElection [B, C, A]).continuing truncateBallot =
        .overvote := by
  decide

/-- With only B continuing, Truncate + Retain counts `skipBallot` for B, whereas
Hybrid and Truncate + Remove make it inactive. -/
theorem skip_truncateAtOvervote :
    IsVoteFor [B] skipBallot.truncateAtOvervote B ∧
      MeetsInactivityCondition [B] skipBallot.toReproduction ∧
      MeetsInactivityCondition [B] skipBallot.dropDuplicates.truncateAtOvervote := by
  decide

/-- With only B continuing, Truncate + Remove counts `overvoteBallot` for B, whereas
Hybrid and Truncate + Retain make it inactive. -/
theorem overvote_truncateAtOvervote_dropDuplicates :
    IsVoteFor [B] overvoteBallot.dropDuplicates.truncateAtOvervote B ∧
      MeetsInactivityCondition [B] overvoteBallot.toReproduction ∧
      MeetsInactivityCondition [B] overvoteBallot.truncateAtOvervote := by
  decide

/-- For the fixed continuing list `[B]` and candidate B, the class counted by Hybrid is
properly included in the class counted by Truncate + Retain. Strictness is about ballot
classes, not a strict count inequality in every election. -/
theorem isVoteFor_toReproduction_ssubset_isVoteFor_truncateAtOvervote :
    (∀ b : Ballot, IsVoteFor [B] b.toReproduction B →
      IsVoteFor [B] b.truncateAtOvervote B) ∧
    (∃ b : Ballot, IsVoteFor [B] b.truncateAtOvervote B ∧
      ¬ IsVoteFor [B] b.toReproduction B) := by
  refine ⟨fun _ h => isVoteFor_truncateAtOvervote_of_isVoteFor_toReproduction h,
    skipBallot, skip_truncateAtOvervote.1, ?_⟩
  exact fun h => h.1 skip_truncateAtOvervote.2.1

/-- For the fixed continuing list `[B]` and candidate B, the class counted by Hybrid is
properly included in the class counted by Truncate + Remove. -/
theorem isVoteFor_toReproduction_ssubset_isVoteFor_truncateAtOvervote_dropDuplicates :
    (∀ b : Ballot, IsVoteFor [B] b.toReproduction B →
      IsVoteFor [B] b.dropDuplicates.truncateAtOvervote B) ∧
    (∃ b : Ballot, IsVoteFor [B] b.dropDuplicates.truncateAtOvervote B ∧
      ¬ IsVoteFor [B] b.toReproduction B) := by
  refine ⟨fun _ h => isVoteFor_truncateAtOvervote_dropDuplicates_of_isVoteFor_toReproduction h,
    overvoteBallot, overvote_truncateAtOvervote_dropDuplicates.1, ?_⟩
  exact fun h => h.1 overvote_truncateAtOvervote_dropDuplicates.2.1

/-- Even with the same continuing list and candidate, neither Truncate + Retain nor
Truncate + Remove counts every ballot counted by the other. -/
theorem truncateAtOvervote_incomparable_truncateAtOvervote_dropDuplicates :
    (∃ b : Ballot, IsVoteFor [B] b.truncateAtOvervote B ∧
      ¬ IsVoteFor [B] b.dropDuplicates.truncateAtOvervote B) ∧
    (∃ b : Ballot, IsVoteFor [B] b.dropDuplicates.truncateAtOvervote B ∧
      ¬ IsVoteFor [B] b.truncateAtOvervote B) := by
  exact ⟨⟨skipBallot, skip_truncateAtOvervote.1,
      fun h => h.1 skip_truncateAtOvervote.2.2⟩,
    ⟨overvoteBallot, overvote_truncateAtOvervote_dropDuplicates.1,
      fun h => h.1 overvote_truncateAtOvervote_dropDuplicates.2.2⟩⟩

/-- For the fixed continuing list `[D]` and candidate D, the class counted by Truncate + Retain is
properly included in the class counted by `resultOf` (Stop + Retain). -/
theorem isVoteFor_truncateAtOvervote_ssubset_isVoteFor :
    (∀ b : Ballot, IsVoteFor [D] b.truncateAtOvervote D → IsVoteFor [D] b D) ∧
    (∃ b : Ballot, IsVoteFor [D] b D ∧ ¬ IsVoteFor [D] b.truncateAtOvervote D) := by
  refine ⟨fun _ h => isVoteFor_of_isVoteFor_truncateAtOvervote h, truncateBallot, ?_, ?_⟩ <;>
    decide

end Alaska.DuplicatesExample
