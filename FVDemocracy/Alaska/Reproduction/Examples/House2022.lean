import FVDemocracy.Alaska.Reproduction.Tabulate

/-!
# Real ballots: U.S. Representative, 2022 general election

These ballots come from the cast vote records of the November 2022 general election
(`cvr/2022-general`), contest 4, U.S. Representative, as `readBallots` reads them: each
session's current state, without ambiguous marks. Each ballot's `ballotIndex` is the session's
position across the `CvrExport_<n>.json` files, and its docstring gives the session's
`TabulatorId-BatchId-RecordId` and the file that holds it. Candidates are their ids in
`CandidateManifest.json`. The write-ins do not qualify under AS 15.15.365(a), so no write-in is
ever a continuing candidate.

`tabulate` and `reproductionTabulate` both defeat Bye and then Begich, and both elect Peltola over
Palin in the final round, as the published report does (<https://www.elections.alaska.gov/results/22GENR/US%20REP.txt>,
`publishedReports`). `resultsByRound b` gives the result of the ballot `b` in each of the three
rounds when `b` is the only ballot: a vote for its highest-ranked continuing candidate while the
round still tabulates `b`, and inactive once it does not. `resultsByRound b.toReproduction` gives
the results the reproduction tabulation gives `b` (`reproductionTabulate`,
`resultOf_toReproduction`).

* `overvoteBallot`: the statutory model counts it for Palin in the final round and the reproduction
  model does not. Its overvote is above its highest continuing ranking but not at it
  (`resultOf_toReproduction_eq_inactive_iff`). Had Begich been defeated before Bye, the statutory
  model would not count it either, with the same continuing candidates in the final round.
* `persistenceBallot`: both models make it inactive in round 1. In round 2 it no longer has an
  overvote at its highest continuing ranking, and both models still do not count it.
* `duplicateBallot`: the statutory model counts it for Palin in the final round and the
  reproduction model does not, because the reproduction model treats rankings that repeat Begich
  as blank.
* `inactiveBallot`: both models make it inactive in round 1, at an overvote at its highest
  continuing ranking.
* `countedBallot`: both models count it for Palin in every round, because a continuing candidate
  is ranked above its overvote.
-/

namespace Alaska.House2022

def Begich : Cand := .regular 263
def Palin : Cand := .regular 264
def Peltola : Cand := .regular 265
def Bye : Cand := .regular 279
def WriteIn : Cand := .writeIn 0

/-- The continuing candidates of the initial tabulation: the regular candidates, in the order of
`CandidateManifest.json`. -/
def initialCont : List Cand := [Begich, Bye, Palin, Peltola]

/-- The initial tabulation with `b` as its only ballot. It tabulates `b` unless `b` is
inactive. -/
def round1 (b : Ballot) : Round :=
  ⟨initialCont, [b].filter fun b => decide (¬ MeetsInactivityCondition initialCont b)⟩

/-- The result of the ballot `b` in round 1, in round 2 (after Bye is defeated) and in the final
round (after Begich is defeated), when `b` is the only ballot: `resultOf` while the round still
tabulates `b`, and inactive once it does not. -/
def resultsByRound (b : Ballot) : List BallotResult :=
  [round1 b, (round1 b).next Bye, ((round1 b).next Bye).next Begich].map fun r =>
    if b ∈ r.ballots then resultOf r.continuing b else .inactive

/-! ## An overvote above the highest continuing ranking -/

/-- `ballotIndex` 241786, session `93600-25-1` (`CvrExport_1069.json`): 1 Begich, 2 Bye and a
write-in, 3 Palin, 4 Peltola. -/
def overvoteBallot : Ballot :=
  ⟨241786, [[Begich], [Bye, WriteIn], [Palin], [Peltola], []]⟩

/-- The statutory model counts `overvoteBallot` for Begich, then for Palin once Begich is
defeated. When Begich is defeated, Bye has already been defeated, so the overvoted ranking 2 marks
no continuing candidate and is never the highest continuing ranking. -/
theorem resultsByRound_overvoteBallot :
    resultsByRound overvoteBallot = [.voteFor Begich, .voteFor Begich, .voteFor Palin] := by
  decide

/-- The reproduction model counts `overvoteBallot` for Begich, but not for anyone once Begich is
defeated. -/
theorem resultsByRound_overvoteBallot_toReproduction :
    resultsByRound overvoteBallot.toReproduction =
      [.voteFor Begich, .voteFor Begich, .inactive] := by
  decide

/-- In the final round, `overvoteBallot` has an overvote at ranking 2, above its highest continuing
ranking, ranking 3, and no overvote at its highest continuing ranking. (Rankings are numbered from
0, so these are ranks 1 and 2.) -/
theorem overvoteBallot_final :
    overvoteBallot.IsOvervoteAt 1 ∧ IsHighestContinuingRank [Palin, Peltola] overvoteBallot 2 ∧
      ¬ IsOvervoteAtHighestCont [Palin, Peltola] overvoteBallot := by
  decide

/-- Had Begich been defeated before Bye, the statutory model would have made `overvoteBallot`
inactive in round 2, at the overvote, and would not tabulate it in the final round. The final
round has the same continuing candidates in either order, and `overvoteBallot` meets no
inactivity condition for them. -/
theorem overvoteBallot_defeat_order :
    ((round1 overvoteBallot).nextAll [Begich]).ballots = [] ∧
      ((round1 overvoteBallot).nextAll [Begich, Bye]).ballots = [] ∧
      ((round1 overvoteBallot).nextAll [Bye, Begich]).ballots = [overvoteBallot] ∧
      ((round1 overvoteBallot).nextAll [Begich, Bye]).continuing = [Palin, Peltola] ∧
      ((round1 overvoteBallot).nextAll [Bye, Begich]).continuing = [Palin, Peltola] ∧
      ¬ MeetsInactivityCondition [Palin, Peltola] overvoteBallot := by
  decide

/-! ## Inactivity persists -/

/-- `ballotIndex` 32679, session `23825-0-47861` (`CvrExport_47.json`): 1 Bye and a write-in,
2 Peltola, 3 Begich, 4 Palin. -/
def persistenceBallot : Ballot :=
  ⟨32679, [[Bye, WriteIn], [Peltola], [Begich], [Palin], []]⟩

/-- Neither model counts `persistenceBallot` in any round. -/
theorem resultsByRound_persistenceBallot :
    resultsByRound persistenceBallot = [.inactive, .inactive, .inactive] ∧
      resultsByRound persistenceBallot.toReproduction = [.inactive, .inactive, .inactive] := by
  decide

/-- In round 1, `persistenceBallot` has an overvote at its highest continuing ranking. In round 2,
after Bye is defeated, it does not, and `resultOf` for round 2's continuing candidates alone would
count it for Peltola. -/
theorem persistenceBallot_rounds :
    IsOvervoteAtHighestCont initialCont persistenceBallot ∧
      ¬ MeetsInactivityCondition (initialCont.erase Bye) persistenceBallot ∧
      resultOf (initialCont.erase Bye) persistenceBallot = .voteFor Peltola := by
  decide

/-! ## Duplicate rankings -/

/-- `ballotIndex` 82311, session `2755-0-354090` (`CvrExport_133.json`): 1 Begich, 2 Begich,
3 Begich, 4 Palin. -/
def duplicateBallot : Ballot :=
  ⟨82311, [[Begich], [Begich], [Begich], [Palin], []]⟩

/-- The statutory model counts `duplicateBallot` for Begich, then for Palin once Begich is
defeated. -/
theorem resultsByRound_duplicateBallot :
    resultsByRound duplicateBallot = [.voteFor Begich, .voteFor Begich, .voteFor Palin] := by
  decide

/-- The reproduction model counts `duplicateBallot` for Begich, but not for anyone once Begich is
defeated. -/
theorem resultsByRound_duplicateBallot_toReproduction :
    resultsByRound duplicateBallot.toReproduction =
      [.voteFor Begich, .voteFor Begich, .inactive] := by
  decide

/-- The reproduction model reads `duplicateBallot` with rankings 2 and 3 blank, so in the final
round it has two sequential skipped rankings before its highest continuing ranking. In the
statutory model, ranking 2 marks Begich and is not a skipped ranking. -/
theorem duplicateBallot_skips :
    duplicateBallot.toReproduction.ranks = [[Begich], [], [], [Palin], []] ∧
      TwoSkips [Palin, Peltola] duplicateBallot.toReproduction ∧
      ¬ duplicateBallot.SkippedRankingAt 1 := by
  decide

/-! ## Ballots both models count the same way -/

/-- `ballotIndex` 5475, session `93901-0-443977` (`CvrExport_3.json`): 1 Palin and Bye, 2 Begich. -/
def inactiveBallot : Ballot :=
  ⟨5475, [[Palin, Bye], [Begich], [], [], []]⟩

/-- Both models make `inactiveBallot` inactive in round 1, at an overvote at its highest
continuing ranking. -/
theorem resultsByRound_inactiveBallot :
    IsOvervoteAtHighestCont initialCont inactiveBallot ∧
      resultsByRound inactiveBallot = [.inactive, .inactive, .inactive] ∧
      resultsByRound inactiveBallot.toReproduction = [.inactive, .inactive, .inactive] := by
  decide

/-- `ballotIndex` 12056, session `35582-0-60942` (`CvrExport_12.json`): 1 Palin, 2 Peltola and
Begich. -/
def countedBallot : Ballot :=
  ⟨12056, [[Palin], [Peltola, Begich], [], [], []]⟩

/-- Both models count `countedBallot` for Palin in every round. -/
theorem resultsByRound_countedBallot :
    resultsByRound countedBallot = [.voteFor Palin, .voteFor Palin, .voteFor Palin] ∧
      resultsByRound countedBallot.toReproduction =
        [.voteFor Palin, .voteFor Palin, .voteFor Palin] := by
  decide

end Alaska.House2022
