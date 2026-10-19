import FVDemocracy.Alaska.Reproduction.Tabulate
import FVDemocracy.Alaska.Reproduction.PublishedReports

/-!
# The rounds of the reproduction in the form of a published report

`reportRounds ids e` gives each round of `reproductionTabulate e` as a `PublishedRound`: the votes
of the candidates `ids`, and the Blanks, Exhausted and Overvotes counts of the published reports.
It gives `none` when some round has a tie for the fewest votes.
-/

namespace Alaska

/-- The rounds of `tabulateRounds cont bs` when each round defeats a single candidate: the
continuing candidates and the ballots of each round, ending with the final round. `none` if some
round has a tie for the fewest votes. -/
def singlePathRounds (cont : List Cand) (bs : List Ballot) :
    Option (List (List Cand × List Ballot)) :=
  if cont.length ≤ 2 then some [(cont, bs)]
  else
    match h : singleRound cont bs with
    | [(d, bs')] =>
      have : d ∈ cont := singleRound_mono (bs' := bs') (h ▸ List.mem_singleton_self _)
      ((cont, bs) :: ·) <$> singlePathRounds (cont.erase d) bs'
    | _ => none
termination_by cont.length
decreasing_by exact List.length_erase_lt_of_mem this

/-- A round with continuing candidates `cont` and ballots `bs` as a `PublishedRound`: the votes of
each candidate of `ids`, 0 for one who is not continuing; `blanks`; the ballots of `allBallots`
that the reproduction makes exhausted, less `blanks`; and the ballots of `allBallots` that the
reproduction makes inactive at an overvote. -/
def PublishedRound.ofRound (ids : List Nat) (allBallots : List Ballot) (blanks : Nat)
    (cont : List Cand) (bs : List Ballot) : PublishedRound where
  votes := ids.map fun id =>
    (id, if Cand.regular id ∈ cont then votesFor (.regular id) cont bs else 0)
  blanks := blanks
  exhausted := allBallots.countP (fun b => reproductionResultOf cont b == .exhausted) - blanks
  overvotes := allBallots.countP fun b => reproductionResultOf cont b == .overvote

/-- The rounds of `reproductionTabulate e` as published rounds listing the candidates `ids`, or
`none` if some round has a tie for the fewest votes. Blanks are the ballots the reproduction makes
exhausted in round 1. -/
def reportRounds (ids : List Nat) (e : Election) : Option (List PublishedRound) :=
  let e' : Election := { e with ballots := e.ballots.map Ballot.toReproduction }
  let cont₁ := initialCands e'
  let rounds := if (majorityWinner cont₁ e'.ballots).isSome then some [(cont₁, e'.ballots)]
    else singlePathRounds cont₁
      (e'.ballots.filter fun b => decide (¬ MeetsInactivityCondition cont₁ b))
  let blanks := e.ballots.countP fun b => reproductionResultOf cont₁ b == .exhausted
  rounds.map fun rs => rs.map fun (cont, bs) => PublishedRound.ofRound ids e.ballots blanks cont bs

end Alaska
