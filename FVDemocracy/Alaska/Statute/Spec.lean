import FVDemocracy.Alaska.Statute.WriteIns

/-!
# The tabulation procedure of AS 15.15.350(d)

A `Round` is a round of the tabulation (AS 15.15.350(g)(5)): the continuing candidates and the
ballots still tabulated. `Elected e defeated c` holds when the procedure of AS 15.15.350(d) can
elect `c` after defeating the candidates in `defeated`, in order. Where the statute resolves a tie
by lot or by AS 15.15.460, every choice is allowed. `MandatoryRecount e defeated` holds when the
final round after defeating the candidates in `defeated` is a tie, which AS 15.15.350(e)(3) and
AS 15.15.460 send to a recount.

The tabulation begins with the initial tabulation, `initialRound`, whose continuing candidates
are `initialCands`: the write-in candidates are removed unless they qualify under
AS 15.15.365(a). If a candidate is highest-ranked on more than one-half of the active ballots in
the initial tabulation (`IsMajorityWinner`), that candidate is elected. "Otherwise, tabulation
proceeds in sequential rounds" (AS 15.15.350(d)) under (d)(1) and (d)(2), starting from
`initialRound`. `Round.Elects`, `Round.CanDefeat`, `Round.next`, `Round.ValidDefeats` and
`roundAfter` describe the sequential rounds, and `Elected` and `MandatoryRecount` apply them only
when no candidate has a majority in the initial tabulation (`NoMajority`).

A ballot that meets an inactivity condition (`MeetsInactivityCondition`) in some round is not
tabulated in that round or any later round, because AS 15.15.350(g)(2) defines an inactive ballot
as one that is "no longer tabulated". In particular,
a ballot with an overvote at its highest continuing ranking stays inactive after the overvoted
candidates are defeated. This is the reading the paper calls Stop.
-/

namespace Alaska

/-- A round of the tabulation: the initial tabulation (`initialRound`) or a sequential round that
begins after a defeat (`Round.next`). -/
structure Round where
  /-- The continuing candidates. -/
  continuing : List Cand
  /-- The ballots still tabulated. -/
  ballots : List Ballot

namespace Round

/-- The number of votes for `c` in the round. -/
def votes (r : Round) (c : Cand) : Nat :=
  votesFor c r.continuing r.ballots

/-- AS 15.15.350(d)(2): in the sequential rounds, which begin only when no candidate has a
majority in the initial tabulation (`NoMajority`), `d` can be defeated when three or more
continuing candidates remain ("otherwise" in (d)(1)) and `d` is "the candidate with the fewest
votes": no continuing candidate has fewer votes than `d`. When several candidates have the
fewest votes, AS 15.15.350(e)(3) resolves the tie by lot, so each of them can be defeated. -/
def CanDefeat (r : Round) (d : Cand) : Prop :=
  3 ≤ r.continuing.length ∧ d ∈ r.continuing ∧ ∀ d' ∈ r.continuing, r.votes d ≤ r.votes d'

/-- AS 15.15.350(d)(1): in the sequential rounds, which begin only when no candidate has a
majority in the initial tabulation (`NoMajority`), `c` is elected when "two or fewer continuing
candidates remain" and `c` is "the candidate with the greatest number of votes": no continuing
candidate has more votes than `c`. A tie is sent to AS 15.15.460 by AS 15.15.350(e)(3), so each
tied candidate can be elected. -/
def Elects (r : Round) (c : Cand) : Prop :=
  r.continuing.length ≤ 2 ∧ c ∈ r.continuing ∧ ∀ c' ∈ r.continuing, r.votes c' ≤ r.votes c

/-- `CanDefeat` in terms of `lowestTally`, which the tabulation computes. -/
theorem canDefeat_iff (r : Round) (d : Cand) :
    r.CanDefeat d ↔
      3 ≤ r.continuing.length ∧ d ∈ r.continuing ∧
        r.votes d = lowestTally r.continuing r.ballots := by
  unfold CanDefeat votes
  constructor
  · rintro ⟨hlen, hd, hle⟩
    exact ⟨hlen, hd, (votesFor_eq_lowestTally_iff _ hd).mpr hle⟩
  · rintro ⟨hlen, hd, heq⟩
    exact ⟨hlen, hd, (votesFor_eq_lowestTally_iff _ hd).mp heq⟩

/-- `Elects` in terms of `highestTally`, which the tabulation computes. -/
theorem elects_iff (r : Round) (c : Cand) :
    r.Elects c ↔
      r.continuing.length ≤ 2 ∧ c ∈ r.continuing ∧
        r.votes c = highestTally r.continuing r.ballots := by
  unfold Elects votes
  constructor
  · rintro ⟨hlen, hc, hle⟩
    exact ⟨hlen, hc, (votesFor_eq_highestTally_iff _ hc).mpr hle⟩
  · rintro ⟨hlen, hc, heq⟩
    exact ⟨hlen, hc, (votesFor_eq_highestTally_iff _ hc).mp heq⟩

/-- AS 15.15.350(d)(2): the sequential round that begins after `d` is defeated. `d` is no longer
a continuing candidate, and the ballots that are now inactive are no longer tabulated
(AS 15.15.350(g)(2)). -/
def next (r : Round) (d : Cand) : Round where
  continuing := r.continuing.erase d
  ballots := r.ballots.filter fun b => decide (¬ MeetsInactivityCondition (r.continuing.erase d) b)

/-- AS 15.15.350(d): "Otherwise, tabulation proceeds in sequential rounds", that is, when no
candidate has a majority in the initial tabulation (`NoMajority`). The candidates in `ds` can be
defeated in order, starting from the round `r`: each is a candidate (d)(2) can defeat in the
round after the ones before it are defeated. `Elected` and `MandatoryRecount` start from
`initialRound e`, the first of the sequential rounds. -/
def ValidDefeats : Round → List Cand → Prop
  | _, [] => True
  | r, d :: ds => r.CanDefeat d ∧ (r.next d).ValidDefeats ds

/-- The round that begins after defeating the candidates in `defeated`, in order, starting from
the round `r`. The candidates in `defeated` are distinct continuing candidates of `r`, and three
or more continuing candidates remain when each of them is defeated. -/
def nextAll (r : Round) (defeated : List Cand)
    (_hnodup : defeated.Nodup := by decide)
    (_hmem : ∀ d ∈ defeated, d ∈ r.continuing := by decide)
    (_hlen : defeated.length + 2 ≤ r.continuing.length := by decide) : Round :=
  defeated.foldl next r

end Round

/-- AS 15.15.350(d): the initial tabulation. The inactive ballots are not tabulated. When no
candidate has a majority (`NoMajority`), it is also the first of the sequential rounds. -/
def initialRound (e : Election) : Round where
  continuing := initialCands e
  ballots := e.ballots.filter fun b => decide (¬ MeetsInactivityCondition (initialCands e) b)

/-- The majority test of AS 15.15.350(d) gives the same answer on all the ballots as on the
ballots tabulated in the initial tabulation, since `votesFor` and `numActive` count only ballots
that meet no inactivity condition. -/
theorem isMajorityWinner_initialRound_iff (e : Election) (c : Cand) :
    IsMajorityWinner (initialRound e).continuing (initialRound e).ballots c ↔
      IsMajorityWinner (initialCands e) e.ballots c := by
  have hv : votesFor c (initialCands e)
      (e.ballots.filter fun b => decide (¬ MeetsInactivityCondition (initialCands e) b)) =
        votesFor c (initialCands e) e.ballots := by
    unfold votesFor
    rw [List.countP_filter]
    congr 1
    funext b
    by_cases h : IsVoteFor (initialCands e) b c
    · simp [h, h.1]
    · simp [h]
  have hn : numActive (initialCands e)
      (e.ballots.filter fun b => decide (¬ MeetsInactivityCondition (initialCands e) b)) =
        numActive (initialCands e) e.ballots := by
    unfold numActive
    rw [List.countP_filter]
    simp
  simp only [initialRound, IsMajorityWinner, hv, hn]

/-- The sequential round that begins after defeating the candidates in `defeated`, in order,
starting from the initial tabulation. Each defeat begins "a new round" (AS 15.15.350(d)(2)). -/
def roundAfter (e : Election) (defeated : List Cand) : Round :=
  defeated.foldl Round.next (initialRound e)

/-- AS 15.15.350(d): no candidate is highest-ranked on more than one-half of the active ballots in
the initial tabulation. -/
def NoMajority (e : Election) : Prop :=
  ∀ c, ¬ IsMajorityWinner (initialRound e).continuing (initialRound e).ballots c

theorem noMajority_iff (e : Election) :
    NoMajority e ↔ ∀ c, ¬ IsMajorityWinner (initialCands e) e.ballots c := by
  simp only [NoMajority, isMajorityWinner_initialRound_iff]

/-- AS 15.15.350(d): `c` is elected after defeating the candidates in `defeated`, in order.
Either `c` is highest-ranked on more than one-half of the active ballots in the initial tabulation
and no candidates are defeated, or no candidate has a majority there (`NoMajority`), the
sequential rounds starting from `initialRound e` defeat the candidates in `defeated`, and `c` is
elected in the round after. -/
def Elected (e : Election) (defeated : List Cand) (c : Cand) : Prop :=
  (IsMajorityWinner (initialRound e).continuing (initialRound e).ballots c ∧ defeated = []) ∨
    (NoMajority e ∧ (initialRound e).ValidDefeats defeated ∧ (roundAfter e defeated).Elects c)

/-- AS 15.15.350(e)(3) and AS 15.15.460: no candidate has a majority in the initial tabulation
(`NoMajority`), and after the sequential rounds defeat the candidates in `defeated`, two
continuing candidates remain and they tie, so the director must recount the votes. -/
def MandatoryRecount (e : Election) (defeated : List Cand) : Prop :=
  NoMajority e ∧ (initialRound e).ValidDefeats defeated ∧
    ∃ c₁ c₂, (roundAfter e defeated).continuing = [c₁, c₂] ∧ c₁ ≠ c₂ ∧
      (roundAfter e defeated).votes c₁ = (roundAfter e defeated).votes c₂

/-- Starting from the round `r`, the ballots tabulated after defeating the candidates in
`defeated`, in order, are the ballots of `r` that meet no inactivity condition in the round after
any of these defeats. -/
theorem mem_foldl_next_ballots_iff (r : Round) (defeated : List Cand) (b : Ballot) :
    b ∈ (defeated.foldl Round.next r).ballots ↔
      b ∈ r.ballots ∧
        ∀ ds, ds <+: defeated → ds ≠ [] →
          ¬ MeetsInactivityCondition (ds.foldl Round.next r).continuing b := by
  induction defeated generalizing r with
  | nil => simp
  | cons d defeated ih =>
    rw [List.foldl_cons, ih]
    simp only [Round.next, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨hb, hd⟩, h⟩
      refine ⟨hb, ?_⟩
      rintro (_ | ⟨d', ds⟩) hds hne
      · exact absurd rfl hne
      · obtain ⟨rfl, hds'⟩ := List.cons_prefix_cons.mp hds
        rcases ds with _ | ⟨d'', ds⟩
        · simpa [Round.next] using hd
        · simpa [Round.next] using h _ hds' (by simp)
    · rintro ⟨hb, h⟩
      refine ⟨⟨hb, ?_⟩, fun ds hds hne => ?_⟩
      · simpa [Round.next] using h [d] (by simp) (by simp)
      · simpa [Round.next] using h (d :: ds) (List.cons_prefix_cons.mpr ⟨rfl, hds⟩) (by simp)

/-- The ballots tabulated in the round after defeating the candidates in `defeated` are those
that meet no inactivity condition in that round or any earlier round. -/
theorem mem_roundAfter_ballots_iff (e : Election) (defeated : List Cand) (b : Ballot) :
    b ∈ (roundAfter e defeated).ballots ↔
      b ∈ e.ballots ∧
        ∀ ds, ds <+: defeated → ¬ MeetsInactivityCondition (roundAfter e ds).continuing b := by
  rw [roundAfter, mem_foldl_next_ballots_iff]
  simp only [initialRound, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hb, h₀⟩, h⟩
    refine ⟨hb, fun ds hds => ?_⟩
    rcases ds with _ | ⟨d, ds⟩
    · simpa [roundAfter, initialRound] using h₀
    · exact h _ hds (by simp)
  · rintro ⟨hb, h⟩
    exact ⟨⟨hb, by simpa [roundAfter, initialRound] using h [] List.nil_prefix⟩,
      fun ds hds _ => h ds hds⟩

/-- A ballot of the round `r` that the round after defeating the candidates in `defeated` no
longer tabulates met an inactivity condition in the round after some of these defeats. -/
theorem exists_prefix_of_not_mem_foldl_next_ballots (r : Round) (defeated : List Cand) {b : Ballot}
    (hb : b ∈ r.ballots) (hn : b ∉ (defeated.foldl Round.next r).ballots) :
    ∃ ds, ds <+: defeated ∧ ds ≠ [] ∧
      MeetsInactivityCondition (ds.foldl Round.next r).continuing b := by
  induction defeated generalizing r with
  | nil => exact absurd hb hn
  | cons d defeated ih =>
    by_cases h : b ∈ (r.next d).ballots
    · obtain ⟨ds, hds, -, hm⟩ := ih (r.next d) h hn
      exact ⟨d :: ds, List.cons_prefix_cons.mpr ⟨rfl, hds⟩, List.cons_ne_nil _ _, hm⟩
    · refine ⟨[d], List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩, List.cons_ne_nil _ _, ?_⟩
      show MeetsInactivityCondition (r.continuing.erase d) b
      exact Decidable.byContradiction fun hm => h (List.mem_filter.mpr ⟨hb, decide_eq_true hm⟩)

/-- AS 15.15.350(g)(2): "“inactive ballot” means a ballot that is no longer tabulated, either in
whole or in part, by the division because" it meets one of the conditions of
`MeetsInactivityCondition`. In the round after defeating the candidates in `defeated`, `b` is an
inactive ballot of `e` when it met one of them in that round or an earlier one.
`isInactive_iff_not_mem_roundAfter` shows that these are the ballots of `e` that the round no
longer tabulates. -/
def IsInactive (e : Election) (defeated : List Cand) (b : Ballot) : Prop :=
  b ∈ e.ballots ∧ ∃ ds, ds <+: defeated ∧ MeetsInactivityCondition (roundAfter e ds).continuing b

/-- AS 15.15.350(g)(2): the inactive ballots of `e` are the ballots that are "no longer
tabulated". -/
theorem isInactive_iff_not_mem_roundAfter (e : Election) (defeated : List Cand) (b : Ballot) :
    IsInactive e defeated b ↔ b ∈ e.ballots ∧ b ∉ (roundAfter e defeated).ballots := by
  constructor
  · rintro ⟨hb, ds, hds, hm⟩
    exact ⟨hb, fun hin => ((mem_roundAfter_ballots_iff e defeated b).mp hin).2 ds hds hm⟩
  · rintro ⟨hb, hn⟩
    refine ⟨hb, ?_⟩
    by_cases h₀ : b ∈ (initialRound e).ballots
    · obtain ⟨ds, hds, -, hm⟩ := exists_prefix_of_not_mem_foldl_next_ballots _ defeated h₀ hn
      exact ⟨ds, hds, hm⟩
    · refine ⟨[], List.nil_prefix, ?_⟩
      show MeetsInactivityCondition (initialCands e) b
      exact Decidable.byContradiction fun hm => h₀ (List.mem_filter.mpr ⟨hb, decide_eq_true hm⟩)

instance (e : Election) (defeated : List Cand) : DecidablePred (IsInactive e defeated) :=
  fun b => decidable_of_iff _ (isInactive_iff_not_mem_roundAfter e defeated b).symm

/-- AS 15.15.350(d) and (g)(2): in the round after defeating the candidates in `defeated`, the
ballot `b` of `e` is tabulated as the result `o`. An inactive ballot (`IsInactive`) is tabulated as
inactive, including a ballot that met an inactivity condition only in an earlier round. A ballot
that the round still tabulates is tabulated as one vote for its highest-ranked continuing
candidate. -/
def IsBallotResultAfter (e : Election) (defeated : List Cand) (b : Ballot) : BallotResult → Prop
  | .voteFor c =>
    b ∈ (roundAfter e defeated).ballots ∧ IsVoteFor (roundAfter e defeated).continuing b c
  | .inactive => IsInactive e defeated b

instance (e : Election) (defeated : List Cand) (b : Ballot) :
    DecidablePred (IsBallotResultAfter e defeated b)
  | .voteFor c => inferInstanceAs
      (Decidable (b ∈ (roundAfter e defeated).ballots ∧
        IsVoteFor (roundAfter e defeated).continuing b c))
  | .inactive => inferInstanceAs (Decidable (IsInactive e defeated b))

theorem highestTally_pair (c₁ c₂ : Cand) (bs : List Ballot) :
    highestTally [c₁, c₂] bs = max (votesFor c₁ [c₁, c₂] bs) (votesFor c₂ [c₁, c₂] bs) := by
  simp [highestTally, tallies, List.max?_cons]

/-- A recount is mandatory after defeating the candidates in `defeated` exactly when two
different candidates can be elected after defeating them. -/
theorem mandatoryRecount_iff (e : Election) (defeated : List Cand) :
    MandatoryRecount e defeated ↔
      ∃ c₁ c₂, c₁ ≠ c₂ ∧ Elected e defeated c₁ ∧ Elected e defeated c₂ := by
  simp only [MandatoryRecount, Elected, Round.elects_iff, Round.votes]
  generalize (roundAfter e defeated).continuing = cont
  generalize (roundAfter e defeated).ballots = bs
  constructor
  · rintro ⟨hm, hv, c₁, c₂, rfl, hne, heq⟩
    refine ⟨c₁, c₂, hne, Or.inr ⟨hm, hv, by simp, by simp, ?_⟩,
      Or.inr ⟨hm, hv, by simp, by simp, ?_⟩⟩
    · rw [highestTally_pair, heq]; simp
    · rw [highestTally_pair, heq]; simp
  · rintro ⟨c₁, c₂, hne, h₁ | ⟨hm₁, hv, hlen, hc₁, hv₁⟩, h₂ | ⟨hm₂, -, -, hc₂, hv₂⟩⟩
    · exact absurd (isMajorityWinner_unique h₁.1 h₂.1) hne
    · exact absurd h₁.1 (hm₂ c₁)
    · exact absurd h₂.1 (hm₁ c₂)
    · have heq : votesFor c₁ cont bs = votesFor c₂ cont bs := by rw [hv₁, hv₂]
      refine ⟨hm₁, hv, ?_⟩
      match cont, hc₁, hc₂, hlen, heq with
      | [a, b], hc₁, hc₂, _, heq =>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc₁ hc₂
        rcases hc₁ with rfl | rfl <;> rcases hc₂ with rfl | rfl
        · exact absurd rfl hne
        · exact ⟨c₁, c₂, rfl, hne, heq⟩
        · exact ⟨c₂, c₁, rfl, Ne.symm hne, heq.symm⟩
        · exact absurd rfl hne
      | [], hc₁, _, _, _ => simp at hc₁
      | [a], hc₁, hc₂, _, _ =>
        simp at hc₁ hc₂
        exact absurd (hc₁.trans hc₂.symm) hne
      | _ :: _ :: _ :: _, _, _, hlen, _ => simp at hlen

end Alaska
