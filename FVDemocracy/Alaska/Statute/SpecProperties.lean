import FVDemocracy.Alaska.Statute.Correctness

/-!
# Properties of the specification

Facts about `Elected`, `MandatoryRecount` and `roundAfter` from `Spec.lean` that follow from
AS 15.15.350, stated without reference to the tabulation. Some are proved through
`tabulate_correct`.
-/

namespace Alaska

/-- AS 15.15.350(f): "The election board may not count an inactive ballot for any candidate." -/
theorem not_isVoteFor_of_meetsInactivityCondition {cont : List Cand} {b : Ballot}
    (h : MeetsInactivityCondition cont b) (c : Cand) : ¬ IsVoteFor cont b c :=
  fun hc => hc.1 h

/-- AS 15.15.350(d): a ballot is tabulated as a vote only for a continuing candidate ranked on
that ballot. -/
theorem exists_mem_ranks_of_isVoteFor {cont : List Cand} {b : Ballot} {c : Cand}
    (h : IsVoteFor cont b c) : c ∈ cont ∧ ∃ r ∈ b.ranks, c ∈ r := by
  obtain ⟨-, hcont, k, hk, hck⟩ := h
  obtain ⟨hlt, -, -⟩ :=
    List.findIdx?_eq_some_iff_getElem.mp ((highestContinuingRank_eq_some_iff cont b k).mpr hk)
  exact ⟨hcont, b.ranks[k], List.getElem_mem hlt, by simpa [Ballot.candsAt, hlt] using hck⟩

/-- AS 15.15.350(d): when there is at least one candidate, the tabulation elects a candidate. -/
theorem exists_elected {e : Election} (hcands : e.cands ≠ []) :
    ∃ defeated c, Elected e defeated c := by
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ (winners_tabulate_ne_nil hcands)
  obtain ⟨path, h⟩ := (mem_winners_iff_hasPath _ c).mp hc
  exact ⟨path.dropLast, c, (tabulate_correct e _ c).mpr ⟨path, h, rfl⟩⟩

/-- Only a candidate of the election can be elected. -/
theorem mem_cands_of_elected {e : Election} {defeated : List Cand} {c : Cand}
    (h : Elected e defeated c) : c ∈ e.cands := by
  obtain ⟨path, hpath, -⟩ := (tabulate_correct e defeated c).mp h
  exact mem_of_mem_winners_tabulate ((mem_winners_iff_hasPath _ c).mpr ⟨path, hpath⟩)

/-- AS 15.15.365(a): if the write-in candidates do not qualify, no write-in candidate is
elected. -/
theorem not_isWriteIn_of_elected {e : Election} {defeated : List Cand} {c : Cand}
    (hq : ¬ WriteInsQualify e.cands e.ballots recountMargin) (h : Elected e defeated c) :
    ¬ IsWriteIn c := by
  obtain ⟨path, hpath, -⟩ := (tabulate_correct e defeated c).mp h
  exact not_isWriteIn_of_mem_winners_tabulate hq ((mem_winners_iff_hasPath _ c).mpr ⟨path, hpath⟩)

/-- If each round has at most one candidate that can be defeated, two sequences of defeats that
both end in a round electing a candidate are the same. -/
theorem eq_of_validDefeats_of_elects {r : Round} {ds₁ ds₂ : List Cand} {c₁ c₂ : Cand}
    (hunique : ∀ ds d₁ d₂, r.ValidDefeats ds → (ds.foldl Round.next r).CanDefeat d₁ →
      (ds.foldl Round.next r).CanDefeat d₂ → d₁ = d₂)
    (hv₁ : r.ValidDefeats ds₁) (he₁ : (ds₁.foldl Round.next r).Elects c₁)
    (hv₂ : r.ValidDefeats ds₂) (he₂ : (ds₂.foldl Round.next r).Elects c₂) : ds₁ = ds₂ := by
  induction ds₁ generalizing r ds₂ with
  | nil =>
    cases ds₂ with
    | nil => rfl
    | cons d ds₂ =>
      have h3 := hv₂.1.1
      have h2 := he₁.1
      simp only [List.foldl_nil] at h2
      omega
  | cons d₁ ds₁ ih =>
    cases ds₂ with
    | nil =>
      have h3 := hv₁.1.1
      have h2 := he₂.1
      simp only [List.foldl_nil] at h2
      omega
    | cons d₂ ds₂ =>
      obtain rfl : d₁ = d₂ := hunique [] d₁ d₂ trivial hv₁.1 hv₂.1
      refine congrArg (d₁ :: ·) (ih (fun ds d d' hv hd hd' => ?_) hv₁.2 he₁ hv₂.2 he₂)
      exact hunique (d₁ :: ds) d d' ⟨hv₁.1, hv⟩ hd hd'

/-- AS 15.15.350(d), (e)(3): the only choices the procedure makes are the resolution of ties. If
no round has two candidates with the fewest votes and no final round is tied, the candidates
defeated and the candidate elected are determined by the election. -/
theorem eq_of_elected_of_elected {e : Election}
    (hunique : ∀ ds d₁ d₂, (initialRound e).ValidDefeats ds → (roundAfter e ds).CanDefeat d₁ →
      (roundAfter e ds).CanDefeat d₂ → d₁ = d₂)
    (hrecount : ∀ ds, ¬ MandatoryRecount e ds)
    {ds₁ ds₂ : List Cand} {c₁ c₂ : Cand} (h₁ : Elected e ds₁ c₁) (h₂ : Elected e ds₂ c₂) :
    ds₁ = ds₂ ∧ c₁ = c₂ := by
  rcases h₁ with ⟨hm₁, rfl⟩ | ⟨hno₁, hv₁, he₁⟩ <;> rcases h₂ with ⟨hm₂, rfl⟩ | ⟨hno₂, hv₂, he₂⟩
  · exact ⟨rfl, isMajorityWinner_unique hm₁ hm₂⟩
  · exact absurd hm₁ (hno₂ c₁)
  · exact absurd hm₂ (hno₁ c₂)
  · obtain rfl : ds₁ = ds₂ := eq_of_validDefeats_of_elects hunique hv₁ he₁ hv₂ he₂
    refine ⟨rfl, Classical.byContradiction fun hne => hrecount ds₁ ?_⟩
    exact (mandatoryRecount_iff e ds₁).mpr
      ⟨c₁, c₂, hne, Or.inr ⟨hno₁, hv₁, he₁⟩, Or.inr ⟨hno₂, hv₂, he₂⟩⟩

/-- The continuing candidates of every round are distinct. -/
theorem nodup_foldl_next_continuing {r : Round} (hnd : r.continuing.Nodup)
    (defeated : List Cand) : (defeated.foldl Round.next r).continuing.Nodup := by
  induction defeated generalizing r with
  | nil => exact hnd
  | cons d defeated ih => exact ih (hnd.erase d)

/-- No ballot tabulated in a round meets an inactivity condition in that round. -/
theorem not_meetsInactivityCondition_of_mem_roundAfter {e : Election} {defeated : List Cand}
    {b : Ballot} (hb : b ∈ (roundAfter e defeated).ballots) :
    ¬ MeetsInactivityCondition (roundAfter e defeated).continuing b :=
  ((mem_roundAfter_ballots_iff e defeated b).mp hb).2 defeated (List.prefix_refl defeated)

/-- A ballot that the round after defeating the candidates in `defeated` still tabulates has the
result there that `IsBallotResult` gives it for that round's continuing candidates. -/
theorem isBallotResultAfter_iff_of_mem_roundAfter {e : Election} {defeated : List Cand}
    {b : Ballot} (hb : b ∈ (roundAfter e defeated).ballots) (o : BallotResult) :
    IsBallotResultAfter e defeated b o ↔
      IsBallotResult (roundAfter e defeated).continuing b o := by
  cases o with
  | voteFor c => exact ⟨fun h => h.2, fun h => ⟨hb, h⟩⟩
  | inactive =>
    exact ⟨fun h => absurd hb ((isInactive_iff_not_mem_roundAfter e defeated b).mp h).2,
      fun h => absurd h (not_meetsInactivityCondition_of_mem_roundAfter hb)⟩

/-- In each round after the candidates in `defeated` are defeated, each ballot of `e` has exactly
one result: it is inactive, or it is tabulated as one vote for one candidate. -/
theorem exists_unique_isBallotResultAfter (e : Election) (defeated : List Cand) {b : Ballot}
    (hb : b ∈ e.ballots) :
    ∃ o, IsBallotResultAfter e defeated b o ∧
      ∀ o', IsBallotResultAfter e defeated b o' → o' = o := by
  by_cases hin : b ∈ (roundAfter e defeated).ballots
  · obtain ⟨o, ho, huniq⟩ := exists_unique_ballot_result (roundAfter e defeated).continuing b
    exact ⟨o, (isBallotResultAfter_iff_of_mem_roundAfter hin o).mpr ho, fun o' ho' =>
      huniq o' ((isBallotResultAfter_iff_of_mem_roundAfter hin o').mp ho')⟩
  · refine ⟨.inactive, (isInactive_iff_not_mem_roundAfter e defeated b).mpr ⟨hb, hin⟩, ?_⟩
    rintro (c | _) h
    · exact absurd h.1 hin
    · rfl

/-- If no ballot of `bs` meets an inactivity condition, the votes of the continuing candidates add
up to the number of ballots. -/
theorem sum_votesFor {cont : List Cand} (hnd : cont.Nodup) {bs : List Ballot}
    (h : ∀ b ∈ bs, ¬ MeetsInactivityCondition cont b) :
    (cont.map fun c => votesFor c cont bs).sum = bs.length := by
  induction bs with
  | nil =>
    simp only [votesFor, List.countP_nil, List.length_nil]
    induction cont <;> simp_all
  | cons b bs ih =>
    have hb := h b List.mem_cons_self
    obtain ⟨c₀, hc₀⟩ : ∃ c₀, highestContinuingCand cont b = some c₀ := by
      cases hc : highestContinuingCand cont b with
      | none =>
        exact absurd (Or.inl ((exhausted_iff_highest_cont_cand_none cont b).mpr hc)) hb
      | some c₀ => exact ⟨c₀, rfl⟩
    have hvote : ∀ c, IsVoteFor cont b c ↔ c = c₀ := by
      intro c
      rw [isVoteFor_iff, hc₀]
      simp [hb, eq_comm]
    have hmem : c₀ ∈ cont := mem_cont_of_isVoteFor ((hvote c₀).mpr rfl)
    have hsplit : (cont.map fun c => votesFor c cont (b :: bs)) =
        cont.map fun c => votesFor c cont bs + if c = c₀ then 1 else 0 := by
      refine List.map_congr_left fun c _ => ?_
      simp only [votesFor, List.countP_cons, decide_eq_true_eq, hvote]
    rw [hsplit, List.sum_map_add, ih fun b' hb' => h b' (List.mem_cons_of_mem _ hb'),
      List.sum_map_ite_eq_one hnd hmem, List.length_cons]

/-- AS 15.15.350(d): every ballot tabulated in a round is "one vote for the highest-ranked
continuing candidate on that ballot", so the votes of the continuing candidates add up to the
number of ballots tabulated in the round. -/
theorem sum_votes_roundAfter (e : Election) (defeated : List Cand) :
    ((roundAfter e defeated).continuing.map (roundAfter e defeated).votes).sum =
      (roundAfter e defeated).ballots.length :=
  sum_votesFor (nodup_foldl_next_continuing (nodup_tabulate_cont e) defeated)
    fun _ hb => not_meetsInactivityCondition_of_mem_roundAfter hb

/-- Every ballot tabulated in a round is active in it. -/
theorem numActive_roundAfter (e : Election) (defeated : List Cand) :
    numActive (roundAfter e defeated).continuing (roundAfter e defeated).ballots =
      (roundAfter e defeated).ballots.length :=
  List.countP_eq_length.mpr fun _ hb =>
    decide_eq_true (not_meetsInactivityCondition_of_mem_roundAfter hb)

/-- AS 15.15.350(d)(2): defeating `d` moves only the "votes cast for the defeated candidate". A
ballot tabulated as a vote for another candidate `c` is tabulated as a vote for `c` in the new
round. -/
theorem Round.isVoteFor_next_of_ne {r : Round} {b : Ballot} {c d : Cand}
    (h : IsVoteFor r.continuing b c) (hne : c ≠ d) : IsVoteFor (r.next d).continuing b c :=
  isVoteFor_of_subset List.erase_subset ((List.mem_erase_of_ne hne).mpr (mem_cont_of_isVoteFor h))
    h

/-- A ballot tabulated in the round `r` as a vote for a candidate other than `d` is still
tabulated after `d` is defeated. -/
theorem Round.mem_next_ballots_of_isVoteFor {r : Round} {b : Ballot} {c d : Cand}
    (hb : b ∈ r.ballots) (h : IsVoteFor r.continuing b c) (hne : c ≠ d) :
    b ∈ (r.next d).ballots :=
  List.mem_filter.mpr ⟨hb, decide_eq_true (Round.isVoteFor_next_of_ne h hne).1⟩

/-- Defeating `d` does not take votes from any other candidate. -/
theorem Round.votes_le_votes_next (r : Round) {c d : Cand} (hne : c ≠ d) :
    r.votes c ≤ (r.next d).votes c := by
  unfold Round.votes votesFor
  rw [Round.next, List.countP_filter]
  refine List.countP_mono_left fun b _ hb => ?_
  have hv := Round.isVoteFor_next_of_ne (of_decide_eq_true hb) hne
  simpa [Round.next] using And.intro hv hv.1

/-- The ballots tabulated after defeating `d` are some of the ballots tabulated before. -/
theorem Round.length_ballots_next_le (r : Round) (d : Cand) :
    (r.next d).ballots.length ≤ r.ballots.length :=
  List.length_filter_le _ _

/-- AS 15.15.350(d)(1), (d)(2): a candidate is defeated only while three or more continuing
candidates remain, so after defeating the candidates in `defeated`, starting from a round with two
or more continuing candidates, two or more remain. -/
theorem two_le_length_foldl_next_continuing {r : Round} {defeated : List Cand}
    (hv : r.ValidDefeats defeated) (h : 2 ≤ r.continuing.length) :
    2 ≤ (defeated.foldl Round.next r).continuing.length := by
  induction defeated generalizing r with
  | nil => exact h
  | cons d defeated ih =>
    refine ih hv.2 ?_
    have h3 := hv.1.1
    simp only [Round.next, List.length_erase_of_mem hv.1.2.1]
    omega

/-- If the initial tabulation has two or more continuing candidates, so does every round: after
defeating the candidates in `defeated`, two or more continuing candidates remain. The continuing
candidates of the initial tabulation are `initialCands e`, which leaves out the write-in candidates
unless they qualify under AS 15.15.365(a). -/
theorem two_le_length_roundAfter_continuing {e : Election} {defeated : List Cand}
    (hv : (initialRound e).ValidDefeats defeated) (h : 2 ≤ (initialCands e).length) :
    2 ≤ (roundAfter e defeated).continuing.length :=
  two_le_length_foldl_next_continuing hv h

section BallotLists

variable {bs bs' : List Ballot} (hlen : bs.length = bs'.length)
  (h : ∀ q ∈ bs.zip bs', ∀ cont o, IsBallotResult cont q.1 o ↔ IsBallotResult cont q.2 o)
include hlen h

theorem votesFor_eq_of_forall_mem_zip (c : Cand) (cont : List Cand) :
    votesFor c cont bs = votesFor c cont bs' :=
  List.countP_eq_of_forall_mem_zip hlen fun q hq =>
    decide_eq_decide.mpr (h q hq cont (.voteFor c))

theorem numActive_eq_of_forall_mem_zip (cont : List Cand) :
    numActive cont bs = numActive cont bs' :=
  List.countP_eq_of_forall_mem_zip hlen fun q hq =>
    decide_eq_decide.mpr (not_congr (h q hq cont .inactive))

/-- After removing the ballots that meet an inactivity condition when `cont` are continuing, the
remaining ballots of `bs` and `bs'` still correspond one to one with the same results. -/
theorem filter_forall_mem_zip (cont : List Cand) :
    let keep := fun b => decide (¬ MeetsInactivityCondition cont b)
    (bs.filter keep).length = (bs'.filter keep).length ∧
      ∀ q ∈ (bs.filter keep).zip (bs'.filter keep),
        ∀ cont o, IsBallotResult cont q.1 o ↔ IsBallotResult cont q.2 o := by
  intro keep
  have hk : ∀ q ∈ bs.zip bs', keep q.1 = keep q.2 := fun q hq =>
    decide_eq_decide.mpr (not_congr (h q hq cont .inactive))
  refine ⟨?_, fun q hq => ?_⟩
  · simpa only [List.countP_eq_length_filter] using List.countP_eq_of_forall_mem_zip hlen hk
  · rw [List.zip_filter_eq_of_forall_mem_zip hlen hk] at hq
    exact h q (List.mem_filter.mp hq).1

end BallotLists

/-- Two rounds with the same continuing candidates, whose ballots correspond one to one with the
same results, have the same continuing candidates and votes after the same defeats, and can defeat
the same candidates. -/
theorem foldl_next_of_forall_mem_zip {r r' : Round} (hc : r.continuing = r'.continuing)
    (hlen : r.ballots.length = r'.ballots.length)
    (h : ∀ q ∈ r.ballots.zip r'.ballots,
      ∀ cont o, IsBallotResult cont q.1 o ↔ IsBallotResult cont q.2 o)
    (ds : List Cand) :
    (ds.foldl Round.next r).continuing = (ds.foldl Round.next r').continuing ∧
      (∀ c, (ds.foldl Round.next r).votes c = (ds.foldl Round.next r').votes c) ∧
      (r.ValidDefeats ds ↔ r'.ValidDefeats ds) := by
  induction ds generalizing r r' with
  | nil =>
    exact ⟨hc, fun c => by simp [Round.votes, hc, votesFor_eq_of_forall_mem_zip hlen h], Iff.rfl⟩
  | cons d ds ih =>
    obtain ⟨hlen', h'⟩ := filter_forall_mem_zip hlen h (r'.continuing.erase d)
    obtain ⟨hcs, hvs, hv⟩ := ih (r := r.next d) (r' := r'.next d) (by simp [Round.next, hc])
      (by simpa [Round.next, hc] using hlen') (by simpa [Round.next, hc] using h')
    have hdef : r.CanDefeat d ↔ r'.CanDefeat d := by
      simp only [Round.CanDefeat, Round.votes, hc, votesFor_eq_of_forall_mem_zip hlen h]
    exact ⟨hcs, hvs, by simp only [Round.ValidDefeats, hdef, hv]⟩

section Elections

variable {e e' : Election} (hcands : e.cands = e'.cands)
  (hlen : e.ballots.length = e'.ballots.length)
  (h : ∀ q ∈ e.ballots.zip e'.ballots,
    ∀ cont o, IsBallotResult cont q.1 o ↔ IsBallotResult cont q.2 o)
include hcands hlen h

theorem initialCands_eq_of_forall_mem_zip : initialCands e = initialCands e' := by
  unfold initialCands
  simp only [WriteInsQualify, writeInTotal, votesFor_eq_of_forall_mem_zip hlen h, hcands]

/-- The initial rounds and the rounds after the same defeats of two elections with the same
candidates, whose ballots correspond one to one with the same results. -/
theorem roundAfter_of_forall_mem_zip (ds : List Cand) :
    (IsMajorityWinner (initialRound e).continuing (initialRound e).ballots =
      IsMajorityWinner (initialRound e').continuing (initialRound e').ballots) ∧
      (roundAfter e ds).continuing = (roundAfter e' ds).continuing ∧
      (∀ c, (roundAfter e ds).votes c = (roundAfter e' ds).votes c) ∧
      ((initialRound e).ValidDefeats ds ↔ (initialRound e').ValidDefeats ds) := by
  have hi := initialCands_eq_of_forall_mem_zip hcands hlen h
  obtain ⟨hlen₀, h₀⟩ := filter_forall_mem_zip hlen h (initialCands e')
  have hc₀ : (initialRound e).continuing = (initialRound e').continuing := by
    simp [initialRound, hi]
  have hlen₁ : (initialRound e).ballots.length = (initialRound e').ballots.length := by
    simpa [initialRound, hi] using hlen₀
  have h₁ : ∀ q ∈ (initialRound e).ballots.zip (initialRound e').ballots,
      ∀ cont o, IsBallotResult cont q.1 o ↔ IsBallotResult cont q.2 o := by
    simpa [initialRound, hi] using h₀
  refine ⟨?_, foldl_next_of_forall_mem_zip hc₀ hlen₁ h₁ ds⟩
  funext c
  simp only [IsMajorityWinner, hc₀, votesFor_eq_of_forall_mem_zip hlen₁ h₁,
    numActive_eq_of_forall_mem_zip hlen₁ h₁]

theorem elected_iff_of_forall_mem_zip (defeated : List Cand) (c : Cand) :
    Elected e defeated c ↔ Elected e' defeated c := by
  obtain ⟨hm, hc, hv, hd⟩ := roundAfter_of_forall_mem_zip hcands hlen h defeated
  simp only [Elected, NoMajority, Round.Elects, hm, hc, hv, hd]

theorem mandatoryRecount_iff_of_forall_mem_zip (defeated : List Cand) :
    MandatoryRecount e defeated ↔ MandatoryRecount e' defeated := by
  obtain ⟨hm, hc, hv, hd⟩ := roundAfter_of_forall_mem_zip hcands hlen h defeated
  simp only [MandatoryRecount, NoMajority, hm, hc, hv, hd]

end Elections

section Perm

variable {e e' : Election} (hcands : e.cands = e'.cands)
  (hlen : e.ballots.length = e'.ballots.length)
  (h : ∀ q ∈ e.ballots.zip e'.ballots, ∀ k, (q.1.candsAt k).Perm (q.2.candsAt k))
include hcands hlen h

/-- No election outcome depends on the order in which the ballots list the candidates at a
ranking: if `e` and `e'` have the same candidates, and each ballot of `e'` lists the same
candidates at each ranking as the corresponding ballot of `e`, in any order, then the same
candidates can be elected after the same defeats. -/
theorem elected_iff_of_perm (defeated : List Cand) (c : Cand) :
    Elected e defeated c ↔ Elected e' defeated c :=
  elected_iff_of_forall_mem_zip hcands hlen
    (fun q hq _ o => isBallotResult_iff_of_perm (h q hq) o) defeated c

/-- No mandatory recount depends on the order in which the ballots list the candidates at a
ranking. -/
theorem mandatoryRecount_iff_of_perm (defeated : List Cand) :
    MandatoryRecount e defeated ↔ MandatoryRecount e' defeated :=
  mandatoryRecount_iff_of_forall_mem_zip hcands hlen
    (fun q hq _ o => isBallotResult_iff_of_perm (h q hq) o) defeated

end Perm

end Alaska
