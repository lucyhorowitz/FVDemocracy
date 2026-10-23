import FVDemocracy.Alaska.Statute.SpecProperties

/-!
# Simplifications of the tabulation

AS 15.15.350(d) treats the first and last rounds of the tabulation differently from the rounds in
between. A candidate highest-ranked on more than one-half of the active ballots in the initial
tabulation is elected without proceeding to the rounds of (d)(1) and (d)(2), and when two
continuing candidates remain, (d)(1) elects the candidate with more votes instead of (d)(2)
defeating the other. Neither changes which candidates can be elected:
`exists_elected_iff_mem_winners_recurseRounds` proves that a candidate can be elected under
AS 15.15.350(d) exactly when the candidate is a winner of `recurseRounds`, started from the
initial tabulation.

`recurseRounds` runs the rounds without a separate final round: it defeats a candidate with the
fewest votes in every round until one continuing candidate remains, including when two remain.
`recurseRounds_eq_tabulateRounds` proves that it returns the same tree as `tabulateRounds`, which
runs the final round of AS 15.15.350(d)(1) separately with `finalRound`.

The separate final round also shows up in the specification. Under AS 15.15.350(d)(1) the
candidate with fewer votes in the final round is not *defeated*; the other candidate is *elected*.
So the candidates defeated in `Elected` stop before the final round, while each path of the
tree, which treats the final round like every other round, ends with an edge labelled by the
candidate who is not elected. Comparing the tree with `Elected` therefore drops the last label
of each path.

`exists_elected_iff_exists_elects_roundAfter` proves that proceeding to the rounds even when a
candidate has a majority in the initial tabulation elects the same candidates: a candidate can be
elected under AS 15.15.350(d) exactly when some defeats that (d)(2) allows lead to a round in
which (d)(1) elects the candidate. A candidate with more than one-half of the ballots tabulated
in a round has more votes than every other continuing candidate, so (d)(2) cannot defeat the
candidate. Defeating another candidate takes no votes from the candidate and tabulates no new
ballots, so the candidate has more than one-half of the ballots tabulated in every later round,
and (d)(1) can elect only the candidate.
-/

namespace Alaska

def recurseRounds (cont : List Cand) (bs : List Ballot) : RCVTree :=
  match cont with
  | [] => RCVTree.branch []
  | [c] => RCVTree.winner c
  | c₁ :: c₂ :: cs =>
      let current := c₁ :: c₂ :: cs
      let next := singleRound current bs
      RCVTree.branch (
        next.attach.map (fun ⟨(c, bs'), hx⟩ =>
          have : c ∈ current := singleRound_mono hx
          (c, recurseRounds (current.erase c) bs'))
      )
termination_by cont.length
decreasing_by
  exact List.length_erase_lt_of_mem this

theorem recurseRounds_eq_tabulateRounds (cont : List Cand) (bs : List Ballot) :
    recurseRounds cont bs = tabulateRounds cont bs := by
  induction cont, bs using recurseRounds.induct with
  | case1 bs => simp [recurseRounds, tabulateRounds]
  | case2 bs c => simp [recurseRounds, tabulateRounds]
  | case3 bs c₁ c₂ cs current next ih =>
    rw [recurseRounds, tabulateRounds_cons_cons]
    refine congrArg RCVTree.branch ((List.map_congr_left ?_).trans List.attach_map_val)
    rintro ⟨⟨c, bs'⟩, hx⟩ -
    exact congrArg (Prod.mk c) (ih c bs' hx)

namespace Round

/-- A candidate `m` with more than one-half of the ballots tabulated in the round `r` has more
votes than every other candidate. -/
theorem votes_lt_votes_of_length_lt {r : Round} {m c : Cand}
    (hm : r.ballots.length < 2 * r.votes m) (hne : c ≠ m) : r.votes c < r.votes m := by
  have h₁ := votesFor_add_votesFor_le r.continuing r.ballots hne
  have h₂ : numActive r.continuing r.ballots ≤ r.ballots.length := List.countP_le_length
  unfold votes at hm ⊢
  omega

/-- AS 15.15.350(d)(2): when three or more continuing candidates remain, a candidate with more
than one-half of the ballots tabulated in the round `r` is not "the candidate with the fewest
votes", so (d)(2) cannot defeat the candidate. -/
theorem not_canDefeat_of_length_lt {r : Round} (hnd : r.continuing.Nodup) {m : Cand}
    (hm : r.ballots.length < 2 * r.votes m) : ¬ r.CanDefeat m := by
  rintro ⟨hlen, hmem, hle⟩
  obtain ⟨c, hc⟩ : ∃ c, c ∈ r.continuing.erase m :=
    List.exists_mem_of_length_pos (by rw [List.length_erase_of_mem' hmem]; omega)
  rw [hnd.mem_erase_iff'] at hc
  exact absurd (hle c hc.2) (Nat.not_le.mpr (votes_lt_votes_of_length_lt hm hc.1))

/-- A candidate `m` with more than one-half of the ballots tabulated in the round `r` is not
among the candidates defeated after `r`, and has more than one-half of the ballots tabulated in
the round after these defeats. -/
theorem foldl_next_of_length_lt {r : Round} (hnd : r.continuing.Nodup) {ds : List Cand}
    (hv : r.ValidDefeats ds) {m : Cand} (hmem : m ∈ r.continuing)
    (hm : r.ballots.length < 2 * r.votes m) :
    m ∉ ds ∧ m ∈ (ds.foldl next r).continuing ∧
      (ds.foldl next r).ballots.length < 2 * (ds.foldl next r).votes m := by
  induction ds generalizing r with
  | nil => exact ⟨by simp, hmem, hm⟩
  | cons d ds ih =>
    have hne : m ≠ d := by
      rintro rfl
      exact not_canDefeat_of_length_lt hnd hm hv.1
    have hlen := r.length_ballots_next_le d
    have hvotes := r.votes_le_votes_next hne
    obtain ⟨hds, h⟩ :=
      ih (hnd.erase d) hv.2 ((List.mem_erase_of_ne' hne).mpr hmem) (by omega)
    exact ⟨by simp [hne, hds], h⟩

/-- AS 15.15.350(d)(1), (d)(2): starting from any round, (d)(2) can defeat candidates until two
or fewer continuing candidates remain. -/
theorem exists_validDefeats (r : Round) :
    ∃ ds, r.ValidDefeats ds ∧ (ds.foldl next r).continuing.length ≤ 2 := by
  obtain ⟨n, hn⟩ : ∃ n, r.continuing.length = n := ⟨_, rfl⟩
  induction n generalizing r with
  | zero => exact ⟨[], trivial, by simp [hn]⟩
  | succ n ih =>
    by_cases h2 : n + 1 ≤ 2
    · exact ⟨[], trivial, by simpa [hn] using h2⟩
    have hne : r.continuing ≠ [] := List.ne_nil_of_length_pos (by omega)
    obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ (loser_exists r.ballots hne)
    rw [losers, List.mem_filter, decide_eq_true_eq] at hd
    have hcd : r.CanDefeat d := (r.canDefeat_iff d).mpr ⟨by omega, hd.1, hd.2⟩
    obtain ⟨ds, hv, hlen⟩ := ih (r.next d) (by simp [next, List.length_erase_of_mem' hd.1, hn])
    exact ⟨d :: ds, ⟨hcd, hv⟩, hlen⟩

end Round

/-- AS 15.15.350(d), (d)(2): a candidate highest-ranked on more than one-half of the active
ballots in the initial tabulation is never defeated, and is highest-ranked on more than one-half
of the active ballots in every round. -/
theorem isMajorityWinner_roundAfter {e : Election} {defeated : List Cand} {m : Cand}
    (hm : IsMajorityWinner (initialRound e).continuing (initialRound e).ballots m)
    (hv : (initialRound e).ValidDefeats defeated) :
    m ∉ defeated ∧ m ∈ (roundAfter e defeated).continuing ∧
      IsMajorityWinner (roundAfter e defeated).continuing (roundAfter e defeated).ballots m := by
  have h₀ : numActive (initialRound e).continuing (initialRound e).ballots =
      (initialRound e).ballots.length := numActive_roundAfter e []
  have hmem₀ := mem_cont_of_isMajorityWinner hm
  rw [IsMajorityWinner, h₀] at hm
  obtain ⟨hd, hmem, h⟩ := Round.foldl_next_of_length_lt (nodup_tabulate_cont e) hv hmem₀ hm
  refine ⟨hd, hmem, ?_⟩
  rw [IsMajorityWinner, numActive_roundAfter]
  exact h

/-- AS 15.15.350(d)(1): if a candidate `m` is highest-ranked on more than one-half of the active
ballots in the initial tabulation, then after any defeats that (d)(2) allows, (d)(1) elects only
`m`, and elects `m` once two or fewer continuing candidates remain. -/
theorem elects_roundAfter_iff_of_isMajorityWinner {e : Election} {defeated : List Cand}
    {m : Cand} (hm : IsMajorityWinner (initialRound e).continuing (initialRound e).ballots m)
    (hv : (initialRound e).ValidDefeats defeated) (c : Cand) :
    (roundAfter e defeated).Elects c ↔ c = m ∧ (roundAfter e defeated).continuing.length ≤ 2 := by
  obtain ⟨-, hmem, h⟩ := isMajorityWinner_roundAfter hm hv
  rw [IsMajorityWinner, numActive_roundAfter] at h
  have hlt : ∀ c, c ≠ m → (roundAfter e defeated).votes c < (roundAfter e defeated).votes m :=
    fun _ hne => Round.votes_lt_votes_of_length_lt h hne
  constructor
  · rintro ⟨hlen, -, hle⟩
    refine ⟨Decidable.byContradiction fun hne => ?_, hlen⟩
    exact absurd (hle m hmem) (Nat.not_le.mpr (hlt c hne))
  · rintro ⟨rfl, hlen⟩
    refine ⟨hlen, hmem, fun c' _ => ?_⟩
    by_cases hc' : c' = c
    · exact Nat.le_of_eq (congrArg _ hc')
    · exact Nat.le_of_lt (hlt c' hc')

/-- AS 15.15.350(d): the majority test of the initial tabulation does not change which candidates
can be elected. A candidate can be elected exactly when some defeats that (d)(2) allows lead to a
round in which (d)(1) elects the candidate. -/
theorem exists_elected_iff_exists_elects_roundAfter (e : Election) (c : Cand) :
    (∃ defeated, Elected e defeated c) ↔
      ∃ defeated, (initialRound e).ValidDefeats defeated ∧ (roundAfter e defeated).Elects c := by
  constructor
  · rintro ⟨defeated, ⟨hm, -⟩ | ⟨-, hv, he⟩⟩
    · obtain ⟨ds, hv, hlen⟩ := (initialRound e).exists_validDefeats
      exact ⟨ds, hv, (elects_roundAfter_iff_of_isMajorityWinner hm hv c).mpr ⟨rfl, hlen⟩⟩
    · exact ⟨defeated, hv, he⟩
  · rintro ⟨defeated, hv, he⟩
    cases hmw : majorityWinner (initialRound e).continuing (initialRound e).ballots with
    | none => exact ⟨defeated, Or.inr ⟨(majorityWinner_eq_none_iff _ _).mp hmw, hv, he⟩⟩
    | some m =>
      have hm := (majorityWinner_eq_some_iff _ _ m).mp hmw
      obtain ⟨rfl, -⟩ := (elects_roundAfter_iff_of_isMajorityWinner hm hv c).mp he
      exact ⟨[], Or.inl ⟨hm, rfl⟩⟩

/-- AS 15.15.350(d): neither the majority test of the initial tabulation nor the separate final
round of (d)(1) changes which candidates can be elected. A candidate can be elected exactly when
the candidate is a winner of `recurseRounds`, started from the initial tabulation, which defeats
a candidate with the fewest votes in every round until one continuing candidate remains. -/
theorem exists_elected_iff_mem_winners_recurseRounds (e : Election) (c : Cand) :
    (∃ defeated, Elected e defeated c) ↔
      c ∈ (recurseRounds (initialRound e).continuing (initialRound e).ballots).winners := by
  rw [exists_elected_iff_exists_elects_roundAfter, recurseRounds_eq_tabulateRounds,
    mem_winners_iff_hasPath]
  constructor
  · rintro ⟨defeated, h⟩
    obtain ⟨path, hpath, -⟩ := (hasPath_tabulateRounds_iff _ _ defeated c).mpr h
    exact ⟨path, hpath⟩
  · rintro ⟨path, hpath⟩
    exact ⟨path.dropLast, (hasPath_tabulateRounds_iff _ _ _ c).mp ⟨path, hpath, rfl⟩⟩

end Alaska
