import FVDemocracy.Alaska.Statute.StatuteDefs

namespace Alaska

/-- AS 15.15.350(d): the number of ballots in `bs` tabulated "as one vote for" `c`, the
highest-ranked continuing candidate on the ballot. -/
def votesFor (c : Cand) (cont : List Cand) (bs : List Ballot) : Nat :=
  bs.countP fun b => decide (IsVoteFor cont b c)

theorem votesFor_le_cons (c : Cand) (cont : List Cand) (bs : List Ballot) (b : Ballot) :
    votesFor c cont bs ≤ votesFor c cont (b :: bs) := by
  simp [votesFor]
  grind

theorem votesFor_cons_le (c : Cand) (cont : List Cand) (bs : List Ballot) (b : Ballot) :
    votesFor c cont (b :: bs) ≤ votesFor c cont bs+ 1 := by
  simp [votesFor]
  grind

def candTallies (cont : List Cand) (bs : List Ballot) : List (Cand × Nat) :=
  cont.map (fun c => (c, votesFor c cont bs))

def tallies (cont : List Cand) (bs : List Ballot) : List Nat :=
  cont.map (fun c => votesFor c cont bs)

def highestTally (cont : List Cand) (bs : List Ballot) : Nat :=
  (tallies cont bs).max?.getD 0

def lowestTally (cont : List Cand) (bs : List Ballot) : Nat :=
  (tallies cont bs).min?.getD 0

def losers (cont : List Cand) (bs : List Ballot) : List Cand :=
  cont.filter (fun c => votesFor c cont bs = lowestTally cont bs)

theorem loser_exists {cont : List Cand} (bs : List Ballot) (h_ne : cont ≠ []) :
    losers cont bs ≠ [] := by
  obtain ⟨m, hm⟩ : ∃ m, (tallies cont bs).min? = some m := by
    cases h : (tallies cont bs).min? with
    | none => simp_all [tallies]
    | some m => exact ⟨m, rfl⟩
  obtain ⟨c, hc, hcm⟩ := List.mem_map.mp (List.min?_mem hm)
  refine List.ne_nil_of_mem (a := c) ?_
  simp [losers, lowestTally, hm, hc, hcm]

/-- A continuing candidate `d` has `lowestTally` votes exactly when no continuing candidate has
fewer votes than `d`. -/
theorem votesFor_eq_lowestTally_iff {cont : List Cand} (bs : List Ballot) {d : Cand}
    (hd : d ∈ cont) :
    votesFor d cont bs = lowestTally cont bs ↔
      ∀ d' ∈ cont, votesFor d cont bs ≤ votesFor d' cont bs := by
  unfold lowestTally tallies
  cases h : (cont.map fun c => votesFor c cont bs).min? with
  | none => simp_all
  | some m =>
    rw [List.min?_eq_some_iff] at h
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at h
    obtain ⟨⟨c, hc, rfl⟩, hmin⟩ := h
    simp only [Option.getD_some]
    constructor
    · intro heq d' hd'
      rw [heq]
      exact hmin d' hd'
    · intro hle
      exact Nat.le_antisymm (hle c hc) (hmin d hd)

/-- A continuing candidate `c` has `highestTally` votes exactly when no continuing candidate has
more votes than `c`. -/
theorem votesFor_eq_highestTally_iff {cont : List Cand} (bs : List Ballot) {c : Cand}
    (hc : c ∈ cont) :
    votesFor c cont bs = highestTally cont bs ↔
      ∀ c' ∈ cont, votesFor c' cont bs ≤ votesFor c cont bs := by
  unfold highestTally tallies
  cases h : (cont.map fun c => votesFor c cont bs).max? with
  | none => simp_all
  | some m =>
    rw [List.max?_eq_some_iff] at h
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at h
    obtain ⟨⟨d, hd, rfl⟩, hmax⟩ := h
    simp only [Option.getD_some]
    constructor
    · intro heq c' hc'
      rw [heq]
      exact hmax c' hc'
    · intro hle
      exact Nat.le_antisymm (hmax c hc) (hle d hd)

/-- AS 15.15.350(d), (g)(2): the number of active ballots, those that meet no inactivity condition.
-/
def numActive (cont : List Cand) (bs : List Ballot) : Nat :=
  bs.countP (fun b => ¬ MeetsInactivityCondition cont b)

theorem numActive_le_cons (cont : List Cand) (bs : List Ballot) (b : Ballot) :
    numActive cont bs ≤ numActive cont (b :: bs) := by
  simp [numActive]
  grind

theorem numActive_cons_le (cont : List Cand) (bs : List Ballot) (b : Ballot) :
     numActive cont (b :: bs) ≤ numActive cont bs + 1  := by
  simp [numActive]
  grind

/-- AS 15.15.350(d): `c` "is highest-ranked on more than one-half of the active ballots". The
statute applies this test only in the initial tabulation, and so do `NoMajority`, `Elected` and
`tabulate`. -/
def IsMajorityWinner (cont : List Cand) (bs : List Ballot) (c : Cand) : Prop :=
  2 * votesFor c cont bs > numActive cont bs

instance (cont : List Cand) (bs : List Ballot) : DecidablePred (IsMajorityWinner cont bs) := by
  unfold IsMajorityWinner
  infer_instance

/-- A candidate of `cont` who has a majority (`IsMajorityWinner`), if there is one. `tabulate`
uses it only in the initial tabulation. -/
def majorityWinner (cont : List Cand) (bs : List Ballot) : Option Cand :=
  cont.find? (fun c => IsMajorityWinner cont bs c)

def ExistsMajorityWinner (cont : List Cand) (bs : List Ballot) : Prop :=
  match majorityWinner cont bs with
  | none => False
  | some _ => True

theorem numActive_cons (cont : List Cand) (bs : List Ballot) (b : Ballot) :
    numActive cont (b :: bs) = numActive cont bs ∨ numActive cont (b :: bs) = numActive cont bs + 1 := by
  simp [numActive]
  grind

theorem votesFor_cons (c : Cand) (cont : List Cand)  (bs : List Ballot) (b : Ballot) :
    votesFor c cont (b :: bs) = votesFor c cont bs ∨ votesFor c cont (b :: bs) = votesFor c cont bs + 1 := by
  simp [votesFor]
  grind

theorem ite_isVoteFor_add_le (cont : List Cand) (b : Ballot) {c d : Cand} (h : c ≠ d) :
    (if IsVoteFor cont b c then 1 else 0) + (if IsVoteFor cont b d then 1 else 0) ≤
      (if ¬ MeetsInactivityCondition cont b then 1 else 0) := by
  by_cases hc : IsVoteFor cont b c <;> by_cases hd : IsVoteFor cont b d
  · exact absurd
      (isHighestContinuingCand_unique (fun hov => hc.1 (Or.inr (Or.inl hov))) hc.2 hd.2) h
  · simp [hc, hd, hc.1]
  · simp [hc, hd, hd.1]
  · simp [hc, hd]

theorem votesFor_add_votesFor_le (cont : List Cand) (bs : List Ballot) {c d : Cand} (h : c ≠ d) :
    votesFor c cont bs + votesFor d cont bs ≤ numActive cont bs := by
  induction bs with
  | nil => simp [votesFor]
  | cons b bs ih =>
    calc
      votesFor c cont (b :: bs) + votesFor d cont (b :: bs)
          = (votesFor c cont bs + votesFor d cont bs) +
            ((if IsVoteFor cont b c then 1 else 0) + (if IsVoteFor cont b d then 1 else 0)) := by
            simp only [votesFor, List.countP_cons, decide_eq_true_eq]
            omega
      _ ≤ numActive cont bs +
            ((if IsVoteFor cont b c then 1 else 0) + (if IsVoteFor cont b d then 1 else 0)) := by
            omega
      _ ≤ numActive cont bs + (if ¬ MeetsInactivityCondition cont b then 1 else 0) := by
            have := ite_isVoteFor_add_le cont b h
            omega
      _ = numActive cont (b :: bs) := by
            simp only [numActive, List.countP_cons, decide_eq_true_eq]

theorem isMajorityWinner_unique {cont : List Cand} {bs : List Ballot} {c c' : Cand}
    (hc : IsMajorityWinner cont bs c) (hc' : IsMajorityWinner cont bs c') : c = c' := by
  by_cases h : c = c'
  · exact h
  · have := votesFor_add_votesFor_le cont bs h
    unfold IsMajorityWinner at hc hc'
    omega

theorem mem_cont_of_isVoteFor {cont : List Cand} {b : Ballot} {c : Cand}
    (h : IsVoteFor cont b c) : c ∈ cont :=
  h.2.1

/-- A candidate with a majority of the active ballots is continuing. -/
theorem mem_cont_of_isMajorityWinner {cont : List Cand} {bs : List Ballot} {c : Cand}
    (h : IsMajorityWinner cont bs c) : c ∈ cont := by
  have hpos : 0 < votesFor c cont bs := by unfold IsMajorityWinner at h; omega
  obtain ⟨b, -, hb⟩ := List.countP_pos_iff.mp hpos
  exact mem_cont_of_isVoteFor (of_decide_eq_true hb)

theorem majorityWinner_eq_some_iff (cont : List Cand) (bs : List Ballot) (c : Cand) :
    majorityWinner cont bs = some c ↔ IsMajorityWinner cont bs c := by
  constructor
  · intro h
    unfold majorityWinner at h
    simpa using List.find?_some h
  · intro h
    cases hf : majorityWinner cont bs with
    | none =>
      unfold majorityWinner at hf
      exact absurd h (by simpa using List.find?_eq_none.mp hf c (mem_cont_of_isMajorityWinner h))
    | some d =>
      unfold majorityWinner at hf
      have hd : IsMajorityWinner cont bs d := by simpa using List.find?_some hf
      rw [isMajorityWinner_unique hd h]

theorem majorityWinner_eq_none_iff (cont : List Cand) (bs : List Ballot) :
    majorityWinner cont bs = none ↔ ∀ c, ¬ IsMajorityWinner cont bs c := by
  constructor
  · intro h c hc
    rw [(majorityWinner_eq_some_iff cont bs c).mpr hc] at h
    contradiction
  · intro h
    cases hf : majorityWinner cont bs with
    | none => rfl
    | some d => exact absurd ((majorityWinner_eq_some_iff cont bs d).mp hf) (h d)

end Alaska
