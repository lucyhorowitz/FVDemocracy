import FVDemocracy.Alaska.Statute.WriteIns
import FVDemocracy.Alaska.Statute.Rounds

namespace Alaska

/-- Implements the Alaska ranked-choice tabulation procedure.

The input election is assumed to come from interpreted CVR data: candidate validity
and ballot-mark interpretation are trusted upstream. Before the ordinary RCV
tabulation begins, the aggregate write-in total is tested under AS 15.15.365(a).
If the write-ins do not qualify, all write-in candidates are removed from the
continuing field. If they do qualify, the input is assumed to identify valid
write-in candidates individually, and they remain in the continuing field.

A majority winner is checked only in the initial tabulation. If there is no majority winner
there, control passes to the sequential rounds of `tabulateRounds`, which defeat a candidate
in each round until the final round.
-/
def tabulate (e : Election) : RCVTree :=
  let cont₁ := initialCands e
  match majorityWinner cont₁ e.ballots with
  | none =>
    tabulateRounds cont₁ (e.ballots.filter fun b => decide (¬ MeetsInactivityCondition cont₁ b))
  | some c => RCVTree.winner c

theorem mem_of_mem_winners_tabulate {e : Election} {c : Cand}
    (h : c ∈ (tabulate e).winners) : c ∈ e.cands := by
  have hcont : ∀ d, d ∈ initialCands e → d ∈ e.cands := by
    intro d hd
    unfold initialCands at hd
    split at hd
    · exact hd
    · exact mem_of_mem_regulars hd
  unfold tabulate at h
  dsimp only at h
  split at h
  · exact hcont c (mem_of_mem_winners_tabulateRounds h)
  · next c' hc' =>
    simp [RCVTree.winners] at h
    subst h
    exact hcont c (List.mem_of_find?_eq_some hc')

theorem winners_tabulate_ne_nil {e : Election} (hcands : e.cands ≠ []) :
    (tabulate e).winners ≠ [] := by
  have hcont : initialCands e ≠ [] := by
    unfold initialCands
    split
    · exact hcands
    · next hq =>
      intro hreg
      refine hq (Or.inl fun c hc => votesFor_le_writeInTotal _ hc ?_)
      refine Decidable.byContradiction fun hw => ?_
      have hreg' : c ∈ regulars e.cands :=
        List.mem_eraseDups_of_mem (List.mem_filter.mpr ⟨hc, by simpa using hw⟩)
      simp [hreg] at hreg'
  unfold tabulate
  dsimp only
  split
  · exact winners_tabulateRounds_ne_nil _ hcont
  · simp [RCVTree.winners]

/-- The continuing candidates of the initial tabulation have no duplicates. -/
theorem nodup_tabulate_cont (e : Election) : (initialCands e).Nodup := by
  unfold initialCands
  split
  · exact e.cands_unique
  · exact nodup_regulars _

/-- AS 15.15.350(d): a candidate with a majority of the active ballots in the initial
tabulation is elected. -/
theorem tabulate_of_isMajorityWinner {e : Election} {c : Cand}
    (h : IsMajorityWinner (initialCands e) e.ballots c) : tabulate e = .winner c := by
  unfold tabulate
  dsimp only
  split
  · next hn => exact absurd h ((majorityWinner_eq_none_iff _ _).mp hn c)
  · next d hd =>
    rw [isMajorityWinner_unique ((majorityWinner_eq_some_iff _ _ d).mp hd) h]

/-- AS 15.15.350(d): if no candidate has a majority of the active ballots in the initial
tabulation, the rounds run over the ballots active in the initial tabulation. -/
theorem tabulate_of_not_isMajorityWinner {e : Election}
    (h : ∀ c, ¬ IsMajorityWinner (initialCands e) e.ballots c) :
    tabulate e = tabulateRounds (initialCands e)
      (e.ballots.filter fun b => decide (¬ MeetsInactivityCondition (initialCands e) b)) := by
  unfold tabulate
  dsimp only
  split
  · rfl
  · next d hd => exact absurd ((majorityWinner_eq_some_iff _ _ d).mp hd) (h d)

/-- AS 15.15.365(a): if the write-in candidates do not qualify, no write-in candidate is
elected. -/
theorem not_isWriteIn_of_mem_winners_tabulate {e : Election} {c : Cand}
    (hq : ¬ WriteInsQualify e.cands e.ballots recountMargin)
    (h : c ∈ (tabulate e).winners) : ¬ IsWriteIn c := by
  unfold tabulate at h
  dsimp only at h
  rw [initialCands, if_neg hq] at h
  split at h
  · exact not_isWriteIn_of_mem_regulars (mem_of_mem_winners_tabulateRounds h)
  · next d hd =>
    simp [RCVTree.winners] at h
    subst h
    exact not_isWriteIn_of_mem_regulars (List.mem_of_find?_eq_some hd)

end Alaska
