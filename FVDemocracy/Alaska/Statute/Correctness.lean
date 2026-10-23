import FVDemocracy.Alaska.Statute.Spec
import FVDemocracy.Alaska.Statute.Tabulate

/-!
# Correctness of the tabulation

A path of `tabulate e` lists the candidate defeated in each round, in order, then the candidate
*not* elected in the final round, and ends at the elected candidate. When a candidate `c` has a
majority in the initial tabulation, or `c` is the only continuing candidate, `tabulate e` is the
leaf `.winner c`, and its only path is `[]`.

`tabulate_correct`: `c` is elected after defeating the candidates in `defeated` exactly when
`tabulate e` has a path to `c` whose labels other than the last are `defeated`.

`hasPath_tabulate_iff` characterizes the whole path, including the last label, so the paths of
`tabulate e` are determined by AS 15.15.350(d) (`hasPath_eq_hasPath_tabulate`).
-/

namespace Alaska

theorem highestTally_singleton (c : Cand) (bs : List Ballot) :
    highestTally [c] bs = votesFor c [c] bs := by
  simp [highestTally, tallies]

/-- The paths of the final round: `c` is elected with at least as many votes as the other
candidate `d`, and the path is `[d]`. -/
theorem hasPath_finalRound_iff (c₁ c₂ : Cand) (bs : List Ballot) (path : List Cand) (c : Cand) :
    (finalRound c₁ c₂ bs).HasPath path c ↔
      ∃ d, path = [d] ∧
        ((c = c₁ ∧ d = c₂ ∧ votesFor c₂ [c₁, c₂] bs ≤ votesFor c₁ [c₁, c₂] bs) ∨
          (c = c₂ ∧ d = c₁ ∧ votesFor c₁ [c₁, c₂] bs ≤ votesFor c₂ [c₁, c₂] bs)) := by
  unfold finalRound
  dsimp only
  rw [apply_ite (RCVTree.HasPath · path c), apply_ite (RCVTree.HasPath · path c),
    RCVTree.hasPath_branch_iff, RCVTree.hasPath_branch_iff, RCVTree.hasPath_branch_iff]
  rcases Nat.lt_trichotomy (votesFor c₁ [c₁, c₂] bs) (votesFor c₂ [c₁, c₂] bs) with h | h | h
  · rw [if_neg (Nat.lt_asymm h), if_pos h]
    constructor
    · rintro ⟨d, t, path', rfl, hmem, ht⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
      obtain ⟨rfl, rfl⟩ := hmem
      obtain ⟨rfl, rfl⟩ := (RCVTree.hasPath_winner_iff _ _ _).mp ht
      exact ⟨_, rfl, Or.inr ⟨rfl, rfl, Nat.le_of_lt h⟩⟩
    · rintro ⟨d, rfl, ⟨rfl, rfl, hv⟩ | ⟨rfl, rfl, -⟩⟩
      · exact absurd hv (Nat.not_le_of_gt h)
      · exact ⟨_, .winner c, [], rfl, by simp, .winner c⟩
  · rw [if_neg (by omega), if_neg (by omega)]
    constructor
    · rintro ⟨d, t, path', rfl, hmem, ht⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        obtain ⟨rfl, rfl⟩ := (RCVTree.hasPath_winner_iff _ _ _).mp ht
      · exact ⟨_, rfl, Or.inr ⟨rfl, rfl, by omega⟩⟩
      · exact ⟨_, rfl, Or.inl ⟨rfl, rfl, by omega⟩⟩
    · rintro ⟨d, rfl, ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩⟩
      · exact ⟨_, .winner c, [], rfl, by simp, .winner c⟩
      · exact ⟨_, .winner c, [], rfl, by simp, .winner c⟩
  · rw [if_pos h]
    constructor
    · rintro ⟨d, t, path', rfl, hmem, ht⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
      obtain ⟨rfl, rfl⟩ := hmem
      obtain ⟨rfl, rfl⟩ := (RCVTree.hasPath_winner_iff _ _ _).mp ht
      exact ⟨_, rfl, Or.inl ⟨rfl, rfl, Nat.le_of_lt h⟩⟩
    · rintro ⟨d, rfl, ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, hv⟩⟩
      · exact ⟨_, .winner c, [], rfl, by simp, .winner c⟩
      · exact absurd hv (Nat.not_le_of_gt h)

/-- Every path of the final round has one branch. -/
theorem exists_eq_singleton_of_hasPath_finalRound {c₁ c₂ : Cand} {bs : List Ballot}
    {path : List Cand} {c : Cand} (h : (finalRound c₁ c₂ bs).HasPath path c) : ∃ d, path = [d] := by
  obtain ⟨d, rfl, -⟩ := (hasPath_finalRound_iff _ _ _ _ _).mp h
  exact ⟨d, rfl⟩

/-- The final round elects the candidates with the greatest number of votes. -/
theorem exists_hasPath_finalRound_iff (c₁ c₂ : Cand) (bs : List Ballot) (c : Cand) :
    (∃ path, (finalRound c₁ c₂ bs).HasPath path c) ↔
      c ∈ [c₁, c₂] ∧ votesFor c [c₁, c₂] bs = highestTally [c₁, c₂] bs := by
  simp only [hasPath_finalRound_iff, highestTally_pair]
  constructor
  · rintro ⟨_, d, rfl, ⟨rfl, rfl, hv⟩ | ⟨rfl, rfl, hv⟩⟩
    · exact ⟨by simp, by omega⟩
    · exact ⟨by simp, by omega⟩
  · rintro ⟨hc, hv⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨[c₂], c₂, rfl, Or.inl ⟨rfl, rfl, by omega⟩⟩
    · exact ⟨[c₁], c₁, rfl, Or.inr ⟨rfl, rfl, by omega⟩⟩

/-- With two or more continuing candidates, every path of the tree of rounds has at least one
branch. -/
theorem ne_nil_of_hasPath_tabulateRounds {cont : List Cand} {bs : List Ballot} {path : List Cand}
    {c : Cand} (hlen : 2 ≤ cont.length) (h : (tabulateRounds cont bs).HasPath path c) :
    path ≠ [] := by
  match cont, hlen with
  | c₁ :: c₂ :: cs, _ =>
    rw [tabulateRounds_cons_cons, RCVTree.hasPath_branch_iff] at h
    obtain ⟨d, t, path', rfl, -⟩ := h
    simp

/-- From the round with continuing candidates `cont` and ballots `bs`, the tree of rounds has a
path to `c` whose labels other than the last are `defeated` exactly when the rounds can defeat
the candidates in `defeated`, in order, and `c` is elected in the round after. -/
theorem hasPath_tabulateRounds_iff (cont : List Cand) (bs : List Ballot) (defeated : List Cand)
    (c : Cand) :
    (∃ path, (tabulateRounds cont bs).HasPath path c ∧ path.dropLast = defeated) ↔
      (Round.mk cont bs).ValidDefeats defeated ∧
        (defeated.foldl Round.next (Round.mk cont bs)).Elects c := by
  induction cont, bs using tabulateRounds.induct generalizing defeated with
  | case1 bs =>
    rw [tabulateRounds]
    cases defeated <;> simp [RCVTree.hasPath_branch_iff, Round.ValidDefeats, Round.canDefeat_iff,
      Round.elects_iff]
  | case2 bs c' =>
    rw [tabulateRounds]
    cases defeated with
    | nil =>
      simp only [RCVTree.hasPath_winner_iff, Round.ValidDefeats, Round.elects_iff, Round.votes,
        highestTally_singleton, List.foldl_nil]
      constructor
      · rintro ⟨_, ⟨rfl, rfl⟩, -⟩
        simp
      · rintro ⟨-, -, hc, -⟩
        exact ⟨[], ⟨rfl, List.mem_singleton.mp hc⟩, rfl⟩
    | cons d defeated => simp [RCVTree.hasPath_winner_iff, Round.ValidDefeats, Round.canDefeat_iff]
  | case3 bs c₁ c₂ =>
    rw [tabulateRounds]
    cases defeated with
    | nil =>
      simp only [Round.ValidDefeats, Round.elects_iff, Round.votes, List.foldl_nil, true_and]
      rw [← exists_hasPath_finalRound_iff]
      constructor
      · rintro ⟨path, h, -⟩
        exact ⟨by simp, path, h⟩
      · rintro ⟨-, path, h⟩
        obtain ⟨d, rfl⟩ := exists_eq_singleton_of_hasPath_finalRound h
        exact ⟨[d], h, rfl⟩
    | cons d defeated =>
      simp only [Round.ValidDefeats, Round.canDefeat_iff]
      constructor
      · rintro ⟨path, h, hpath⟩
        obtain ⟨d', rfl⟩ := exists_eq_singleton_of_hasPath_finalRound h
        simp at hpath
      · rintro ⟨⟨h3, -⟩, -⟩
        simp at h3
  | case4 bs c₁ c₂ c₃ cs current ih =>
    have hlen : ∀ d, d ∈ current → 2 ≤ (current.erase d).length := by
      intro d hd
      rw [List.length_erase_of_mem' hd]
      simp [current]
    rw [tabulateRounds_cons_cons]
    constructor
    · rintro ⟨path, h, rfl⟩
      obtain ⟨d₀, t, path', rfl, hdt, h⟩ := (RCVTree.hasPath_branch_iff _ _ _).mp h
      obtain ⟨⟨d, bs'⟩, hmem, heq⟩ := List.mem_map.mp hdt
      simp only [Prod.mk.injEq] at heq
      obtain ⟨h₁, h₂⟩ := heq
      subst h₁ h₂
      rw [List.dropLast_cons_of_ne_nil
        (ne_nil_of_hasPath_tabulateRounds (hlen d (singleRound_mono hmem)) h)]
      have hsub := (ih d bs' hmem path'.dropLast).mp ⟨path', h, rfl⟩
      obtain ⟨-, hd, hlow, rfl⟩ := (singleRound_correct _ _ _ _).mp hmem
      exact ⟨⟨(Round.canDefeat_iff _ _).mpr ⟨by simp, hd, hlow⟩, hsub.1⟩, hsub.2⟩
    · rintro ⟨hv, he⟩
      cases defeated with
      | nil =>
        simp [Round.elects_iff] at he
      | cons d defeated =>
        obtain ⟨hdef, hv⟩ := hv
        obtain ⟨-, hd, hlow⟩ := (Round.canDefeat_iff _ _).mp hdef
        have hmem : (d, ((Round.mk current bs).next d).ballots) ∈ singleRound current bs :=
          (singleRound_correct _ _ _ _).mpr ⟨by simp [current], hd, hlow, rfl⟩
        obtain ⟨path', h, hpath⟩ := (ih d _ hmem defeated).mpr ⟨hv, he⟩
        refine ⟨d :: path', (RCVTree.hasPath_branch_iff _ _ _).mpr
          ⟨d, _, path', rfl, List.mem_map.mpr ⟨_, hmem, rfl⟩, h⟩, ?_⟩
        rw [List.dropLast_cons_of_ne_nil (ne_nil_of_hasPath_tabulateRounds (hlen d hd) h), hpath]

/-- The tabulation is correct: `c` is elected after defeating the candidates in `defeated`, in
order, exactly when `tabulate e` has a path to `c` whose labels other than the last are
`defeated`. -/
theorem tabulate_correct (e : Election) (defeated : List Cand) (c : Cand) :
    Elected e defeated c ↔ ∃ path, (tabulate e).HasPath path c ∧ path.dropLast = defeated := by
  unfold Elected
  rw [isMajorityWinner_initialRound_iff, noMajority_iff]
  cases hm : majorityWinner (initialCands e) e.ballots with
  | none =>
    have hno := (majorityWinner_eq_none_iff _ _).mp hm
    rw [tabulate_of_not_isMajorityWinner hno, hasPath_tabulateRounds_iff]
    constructor
    · rintro (⟨hc, -⟩ | ⟨-, hv, he⟩)
      · exact absurd hc (hno c)
      · exact ⟨hv, he⟩
    · rintro ⟨hv, he⟩
      exact Or.inr ⟨hno, hv, he⟩
  | some m =>
    have hmaj := (majorityWinner_eq_some_iff _ _ m).mp hm
    rw [tabulate_of_isMajorityWinner hmaj]
    constructor
    · rintro (⟨hc, rfl⟩ | ⟨hno, -⟩)
      · obtain rfl := isMajorityWinner_unique hc hmaj
        exact ⟨[], (RCVTree.hasPath_winner_iff _ _ _).mpr ⟨rfl, rfl⟩, rfl⟩
      · exact absurd hmaj (hno m)
    · rintro ⟨path, h, rfl⟩
      obtain ⟨rfl, rfl⟩ := (RCVTree.hasPath_winner_iff _ _ _).mp h
      exact Or.inl ⟨hmaj, rfl⟩

/-- A recount is mandatory after defeating the candidates in `defeated` exactly when `tabulate e`
has paths to two different candidates whose labels other than the last are `defeated`. -/
theorem mandatoryRecount_iff_hasPath (e : Election) (defeated : List Cand) :
    MandatoryRecount e defeated ↔
      ∃ c₁ c₂, c₁ ≠ c₂ ∧
        (∃ path, (tabulate e).HasPath path c₁ ∧ path.dropLast = defeated) ∧
        (∃ path, (tabulate e).HasPath path c₂ ∧ path.dropLast = defeated) := by
  simp only [mandatoryRecount_iff, tabulate_correct]

/-- From the round with continuing candidates `cont` and ballots `bs`, if the tree of rounds has
a nonempty path to `c`, the last label of the path and `c` are the two continuing candidates of
the round after defeating the candidates in the rest of the path. -/
theorem continuing_of_hasPath_tabulateRounds {cont : List Cand} {bs : List Ballot}
    (path : List Cand) {c : Cand} (h : (tabulateRounds cont bs).HasPath path c)
    (hne : path ≠ []) :
    (path.dropLast.foldl Round.next (Round.mk cont bs)).continuing = [path.getLast hne, c] ∨
      (path.dropLast.foldl Round.next (Round.mk cont bs)).continuing = [c, path.getLast hne] := by
  induction cont, bs using tabulateRounds.induct generalizing path with
  | case1 bs =>
    rw [tabulateRounds, RCVTree.hasPath_branch_iff] at h
    simp at h
  | case2 bs c' =>
    rw [tabulateRounds, RCVTree.hasPath_winner_iff] at h
    exact absurd h.1 hne
  | case3 bs c₁ c₂ =>
    rw [tabulateRounds, hasPath_finalRound_iff] at h
    obtain ⟨d, rfl, ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩⟩ := h <;> simp
  | case4 bs c₁ c₂ c₃ cs current ih =>
    rw [tabulateRounds_cons_cons, RCVTree.hasPath_branch_iff] at h
    obtain ⟨d₀, t, path', rfl, hdt, h⟩ := h
    obtain ⟨⟨d, bs'⟩, hmem, heq⟩ := List.mem_map.mp hdt
    simp only [Prod.mk.injEq] at heq
    obtain ⟨h₁, h₂⟩ := heq
    subst h₁ h₂
    have hd := singleRound_mono hmem
    have hlen : 2 ≤ (current.erase d).length := by
      rw [List.length_erase_of_mem' hd]
      simp
    have hne' := ne_nil_of_hasPath_tabulateRounds hlen h
    obtain ⟨-, -, -, rfl⟩ := (singleRound_correct _ _ _ _).mp hmem
    rw [List.dropLast_cons_of_ne_nil hne', List.getLast_cons hne', List.foldl_cons]
    exact ih d _ hmem path' h hne'

/-- If `tabulate e` has a nonempty path to `c`, the last label of the path and `c` are the two
continuing candidates of the round after defeating the candidates in the rest of the path. -/
theorem continuing_roundAfter_of_hasPath_tabulate {e : Election} {path : List Cand} {c : Cand}
    (h : (tabulate e).HasPath path c) (hne : path ≠ []) :
    (roundAfter e path.dropLast).continuing = [path.getLast hne, c] ∨
      (roundAfter e path.dropLast).continuing = [c, path.getLast hne] := by
  cases hm : majorityWinner (initialCands e) e.ballots with
  | none =>
    rw [tabulate_of_not_isMajorityWinner ((majorityWinner_eq_none_iff _ _).mp hm)] at h
    exact continuing_of_hasPath_tabulateRounds path h hne
  | some m =>
    rw [tabulate_of_isMajorityWinner ((majorityWinner_eq_some_iff _ _ m).mp hm),
      RCVTree.hasPath_winner_iff] at h
    exact absurd h.1 hne

/-- `path` is a path of `tabulate e` to `c` exactly when either `c` has a majority in the initial
tabulation and `path = []`, or the rounds can defeat the candidates in `path.dropLast`, in order,
`c` is elected in the round after, and the other continuing candidate of that round, if there is
one, is the last label of `path`. -/
theorem hasPath_tabulate_iff (e : Election) (path : List Cand) (c : Cand) :
    (tabulate e).HasPath path c ↔
      (IsMajorityWinner (initialRound e).continuing (initialRound e).ballots c ∧ path = []) ∨
        (NoMajority e ∧ (initialRound e).ValidDefeats path.dropLast ∧
          (roundAfter e path.dropLast).Elects c ∧
          (roundAfter e path.dropLast).continuing.erase c = path.getLast?.toList) := by
  rw [isMajorityWinner_initialRound_iff]
  cases hm : majorityWinner (initialCands e) e.ballots with
  | none =>
    have hno' := (majorityWinner_eq_none_iff _ _).mp hm
    have hno : NoMajority e := (noMajority_iff e).mpr hno'
    have hlast : ∀ {path}, (tabulate e).HasPath path c →
        (roundAfter e path.dropLast).continuing.erase c = path.getLast?.toList := by
      intro path h
      cases path with
      | nil =>
        rw [tabulate_of_not_isMajorityWinner hno'] at h
        have hcont : initialCands e = [c] := by
          rcases hcont : initialCands e with _ | ⟨c₁, _ | ⟨c₂, cs⟩⟩ <;> rw [hcont] at h
          · rw [tabulateRounds, RCVTree.hasPath_branch_iff] at h
            simp at h
          · rw [tabulateRounds, RCVTree.hasPath_winner_iff] at h
            rw [h.2]
          · exact absurd rfl (ne_nil_of_hasPath_tabulateRounds (by simp) h)
        simp [roundAfter, initialRound, hcont]
      | cons d path' =>
        rw [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _)]
        rcases continuing_roundAfter_of_hasPath_tabulate h (List.cons_ne_nil _ _) with hc | hc <;>
          rw [hc] <;> by_cases hd : (d :: path').getLast (List.cons_ne_nil _ _) = c <;> simp [hd]
    constructor
    · intro h
      obtain ⟨hmaj, -⟩ | ⟨-, hv, hel⟩ := (tabulate_correct e path.dropLast c).mpr ⟨path, h, rfl⟩
      · exact absurd hmaj (hno c)
      · exact Or.inr ⟨hno, hv, hel, hlast h⟩
    · rintro (⟨hmaj, -⟩ | ⟨-, hv, hel, hrest⟩)
      · exact absurd hmaj (hno' c)
      · obtain ⟨path', h', hdrop⟩ :=
          (tabulate_correct e path.dropLast c).mp (Or.inr ⟨hno, hv, hel⟩)
        have hget : path'.getLast?.toList = path.getLast?.toList := by
          rw [← hlast h', hdrop, hrest]
        have hsplit : ∀ l : List Cand, l.dropLast ++ l.getLast?.toList = l := by
          intro l
          cases l with
          | nil => rfl
          | cons x l =>
            rw [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _)]
            exact List.dropLast_concat_getLast _
        rw [← hsplit path, ← hdrop, ← hget, hsplit]
        exact h'
  | some m =>
    have hmaj := (majorityWinner_eq_some_iff _ _ m).mp hm
    rw [tabulate_of_isMajorityWinner hmaj, RCVTree.hasPath_winner_iff]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact Or.inl ⟨hmaj, rfl⟩
    · rintro (⟨hc, rfl⟩ | ⟨hno, -⟩)
      · exact ⟨rfl, isMajorityWinner_unique hc hmaj⟩
      · exact absurd hmaj ((noMajority_iff e).mp hno m)

/-- The paths of `tabulate e` are determined by AS 15.15.350(d): a tree whose paths are those
described by `hasPath_tabulate_iff` has the same paths as `tabulate e`. -/
theorem hasPath_eq_hasPath_tabulate {e : Election} {t : RCVTree}
    (ht : ∀ path c, t.HasPath path c ↔
      (IsMajorityWinner (initialRound e).continuing (initialRound e).ballots c ∧ path = []) ∨
        (NoMajority e ∧ (initialRound e).ValidDefeats path.dropLast ∧
          (roundAfter e path.dropLast).Elects c ∧
          (roundAfter e path.dropLast).continuing.erase c = path.getLast?.toList)) :
    t.HasPath = (tabulate e).HasPath := by
  funext path c
  exact propext ((ht path c).trans (hasPath_tabulate_iff e path c).symm)

end Alaska
