import FVDemocracy.Alaska.Statute.Correctness
import FVDemocracy.Alaska.Statute.ReadBallot

/-!
# The tabulation that reproduces Alaska's published results

`readReproduction` reads a ballot by the rules that reproduce, from the cast vote records, every
round of the published reports in `publishedReports`. `reproductionTabulate` tabulates an election
with it. The reports list the tabulator's options "Skip overvoted rankings: False", "Handling skip
rankings: Exhausted on Two or More Ranks Skipped" and "Exclude unresolved write-ins: True".

`readReproduction` reads a ballot's rankings from the highest down.

* A ranking with two or more candidates is an overvote, and the ballot becomes inactive when the
  reading reaches it, even if every candidate at that ranking has been defeated. We call this
  reading Truncate. Under AS 15.15.350(e)(1) and (g)(2) an overvote makes a ballot inactive
  only at its highest continuing ranking.
* A mark for a candidate that the ballot also marks at a higher ranking (the export's
  `DuplicatedRcvCandidate`) does not count, and a ranking holding only such marks is blank. The
  mark still counts toward an overvote.
* Two sequential blank rankings make the ballot inactive. A ranking that marks only defeated
  candidates is not blank.

`resultOf_toReproduction` shows that this reading gives a ballot `b` the result `resultOf` gives
`b.toReproduction`: the rankings of `b` above its first overvote, with repeated candidates removed.
So `reproductionTabulate` is `tabulate` on these ballots. `not_reproductionTabulate_correct` shows
that it does not give the outcomes `Spec.lean` allows.
-/

namespace Alaska

/-- The rankings `rs` with each candidate removed from every ranking after the first one marking
it, or from every ranking if it is in `earlier`. -/
def dropRepeats (earlier : List Cand) : List (List Cand) → List (List Cand)
  | [] => []
  | r :: rs => r.filter (· ∉ earlier) :: dropRepeats (earlier ++ r) rs

/-- The ballot `b` with its rankings from the first overvote down removed, and with each candidate
removed from every ranking after the first one marking it. -/
def Ballot.toReproduction (b : Ballot) : Ballot :=
  ⟨b.ballotIndex, dropRepeats [] (b.ranks.takeWhile fun r => decide (r.eraseDups.length < 2))⟩

/-- The result of a ballot in a round of the reproduction tabulation. The reports count inactive
ballots that reached an overvote separately from the other inactive ballots. -/
inductive ReproductionResult where
  | voteFor (c : Cand)
  | overvote
  | exhausted
deriving Repr, DecidableEq

def ReproductionResult.toBallotResult : ReproductionResult → BallotResult
  | .voteFor c => .voteFor c
  | .overvote => .inactive
  | .exhausted => .inactive

/-- The result of the rankings `rs` in the reproduction tabulation, read from the highest ranking
down, when `cont` are the continuing candidates. `earlier` are the candidates marked at the
rankings read before `rs`, and `skipped` is whether the ranking read just before `rs` was blank.
`reproductionResultOf` reads a ballot from its first ranking, with `skipped` false and `earlier`
empty.

* A ranking with two or more candidates is an overvote, and reading stops.
* Otherwise the reading drops the marks for candidates in `earlier`. If a continuing candidate is
  left, the ballot counts for it.
* If nothing is left, the ranking is blank, and the ballot is exhausted if the ranking before it
  was also blank.
* If only defeated candidates are left, the reading moves to the next ranking.
* A ballot whose rankings run out is exhausted. -/
def readReproduction (cont : List Cand) (skipped : Bool) (earlier : List Cand) :
    List (List Cand) → ReproductionResult
  | [] => .exhausted
  | r :: rs =>
    if 2 ≤ r.eraseDups.length then .overvote
    else
      match (r.filter (· ∉ earlier)).find? (· ∈ cont) with
      | some c => .voteFor c
      | none =>
        if r.filter (· ∉ earlier) = [] then
          if skipped then .exhausted else readReproduction cont true (earlier ++ r) rs
        else readReproduction cont false (earlier ++ r) rs

/-- The result of the ballot `b` in the reproduction tabulation when `cont` are the continuing
candidates. -/
def reproductionResultOf (cont : List Cand) (b : Ballot) : ReproductionResult :=
  readReproduction cont false [] b.ranks

/-- The reproduction tabulation of the election `e`: `tabulate` on the ballots
`Ballot.toReproduction` gives. -/
def reproductionTabulate (e : Election) : RCVTree :=
  tabulate { e with ballots := e.ballots.map Ballot.toReproduction }

/-- A ranking with no overvote has none after some of its candidates are removed. -/
theorem eraseDups_filter_length_lt_two {l : List Cand} (p : Cand → Bool)
    (hl : l.eraseDups.length < 2) : (l.filter p).eraseDups.length < 2 := by
  have hnd := List.nodup_eraseDups (l.filter p)
  have hmem : ∀ x ∈ (l.filter p).eraseDups, x ∈ l :=
    fun x hx => (List.mem_filter.mp (List.mem_of_mem_eraseDups hx)).1
  match h : (l.filter p).eraseDups, hnd, hmem with
  | [], _, _ => simp
  | [_], _, _ => simp
  | a :: b :: _, hnd, hmem =>
    have hab := List.eq_of_mem_of_eraseDups_length_le_one (by omega) (hmem a (by simp))
      (hmem b (by simp))
    simp [hab] at hnd

/-- Rankings that are all blank give an inactive ballot. -/
theorem readRankings_of_forall_eq_nil (cont : List Cand) (skipped : Bool)
    {rs : List (List Cand)} (h : ∀ r ∈ rs, r = []) : readRankings cont skipped rs = .inactive := by
  induction rs generalizing skipped with
  | nil => rfl
  | cons r rs ih =>
    obtain rfl := h r List.mem_cons_self
    have hrs : ∀ r ∈ rs, r = [] := fun r hr => h r (List.mem_cons_of_mem _ hr)
    have hno : ¬ ∃ r' ∈ rs, r' ≠ [] := fun ⟨r', hr', hne⟩ => hne (hrs r' hr')
    simp only [readRankings, List.find?_nil, true_and, if_neg hno]
    exact ih false hrs

/-- If the rankings above the first overvote are blank once repeated candidates are removed, the
reproduction tabulation counts the ballot for no one. -/
theorem readReproduction_toBallotResult_of_forall_eq_nil (cont : List Cand) (skipped : Bool)
    (earlier : List Cand) {rs : List (List Cand)}
    (h : ∀ r ∈ dropRepeats earlier (rs.takeWhile fun r => decide (r.eraseDups.length < 2)),
      r = []) :
    (readReproduction cont skipped earlier rs).toBallotResult = .inactive := by
  induction rs generalizing skipped earlier with
  | nil => rfl
  | cons r rs ih =>
    by_cases hov : 2 ≤ r.eraseDups.length
    · simp [readReproduction, hov, ReproductionResult.toBallotResult]
    · rw [List.takeWhile_cons_of_pos (by simpa using hov), dropRepeats] at h
      have hr : r.filter (· ∉ earlier) = [] := h _ List.mem_cons_self
      have hrs := fun r hr => h r (List.mem_cons_of_mem _ hr)
      simp only [readReproduction, if_neg hov, hr, List.find?_nil, if_true]
      cases skipped
      · exact ih true _ hrs
      · rfl

/-- Reading the rankings `rs` by the rules of the reproduction tabulation gives the result that
reading `dropRepeats earlier` of the rankings above the first overvote gives under
AS 15.15.350(d), (e)(1) and (e)(2). -/
theorem readRankings_dropRepeats (cont : List Cand) (skipped : Bool) (earlier : List Cand)
    (rs : List (List Cand)) :
    readRankings cont skipped
        (dropRepeats earlier (rs.takeWhile fun r => decide (r.eraseDups.length < 2))) =
      (readReproduction cont skipped earlier rs).toBallotResult := by
  induction rs generalizing skipped earlier with
  | nil => rfl
  | cons r rs ih =>
    by_cases hov : 2 ≤ r.eraseDups.length
    · rw [List.takeWhile_cons_of_neg (by simpa using hov)]
      simp [readReproduction, hov, dropRepeats, readRankings, ReproductionResult.toBallotResult]
    · rw [List.takeWhile_cons_of_pos (by simpa using hov), dropRepeats]
      have hkept :=
        eraseDups_filter_length_lt_two (l := r) (fun c => decide (c ∉ earlier)) (by omega)
      cases hc : (r.filter (· ∉ earlier)).find? (· ∈ cont) with
      | some c =>
        simp only [readRankings, readReproduction, hc, if_neg hov,
          if_neg (show ¬ 2 ≤ (r.filter (· ∉ earlier)).eraseDups.length by omega)]
        rfl
      | none =>
        simp only [readRankings, readReproduction, hc, if_neg hov]
        by_cases hnil : r.filter (· ∉ earlier) = []
        · rw [if_pos hnil]
          by_cases hrest : ∃ r' ∈ dropRepeats (earlier ++ r)
              (rs.takeWhile fun r => decide (r.eraseDups.length < 2)), r' ≠ []
          · rw [if_pos ⟨hnil, hrest⟩]
            cases skipped
            · exact ih true _
            · rfl
          · have hall : ∀ r' ∈ dropRepeats (earlier ++ r)
                (rs.takeWhile fun r => decide (r.eraseDups.length < 2)), r' = [] :=
              fun r' hr' => Decidable.byContradiction fun hne => hrest ⟨r', hr', hne⟩
            rw [if_neg (fun h => hrest h.2), readRankings_of_forall_eq_nil cont false hall]
            cases skipped
            · exact (readReproduction_toBallotResult_of_forall_eq_nil cont true _ hall).symm
            · rfl
        · rw [if_neg (fun h => hnil h.1), if_neg hnil]
          exact ih false _

/-- The reproduction tabulation gives the ballot `b` the result that AS 15.15.350(g)(2) gives
`b.toReproduction`. -/
theorem resultOf_toReproduction (cont : List Cand) (b : Ballot) :
    resultOf cont b.toReproduction = (reproductionResultOf cont b).toBallotResult := by
  rw [← readRankings_eq_resultOf]
  exact readRankings_dropRepeats cont false [] b.ranks

/-- A ballot is tabulated as inactive exactly when it meets an inactivity condition. -/
private theorem resultOf_eq_inactive_iff (cont : List Cand) (b : Ballot) :
    resultOf cont b = .inactive ↔ MeetsInactivityCondition cont b := by
  unfold resultOf
  by_cases hi : MeetsInactivityCondition cont b
  · simp [hi]
  · rw [if_neg hi]
    cases hc : highestContinuingCand cont b with
    | none => exact absurd (Or.inl ((exhausted_iff_highest_cont_cand_none cont b).mpr hc)) hi
    | some c => simp [hi]

/-- `dropRepeats earlier rs` marks `c` exactly when `rs` marks `c` and `c` is not in `earlier`. -/
private theorem exists_mem_dropRepeats_iff (c : Cand) (earlier : List Cand)
    (rs : List (List Cand)) :
    (∃ r ∈ dropRepeats earlier rs, c ∈ r) ↔ c ∉ earlier ∧ ∃ r ∈ rs, c ∈ r := by
  induction rs generalizing earlier with
  | nil => simp [dropRepeats]
  | cons r rs ih =>
    rw [dropRepeats]
    constructor
    · rintro ⟨r', hr', hc⟩
      rcases List.mem_cons.mp hr' with rfl | hr'
      · obtain ⟨hcr, hce⟩ := List.mem_filter.mp hc
        exact ⟨by simpa using hce, r, List.mem_cons_self, hcr⟩
      · obtain ⟨hce, r'', hr'', hcr''⟩ := (ih (earlier ++ r)).mp ⟨r', hr', hc⟩
        exact ⟨fun h => hce (List.mem_append_left _ h), r'', List.mem_cons_of_mem _ hr'', hcr''⟩
    · rintro ⟨hce, r', hr', hcr'⟩
      by_cases hcr : c ∈ r
      · exact ⟨_, List.mem_cons_self, List.mem_filter.mpr ⟨hcr, by simpa using hce⟩⟩
      · rcases List.mem_cons.mp hr' with rfl | hr'
        · exact absurd hcr' hcr
        · obtain ⟨r'', hr'', hc''⟩ := (ih (earlier ++ r)).mpr
            ⟨fun h => (List.mem_append.mp h).elim hce hcr, r', hr', hcr'⟩
          exact ⟨r'', List.mem_cons_of_mem _ hr'', hc''⟩

/-- If no ranking of `rs` has two or more candidates, no ranking of `dropRepeats earlier rs`
does. -/
private theorem eraseDups_length_lt_two_of_mem_dropRepeats {earlier : List Cand}
    {rs : List (List Cand)} (h : ∀ r ∈ rs, r.eraseDups.length < 2) :
    ∀ r' ∈ dropRepeats earlier rs, r'.eraseDups.length < 2 := by
  induction rs generalizing earlier with
  | nil => simp [dropRepeats]
  | cons r rs ih =>
    intro r' hr'
    rw [dropRepeats, List.mem_cons] at hr'
    rcases hr' with rfl | hr'
    · exact eraseDups_filter_length_lt_two _ (h r List.mem_cons_self)
    · exact ih (fun r hr => h r (List.mem_cons_of_mem _ hr)) r' hr'

/-- `b.toReproduction` has no overvote. -/
private theorem not_isOvervoteAt_toReproduction (b : Ballot) (k : Nat) :
    ¬ b.toReproduction.IsOvervoteAt k := by
  have hall : ∀ r' ∈ dropRepeats [] (b.ranks.takeWhile fun r => decide (r.eraseDups.length < 2)),
      r'.eraseDups.length < 2 :=
    eraseDups_length_lt_two_of_mem_dropRepeats fun r hr => by
      simpa using List.all_eq_true.mp
        (List.all_takeWhile (p := fun r => decide (r.eraseDups.length < 2)) (l := b.ranks)) r hr
  rw [Ballot.isOvervoteAt_iff, Ballot.candsAt, List.getD_eq_getElem?_getD]
  cases hk : b.toReproduction.ranks[k]? with
  | none => simp
  | some r' =>
    have := hall r' (List.mem_of_getElem? hk)
    simp only [Option.getD_some]
    omega

/-- The rankings `rs` mark a continuing candidate above their first overvote exactly when their
highest continuing ranking is above all of their overvotes. -/
private theorem exists_mem_takeWhile_iff (cont : List Cand) (i : Nat) (rs : List (List Cand)) :
    (∃ r ∈ rs.takeWhile (fun r => decide (r.eraseDups.length < 2)), ∃ c ∈ r, c ∈ cont) ↔
      ∃ k, IsHighestContinuingRank cont ⟨i, rs⟩ k ∧
        ∀ o, Ballot.IsOvervoteAt ⟨i, rs⟩ o → k < o := by
  induction rs with
  | nil => simp [IsHighestContinuingRank, Ballot.candsAt]
  | cons r rs ih =>
    have hshift : ∀ k, IsHighestContinuingRank cont ⟨i, r :: rs⟩ (k + 1) ↔
        (∀ c ∈ r, c ∉ cont) ∧ IsHighestContinuingRank cont ⟨i, rs⟩ k := by
      intro k
      simp only [IsHighestContinuingRank, Ballot.candsAt, List.getD_cons_succ]
      constructor
      · rintro ⟨hex, hbefore⟩
        exact ⟨fun c hc => hbefore 0 (Nat.succ_pos k) c (by simpa using hc),
          hex, fun j hj => hbefore (j + 1) (Nat.succ_lt_succ hj)⟩
      · rintro ⟨hr, hex, hbefore⟩
        refine ⟨hex, fun j hj => ?_⟩
        cases j with
        | zero => simpa using hr
        | succ j => exact hbefore j (Nat.lt_of_succ_lt_succ hj)
    have hov : ∀ o, Ballot.IsOvervoteAt ⟨i, r :: rs⟩ (o + 1) ↔ Ballot.IsOvervoteAt ⟨i, rs⟩ o := by
      intro o
      simp [Ballot.IsOvervoteAt, Ballot.candsAt]
    by_cases hr : r.eraseDups.length < 2
    · rw [List.takeWhile_cons_of_pos (by simpa using hr)]
      simp only [List.mem_cons, or_and_right, exists_or, exists_eq_left]
      have hov0 : ¬ Ballot.IsOvervoteAt ⟨i, r :: rs⟩ 0 := by
        rw [Ballot.isOvervoteAt_iff]
        simp only [Ballot.candsAt, List.getD_cons_zero]
        omega
      by_cases hc : ∃ c ∈ r, c ∈ cont
      · refine iff_of_true (Or.inl hc) ⟨0, ⟨by simpa [Ballot.candsAt] using hc,
          fun j hj => absurd hj (Nat.not_lt_zero j)⟩, fun o ho => ?_⟩
        cases o with
        | zero => exact absurd ho hov0
        | succ o => exact Nat.succ_pos o
      · rw [or_iff_right hc, ih]
        constructor
        · rintro ⟨k, hk, hlt⟩
          refine ⟨k + 1, (hshift k).mpr ⟨fun c hcr hcc => hc ⟨c, hcr, hcc⟩, hk⟩, fun o ho => ?_⟩
          cases o with
          | zero => exact absurd ho hov0
          | succ o => exact Nat.succ_lt_succ (hlt o ((hov o).mp ho))
        · rintro ⟨k, hk, hlt⟩
          cases k with
          | zero => exact absurd (by simpa [Ballot.candsAt] using hk.1) hc
          | succ k =>
            obtain ⟨-, hk'⟩ := (hshift k).mp hk
            exact ⟨k, hk', fun o ho => Nat.lt_of_succ_lt_succ (hlt (o + 1) ((hov o).mpr ho))⟩
    · rw [List.takeWhile_cons_of_neg (by simpa using hr)]
      have hov0 : Ballot.IsOvervoteAt ⟨i, r :: rs⟩ 0 := by
        rw [Ballot.isOvervoteAt_iff]
        simp only [Ballot.candsAt, List.getD_cons_zero]
        omega
      simp only [List.not_mem_nil, false_and, exists_false, false_iff, not_exists, not_and]
      intro k _ hlt
      exact Nat.not_lt_zero k (hlt 0 hov0)

/-- The reproduction tabulation counts the ballot `b` as inactive exactly when `b` ranks no
continuing candidate, has an overvote at or above its highest continuing ranking, or has two
sequential skipped rankings before its highest continuing ranking once the rankings from its first
overvote down and its repeated candidates are removed. AS 15.15.350(e)(1) and (g)(2) make an
overvote count only at the highest continuing ranking (`IsOvervoteAtHighestCont`). -/
theorem resultOf_toReproduction_eq_inactive_iff (cont : List Cand) (b : Ballot) :
    resultOf cont b.toReproduction = .inactive ↔
      Exhausted cont b ∨
        (∃ o k, b.IsOvervoteAt o ∧ IsHighestContinuingRank cont b k ∧ o ≤ k) ∨
        TwoSkips cont b.toReproduction := by
  have hex : Exhausted cont b.toReproduction ↔
      Exhausted cont b ∨ ∃ o k, b.IsOvervoteAt o ∧ IsHighestContinuingRank cont b k ∧ o ≤ k := by
    obtain ⟨i, rs⟩ := b
    have hmem : (∃ r ∈ (Ballot.toReproduction ⟨i, rs⟩).ranks, ∃ c ∈ r, c ∈ cont) ↔
        ∃ r ∈ rs.takeWhile (fun r => decide (r.eraseDups.length < 2)), ∃ c ∈ r, c ∈ cont := by
      constructor
      · rintro ⟨r', hr', c, hc, hcont⟩
        obtain ⟨-, r, hr, hcr⟩ := (exists_mem_dropRepeats_iff c [] _).mp ⟨r', hr', hc⟩
        exact ⟨r, hr, c, hcr, hcont⟩
      · rintro ⟨r, hr, c, hcr, hcont⟩
        obtain ⟨r', hr', hc⟩ :=
          (exists_mem_dropRepeats_iff c [] _).mpr ⟨List.not_mem_nil, r, hr, hcr⟩
        exact ⟨r', hr', c, hc, hcont⟩
    show (¬ ∃ r ∈ (Ballot.toReproduction ⟨i, rs⟩).ranks, ∃ c ∈ r, c ∈ cont) ↔ _
    rw [hmem, exists_mem_takeWhile_iff, exhausted_iff_not_exists_isHighestContinuingRank]
    constructor
    · intro h
      cases hkc : highestContinuingRank cont ⟨i, rs⟩ with
      | none =>
        refine Or.inl fun ⟨k, hk⟩ => ?_
        rw [(highestContinuingRank_eq_some_iff _ _ k).mpr hk] at hkc
        cases hkc
      | some k =>
        have hk := (highestContinuingRank_eq_some_iff _ _ k).mp hkc
        by_cases ho : ∃ o, o ≤ k ∧ Ballot.IsOvervoteAt ⟨i, rs⟩ o
        · obtain ⟨o, hle, ho⟩ := ho
          exact Or.inr ⟨o, k, ho, hk, hle⟩
        · exact absurd ⟨k, hk, fun o ho' => Nat.lt_of_not_le fun hle => ho ⟨o, hle, ho'⟩⟩ h
    · rintro (hno | ⟨o, k, ho, hk, hle⟩) ⟨k', hk', hlt⟩
      · exact hno ⟨k', hk'⟩
      · obtain rfl := isHighestContinuingRank_unique hk hk'
        exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hlt o ho) hle)
  have hov : ¬ IsOvervoteAtHighestCont cont b.toReproduction :=
    fun ⟨k, _, hk⟩ => not_isOvervoteAt_toReproduction b k hk
  rw [resultOf_eq_inactive_iff, MeetsInactivityCondition, hex]
  simp only [hov, false_or, or_assoc]

namespace Counterexample

def A : Cand := .regular 0
def B : Cand := .regular 1
def C : Cand := .regular 2
def D : Cand := .regular 3
def W : Cand := .writeIn 0

/-- 1: A, 2: W and B, 3: C, 4: D, 5: blank. -/
def exampleBallot : Ballot := ⟨0, [[A], [W, B], [C], [D], []]⟩

/-- Two copies of `exampleBallot`, with one ballot ranking only B, three only C and four only D.
The write-ins do not qualify under AS 15.15.365(a), so W is not a continuing candidate
(`initialCands_election`). No candidate has a majority, and B and then A are
defeated. When A is defeated, W and B are not continuing, so under AS 15.15.350(e)(1) the overvote
at rank 2 is not encountered and the copies of `exampleBallot` count for C, who is elected 5 to 4.
In the reproduction tabulation they reach the overvote and are inactive, and D is elected 4 to 3. -/
def election : Election where
  ballots := List.replicate 2 exampleBallot ++ [⟨1, [[B]]⟩] ++ List.replicate 3 ⟨2, [[C]]⟩ ++
    List.replicate 4 ⟨3, [[D]]⟩
  cands := [A, B, C, D, W]
  cands_unique := by decide

theorem initialCands_election : initialCands election = [A, B, C, D] := by
  decide

unseal tabulateRounds in
theorem tabulate_election : (tabulate election).winners = [C] := by
  decide +kernel

unseal tabulateRounds in
theorem reproductionTabulate_election : (reproductionTabulate election).winners = [D] := by
  decide +kernel

end Counterexample

/-- The reproduction tabulation can elect a candidate that AS 15.15.350(d) does not allow to be
elected under any order of defeats. -/
theorem exists_reproductionTabulate_not_elected :
    ∃ e c, c ∈ (reproductionTabulate e).winners ∧ ∀ defeated, ¬ Elected e defeated c := by
  refine ⟨Counterexample.election, Counterexample.D,
    by simp [Counterexample.reproductionTabulate_election], fun defeated h => ?_⟩
  obtain ⟨path, hpath, -⟩ := (tabulate_correct _ _ _).mp h
  have hmem := (mem_winners_iff_hasPath _ _).mpr ⟨path, hpath⟩
  rw [Counterexample.tabulate_election] at hmem
  exact absurd hmem (by decide)

/-- The reproduction tabulation does not give the outcomes `Spec.lean` allows: `tabulate_correct`
fails for `reproductionTabulate`. -/
theorem not_reproductionTabulate_correct :
    ¬ ∀ e defeated c, (Elected e defeated c ↔
      ∃ path, (reproductionTabulate e).HasPath path c ∧ path.dropLast = defeated) := by
  intro h
  obtain ⟨e, c, hc, hne⟩ := exists_reproductionTabulate_not_elected
  obtain ⟨path, hpath⟩ := (mem_winners_iff_hasPath _ c).mp hc
  exact hne _ ((h e path.dropLast c).mpr ⟨path, hpath, rfl⟩)

end Alaska
