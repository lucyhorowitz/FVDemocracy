import FVDemocracy.Alaska.Reproduction.Tabulate

/-!
# Removing duplicate rankings before the tabulation

6 AAC 25.072: "a duplicate ranking occurs when a voter marks more than one ranking for the same
candidate. The election board shall count a duplicate ranking as the highest ranking marked for
the candidate and disregard the remaining rankings for that candidate."

`Ballot.dropDuplicates` reads "disregard" as removing the candidate from every ranking below its
highest one, and `Election.dropDuplicates` applies it to every ballot before the tabulation. This
differs from the reading of `resultOf`, which keeps the marks: a ranking that marks only such
candidates becomes blank, so it can be a skipped ranking, and a candidate removed from a ranking
no longer counts toward an overvote there.

`truncateTabulate` cuts each ballot at its first overvote (`Ballot.truncateAtOvervote`) and keeps
every mark. The reproduction cuts each ballot the same way and then removes duplicates
(`Ballot.toReproduction_eq_dropDuplicates_truncateAtOvervote`). `truncateTabulate e.dropDuplicates`
removes duplicates first and then cuts each ballot.

* `resultOf_dropDuplicates` and `tabulate_dropDuplicates`: on ballots without a duplicate
  ranking, removing duplicates changes nothing.
* `reproductionResultOf_eq_resultOf_dropDuplicates` and
  `reproductionTabulate_eq_tabulate_dropDuplicates`: on ballots without an overvote, the
  reproduction is the tabulation of the ballots with duplicates removed.
* `reproductionTabulate_eq_tabulate`: on ballots with neither, the reproduction and `tabulate`
  agree.
* `truncateTabulate_eq_tabulate`: on ballots without an overvote, `truncateTabulate` and
  `tabulate` agree. `reproductionTabulate_eq_truncateTabulate`: on ballots without a duplicate
  ranking, the reproduction and `truncateTabulate` agree.
* `isVoteFor_of_isVoteFor_toReproduction` and
  `isVoteFor_dropDuplicates_of_isVoteFor_toReproduction`: in any round, a ballot the reproduction
  counts for `c` counts for `c` under `resultOf`, with or without duplicates removed.
  `mem_roundAfter_of_mem_roundAfter_toReproduction` and
  `mem_roundAfter_dropDuplicates_of_mem_roundAfter_toReproduction`: so after the same defeats, a
  ballot the reproduction still tabulates is still tabulated by the other two readings.

For any fixed continuing-candidate list, Hybrid also counts only ballots counted for the same
candidate by Truncate + Retain and Truncate + Remove. The corresponding `mem_roundAfter`
inclusions assume equal initial continuing-candidate lists and the same defeat sequence; they
do not order final totals for tabulations choosing different defeat sequences.

`Statute/Examples/Duplicates.lean` gives strict ballot-class inclusions for Hybrid in both
Truncate readings and witnesses that Truncate + Retain and Truncate + Remove are incomparable.
-/

namespace Alaska

namespace Ballot

/-- The ballot `b` with each candidate removed from every ranking below the highest one marking
it. -/
def dropDuplicates (b : Ballot) : Ballot :=
  ⟨b.ballotIndex, dropRepeats [] b.ranks⟩

end Ballot

/-- The election `e` with duplicate rankings removed from every ballot. -/
def Election.dropDuplicates (e : Election) : Election :=
  { e with ballots := e.ballots.map Ballot.dropDuplicates }

/-- The ballot `b` with its rankings from the first overvote down removed. -/
def Ballot.truncateAtOvervote (b : Ballot) : Ballot :=
  ⟨b.ballotIndex, b.ranks.takeWhile fun r => decide (r.eraseDups.length < 2)⟩

/-- `tabulate` on the ballots of `e` with their rankings from the first overvote down removed. It
reads overvotes as the reproduction does (Truncate) and duplicate rankings as `resultOf` does. -/
def truncateTabulate (e : Election) : RCVTree :=
  tabulate { e with ballots := e.ballots.map Ballot.truncateAtOvervote }

/-- The reproduction's ballot is the ballot cut at its first overvote, with duplicates then
removed. -/
theorem Ballot.toReproduction_eq_dropDuplicates_truncateAtOvervote (b : Ballot) :
    b.toReproduction = b.truncateAtOvervote.dropDuplicates :=
  rfl

/-- `dropRepeats earlier` leaves the rankings `rs` unchanged when no candidate of `earlier` and
no candidate of an earlier ranking of `rs` appears in a ranking of `rs`. -/
theorem dropRepeats_eq_self {earlier : List Cand} {rs : List (List Cand)}
    (hearlier : ∀ r ∈ rs, ∀ c ∈ r, c ∉ earlier)
    (hrs : rs.Pairwise fun r r' => ∀ c ∈ r, c ∉ r') :
    dropRepeats earlier rs = rs := by
  induction rs generalizing earlier with
  | nil => rfl
  | cons r rs ih =>
    rw [List.pairwise_cons] at hrs
    rw [dropRepeats, List.filter_eq_self.mpr fun c hc => by
      simpa using hearlier r List.mem_cons_self c hc]
    congr 1
    refine ih (fun r' hr' c hc => ?_) hrs.2
    rw [List.mem_append, not_or]
    exact ⟨hearlier r' (List.mem_cons_of_mem r hr') c hc, fun hcr => hrs.1 r' hr' c hcr hc⟩

/-- A ballot without a duplicate ranking is unchanged by removing duplicates. -/
theorem Ballot.dropDuplicates_eq_self {b : Ballot} (h : ¬ b.HasDuplicateRanking) :
    b.dropDuplicates = b := by
  unfold HasDuplicateRanking at h
  rw [dropDuplicates, dropRepeats_eq_self (fun _ _ _ _ => by simp) (Decidable.not_not.mp h)]

theorem resultOf_dropDuplicates (cont : List Cand) {b : Ballot} (h : ¬ b.HasDuplicateRanking) :
    resultOf cont b.dropDuplicates = resultOf cont b := by
  rw [Ballot.dropDuplicates_eq_self h]

/-- An election in which no ballot has a duplicate ranking is unchanged by removing
duplicates. -/
theorem Election.dropDuplicates_eq_self {e : Election}
    (h : ∀ b ∈ e.ballots, ¬ b.HasDuplicateRanking) : e.dropDuplicates = e := by
  obtain ⟨ballots, cands, hcands⟩ := e
  simp only [dropDuplicates, Election.mk.injEq, and_true]
  exact (List.map_congr_left fun b hb => Ballot.dropDuplicates_eq_self (h b hb)).trans
    (List.map_id _)

theorem tabulate_dropDuplicates {e : Election} (h : ∀ b ∈ e.ballots, ¬ b.HasDuplicateRanking) :
    tabulate e.dropDuplicates = tabulate e := by
  rw [Election.dropDuplicates_eq_self h]

/-- On a ballot without an overvote, the reproduction's ballot is the ballot with duplicates
removed. -/
theorem Ballot.toReproduction_eq_dropDuplicates {b : Ballot} (h : ¬ b.HasOvervote) :
    b.toReproduction = b.dropDuplicates := by
  have hall : ∀ r ∈ b.ranks, r.eraseDups.length < 2 := by
    intro r hr
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr
    have := fun hov => h ⟨k, hk, hov⟩
    simp only [isOvervoteAt_iff, candsAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
      Option.getD_some] at this
    exact Nat.lt_of_not_le this
  have htake : ∀ rs : List (List Cand), (∀ r ∈ rs, r.eraseDups.length < 2) →
      rs.takeWhile (fun r => decide (r.eraseDups.length < 2)) = rs := by
    intro rs hrs
    induction rs with
    | nil => rfl
    | cons r rs ih =>
      rw [List.takeWhile_cons_of_pos (by simpa using hrs r List.mem_cons_self),
        ih fun r' hr' => hrs r' (List.mem_cons_of_mem r hr')]
  simp only [toReproduction, dropDuplicates, htake b.ranks hall]

/-- On a ballot without an overvote, the reproduction reads the ballot as `resultOf` reads it
with duplicates removed. -/
theorem reproductionResultOf_eq_resultOf_dropDuplicates (cont : List Cand) {b : Ballot}
    (h : ¬ b.HasOvervote) :
    (reproductionResultOf cont b).toBallotResult = resultOf cont b.dropDuplicates := by
  rw [← resultOf_toReproduction, Ballot.toReproduction_eq_dropDuplicates h]

/-- On an election in which no ballot has an overvote, the reproduction is the tabulation of the
election with duplicates removed. -/
theorem reproductionTabulate_eq_tabulate_dropDuplicates {e : Election}
    (h : ∀ b ∈ e.ballots, ¬ b.HasOvervote) :
    reproductionTabulate e = tabulate e.dropDuplicates := by
  unfold reproductionTabulate Election.dropDuplicates
  congr 2
  exact List.map_congr_left fun b hb => Ballot.toReproduction_eq_dropDuplicates (h b hb)

/-- On an election in which no ballot has an overvote or a duplicate ranking, the reproduction
and `tabulate` agree. -/
theorem reproductionTabulate_eq_tabulate {e : Election}
    (hov : ∀ b ∈ e.ballots, ¬ b.HasOvervote) (hdup : ∀ b ∈ e.ballots, ¬ b.HasDuplicateRanking) :
    reproductionTabulate e = tabulate e := by
  rw [reproductionTabulate_eq_tabulate_dropDuplicates hov, tabulate_dropDuplicates hdup]

/-- A ballot without an overvote is unchanged by cutting it at its first overvote. -/
theorem Ballot.truncateAtOvervote_eq_self {b : Ballot} (h : ¬ b.HasOvervote) :
    b.truncateAtOvervote = b := by
  have hall : ∀ r ∈ b.ranks, decide (r.eraseDups.length < 2) = true := by
    intro r hr
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr
    have := fun hov => h ⟨k, hk, hov⟩
    simp only [isOvervoteAt_iff, candsAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
      Option.getD_some] at this
    simpa using Nat.lt_of_not_le this
  obtain ⟨idx, ranks⟩ := b
  simp only [truncateAtOvervote, Ballot.mk.injEq, true_and]
  clear h
  induction ranks with
  | nil => rfl
  | cons r rs ih =>
    rw [List.takeWhile_cons_of_pos (p := fun x : List Cand => decide (x.eraseDups.length < 2))
      (hall r List.mem_cons_self), ih fun r' hr' => hall r' (List.mem_cons_of_mem r hr')]

/-- On an election in which no ballot has an overvote, `truncateTabulate` and `tabulate`
agree. -/
theorem truncateTabulate_eq_tabulate {e : Election} (h : ∀ b ∈ e.ballots, ¬ b.HasOvervote) :
    truncateTabulate e = tabulate e := by
  unfold truncateTabulate
  rw [List.map_congr_left fun b hb => Ballot.truncateAtOvervote_eq_self (h b hb), List.map_id']

/-- A ballot without a duplicate ranking has none after it is cut at its first overvote. -/
theorem Ballot.not_hasDuplicateRanking_truncateAtOvervote {b : Ballot}
    (h : ¬ b.HasDuplicateRanking) : ¬ b.truncateAtOvervote.HasDuplicateRanking := by
  unfold HasDuplicateRanking at h ⊢
  exact fun hdup => hdup ((Decidable.not_not.mp h).sublist (List.takeWhile_sublist _))

/-- On an election in which no ballot has a duplicate ranking, the reproduction and
`truncateTabulate` agree. -/
theorem reproductionTabulate_eq_truncateTabulate {e : Election}
    (h : ∀ b ∈ e.ballots, ¬ b.HasDuplicateRanking) :
    reproductionTabulate e = truncateTabulate e := by
  have := tabulate_dropDuplicates
    (e := { e with ballots := e.ballots.map Ballot.truncateAtOvervote }) (by simpa using fun b hb => Ballot.not_hasDuplicateRanking_truncateAtOvervote (h b hb))
  simpa [Election.dropDuplicates, reproductionTabulate, truncateTabulate, Function.comp_def,
    ← Ballot.toReproduction_eq_dropDuplicates_truncateAtOvervote] using this

section Inclusions

/-- `dropRepeats earlier` of the rankings above the first overvote is a prefix of `dropRepeats
earlier` of all the rankings. -/
theorem dropRepeats_takeWhile_prefix (earlier : List Cand) (rs : List (List Cand)) :
    dropRepeats earlier (rs.takeWhile fun r => decide (r.eraseDups.length < 2)) <+:
      dropRepeats earlier rs := by
  induction rs generalizing earlier with
  | nil => exact List.prefix_refl _
  | cons r rs ih =>
    by_cases hr : r.eraseDups.length < 2
    · rw [List.takeWhile_cons_of_pos (by simpa using hr), dropRepeats, dropRepeats]
      obtain ⟨t, ht⟩ := ih (earlier ++ r)
      exact ⟨t, by rw [List.cons_append, ht]⟩
    · rw [List.takeWhile_cons_of_neg (by simpa using hr), dropRepeats]
      exact List.nil_prefix

/-- Rankings that count for `c` still count for `c` with rankings `rs'` added below them. -/
theorem readRankings_append_of_eq_voteFor {cont : List Cand} {skipped : Bool}
    {rs : List (List Cand)} {c : Cand} (rs' : List (List Cand))
    (h : readRankings cont skipped rs = .voteFor c) :
    readRankings cont skipped (rs ++ rs') = .voteFor c := by
  induction rs generalizing skipped with
  | nil => simp [readRankings] at h
  | cons r rs ih =>
    simp only [List.cons_append, readRankings] at h ⊢
    cases hf : r.find? (· ∈ cont) with
    | some d => simpa [hf] using h
    | none =>
      simp only [hf] at h ⊢
      by_cases hskip : r = [] ∧ ∃ r' ∈ rs, r' ≠ []
      · obtain ⟨hr, r', hr', hne⟩ := hskip
        rw [if_pos ⟨hr, r', hr', hne⟩] at h
        rw [if_pos ⟨hr, r', List.mem_append_left _ hr', hne⟩]
        cases skipped
        · exact ih h
        · exact h
      · rw [if_neg hskip] at h
        by_cases hr : r = []
        · have hall : ∀ r' ∈ rs, r' = [] := fun r' hr' =>
            Decidable.byContradiction fun hne => hskip ⟨hr, r', hr', hne⟩
          rw [readRankings_of_forall_eq_nil cont false hall] at h
          cases h
        · rw [if_neg fun h' => hr h'.1]
          exact ih h

/-- If the reproduction tabulation counts the rankings `rs` for `c`, so does reading them under
AS 15.15.350(d), (e)(1) and (e)(2), when no candidate of `earlier` is continuing and the ranking
read just before `rs` was a skipped ranking only if it was blank for the reproduction tabulation. -/
theorem readRankings_eq_voteFor_of_readReproduction {cont : List Cand} {c : Cand}
    {skipped skipped' : Bool} {earlier : List Cand} {rs : List (List Cand)}
    (hearlier : ∀ x ∈ earlier, x ∉ cont) (hskipped : skipped = true → skipped' = true)
    (h : readReproduction cont skipped' earlier rs = .voteFor c) :
    readRankings cont skipped rs = .voteFor c := by
  induction rs generalizing skipped skipped' earlier with
  | nil => simp [readReproduction] at h
  | cons r rs ih =>
    by_cases hov : 2 ≤ r.eraseDups.length
    · simp [readReproduction, hov] at h
    have hfind : r.find? (· ∈ cont) = (r.filter (· ∉ earlier)).find? (· ∈ cont) := by
      rw [List.find?_filter]
      congr 1
      funext x
      by_cases hx : x ∈ cont
      · simp [hx, show x ∉ earlier from fun hx' => hearlier x hx' hx]
      · simp [hx]
    simp only [readReproduction, if_neg hov] at h
    simp only [readRankings]
    rw [hfind]
    cases hf : (r.filter (· ∉ earlier)).find? (· ∈ cont) with
    | some d =>
      simp only [hf, ReproductionResult.voteFor.injEq] at h
      simp [hov, h]
    | none =>
      simp only [hf] at h
      have hr : ∀ x ∈ r, x ∉ cont := by
        have := hfind.trans hf
        simpa using this
      have hearlier' : ∀ x ∈ earlier ++ r, x ∉ cont := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hearlier x hx
        · exact hr x hx
      by_cases hskip : r = [] ∧ ∃ r' ∈ rs, r' ≠ []
      · rw [if_pos hskip]
        have hnil : r.filter (· ∉ earlier) = [] := by simp [hskip.1]
        rw [if_pos hnil] at h
        cases skipped'
        · have hs : skipped = false := by
            cases skipped
            · rfl
            · exact absurd (hskipped rfl) (by simp)
          subst hs
          exact ih hearlier' (fun _ => rfl) h
        · simp at h
      · rw [if_neg hskip]
        by_cases hnil : r.filter (· ∉ earlier) = []
        · rw [if_pos hnil] at h
          cases skipped'
          · exact ih hearlier' (fun _ => rfl) h
          · simp at h
        · rw [if_neg hnil] at h
          exact ih hearlier' (by simp) h

/-- If the reproduction tabulation counts the ballot `b` for `c`, so does AS 15.15.350(g)(2). -/
theorem isVoteFor_of_isVoteFor_toReproduction {cont : List Cand} {b : Ballot} {c : Cand}
    (h : IsVoteFor cont b.toReproduction c) : IsVoteFor cont b c := by
  have h' := (readRankings_eq_iff cont b.toReproduction (.voteFor c)).mpr h
  simp only [Ballot.toReproduction, readRankings_dropRepeats] at h'
  have hr : readReproduction cont false [] b.ranks = .voteFor c := by
    cases hr : readReproduction cont false [] b.ranks <;>
      simp_all [ReproductionResult.toBallotResult]
  exact (readRankings_eq_iff cont b (.voteFor c)).mp
    (readRankings_eq_voteFor_of_readReproduction (by simp) (fun h => h) hr)

/-- If the reproduction tabulation counts the ballot `b` for `c`, so does AS 15.15.350(g)(2) with
duplicate rankings removed. -/
theorem isVoteFor_dropDuplicates_of_isVoteFor_toReproduction {cont : List Cand} {b : Ballot}
    {c : Cand} (h : IsVoteFor cont b.toReproduction c) : IsVoteFor cont b.dropDuplicates c := by
  have h' := (readRankings_eq_iff cont b.toReproduction (.voteFor c)).mpr h
  obtain ⟨rs', hrs'⟩ := dropRepeats_takeWhile_prefix [] b.ranks
  refine (readRankings_eq_iff cont b.dropDuplicates (.voteFor c)).mp ?_
  simp only [Ballot.dropDuplicates, ← hrs']
  exact readRankings_append_of_eq_voteFor rs' h'

/-- Cutting at the first overvote before applying the reproduction changes nothing. -/
theorem Ballot.toReproduction_truncateAtOvervote (b : Ballot) :
    b.truncateAtOvervote.toReproduction = b.toReproduction := by
  have htake (rs : List (List Cand)) :
      (rs.takeWhile fun r => decide (r.eraseDups.length < 2)).takeWhile
        (fun r => decide (r.eraseDups.length < 2)) =
      rs.takeWhile (fun r => decide (r.eraseDups.length < 2)) := by
    induction rs with
    | nil => rfl
    | cons r rs ih =>
      by_cases hr : r.eraseDups.length < 2 <;> simp [hr, ih]
  simp only [Ballot.truncateAtOvervote, Ballot.toReproduction, htake]

/-- Hybrid counts only ballots counted for the same candidate by Truncate + Retain,
for a fixed list of continuing candidates. -/
theorem isVoteFor_truncateAtOvervote_of_isVoteFor_toReproduction {cont : List Cand}
    {b : Ballot} {c : Cand} (h : IsVoteFor cont b.toReproduction c) :
    IsVoteFor cont b.truncateAtOvervote c := by
  apply isVoteFor_of_isVoteFor_toReproduction
  rwa [Ballot.toReproduction_truncateAtOvervote]

/-- Truncate + Retain counts only ballots counted for the same candidate by AS 15.15.350(g)(2),
for a fixed list of continuing candidates. -/
theorem isVoteFor_of_isVoteFor_truncateAtOvervote {cont : List Cand} {b : Ballot} {c : Cand}
    (h : IsVoteFor cont b.truncateAtOvervote c) : IsVoteFor cont b c := by
  have h' := (readRankings_eq_iff cont b.truncateAtOvervote (.voteFor c)).mpr h
  refine (readRankings_eq_iff cont b (.voteFor c)).mp ?_
  have := readRankings_append_of_eq_voteFor
    (b.ranks.dropWhile fun r => decide (r.eraseDups.length < 2)) h'
  rwa [Ballot.truncateAtOvervote, List.takeWhile_append_dropWhile] at this

/-- Removing duplicates after cutting at the first overvote yields a prefix of the rankings
obtained by removing duplicates first and then cutting at the first remaining overvote. -/
theorem dropRepeats_takeWhile_prefix_takeWhile_dropRepeats (earlier : List Cand)
    (rs : List (List Cand)) :
    dropRepeats earlier (rs.takeWhile fun r => decide (r.eraseDups.length < 2)) <+:
      (dropRepeats earlier rs).takeWhile (fun r => decide (r.eraseDups.length < 2)) := by
  induction rs generalizing earlier with
  | nil => exact List.prefix_refl _
  | cons r rs ih =>
    by_cases hr : r.eraseDups.length < 2
    · rw [List.takeWhile_cons_of_pos (by simpa using hr), dropRepeats, dropRepeats,
        List.takeWhile_cons_of_pos (by
          simpa using eraseDups_filter_length_lt_two (fun c => decide (c ∉ earlier)) hr)]
      obtain ⟨rs', hrs'⟩ := ih (earlier ++ r)
      exact ⟨rs', by rw [List.cons_append, hrs']⟩
    · rw [List.takeWhile_cons_of_neg (by simpa using hr), dropRepeats]
      exact List.nil_prefix

/-- Hybrid's rankings are a prefix of the Truncate + Remove rankings. -/
theorem Ballot.toReproduction_prefix_truncateAtOvervote_dropDuplicates (b : Ballot) :
    b.toReproduction.ranks <+: b.dropDuplicates.truncateAtOvervote.ranks :=
  dropRepeats_takeWhile_prefix_takeWhile_dropRepeats [] b.ranks

/-- Hybrid counts only ballots counted for the same candidate by Truncate + Remove,
for a fixed list of continuing candidates. -/
theorem isVoteFor_truncateAtOvervote_dropDuplicates_of_isVoteFor_toReproduction
    {cont : List Cand} {b : Ballot} {c : Cand} (h : IsVoteFor cont b.toReproduction c) :
    IsVoteFor cont b.dropDuplicates.truncateAtOvervote c := by
  obtain ⟨rs', hrs'⟩ := b.toReproduction_prefix_truncateAtOvervote_dropDuplicates
  apply (readRankings_eq_iff cont b.dropDuplicates.truncateAtOvervote (.voteFor c)).mp
  rw [← hrs']
  exact readRankings_append_of_eq_voteFor rs'
    ((readRankings_eq_iff cont b.toReproduction (.voteFor c)).mpr h)

theorem exists_isVoteFor_of_not_meetsInactivityCondition {cont : List Cand} {b : Ballot}
    (h : ¬ MeetsInactivityCondition cont b) : ∃ c, IsVoteFor cont b c := by
  have hres := resultOf_eq_result cont b
  cases ho : resultOf cont b with
  | inactive => rw [ho] at hres; exact absurd hres h
  | voteFor c => rw [ho] at hres; exact ⟨c, hres⟩

/-- Two elections with the same initial continuing candidates have the same continuing candidates
after defeating the candidates in `defeated`. -/
theorem roundAfter_continuing_eq {e e' : Election} (h : initialCands e = initialCands e')
    (defeated : List Cand) :
    (roundAfter e defeated).continuing = (roundAfter e' defeated).continuing := by
  unfold roundAfter
  suffices ∀ r r' : Round, r.continuing = r'.continuing →
      (defeated.foldl Round.next r).continuing = (defeated.foldl Round.next r').continuing from
    this _ _ h
  induction defeated with
  | nil => exact fun _ _ h => h
  | cons d ds ih => exact fun r r' h => ih _ _ (by simp [Round.next, h])

/-- Defeating the candidates in `defeated`, in order, every ballot the reproduction tabulation still
tabulates is still tabulated under AS 15.15.350, when both start from the same continuing
candidates. -/
theorem mem_roundAfter_of_mem_roundAfter_toReproduction {e : Election} {defeated : List Cand}
    {b : Ballot}
    (hcands : initialCands { e with ballots := e.ballots.map Ballot.toReproduction } =
      initialCands e)
    (hb : b ∈ e.ballots)
    (h : b.toReproduction ∈
      (roundAfter { e with ballots := e.ballots.map Ballot.toReproduction } defeated).ballots) :
    b ∈ (roundAfter e defeated).ballots := by
  rw [mem_roundAfter_ballots_iff] at h ⊢
  refine ⟨hb, fun ds hds => ?_⟩
  obtain ⟨c, hc⟩ := exists_isVoteFor_of_not_meetsInactivityCondition (h.2 ds hds)
  rw [← roundAfter_continuing_eq hcands]
  exact (isVoteFor_of_isVoteFor_toReproduction hc).1

/-- Defeating the candidates in `defeated`, in order, every ballot the reproduction tabulation still
tabulates is still tabulated under AS 15.15.350 with duplicate rankings removed, when both start
from the same continuing candidates. -/
theorem mem_roundAfter_dropDuplicates_of_mem_roundAfter_toReproduction {e : Election}
    {defeated : List Cand} {b : Ballot}
    (hcands : initialCands { e with ballots := e.ballots.map Ballot.toReproduction } =
      initialCands e.dropDuplicates)
    (hb : b ∈ e.ballots)
    (h : b.toReproduction ∈
      (roundAfter { e with ballots := e.ballots.map Ballot.toReproduction } defeated).ballots) :
    b.dropDuplicates ∈ (roundAfter e.dropDuplicates defeated).ballots := by
  rw [mem_roundAfter_ballots_iff] at h ⊢
  refine ⟨List.mem_map_of_mem hb, fun ds hds => ?_⟩
  obtain ⟨c, hc⟩ := exists_isVoteFor_of_not_meetsInactivityCondition (h.2 ds hds)
  rw [← roundAfter_continuing_eq hcands]
  exact (isVoteFor_dropDuplicates_of_isVoteFor_toReproduction hc).1

/-- Along the same defeat sequence, every surviving Hybrid ballot survives under
Truncate + Retain, provided the initial continuing-candidate lists agree. This does not
compare tabulations that choose different defeat sequences. -/
theorem mem_roundAfter_truncateAtOvervote_of_mem_roundAfter_toReproduction
    {e : Election} {defeated : List Cand} {b : Ballot}
    (hcands : initialCands { e with ballots := e.ballots.map Ballot.toReproduction } =
      initialCands { e with ballots := e.ballots.map Ballot.truncateAtOvervote })
    (hb : b ∈ e.ballots)
    (h : b.toReproduction ∈
      (roundAfter { e with ballots := e.ballots.map Ballot.toReproduction } defeated).ballots) :
    b.truncateAtOvervote ∈
      (roundAfter { e with ballots := e.ballots.map Ballot.truncateAtOvervote } defeated).ballots := by
  rw [mem_roundAfter_ballots_iff] at h ⊢
  refine ⟨List.mem_map_of_mem hb, fun ds hds => ?_⟩
  obtain ⟨c, hc⟩ := exists_isVoteFor_of_not_meetsInactivityCondition (h.2 ds hds)
  rw [← roundAfter_continuing_eq hcands]
  exact (isVoteFor_truncateAtOvervote_of_isVoteFor_toReproduction hc).1

/-- Along the same defeat sequence, every surviving Hybrid ballot survives under
Truncate + Remove, provided the initial continuing-candidate lists agree. This does not
compare tabulations that choose different defeat sequences. -/
theorem mem_roundAfter_truncateAtOvervote_dropDuplicates_of_mem_roundAfter_toReproduction
    {e : Election} {defeated : List Cand} {b : Ballot}
    (hcands : initialCands { e with ballots := e.ballots.map Ballot.toReproduction } =
      initialCands { e with ballots := e.ballots.map (fun b => b.dropDuplicates.truncateAtOvervote) })
    (hb : b ∈ e.ballots)
    (h : b.toReproduction ∈
      (roundAfter { e with ballots := e.ballots.map Ballot.toReproduction } defeated).ballots) :
    b.dropDuplicates.truncateAtOvervote ∈
      (roundAfter
        { e with ballots := e.ballots.map (fun b => b.dropDuplicates.truncateAtOvervote) }
        defeated).ballots := by
  rw [mem_roundAfter_ballots_iff] at h ⊢
  refine ⟨List.mem_map_of_mem hb, fun ds hds => ?_⟩
  obtain ⟨c, hc⟩ := exists_isVoteFor_of_not_meetsInactivityCondition (h.2 ds hds)
  rw [← roundAfter_continuing_eq hcands]
  exact (isVoteFor_truncateAtOvervote_dropDuplicates_of_isVoteFor_toReproduction hc).1

end Inclusions

end Alaska
