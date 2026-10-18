import Std.Data.TreeMap.Raw.Lemmas
import FVDemocracy.Alaska.ParseCVR.Parse

/-!
# Correctness of the CVR parser

`fromJson? (toJson x) = .ok x` for every type read from the export, and a
characterisation of the ballots `Session.toBallot?` produces.
-/

open Lean

namespace Alaska.CVRExport

/-! ## Json lemmas -/

/-- Looking up a key in an object built from a list with distinct keys agrees
with `List.lookup`, reading an absent key as `null`. -/
theorem getObjValD_mkObj {l : List (String × Json)} (hd : (l.map Prod.fst).Nodup)
    (k : String) : (Json.mkObj l).getObjValD k = (l.lookup k).getD Json.null := by
  simp only [Json.getObjValD, Json.mkObj, Json.getObjVal?]
  cases h : l.lookup k with
  | none =>
    have hc : (l.map Prod.fst).contains k = false := by
      rw [List.lookup_eq_none_iff] at h
      rw [Bool.eq_false_iff]
      intro hc
      obtain ⟨a, ha, hb⟩ := List.contains_iff_exists_mem_beq.mp hc
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
      have := h p hp
      simp_all
    rw [Std.TreeMap.Raw.get?_eq_getElem?,
      Std.TreeMap.Raw.getElem?_ofList_of_contains_eq_false hc]
    rfl
  | some v =>
    obtain ⟨l₁, l₂, rfl, -⟩ := List.lookup_eq_some_iff.mp h
    have hdist : (l₁ ++ (k, v) :: l₂).Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) :=
      (List.pairwise_map.mp hd).imp fun hne heq => hne (Std.LawfulEqCmp.eq_of_compare heq)
    rw [Std.TreeMap.Raw.get?_eq_getElem?,
      Std.TreeMap.Raw.getElem?_ofList_of_mem Std.ReflCmp.compare_self hdist (v := v) (by simp)]
    rfl

theorem fromJson_toJson_nat (n : Nat) : fromJson? (toJson n) = Except.ok n := rfl

theorem fromJson_toJson_string (s : String) : fromJson? (toJson s) = Except.ok s := rfl

theorem fromJson_toJson_bool (b : Bool) : fromJson? (toJson b) = Except.ok b := by
  cases b <;> rfl

theorem fromJson_toJson_array {α : Type} [FromJson α] [ToJson α]
    (h : ∀ x : α, fromJson? (toJson x) = Except.ok x) (xs : Array α) :
    fromJson? (toJson xs) = Except.ok xs := by
  have hc : (fromJson? ∘ toJson : α → Except String α) = (pure <| id ·) := funext h
  show Array.mapM fromJson? (xs.map toJson) = Except.ok xs
  rw [Array.mapM_map, hc, Array.mapM_pure, Array.map_id]
  rfl

theorem fromJson_null_option {α : Type} [FromJson α] :
    fromJson? (α := Option α) Json.null = Except.ok none := rfl

theorem fromJson_toJson_option_nat (n : Nat) :
    fromJson? (α := Option Nat) (toJson n) = Except.ok (some n) := rfl

theorem fromJson_toJson_option_string (s : String) :
    fromJson? (α := Option String) (toJson s) = Except.ok (some s) := rfl

theorem except_ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

theorem except_map_ok {ε α β : Type} (a : α) (f : α → β) :
    (f <$> (Except.ok a : Except ε α)) = Except.ok (f a) := rfl

/-! ## Round trips

Each proof unfolds the two instances, replaces every key lookup in the encoded
object by the field's encoding using `getObjValD_mkObj` (its distinct-keys
hypothesis is decided on the literal key list), and decodes each field with the
lemmas above. -/

section RoundTrip

attribute [local simp] Json.getObjValAs? Json.opt List.lookup_cons
  fromJson_toJson_nat fromJson_toJson_string fromJson_toJson_bool
  fromJson_null_option fromJson_toJson_option_nat fromJson_toJson_option_string
  except_ok_bind except_map_ok

theorem fromJson_toJson_manifest {α : Type} [FromJson α] [ToJson α]
    (h : ∀ x : α, fromJson? (toJson x) = Except.ok x) (m : Manifest α) :
    fromJson? (toJson m) = Except.ok m := by
  simp (disch := simp only [List.map_cons, List.map_nil]; decide)
    [instToJsonManifest, instFromJsonManifest, getObjValD_mkObj, fromJson_toJson_array h]

theorem fromJson_toJson_configuration (c : Configuration) :
    fromJson? (toJson c) = Except.ok c := by
  simp (disch := simp only [List.map_cons, List.map_nil]; decide)
    [instToJsonConfiguration, instFromJsonConfiguration, getObjValD_mkObj]

theorem fromJson_toJson_ballotType (b : BallotType) : fromJson? (toJson b) = Except.ok b := by
  obtain ⟨_, _, e⟩ := b
  cases e <;>
  simp (disch := simp only [List.map_cons, List.map_nil, List.map_append]; decide)
    [instToJsonBallotType, instFromJsonBallotType, getObjValD_mkObj]

theorem fromJson_toJson_ballotTypeContest (b : BallotTypeContest) :
    fromJson? (toJson b) = Except.ok b := by
  simp (disch := simp only [List.map_cons, List.map_nil]; decide)
    [instToJsonBallotTypeContest, instFromJsonBallotTypeContest, getObjValD_mkObj]

theorem fromJson_toJson_candidateType (t : CandidateType) :
    fromJson? (toJson t) = Except.ok t := by
  cases t <;> rfl

theorem fromJson_toJson_option_array_nat (xs : Array Nat) :
    fromJson? (α := Option (Array Nat)) (toJson xs) = Except.ok (some xs) := by
  show some <$> fromJson? (toJson xs) = _
  rw [fromJson_toJson_array fromJson_toJson_nat]
  rfl

theorem fromJson_toJson_candidate (c : Candidate) : fromJson? (toJson c) = Except.ok c := by
  obtain ⟨_, _, _, _, _, a, d⟩ := c
  cases a <;> cases d <;>
  simp (disch := simp only [List.map_cons, List.map_nil, List.map_append]; decide)
    [instToJsonCandidate, instFromJsonCandidate, getObjValD_mkObj,
      fromJson_toJson_candidateType, fromJson_toJson_option_array_nat]

theorem fromJson_toJson_contest (c : Contest) : fromJson? (toJson c) = Except.ok c := by
  obtain ⟨_, _, _, _, _, _, w, d, t⟩ := c
  cases w <;> cases d <;> cases t <;>
  simp (disch := simp only [List.map_cons, List.map_nil, List.map_append]; decide)
    [instToJsonContest, instFromJsonContest, getObjValD_mkObj]

theorem fromJson_toJson_countingGroup (c : CountingGroup) :
    fromJson? (toJson c) = Except.ok c := by
  simp (disch := simp only [List.map_cons, List.map_nil]; decide)
    [instToJsonCountingGroup, instFromJsonCountingGroup, getObjValD_mkObj]

theorem fromJson_toJson_district (d : District) : fromJson? (toJson d) = Except.ok d := by
  simp (disch := simp only [List.map_cons, List.map_nil]; decide)
    [instToJsonDistrict, instFromJsonDistrict, getObjValD_mkObj]

theorem fromJson_toJson_districtPrecinctPortion (d : DistrictPrecinctPortion) :
    fromJson? (toJson d) = Except.ok d := by
  simp (disch := simp only [List.map_cons, List.map_nil]; decide)
    [instToJsonDistrictPrecinctPortion, instFromJsonDistrictPrecinctPortion, getObjValD_mkObj]

theorem fromJson_toJson_districtType (d : DistrictType) :
    fromJson? (toJson d) = Except.ok d := by
  simp (disch := simp only [List.map_cons, List.map_nil]; decide)
    [instToJsonDistrictType, instFromJsonDistrictType, getObjValD_mkObj]

theorem fromJson_toJson_electionEvent (e : ElectionEvent) :
    fromJson? (toJson e) = Except.ok e := by
  simp (disch := simp only [List.map_cons, List.map_nil]; decide)
    [instToJsonElectionEvent, instFromJsonElectionEvent, getObjValD_mkObj,
      fromJson_toJson_array fromJson_toJson_nat]

theorem fromJson_toJson_outstackCondition (o : OutstackCondition) :
    fromJson? (toJson o) = Except.ok o := by
  simp (disch := simp only [List.map_cons, List.map_nil]; decide)
    [instToJsonOutstackCondition, instFromJsonOutstackCondition, getObjValD_mkObj]

theorem fromJson_toJson_party (p : Party) : fromJson? (toJson p) = Except.ok p := by
  simp (disch := simp only [List.map_cons, List.map_nil]; decide)
    [instToJsonParty, instFromJsonParty, getObjValD_mkObj]

theorem fromJson_toJson_precinct (p : Precinct) : fromJson? (toJson p) = Except.ok p := by
  simp (disch := simp only [List.map_cons, List.map_nil]; decide)
    [instToJsonPrecinct, instFromJsonPrecinct, getObjValD_mkObj]

theorem fromJson_toJson_precinctPortion (p : PrecinctPortion) :
    fromJson? (toJson p) = Except.ok p := by
  simp (disch := simp only [List.map_cons, List.map_nil]; decide)
    [instToJsonPrecinctPortion, instFromJsonPrecinctPortion, getObjValD_mkObj]

theorem fromJson_toJson_tabulatorType (t : TabulatorType) :
    fromJson? (toJson t) = Except.ok t := by
  cases t <;> rfl

theorem fromJson_toJson_tabulator (t : Tabulator) : fromJson? (toJson t) = Except.ok t := by
  simp (disch := simp only [List.map_cons, List.map_nil]; decide)
    [instToJsonTabulator, instFromJsonTabulator, getObjValD_mkObj,
      fromJson_toJson_tabulatorType]

theorem fromJson_toJson_mark (m : Mark) : fromJson? (toJson m) = Except.ok m := by
  obtain ⟨_, _, p, _, wi, _, wd, _, _, _⟩ := m
  cases p <;> cases wi <;> cases wd <;>
  simp (disch := simp only [List.map_cons, List.map_nil, List.map_append]; decide)
    [instToJsonMark, instFromJsonMark, getObjValD_mkObj,
      fromJson_toJson_array fromJson_toJson_nat]

theorem fromJson_toJson_cardContest (c : CardContest) :
    fromJson? (toJson c) = Except.ok c := by
  simp (disch := simp only [List.map_cons, List.map_nil]; decide)
    [instToJsonCardContest, instFromJsonCardContest, getObjValD_mkObj,
      fromJson_toJson_array fromJson_toJson_nat, fromJson_toJson_array fromJson_toJson_mark]

theorem fromJson_toJson_card (c : Card) : fromJson? (toJson c) = Except.ok c := by
  obtain ⟨_, k, _, _, _⟩ := c
  cases k <;>
  simp (disch := simp only [List.map_cons, List.map_nil, List.map_append]; decide)
    [instToJsonCard, instFromJsonCard, getObjValD_mkObj,
      fromJson_toJson_array fromJson_toJson_nat,
      fromJson_toJson_array fromJson_toJson_cardContest]

theorem fromJson_toJson_sessionState (s : SessionState) :
    fromJson? (toJson s) = Except.ok s := by
  simp (disch := simp only [List.map_cons, List.map_nil]; decide)
    [instToJsonSessionState, instFromJsonSessionState, getObjValD_mkObj,
      fromJson_toJson_array fromJson_toJson_card]

theorem fromJson_toJson_sessionType (t : SessionType) :
    fromJson? (toJson t) = Except.ok t := by
  cases t <;> rfl

theorem fromJson_toJson_option_sessionState (s : SessionState) :
    fromJson? (α := Option SessionState) (toJson s) = Except.ok (some s) := by
  show some <$> fromJson? (toJson s) = _
  rw [fromJson_toJson_sessionState]
  rfl

theorem fromJson_toJson_session (s : Session) : fromJson? (toJson s) = Except.ok s := by
  obtain ⟨_, _, _, _, _, _, _, _, _, m⟩ := s
  cases m <;>
  simp (disch := simp only [List.map_cons, List.map_nil, List.map_append]; decide)
    [instToJsonSession, instFromJsonSession, getObjValD_mkObj,
      fromJson_toJson_sessionType, fromJson_toJson_sessionState,
      fromJson_toJson_option_sessionState]

end RoundTrip

/-! ## Ballots -/

/-- The rank check in `toBallot?`, as a statement about each mark. -/
private theorem find?_rank_eq_none_iff {marks : Array Mark} {n : Nat} :
    marks.find? (fun m => m.rank == 0 || decide (m.rank > n)) = none ↔
      ∀ m ∈ marks, m.rank ≠ 0 ∧ m.rank ≤ n := by
  rw [Array.find?_eq_none]
  refine forall₂_congr fun m _ => ?_
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or, gt_iff_lt, Nat.not_lt]

private theorem find?_rank_eq_none_of_forall {marks : Array Mark} {n : Nat}
    (h : ∀ m, marks.find? (fun m => m.rank == 0 || decide (m.rank > n)) = some m → False) :
    marks.find? (fun m => m.rank == 0 || decide (m.rank > n)) = none := by
  cases hf : marks.find? (fun m => m.rank == 0 || decide (m.rank > n)) with
  | none => rfl
  | some m => exact (h m hf).elim

/-- The repeat check in `toBallot?`, as a statement about each rank. -/
private theorem findIdx?_not_nodup_eq_none_iff {ranks : List (List Cand)} :
    ranks.findIdx? (fun l => !decide l.Nodup) = none ↔ ∀ l ∈ ranks, l.Nodup := by
  rw [List.findIdx?_eq_none_iff]
  refine forall₂_congr fun l _ => ?_
  simp

private theorem findIdx?_not_nodup_eq_none_of_forall {ranks : List (List Cand)}
    (h : ∀ r, ranks.findIdx? (fun l => !decide l.Nodup) = some r → False) :
    ranks.findIdx? (fun l => !decide l.Nodup) = none := by
  cases hf : ranks.findIdx? (fun l => !decide l.Nodup) with
  | none => rfl
  | some r => exact (h r hf).elim

/-- `toBallot?` gives `none` exactly when the contest is not in the session's
current state. -/
theorem Session.toBallot?_eq_ok_none_iff {keep : Mark → Bool}
    {contestId numOfRanks ballotIndex : Nat} {s : Session} :
    s.toBallot? keep contestId numOfRanks ballotIndex = .ok none ↔
      s.current.contestMarks? contestId = none := by
  unfold Session.toBallot?
  cases hm : s.current.contestMarks? contestId with
  | none => simp [pure, Except.pure]
  | some marks =>
    simp only [reduceCtorEq, iff_false]
    split <;> simp only [bind, Except.bind, pure, Except.pure]
    · simp
    · split <;> simp

/-- `toBallot?` fails exactly when the contest is in the session's current state
and either one of its marks has a rank outside `1 … numOfRanks`, or for some rank
the candidates of the kept marks at that rank are not distinct. -/
theorem Session.toBallot?_isOk_eq_false_iff {keep : Mark → Bool}
    {contestId numOfRanks ballotIndex : Nat} {s : Session} :
    (s.toBallot? keep contestId numOfRanks ballotIndex).isOk = false ↔
      ∃ marks, s.current.contestMarks? contestId = some marks ∧
        ((∃ m ∈ marks, m.rank = 0 ∨ numOfRanks < m.rank) ∨
          ∃ r < numOfRanks,
            ¬((marks.filter (fun m => keep m && m.rank == r + 1)).toList.map Mark.cand).Nodup) := by
  unfold Session.toBallot?
  cases hm : s.current.contestMarks? contestId with
  | none => simp [pure, Except.pure, Except.isOk, Except.toBool]
  | some marks =>
    simp only [Option.some.injEq, exists_eq_left']
    split
    · next m hfind =>
      have hr := Array.find?_some hfind
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hr
      constructor
      · intro _
        exact Or.inl ⟨m, Array.mem_of_find?_eq_some hfind, hr⟩
      · intro _
        rfl
    · next hfind =>
      have hall := find?_rank_eq_none_iff.mp (find?_rank_eq_none_of_forall hfind)
      have hrank : ¬∃ m ∈ marks, m.rank = 0 ∨ numOfRanks < m.rank := by
        rintro ⟨m, hm, hr⟩
        have := hall m hm
        omega
      simp only [hrank, false_or, bind, Except.bind, pure, Except.pure]
      split
      · next r hr =>
        have hany := congrArg Option.isSome hr
        simp only [List.findIdx?_isSome, Option.isSome_some, List.any_eq_true, List.mem_map,
          List.mem_range] at hany
        obtain ⟨_, ⟨r', hlt, rfl⟩, hnd⟩ := hany
        refine ⟨fun _ => ⟨r', hlt, ?_⟩, fun _ => rfl⟩
        simpa using hnd
      · next hnone =>
        have hall' := findIdx?_not_nodup_eq_none_iff.mp (findIdx?_not_nodup_eq_none_of_forall hnone)
        refine ⟨fun h => (nomatch h), fun ⟨r, hlt, hnd⟩ => (hnd ?_).elim⟩
        exact hall' _ (List.mem_map.mpr ⟨r, List.mem_range.mpr hlt, rfl⟩)

/-- A ballot from `toBallot?` has `numOfRanks` ranks, and `c` is at rank `r + 1`
exactly when some mark kept by `keep` in the contest's marks in the session's
current state has `Mark.cand` equal to `c` and rank `r + 1`. -/
theorem Session.toBallot?_spec {keep : Mark → Bool}
    {contestId numOfRanks ballotIndex : Nat} {s : Session} {b : Ballot}
    (h : s.toBallot? keep contestId numOfRanks ballotIndex = .ok (some b)) :
    ∃ marks, s.current.contestMarks? contestId = some marks ∧
      b.ballotIndex = ballotIndex ∧
      b.ranks.length = numOfRanks ∧
      ∀ r c, (∃ l, b.ranks[r]? = some l ∧ c ∈ l) ↔
        ∃ m ∈ marks, keep m ∧ m.rank = r + 1 ∧ m.cand = c := by
  unfold Session.toBallot? at h
  cases hm : s.current.contestMarks? contestId with
  | none => simp [hm, pure, Except.pure] at h
  | some marks =>
    simp only [hm] at h
    split at h
    · exact nomatch h
    · next hfind =>
      have hall := find?_rank_eq_none_iff.mp (find?_rank_eq_none_of_forall hfind)
      simp only [pure, Except.pure, bind, Except.bind] at h
      split at h
      · exact nomatch h
      simp only [Except.ok.injEq, Option.some.injEq] at h
      subst h
      refine ⟨marks, rfl, rfl, by simp, fun r c => ?_⟩
      constructor
      · rintro ⟨l, hl, hc⟩
        by_cases hlt : r < numOfRanks
        · simp only [List.getElem?_map, List.getElem?_range hlt, Option.map_some,
            Option.some.injEq] at hl
          subst hl
          simp only [List.mem_map, Array.mem_toList_iff, Array.mem_filter, Bool.and_eq_true,
            beq_iff_eq] at hc
          obtain ⟨m, ⟨hm, hk, hr⟩, rfl⟩ := hc
          exact ⟨m, hm, hk, hr, rfl⟩
        · simp [hlt] at hl
      · rintro ⟨m, hm, hk, hr, rfl⟩
        have hlt : r < numOfRanks := by have := (hall m hm).2; omega
        refine ⟨_, by simp only [List.getElem?_map, List.getElem?_range hlt, Option.map_some]; rfl,
          ?_⟩
        simp only [List.mem_map, Array.mem_toList_iff, Array.mem_filter, Bool.and_eq_true,
          beq_iff_eq]
        exact ⟨m, ⟨hm, hk, hr⟩, rfl⟩

/-- No rank of a ballot from `toBallot?` lists a candidate more than once. -/
theorem Session.toBallot?_ranks_nodup {keep : Mark → Bool}
    {contestId numOfRanks ballotIndex : Nat} {s : Session} {b : Ballot}
    (h : s.toBallot? keep contestId numOfRanks ballotIndex = .ok (some b)) :
    ∀ l ∈ b.ranks, l.Nodup := by
  unfold Session.toBallot? at h
  cases hm : s.current.contestMarks? contestId with
  | none => simp [hm, pure, Except.pure] at h
  | some marks =>
    simp only [hm] at h
    split at h
    · exact nomatch h
    · simp only [pure, Except.pure, bind, Except.bind] at h
      split at h
      · exact nomatch h
      · next hnone =>
        simp only [Except.ok.injEq, Option.some.injEq] at h
        subst h
        exact findIdx?_not_nodup_eq_none_iff.mp (findIdx?_not_nodup_eq_none_of_forall hnone)

end Alaska.CVRExport
