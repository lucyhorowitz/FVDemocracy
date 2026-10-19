import FVDemocracy.Alaska.Reproduction.Report

/-!
# Tabulating a ballot profile

A ballot profile lists each distinct list of rankings with the number of ballots that have it.
`p.IsProfileOf bs` says that `p` lists the rankings of the ballots `bs` with their multiplicities.
`Profile.ofBallots bs` computes a profile of `bs`. `Profile.tabulate` tabulates a profile, counting
each entry once with its number of ballots, and reads the rankings with `readRankings`.

* `ofBallots_isProfileOf`: `Profile.ofBallots bs` is a profile of `bs`.
* `tabulate_eq_profileTabulate`: `tabulate e` is `Profile.tabulate` on a profile of `e.ballots`.
* `reproductionTabulate_eq_profileTabulate`: `reproductionTabulate e` is `Profile.tabulate` on
  that profile after `Profile.toReproduction`.
* `reportRounds_eq_profileReportRounds`: `reportRounds ids e` is `Profile.reportRounds` on that
  profile.
-/

namespace Alaska

mutual
/-- Equality of trees, comparing candidates and children in order. -/
def RCVTree.beq : RCVTree → RCVTree → Bool
  | .winner c, .winner d => c == d
  | .branch xs, .branch ys => RCVTree.beqList xs ys
  | _, _ => false

def RCVTree.beqList : List (Cand × RCVTree) → List (Cand × RCVTree) → Bool
  | [], [] => true
  | (c, t) :: xs, (d, u) :: ys => c == d && t.beq u && RCVTree.beqList xs ys
  | _, _ => false
end

mutual
theorem RCVTree.eq_of_beq : (t u : RCVTree) → t.beq u = true → t = u
  | .winner c, .winner d, h => by simp_all [RCVTree.beq]
  | .branch xs, .branch ys, h => by
    rw [RCVTree.beq] at h
    rw [RCVTree.eq_of_beqList xs ys h]
  | .winner _, .branch _, h => by simp [RCVTree.beq] at h
  | .branch _, .winner _, h => by simp [RCVTree.beq] at h

theorem RCVTree.eq_of_beqList : (xs ys : List (Cand × RCVTree)) → RCVTree.beqList xs ys = true →
    xs = ys
  | [], [], _ => rfl
  | (c, t) :: xs, (d, u) :: ys, h => by
    simp only [RCVTree.beqList, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1.1, RCVTree.eq_of_beq t u h.1.2, RCVTree.eq_of_beqList xs ys h.2]
  | [], _ :: _, h => by simp [RCVTree.beqList] at h
  | _ :: _, [], h => by simp [RCVTree.beqList] at h
end

mutual
theorem RCVTree.beq_self : (t : RCVTree) → t.beq t = true
  | .winner c => by simp [RCVTree.beq]
  | .branch xs => by rw [RCVTree.beq]; exact RCVTree.beqList_self xs

theorem RCVTree.beqList_self : (xs : List (Cand × RCVTree)) → RCVTree.beqList xs xs = true
  | [] => rfl
  | (c, t) :: xs => by
    simp only [RCVTree.beqList, beq_self_eq_true, Bool.true_and, Bool.and_eq_true]
    exact ⟨RCVTree.beq_self t, RCVTree.beqList_self xs⟩
end

instance : DecidableEq RCVTree := fun t u =>
  decidable_of_iff (t.beq u = true) ⟨RCVTree.eq_of_beq t u, fun h => h ▸ RCVTree.beq_self t⟩

/-- A ballot profile: each entry is a list of rankings and the number of ballots with exactly
those rankings. -/
abbrev Profile := List (List (List Cand) × Nat)

namespace Profile

/-- The rankings of the ballots of `p`: the rankings of each entry, repeated as many times as its
number of ballots. -/
def rankings (p : Profile) : List (List (List Cand)) :=
  p.flatMap fun x => List.replicate x.2 x.1

/-- `p` is a profile of the ballots `bs`: the rankings of `bs` are those of `p`, with the same
multiplicities. -/
def IsProfileOf (p : Profile) (bs : List Ballot) : Prop :=
  (bs.map Ballot.ranks).Perm p.rankings

/-- The number of ballots of `p` whose rankings satisfy `f`. -/
def count (f : List (List Cand) → Bool) (p : Profile) : Nat :=
  ((p.filter fun x => f x.1).map (·.2)).sum

theorem countP_rankings (f : List (List Cand) → Bool) (p : Profile) :
    p.rankings.countP f = p.count f := by
  induction p with
  | nil => rfl
  | cons x p ih =>
    simp only [rankings, count, List.flatMap_cons, List.countP_append, List.countP_replicate,
      List.filter_cons] at ih ⊢
    rw [ih]
    split <;> simp_all

theorem filter_rankings (f : List (List Cand) → Bool) (p : Profile) :
    p.rankings.filter f = Profile.rankings (p.filter fun x => f x.1) := by
  induction p with
  | nil => rfl
  | cons x p ih =>
    simp only [rankings, List.flatMap_cons, List.filter_append, List.filter_replicate,
      List.filter_cons] at ih ⊢
    rw [ih]
    split <;> simp_all

theorem map_rankings (g : List (List Cand) → List (List Cand)) (p : Profile) :
    p.rankings.map g = Profile.rankings (p.map fun x => (g x.1, x.2)) := by
  induction p with
  | nil => rfl
  | cons x p ih =>
    simp only [rankings, List.flatMap_cons, List.map_append, List.map_replicate,
      List.map_cons] at ih ⊢
    rw [ih]

theorem IsProfileOf.countP {p : Profile} {bs : List Ballot} (h : p.IsProfileOf bs)
    (f : List (List Cand) → Bool) : bs.countP (fun b => f b.ranks) = p.count f := by
  rw [← countP_rankings, ← h.countP_eq, List.countP_map]
  rfl

theorem IsProfileOf.filter {p : Profile} {bs : List Ballot} (h : p.IsProfileOf bs)
    (f : List (List Cand) → Bool) :
    Profile.IsProfileOf (p.filter fun x => f x.1) (bs.filter fun b => f b.ranks) := by
  have := List.Perm.filter f h
  rw [List.filter_map, filter_rankings] at this
  exact this

theorem IsProfileOf.map {p : Profile} {bs : List Ballot} (h : p.IsProfileOf bs)
    (g : List (List Cand) → List (List Cand)) (φ : Ballot → Ballot)
    (hφ : ∀ b, (φ b).ranks = g b.ranks) :
    Profile.IsProfileOf (p.map fun x => (g x.1, x.2)) (bs.map φ) := by
  have := List.Perm.map g h
  rw [List.map_map, map_rankings] at this
  unfold IsProfileOf
  rw [List.map_map]
  exact (List.map_congr_left fun b _ => hφ b) ▸ this

theorem perm_rankings {p q : Profile} (h : p.Perm q) : p.rankings.Perm q.rankings :=
  h.flatMap_right _

/-! ## The profile of a list of ballots -/

/-- Write-ins before regular candidates, each in the order of their numbers. -/
def compareCand : Cand → Cand → Ordering
  | .writeIn i, .writeIn j => compare i j
  | .writeIn _, .regular _ => .lt
  | .regular _, .writeIn _ => .gt
  | .regular i, .regular j => compare i j

/-- Lists of rankings in lexicographic order: ranking by ranking, and each ranking candidate by
candidate with `compareCand`. -/
def rankingsLE (rs rs' : List (List Cand)) : Bool :=
  List.compareLex (List.compareLex compareCand) rs rs' != .gt

/-- `runs l` after the entries `acc`, which are in reverse order. -/
def runsAux : List (List (List Cand)) → Profile → Profile
  | [], acc => acc.reverse
  | rs :: l, [] => runsAux l [(rs, 1)]
  | rs :: l, (rs', n) :: acc =>
    if rs = rs' then runsAux l ((rs', n + 1) :: acc) else runsAux l ((rs, 1) :: (rs', n) :: acc)

/-- Each run of equal adjacent lists of rankings in `l` as one entry, with the length of the
run. -/
def runs (l : List (List (List Cand))) : Profile :=
  runsAux l []

/-- The profile of the ballots `bs`: their lists of rankings sorted with `rankingsLE`, so that equal
ones are adjacent, and counted with `runs`. The entries are ordered by number of ballots, most
first, and then by `rankingsLE`. -/
def ofBallots (bs : List Ballot) : Profile :=
  (runs ((bs.map Ballot.ranks).mergeSort rankingsLE)).mergeSort fun x y =>
    decide (y.2 < x.2) || (x.2 == y.2 && rankingsLE x.1 y.1)

theorem rankings_runsAux (l : List (List (List Cand))) (acc : Profile) :
    (runsAux l acc).rankings = Profile.rankings acc.reverse ++ l := by
  induction l generalizing acc with
  | nil => simp [runsAux]
  | cons rs l ih =>
    match acc with
    | [] => rw [runsAux, ih]; simp [rankings]
    | (rs', n) :: acc =>
      rw [runsAux]
      split
      · next h =>
        subst h
        rw [ih]
        simp [rankings, List.replicate_succ']
      · rw [ih]
        simp [rankings]

theorem rankings_runs (l : List (List (List Cand))) : (runs l).rankings = l := by
  rw [runs, rankings_runsAux]
  rfl

/-- `ofBallots bs` is a profile of `bs`. -/
theorem ofBallots_isProfileOf (bs : List Ballot) : (ofBallots bs).IsProfileOf bs := by
  unfold IsProfileOf ofBallots
  refine List.Perm.trans ?_ (perm_rankings (List.mergeSort_perm _ _)).symm
  rw [rankings_runs]
  exact (List.mergeSort_perm _ _).symm

/-! ## Tallies -/

/-- The number of ballots of `p` that count as one vote for `c` when `cont` are the continuing
candidates. -/
def votesFor (c : Cand) (cont : List Cand) (p : Profile) : Nat :=
  p.count fun rs => decide (readRankings cont false rs = .voteFor c)

/-- The number of ballots of `p` that are active when `cont` are the continuing candidates. -/
def numActive (cont : List Cand) (p : Profile) : Nat :=
  p.count fun rs => decide (readRankings cont false rs ≠ .inactive)

/-- The entries of `p` whose ballots are active when `cont` are the continuing candidates. -/
def active (cont : List Cand) (p : Profile) : Profile :=
  p.filter fun x => decide (readRankings cont false x.1 ≠ .inactive)

def lowestTally (cont : List Cand) (p : Profile) : Nat :=
  (cont.map fun c => p.votesFor c cont).min?.getD 0

def writeInTotal (cands : List Cand) (p : Profile) : Nat :=
  ((cands.filter IsWriteIn).map fun c => p.votesFor c cands).sum

/-- `WriteInsQualify` with the votes of `p`. -/
def WriteInsQualify (cands : List Cand) (p : Profile) (margin : Rat) : Prop :=
  let W := p.writeInTotal cands
  (∀ c ∈ cands, p.votesFor c cands ≤ W) ∨
    ∃ c ∈ cands, W < p.votesFor c cands ∧
      (∀ c' ∈ cands, W < p.votesFor c' cands → p.votesFor c' cands = p.votesFor c cands) ∧
      ((p.votesFor c cands : Int) - W) * margin.den <
        margin.num * ((p.votesFor c cands : Int) + W)

instance (cands : List Cand) (p : Profile) (margin : Rat) :
    Decidable (p.WriteInsQualify cands margin) := by
  unfold WriteInsQualify
  infer_instance

def initialCands (cands : List Cand) (p : Profile) : List Cand :=
  if p.WriteInsQualify cands recountMargin then cands else regulars cands

def majorityWinner (cont : List Cand) (p : Profile) : Option Cand :=
  cont.find? fun c => decide (2 * p.votesFor c cont > p.numActive cont)

theorem decide_isVoteFor (cont : List Cand) (b : Ballot) (c : Cand) :
    decide (IsVoteFor cont b c) = decide (readRankings cont false b.ranks = .voteFor c) :=
  decide_eq_decide.mpr (readRankings_eq_iff cont b (.voteFor c)).symm

theorem decide_not_meetsInactivityCondition (cont : List Cand) (b : Ballot) :
    decide (¬ MeetsInactivityCondition cont b) =
      decide (readRankings cont false b.ranks ≠ .inactive) :=
  decide_eq_decide.mpr (not_congr (readRankings_eq_iff cont b .inactive).symm)

theorem IsProfileOf.votesFor {p : Profile} {bs : List Ballot} (h : p.IsProfileOf bs)
    (c : Cand) (cont : List Cand) : Alaska.votesFor c cont bs = p.votesFor c cont := by
  unfold Alaska.votesFor Profile.votesFor
  rw [← h.countP]
  simp only [decide_isVoteFor]

theorem IsProfileOf.numActive {p : Profile} {bs : List Ballot} (h : p.IsProfileOf bs)
    (cont : List Cand) : Alaska.numActive cont bs = p.numActive cont := by
  unfold Alaska.numActive Profile.numActive
  rw [← h.countP]
  simp only [decide_not_meetsInactivityCondition]

theorem active_filter (cont : List Cand) (bs : List Ballot) :
    bs.filter (fun b => decide (¬ MeetsInactivityCondition cont b)) =
      bs.filter fun b => decide (readRankings cont false b.ranks ≠ .inactive) := by
  simp only [decide_not_meetsInactivityCondition]

theorem IsProfileOf.active {p : Profile} {bs : List Ballot} (h : p.IsProfileOf bs)
    (cont : List Cand) :
    (p.active cont).IsProfileOf (bs.filter fun b => decide (¬ MeetsInactivityCondition cont b)) := by
  rw [active_filter]
  exact h.filter fun rs => decide (readRankings cont false rs ≠ .inactive)

theorem IsProfileOf.lowestTally {p : Profile} {bs : List Ballot} (h : p.IsProfileOf bs)
    (cont : List Cand) : Alaska.lowestTally cont bs = p.lowestTally cont := by
  simp only [Alaska.lowestTally, Profile.lowestTally, tallies, h.votesFor]

theorem IsProfileOf.writeInsQualify {p : Profile} {bs : List Ballot} (h : p.IsProfileOf bs)
    (cands : List Cand) (margin : Rat) :
    Alaska.WriteInsQualify cands bs margin ↔ p.WriteInsQualify cands margin := by
  simp only [Alaska.WriteInsQualify, Profile.WriteInsQualify, Alaska.writeInTotal,
    Profile.writeInTotal, h.votesFor]

theorem IsProfileOf.initialCands {e : Election} {p : Profile} (h : p.IsProfileOf e.ballots) :
    Alaska.initialCands e = p.initialCands e.cands := by
  simp only [Alaska.initialCands, Profile.initialCands, h.writeInsQualify]

theorem IsProfileOf.majorityWinner {p : Profile} {bs : List Ballot} (h : p.IsProfileOf bs)
    (cont : List Cand) : Alaska.majorityWinner cont bs = p.majorityWinner cont := by
  simp only [Alaska.majorityWinner, Profile.majorityWinner, IsMajorityWinner, h.votesFor,
    h.numActive]

/-! ## Rounds -/

/-- `tabulateRounds` on a profile. With two or more continuing candidates, each candidate with the
fewest votes may be defeated, and the rounds continue on the remaining candidates with the entries
that are still active. -/
def tabulateRounds (cont : List Cand) (p : Profile) : RCVTree :=
  match cont with
  | [] => .branch []
  | [c] => .winner c
  | c₁ :: c₂ :: cs =>
    .branch (((c₁ :: c₂ :: cs).filter fun c =>
        p.votesFor c (c₁ :: c₂ :: cs) == p.lowestTally (c₁ :: c₂ :: cs)).attach.map fun ⟨c, hc⟩ =>
      have : c ∈ c₁ :: c₂ :: cs := (List.mem_filter.mp hc).1
      (c, tabulateRounds ((c₁ :: c₂ :: cs).erase c) (p.active ((c₁ :: c₂ :: cs).erase c))))
termination_by cont.length
decreasing_by exact List.length_erase_lt_of_mem this

theorem IsProfileOf.tabulateRounds (cont : List Cand) {p : Profile} {bs : List Ballot}
    (h : p.IsProfileOf bs) : Alaska.tabulateRounds cont bs = p.tabulateRounds cont := by
  match cont with
  | [] => simp [Alaska.tabulateRounds, Profile.tabulateRounds]
  | [c] => simp [Alaska.tabulateRounds, Profile.tabulateRounds]
  | c₁ :: c₂ :: cs =>
    rw [tabulateRounds_cons_cons, Profile.tabulateRounds]
    simp only [singleRound, h.votesFor, h.lowestTally, List.map_map]
    congr 1
    rw [List.attach_map_val (f := fun c => (c, Profile.tabulateRounds ((c₁ :: c₂ :: cs).erase c)
      (p.active ((c₁ :: c₂ :: cs).erase c))))]
    refine List.map_congr_left fun c hc => ?_
    have : c ∈ c₁ :: c₂ :: cs := (List.mem_filter.mp hc).1
    simp only [Function.comp, Prod.mk.injEq, true_and]
    exact IsProfileOf.tabulateRounds _ (h.active _)
termination_by cont.length
decreasing_by exact List.length_erase_lt_of_mem this

/-- `tabulate` on a profile of the ballots, with candidates `cands`. -/
def tabulate (cands : List Cand) (p : Profile) : RCVTree :=
  let cont₁ := p.initialCands cands
  match p.majorityWinner cont₁ with
  | none => (p.active cont₁).tabulateRounds cont₁
  | some c => .winner c

/-- The rankings of a ballot after `Ballot.toReproduction`. -/
def toReproductionRanks (rs : List (List Cand)) : List (List Cand) :=
  dropRepeats [] (rs.takeWhile fun r => decide (r.eraseDups.length < 2))

/-- The profile of the ballots of `p` after `Ballot.toReproduction`. -/
def toReproduction (p : Profile) : Profile :=
  p.map fun x => (toReproductionRanks x.1, x.2)

theorem IsProfileOf.toReproduction {p : Profile} {bs : List Ballot} (h : p.IsProfileOf bs) :
    p.toReproduction.IsProfileOf (bs.map Ballot.toReproduction) :=
  h.map toReproductionRanks Ballot.toReproduction fun _ => rfl

/-! ## Published rounds -/

/-- `singlePathRounds` on a profile. -/
def singlePathRounds (cont : List Cand) (p : Profile) :
    Option (List (List Cand × Profile)) :=
  if cont.length ≤ 2 then some [(cont, p)]
  else
    match h : cont.filter fun c => p.votesFor c cont == p.lowestTally cont with
    | [d] =>
      have : d ∈ cont := (List.mem_filter.mp (h ▸ List.mem_singleton_self d)).1
      ((cont, p) :: ·) <$> singlePathRounds (cont.erase d) (p.active (cont.erase d))
    | _ => none
termination_by cont.length
decreasing_by exact List.length_erase_lt_of_mem this

theorem IsProfileOf.singlePathRounds {α : Type} (F : List Cand → List Ballot → α)
    (G : List Cand → Profile → α)
    (hFG : ∀ cont bs (p : Profile), p.IsProfileOf bs → F cont bs = G cont p)
    (cont : List Cand) {p : Profile} {bs : List Ballot} (h : p.IsProfileOf bs) :
    (Alaska.singlePathRounds cont bs).map (·.map fun x => F x.1 x.2) =
      (p.singlePathRounds cont).map (·.map fun x => G x.1 x.2) := by
  rw [Alaska.singlePathRounds, Profile.singlePathRounds]
  split
  · simp [hFG _ _ _ h]
  · next hlen =>
    have hsr : singleRound cont bs = (cont.filter fun c => p.votesFor c cont == p.lowestTally cont).map
        fun c => (c, bs.filter fun b => decide (¬ MeetsInactivityCondition (cont.erase c) b)) := by
      match cont, hlen with
      | c₁ :: c₂ :: cs, _ => simp only [singleRound, h.votesFor, h.lowestTally]
      | [], hlen | [_], hlen => simp at hlen
    split
    · next d bs' hs =>
      rw [hsr] at hs
      obtain ⟨d', hd', hrest⟩ : ∃ d', (cont.filter fun c => p.votesFor c cont == p.lowestTally cont)
          = [d'] ∧ (d', bs.filter fun b => decide (¬ MeetsInactivityCondition (cont.erase d') b)) =
            (d, bs') := by
        match hl : cont.filter fun c => p.votesFor c cont == p.lowestTally cont with
        | [d'] => rw [hl] at hs; exact ⟨d', rfl, List.singleton_inj.mp hs⟩
        | [] => rw [hl] at hs; simp at hs
        | _ :: _ :: _ => rw [hl] at hs; simp at hs
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrest
      have hd : d' ∈ cont := (List.mem_filter.mp (hd' ▸ List.mem_singleton_self d')).1
      split
      · next d'' hl =>
        rw [hd'] at hl
        obtain rfl := List.singleton_inj.mp hl
        have ih := IsProfileOf.singlePathRounds F G hFG (cont.erase d') (h.active (cont.erase d'))
        cases hl : Alaska.singlePathRounds (cont.erase d')
            (bs.filter fun b => decide (¬ MeetsInactivityCondition (cont.erase d') b)) <;>
          cases hr : Profile.singlePathRounds (cont.erase d') (p.active (cont.erase d')) <;>
          simp_all [hFG _ _ _ h]
      · next hne => exact absurd hd' (hne d')
    · next hne =>
      split
      · next d hl =>
        exact absurd (by rw [hsr, hl]; rfl) (hne d _)
      · rfl
termination_by cont.length
decreasing_by exact List.length_erase_lt_of_mem hd

/-- `PublishedRound.ofRound` on profiles: `all` is the profile of all the ballots and `p` that of
the ballots of the round. -/
def ofRound (ids : List Nat) (all : Profile) (blanks : Nat) (cont : List Cand) (p : Profile) :
    PublishedRound where
  votes := ids.map fun id =>
    (id, if Cand.regular id ∈ cont then p.votesFor (.regular id) cont else 0)
  blanks := blanks
  exhausted := all.count (fun rs => readReproduction cont false [] rs == .exhausted) - blanks
  overvotes := all.count fun rs => readReproduction cont false [] rs == .overvote

/-- `reportRounds` on a profile of the ballots, with candidates `cands`. -/
def reportRounds (ids : List Nat) (cands : List Cand) (p : Profile) :
    Option (List PublishedRound) :=
  let p' := p.toReproduction
  let cont₁ := p'.initialCands cands
  let rounds := if (p'.majorityWinner cont₁).isSome then some [(cont₁, p')]
    else (p'.active cont₁).singlePathRounds cont₁
  let blanks := p.count fun rs => readReproduction cont₁ false [] rs == .exhausted
  rounds.map fun rs => rs.map fun (cont, q) => ofRound ids p blanks cont q

end Profile

open Profile

/-- `tabulate e` is `Profile.tabulate` on a profile of the ballots of `e`. -/
theorem tabulate_eq_profileTabulate {e : Election} {p : Profile} (h : p.IsProfileOf e.ballots) :
    tabulate e = p.tabulate e.cands := by
  unfold Alaska.tabulate Profile.tabulate
  dsimp only
  rw [h.initialCands, h.majorityWinner]
  cases Profile.majorityWinner (p.initialCands e.cands) p with
  | none => exact (h.active _).tabulateRounds _
  | some c => rfl

/-- `reproductionTabulate e` is `Profile.tabulate` on a profile of the ballots of `e` after
`Profile.toReproduction`. -/
theorem reproductionTabulate_eq_profileTabulate {e : Election} {p : Profile}
    (h : p.IsProfileOf e.ballots) : reproductionTabulate e = p.toReproduction.tabulate e.cands :=
  tabulate_eq_profileTabulate (e := { e with ballots := e.ballots.map Ballot.toReproduction })
    h.toReproduction

/-- `reportRounds ids e` is `Profile.reportRounds` on a profile of the ballots of `e`. -/
theorem reportRounds_eq_profileReportRounds (ids : List Nat) {e : Election} {p : Profile}
    (h : p.IsProfileOf e.ballots) : reportRounds ids e = p.reportRounds ids e.cands := by
  let e' : Election := { e with ballots := e.ballots.map Ballot.toReproduction }
  have h' : p.toReproduction.IsProfileOf e'.ballots := h.toReproduction
  have hblanks : ∀ cont o, e.ballots.countP (fun b => reproductionResultOf cont b == o) =
      p.count fun rs => readReproduction cont false [] rs == o :=
    fun cont o => h.countP fun rs => readReproduction cont false [] rs == o
  have hF : ∀ blanks cont bs (q : Profile), q.IsProfileOf bs →
      PublishedRound.ofRound ids e.ballots blanks cont bs = ofRound ids p blanks cont q := by
    intro blanks cont bs q hq
    simp only [PublishedRound.ofRound, Profile.ofRound, hq.votesFor, hblanks]
  unfold Alaska.reportRounds Profile.reportRounds
  simp only [hblanks]
  rw [show initialCands e' = p.toReproduction.initialCands e.cands from h'.initialCands,
    show majorityWinner (p.toReproduction.initialCands e.cands) e'.ballots =
      p.toReproduction.majorityWinner (p.toReproduction.initialCands e.cands) from
      h'.majorityWinner _]
  split
  · simp only [Option.map_some, List.map_cons, List.map_nil]
    rw [hF _ _ _ _ h']
  · exact IsProfileOf.singlePathRounds _ _ (hF _) _ (h'.active _)

end Alaska
