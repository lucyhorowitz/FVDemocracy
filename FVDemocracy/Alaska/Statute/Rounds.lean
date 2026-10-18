import FVDemocracy.Alaska.Statute.Tallies

namespace Alaska

/-- AS 15.15.350(d)(2): the possible results of one of the sequential rounds.
Each pair `(c, bs')` means that `c` may be defeated this round, and `bs'`
is the list of ballots remaining active after defeating `c`. `tabulateRounds` calls it only when
three or more candidates are continuing. -/
def singleRound (cont : List Cand) (bs : List Ballot) : List (Cand × List Ballot) :=
  match cont with
  | [] => []
  | [_] => []
  | _ =>
      let losers := cont.filter (fun c => votesFor c cont bs == lowestTally cont bs)
      losers.map fun c =>
        (c, bs.filter fun b => decide (¬ MeetsInactivityCondition (cont.erase c) b))

theorem singleRound_mono {cont : List Cand} {bs : List Ballot} {c : Cand} {bs' : List Ballot}
    (h : (c, bs') ∈ singleRound cont bs) : c ∈ cont := by
  unfold singleRound at h
  split at h
  · exact absurd h List.not_mem_nil
  · exact absurd h List.not_mem_nil
  · obtain ⟨d, hd, heq⟩ := List.mem_map.mp h
    cases heq
    exact (List.mem_filter.mp hd).1

/-- `(c, bs')` is an outcome of `singleRound` iff at least two candidates are continuing, `c` is
one of them with the fewest votes, and `bs'` is the ballots of `bs` that meet no inactivity
condition once `c` is defeated.

AS 15.15.350(d)(2) defeats a candidate only when more than two candidates are continuing
(`Round.CanDefeat` in `Spec.lean`); with two, (d)(1) elects the one with more votes instead.
`tabulateRounds` calls `singleRound` only with three or more continuing candidates. The
two-candidate case is an extension used by `recurseRounds`. -/
theorem singleRound_correct (cont : List Cand) (bs : List Ballot) (c : Cand) (bs' : List Ballot) :
    (c, bs') ∈ singleRound cont bs ↔
      cont.length ≥ 2 ∧ c ∈ cont ∧ votesFor c cont bs = lowestTally cont bs ∧
        bs' = bs.filter (fun b => ¬ MeetsInactivityCondition (cont.erase c) b) := by
  cases cont with
  | nil =>
      simp [singleRound]
  | cons c₁ cs =>
      cases cs with
      | nil =>
          simp [singleRound]
      | cons c₂ cs =>
          simp [singleRound]
          grind

theorem singleRound_nonempty {cont : List Cand} (bs : List Ballot) (hlen : cont.length ≥ 2) :
    singleRound cont bs ≠ [] := by
  have hne : cont ≠ [] := by
    rintro rfl
    simp at hlen
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ (loser_exists bs hne)
  simp only [losers, List.mem_filter, decide_eq_true_eq] at hc
  exact List.ne_nil_of_mem ((singleRound_correct cont bs c _).mpr ⟨hlen, hc.1, hc.2, rfl⟩)

/-- The ballots passed to the next round are the ballots of this round that are still active
once `c` is defeated. -/
theorem mem_singleRound_ballots_iff {cont : List Cand} {bs bs' : List Ballot} {c : Cand}
    (h : (c, bs') ∈ singleRound cont bs) (b : Ballot) :
    b ∈ bs' ↔ b ∈ bs ∧ ¬ MeetsInactivityCondition (cont.erase c) b := by
  obtain ⟨-, -, -, rfl⟩ := (singleRound_correct cont bs c bs').mp h
  simp

/-- No ballot enters the next round that was not in this round. -/
theorem singleRound_ballots_sublist {cont : List Cand} {bs bs' : List Ballot} {c : Cand}
    (h : (c, bs') ∈ singleRound cont bs) : bs'.Sublist bs := by
  obtain ⟨-, -, -, rfl⟩ := (singleRound_correct cont bs c bs').mp h
  exact List.filter_sublist

/-- The continuing candidates of the next round are those of this round with one candidate
removed. -/
theorem singleRound_cont_sublist {cont : List Cand} {bs bs' : List Ballot} {c : Cand}
    (h : (c, bs') ∈ singleRound cont bs) :
    (cont.erase c).Sublist cont ∧ (cont.erase c).length + 1 = cont.length := by
  have hc := singleRound_mono h
  have hpos : 0 < cont.length := List.length_pos_of_mem hc
  refine ⟨List.erase_sublist, ?_⟩
  rw [List.length_erase_of_mem hc]
  omega

/-- If the continuing candidates have no duplicates, then after defeating `c`, `c` is not
continuing, every other candidate still is, and there are still no duplicates. -/
theorem erase_cont_nodup {cont : List Cand} (hnd : cont.Nodup) (c : Cand) :
    (cont.erase c).Nodup ∧ ∀ d, d ∈ cont.erase c ↔ d ≠ c ∧ d ∈ cont :=
  ⟨hnd.erase c, fun _ => hnd.mem_erase_iff⟩

inductive RCVTree where
  | winner : Cand → RCVTree
  | branch : List (Cand × RCVTree) → RCVTree
deriving Repr

/-- AS 15.15.350(d)(1) in the last of the sequential rounds, with two continuing candidates: the
candidate with the greater number of votes is elected. Each pair `(d, t)` holds the candidate
`d` who is not elected and the result `t`. A tie, which AS 15.15.350(e)(3) sends to AS 15.15.460
and AS 15.20.430 — 15.20.530, gives both pairs. -/
def finalRound (c₁ c₂ : Cand) (bs : List Ballot) : RCVTree :=
  let v₁ := votesFor c₁ [c₁, c₂] bs
  let v₂ := votesFor c₂ [c₁, c₂] bs
  if v₂ < v₁ then .branch [(c₂, .winner c₁)]
  else if v₁ < v₂ then .branch [(c₁, .winner c₂)]
  else .branch [(c₁, .winner c₂), (c₂, .winner c₁)]

/-- The sequential rounds of AS 15.15.350(d)(1) and (d)(2), which `tabulate` runs only when no
candidate has a majority in the initial tabulation: with two or fewer continuing candidates the
final round is run by `finalRound`; otherwise a candidate with the fewest votes is defeated and a
new round begins. -/
def tabulateRounds (cont : List Cand) (bs : List Ballot) : RCVTree :=
  match cont with
  | [] => .branch []
  | [c] => .winner c
  | [c₁, c₂] => finalRound c₁ c₂ bs
  | c₁ :: c₂ :: c₃ :: cs =>
      let current := c₁ :: c₂ :: c₃ :: cs
      .branch ((singleRound current bs).attach.map fun ⟨(c, bs'), hx⟩ =>
        have : c ∈ current := singleRound_mono hx
        (c, tabulateRounds (current.erase c) bs'))
termination_by cont.length
decreasing_by
  exact List.length_erase_lt_of_mem this

/-- With two or more continuing candidates, each outcome of `singleRound` is followed by the
rounds on the remaining candidates. -/
theorem tabulateRounds_cons_cons (c₁ c₂ : Cand) (cs : List Cand) (bs : List Ballot) :
    tabulateRounds (c₁ :: c₂ :: cs) bs =
      .branch ((singleRound (c₁ :: c₂ :: cs) bs).map fun (c, bs') =>
        (c, tabulateRounds ((c₁ :: c₂ :: cs).erase c) bs')) := by
  match cs with
  | [] =>
    have h₂ : ∀ bs', tabulateRounds ([c₁, c₂].erase c₂) bs' = .winner c₁ := by
      intro bs'
      by_cases hc : c₁ = c₂ <;> simp [hc, tabulateRounds]
    rw [tabulateRounds]
    simp only [finalRound, singleRound, lowestTally, tallies]
    rcases Nat.lt_trichotomy (votesFor c₁ [c₁, c₂] bs) (votesFor c₂ [c₁, c₂] bs) with h | h | h
    · simp [h, Nat.not_lt_of_gt h, Nat.le_of_lt h, Nat.ne_of_gt h, tabulateRounds]
    · simp [h, tabulateRounds, h₂]
    · simp [h, Nat.min_def, Nat.not_le_of_gt h, Nat.ne_of_gt h, h₂]
  | c₃ :: cs =>
    rw [tabulateRounds]
    congr 1
    exact List.attach_map_val (f := fun (p : Cand × List Ballot) =>
      (p.1, tabulateRounds ((c₁ :: c₂ :: c₃ :: cs).erase p.1) p.2))

theorem tabulateRounds_result {cont : List Cand} (bs : List Ballot) (hcont : cont ≠ []) :
    ¬ tabulateRounds cont bs = RCVTree.branch [] := by
  match cont with
  | [] => contradiction
  | [c] => simp [tabulateRounds]
  | c₁ :: c₂ :: cs => simp [tabulateRounds_cons_cons, singleRound_nonempty]

theorem tabulateRounds_winner (cont : List Cand) (bs : List Ballot) (c : Cand) :
    tabulateRounds cont bs = RCVTree.winner c ↔ cont = [c] := by
  match cont with
  | [] => simp [tabulateRounds]
  | [c'] => simp [tabulateRounds]
  | c₁ :: c₂ :: cs => simp [tabulateRounds_cons_cons]

mutual
def RCVTree.winners : RCVTree → List Cand
  | .winner c => [c]
  | .branch children => winnersList children

def winnersList : List (Cand × RCVTree) → List Cand
  | [] => []
  | (_, t) :: rest => t.winners ++ winnersList rest
end

theorem winnersList_flatMap (children : List (Cand × RCVTree)) :
    winnersList children = children.flatMap (·.2.winners) := by
  induction children with
  | nil => simp [winnersList]
  | cons child children ih => simpa [winnersList]

theorem mem_winnersList_iff (children : List (Cand × RCVTree)) (c : Cand) :
    c ∈ winnersList children ↔ ∃ d t, (d, t) ∈ children ∧ c ∈ t.winners := by
  induction children with
  | nil => simp; exact List.count_eq_zero.mp rfl
  | cons child children ih => simp [winnersList]; grind

/-- `t.HasPath path c`: True iff following the branches of `t` labelled by the candidates in
`path`, in order, leads to the leaf `RCVTree.winner c`. -/
inductive RCVTree.HasPath : RCVTree → List Cand → Cand → Prop
  | winner (c : Cand) : HasPath (.winner c) [] c
  | branch (children : List (Cand × RCVTree)) (d : Cand) (t : RCVTree) (path : List Cand)
      (c : Cand) :
      (d, t) ∈ children → HasPath t path c → HasPath (.branch children) (d :: path) c

/-- The winners of a tree are the candidates at the ends of its paths. -/
theorem mem_winners_iff_hasPath : (t : RCVTree) → (c : Cand) →
    (c ∈ t.winners ↔ ∃ path, t.HasPath path c)
  | .winner c', c => by
      simp only [RCVTree.winners, List.mem_singleton]
      constructor
      · rintro rfl
        exact ⟨[], .winner c⟩
      · rintro ⟨path, h⟩
        cases h
        rfl
  | .branch children, c => by
      rw [RCVTree.winners, mem_winnersList_iff]
      constructor
      · rintro ⟨d, t, hdt, hc⟩
        obtain ⟨path, h⟩ := (mem_winners_iff_hasPath t c).mp hc
        exact ⟨d :: path, .branch children d t path c hdt h⟩
      · rintro ⟨path, h⟩
        cases h with
        | branch _ d t path _ hdt h =>
          exact ⟨d, t, hdt, (mem_winners_iff_hasPath t c).mpr ⟨path, h⟩⟩
termination_by t => t
decreasing_by
  all_goals
    have := List.sizeOf_lt_of_mem hdt
    simp_all
    omega

theorem RCVTree.hasPath_winner_iff (w : Cand) (path : List Cand) (c : Cand) :
    (RCVTree.winner w).HasPath path c ↔ path = [] ∧ c = w := by
  constructor
  · rintro ⟨⟩
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact .winner c

theorem RCVTree.hasPath_branch_iff (children : List (Cand × RCVTree)) (path : List Cand)
    (c : Cand) :
    (RCVTree.branch children).HasPath path c ↔
      ∃ d t path', path = d :: path' ∧ (d, t) ∈ children ∧ t.HasPath path' c := by
  constructor
  · rintro ⟨⟩
    next d t path' hdt h => exact ⟨d, t, path', rfl, hdt, h⟩
  · rintro ⟨d, t, path', rfl, hdt, h⟩
    exact .branch children d t path' c hdt h

theorem mem_winners_tabulateRounds_cons_cons (c₁ c₂ : Cand) (cs : List Cand) (bs : List Ballot)
    (c : Cand) :
    c ∈ (tabulateRounds (c₁ :: c₂ :: cs) bs).winners ↔
      ∃ d bs', (d, bs') ∈ singleRound (c₁ :: c₂ :: cs) bs ∧
        c ∈ (tabulateRounds ((c₁ :: c₂ :: cs).erase d) bs').winners := by
  rw [tabulateRounds_cons_cons, RCVTree.winners, mem_winnersList_iff]
  simp
  grind

theorem winners_tabulateRounds_singleton (c : Cand) (bs : List Ballot) :
    (tabulateRounds [c] bs).winners = [c] := by
  simp [tabulateRounds, RCVTree.winners]

theorem mem_of_mem_winners_tabulateRounds {cont : List Cand} {bs : List Ballot} {c : Cand}
    (h : c ∈ (tabulateRounds cont bs).winners) : c ∈ cont := by
  induction cont, bs using tabulateRounds.induct with
  | case1 bs => simp [tabulateRounds, RCVTree.winners, winnersList] at h
  | case2 bs c' => simpa [winners_tabulateRounds_singleton] using h
  | case3 bs c₁ c₂ =>
    rw [tabulateRounds, finalRound] at h
    split at h <;> (try split at h) <;> simp [RCVTree.winners, winnersList] at h <;> grind
  | case4 bs c₁ c₂ c₃ cs current ih =>
    obtain ⟨d, bs', hd, hc⟩ := (mem_winners_tabulateRounds_cons_cons c₁ c₂ (c₃ :: cs) bs c).mp h
    exact List.mem_of_mem_erase (ih d bs' hd hc)

theorem winners_tabulateRounds_ne_nil {cont : List Cand} (bs : List Ballot) (hcont : cont ≠ []) :
    (tabulateRounds cont bs).winners ≠ [] := by
  induction cont, bs using tabulateRounds.induct with
  | case1 bs => contradiction
  | case2 bs c' => simp [winners_tabulateRounds_singleton]
  | case3 bs c₁ c₂ =>
    rw [tabulateRounds, finalRound]
    split <;> (try split) <;> simp [RCVTree.winners, winnersList]
  | case4 bs c₁ c₂ c₃ cs current ih =>
    obtain ⟨⟨d, bs'⟩, hd⟩ :=
      List.exists_mem_of_ne_nil _ (singleRound_nonempty (cont := c₁ :: c₂ :: c₃ :: cs) bs (by simp))
    have hne : (c₁ :: c₂ :: c₃ :: cs).erase d ≠ [] := by
      intro h0
      have := List.length_erase_of_mem (singleRound_mono hd)
      simp_all
    obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ (ih d bs' hd hne)
    exact List.ne_nil_of_mem
      ((mem_winners_tabulateRounds_cons_cons c₁ c₂ (c₃ :: cs) bs w).mpr ⟨d, bs', hd, hw⟩)

end Alaska
