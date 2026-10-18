import FVDemocracy.Alaska.Statute.Tallies

namespace Alaska

/-- AS 15.20.450: … less than .5 percent of the total number of votes cast for
the two candidates … -/
def recountMargin : Rat := { num := 1, den := 200 }

def writeIns (cands : List Cand) : List Cand :=
  (cands.filter (IsWriteIn)).eraseDups

def regulars (cands : List Cand) : List Cand :=
  (cands.filter (¬ IsWriteIn ·)).eraseDups

theorem mem_of_mem_regulars {cands : List Cand} {c : Cand} (h : c ∈ regulars cands) :
    c ∈ cands :=
  (List.mem_filter.mp (List.mem_of_mem_eraseDups h)).1

theorem nodup_regulars (cands : List Cand) : (regulars cands).Nodup :=
  List.nodup_eraseDups _

/-- AS 15.15.365(a): "the aggregate of all votes cast for all write-in candidates for the
particular office". The votes of each write-in candidate are counted with every candidate of
`cands` continuing, and `initialCands` passes all the candidates of the election. -/
def writeInTotal (cands : List Cand) (bs : List Ballot) : Nat :=
  ((cands.filter IsWriteIn).map fun c => votesFor c cands bs).sum

/-- A write-in candidate receives no more votes than all write-in candidates together. -/
theorem votesFor_le_writeInTotal {cands : List Cand} {c : Cand} (bs : List Ballot)
    (hc : c ∈ cands) (hw : IsWriteIn c) : votesFor c cands bs ≤ writeInTotal cands bs :=
  List.le_sum_of_mem (List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨hc, by simpa using hw⟩, rfl⟩)

/-- AS 15.15.365(a): the aggregate `W` of the votes for all write-in candidates is

* (1) "the highest number of votes received by any candidate": no candidate has more votes than
  `W`; or
* (2) "the second highest number of votes received by any candidate": some candidate `c` has more
  votes than `W`, and every candidate with more votes than `W` has as many as `c`. Also, "the
  difference between the total number of votes received by the candidate having the highest
  number of votes", `c`, "and the aggregate of all votes cast for all write-in candidates" is less
  than the fraction `margin` of their sum.

The votes a candidate receives are counted with every candidate of `cands` continuing, and
`initialCands` passes all the candidates of the election. If two candidates tie for the highest
number of votes, `W` can be the second highest.
-/
def WriteInsQualify (cands : List Cand) (bs : List Ballot) (margin : Rat) : Prop :=
  let W := writeInTotal cands bs
  (∀ c ∈ cands, votesFor c cands bs ≤ W) ∨
    ∃ c ∈ cands, W < votesFor c cands bs ∧
      (∀ c' ∈ cands, W < votesFor c' cands bs → votesFor c' cands bs = votesFor c cands bs) ∧
      ((votesFor c cands bs : Int) - W) * margin.den <
        margin.num * ((votesFor c cands bs : Int) + W)

instance (cands : List Cand) (bs : List Ballot) (margin : Rat) :
    Decidable (WriteInsQualify cands bs margin) := by
  unfold WriteInsQualify
  infer_instance

theorem not_isWriteIn_of_mem_regulars {cands : List Cand} {c : Cand} (h : c ∈ regulars cands) :
    ¬ IsWriteIn c :=
  of_decide_eq_true (List.mem_filter.mp (List.mem_of_mem_eraseDups h)).2

/-- The continuing candidates of the initial tabulation: the write-in candidates are removed
unless the write-ins qualify under AS 15.15.365(a). -/
def initialCands (e : Election) : List Cand :=
  if WriteInsQualify e.cands e.ballots recountMargin then e.cands else regulars e.cands

end Alaska
