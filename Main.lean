import FVDemocracy.Alaska.Statute.Tabulate
import FVDemocracy.Alaska.Reproduction.Tabulate
import FVDemocracy.Alaska.Reproduction.PublishedReports
import FVDemocracy.Alaska.ParseCVR.Parse
import FVDemocracy.Alaska.Duplicates
import FVDemocracy.Alaska.ProfileData

/-!
# Tabulating the ranked-choice contests of a CVR export

`lake exe alaska <export-dir> [contest-id ...]` runs `tabulate` on the given
contests of the CVR export in `<export-dir>`, or on every ranked-choice
contest when no id is given, and prints the rounds.
`lake exe alaska <export-dir> --list` lists the ranked-choice contests.
`lake exe alaska <export-dir> --reproduce <election>` runs `reproductionTabulate` on the contests of
`publishedReports` for `<election>` and compares each round with the published report.
`lake exe alaska <export-dir> --dropduplicates [contest-id ...]` tabulates the given contests, or
every ranked-choice contest, with `tabulate`, with `tabulate` after `Election.dropDuplicates`, with
`reproductionTabulate`, with `truncateTabulate` and with `truncateTabulate` after
`Election.dropDuplicates`, and prints the rounds of the five side by side.
`lake exe alaska <export-dir> --results <election> <out-dir>` writes, for each ranked-choice
contest, the data file of the profile of its ballots (`writeProfileData`) and a Lean file with
theorems giving the results of `tabulate`, `reproductionTabulate` and, for the contests of
`publishedReports`, `reportRounds` (`resultSource`), after checking that the profile functions give
the results of these on the ballots.

Ballots use each session's current state with ambiguous marks dropped. A card
contest with the `InvalidContest` outstack condition is left out. The candidates
of a contest are its regular candidates in `CandidateManifest.json` followed by
the distinct write-ins appearing on its ballots.
-/

open Alaska Alaska.CVRExport

def padLeft (s : String) (width : Nat) : String :=
  "".pushn ' ' (width - s.length) ++ s

def padRight (s : String) (width : Nat) : String :=
  s.pushn ' ' (width - s.length)

/-- `n` with commas between groups of three digits. -/
def formatNat (n : Nat) : String :=
  if n < 1000 then toString n
  else
    let r := toString (n % 1000)
    formatNat (n / 1000) ++ "," ++ "".pushn '0' (3 - r.length) ++ r
termination_by n
decreasing_by omega

/-- `num / den` as a percentage rounded to two decimal places. -/
def formatPercent (num den : Nat) : String :=
  if den = 0 then "-"
  else
    let hundredths := (num * 10000 + den / 2) / den
    let r := toString (hundredths % 100)
    s!"{hundredths / 100}.{"".pushn '0' (2 - r.length)}{r}%"

/-- The tallies of `cont` on `bs`, highest first, followed by the numbers of
active and inactive ballots out of `total`. -/
def printTallies (name : Cand → String) (indent : String) (total : Nat) (cont : List Cand)
    (bs : List Ballot) : IO Unit := do
  let active := numActive cont bs
  let rows := (candTallies cont bs).mergeSort fun a b => b.2 ≤ a.2
  let nameWidth := (rows.map fun (c, _) => (name c).length).foldl max 0
  let voteWidth := (rows.map fun (_, v) => (formatNat v).length).foldl max 0
  for (c, v) in rows do
    IO.println s!"{indent}  {padRight (name c) nameWidth}  {padLeft (formatNat v) voteWidth}  \
      {padLeft (formatPercent v active) 7}"
  IO.println s!"{indent}  active {formatNat active}, inactive {formatNat (total - active)}"

/-- Prints the rounds `tabulateRounds cont bs` runs, starting at round number
`round`, following every branch of a tie, and returns the winners in the order
of `RCVTree.winners`. -/
partial def printRounds (name : Cand → String) (total : Nat) (indent : String) (round : Nat)
    (cont : List Cand) (bs : List Ballot) : IO (List Cand) := do
  match cont with
  | [] =>
      IO.println s!"{indent}no continuing candidates"
      pure []
  | [c] =>
      IO.println s!"{indent}{name c} is the only continuing candidate and is elected"
      pure [c]
  | [c₁, c₂] =>
      IO.println s!"{indent}Round {round} (final)"
      printTallies name indent total cont bs
      let winners := (finalRound c₁ c₂ bs).winners
      match winners with
      | [w] => IO.println s!"{indent}  {name w} is elected"
      | _ => IO.println s!"{indent}  tie between {name c₁} and {name c₂}, resolved under \
          AS 15.15.460"
      pure winners
  | _ =>
      IO.println s!"{indent}Round {round}"
      printTallies name indent total cont bs
      match singleRound cont bs with
      | [(d, bs')] =>
          IO.println s!"{indent}  {name d} is defeated"
          IO.println ""
          printRounds name total indent (round + 1) (cont.erase d) bs'
      | children =>
          IO.println s!"{indent}  tie for the fewest votes between \
            {", ".intercalate (children.map (name ·.1))}"
          let mut winners := []
          for (d, bs') in children do
            IO.println ""
            IO.println s!"{indent}  if {name d} is defeated:"
            winners := winners ++
              (← printRounds name total (indent ++ "    ") (round + 1) (cont.erase d) bs')
          pure winners

/-- The name of `c` in `CandidateManifest.json`. -/
def candName (candidates : Array Candidate) : Cand → String
  | .regular id =>
      (candidates.find? (·.id == id)).map (·.description) |>.getD s!"candidate {id}"
  | .writeIn 0 => "Write-in"
  | .writeIn i => s!"Write-in {i}"

/-- The election of `contest` on `ballots`: its candidates are the regular candidates of
`contest` followed by the distinct write-ins marked on `ballots`. -/
def contestElection (candidates : Array Candidate) (contest : Contest) (ballots : List Ballot) :
    IO Election := do
  let regularCands := candidates.toList.filterMap fun c =>
    if c.contestId == contest.id && c.type == .regular then some (Cand.regular c.id) else none
  let writeInCands := (ballots.flatMap fun b => b.ranks.flatten.filter IsWriteIn).eraseDups
  let cands := regularCands ++ writeInCands
  let unlisted := (ballots.flatMap fun b => b.ranks.flatten).eraseDups.filter (· ∉ cands)
  unless unlisted.isEmpty do
    IO.println s!"marked but not candidates of this contest: \
      {", ".intercalate (unlisted.map (candName candidates))}"
  let some e := if h : cands.Nodup then some { ballots, cands, cands_unique := h : Election }
      else none
    | throw (IO.userError s!"contest {contest.id}: candidate list has duplicates")
  pure e

/-- Prints the tabulation of `contest` on `ballots`, failing if the winners it
prints differ from those of `tabulate`. -/
def printContest (candidates : Array Candidate) (contest : Contest) (ballots : List Ballot) :
    IO Unit := do
  let title := s!"{contest.description} (contest {contest.id})"
  IO.println title
  IO.println ("".pushn '=' title.length)
  let name := candName candidates
  let e ← contestElection candidates contest ballots
  let cands := e.cands
  let qualify := decide (WriteInsQualify cands ballots recountMargin)
  IO.println s!"{formatNat ballots.length} ballots; {formatNat (writeInTotal cands ballots)} \
    write-in votes, which {if qualify then "qualify" else "do not qualify"} under AS 15.15.365(a)"
  IO.println ""
  let cont₁ := initialCands e
  let winners ← match majorityWinner cont₁ ballots with
    | some c => do
        IO.println "Round 1"
        printTallies name "" ballots.length cont₁ ballots
        IO.println s!"  {name c} has a majority and is elected"
        pure [c]
    | none =>
        printRounds name ballots.length "" 1 cont₁
          (ballots.filter fun b => decide (¬ MeetsInactivityCondition cont₁ b))
  unless winners == (tabulate e).winners do
    throw (IO.userError s!"contest {contest.id}: printed winners differ from tabulate")

/-- Compares the rounds of `reproductionTabulate` on `contest` and `ballots` with the published
`report`, and prints a line for the contest and one for each number that differs. Returns whether
all of them agree. -/
def checkReport (candidates : Array Candidate) (contest : Contest) (report : PublishedReport)
    (ballots : List Ballot) : IO Bool := do
  let name := candName candidates
  let e ← contestElection candidates contest ballots
  let e' : Election := { e with ballots := e.ballots.map Ballot.toReproduction }
  let cont₁ := initialCands e'
  let rounds := if (majorityWinner cont₁ e'.ballots).isSome then some [(cont₁, e'.ballots)]
    else singlePathRounds cont₁
      (e'.ballots.filter fun b => decide (¬ MeetsInactivityCondition cont₁ b))
  let some rounds := rounds
    | IO.println s!"{contest.description}: a round has a tie for the fewest votes"
      pure false
  let count (cont : List Cand) (o : ReproductionResult) : Nat :=
    ballots.countP fun b => reproductionResultOf cont b == o
  let blanks := count cont₁ .exhausted
  let mut diffs : Array String := #[]
  if rounds.length != report.rounds.length then
    diffs := diffs.push s!"{rounds.length} rounds, published {report.rounds.length}"
  let mut k := 1
  for ((cont, bs), published) in rounds.zip report.rounds do
    for c in cont do
      unless published.votes.any (fun (id, _) => Cand.regular id == c) do
        diffs := diffs.push s!"round {k}: {name c} is continuing but not in the report"
    for (id, v) in published.votes do
      let c := Cand.regular id
      let votes := if c ∈ cont then votesFor c cont bs else 0
      if votes != v then
        diffs := diffs.push s!"round {k}: {name c} {votes}, published {v}"
    let buckets := [("blanks", blanks, published.blanks),
      ("exhausted", count cont .exhausted - blanks, published.exhausted),
      ("overvotes", count cont .overvote, published.overvotes)]
    for (bucket, n, v) in buckets do
      if n != v then
        diffs := diffs.push s!"round {k}: {bucket} {n}, published {v}"
    k := k + 1
  let winners := ", ".intercalate ((reproductionTabulate e).winners.map name)
  if diffs.isEmpty then
    IO.println s!"{contest.description}: {formatNat ballots.length} ballots, \
      {rounds.length} rounds, {winners} elected; matches the published report"
  else
    IO.println s!"{contest.description}: differs from the published report"
    for d in diffs do
      IO.println s!"  {d}"
  pure diffs.isEmpty

/-- The rounds of `tabulate e` when each round defeats a single candidate, as in
`singlePathRounds`, or the first round alone if a candidate has a majority in it. -/
def tabulateRoundsOf (e : Election) : Option (List (List Cand × List Ballot)) :=
  let cont₁ := initialCands e
  if (majorityWinner cont₁ e.ballots).isSome then some [(cont₁, e.ballots)]
  else singlePathRounds cont₁
    (e.ballots.filter fun b => decide (¬ MeetsInactivityCondition cont₁ b))

/-- Prints the rounds of `contest` on `ballots` under `tabulate`, under `tabulate` after
`Election.dropDuplicates`, under `reproductionTabulate`, under `truncateTabulate` and under
`truncateTabulate` after `Election.dropDuplicates`, side by side: in each round the votes of each
continuing candidate and the number of inactive ballots, then the winners. -/
def compareDuplicates (candidates : Array Candidate) (contest : Contest) (ballots : List Ballot) :
    IO Unit := do
  let title := s!"{contest.description} (contest {contest.id})"
  IO.println title
  IO.println ("".pushn '=' title.length)
  let name := candName candidates
  let e ← contestElection candidates contest ballots
  let dups := ballots.filter fun b => decide b.HasDuplicateRanking
  IO.println s!"{formatNat ballots.length} ballots, {formatNat dups.length} with a duplicate \
    ranking, {formatNat (dups.countP fun b => decide b.HasOvervote)} of them with an overvote"
  let models : List (String × Election) := [("statute", e),
    ("duplicates removed", e.dropDuplicates),
    ("reproduction", { e with ballots := e.ballots.map Ballot.toReproduction }),
    ("repro, dups kept", { e with ballots := e.ballots.map Ballot.truncateAtOvervote }),
    ("repro, dups dropped", { e.dropDuplicates with
      ballots := e.dropDuplicates.ballots.map Ballot.truncateAtOvervote })]
  let rounds := models.map fun (_, e') => (tabulateRoundsOf e').getD []
  for ((label, _), rs) in models.zip rounds do
    if rs.isEmpty then
      IO.println s!"{label}: a round has a tie for the fewest votes"
  let total := ballots.length
  let numRounds := (rounds.map (·.length)).foldl max 0
  let rows : List (String × List String) := (List.range numRounds).flatMap
    fun k =>
      let cs := e.cands.filter fun c =>
        rounds.any fun rs => (rs[k]?.map fun (cont, _) => decide (c ∈ cont)).getD false
      let cell (f : List Cand → List Ballot → Option Nat) : List String := rounds.map fun rs =>
        match rs[k]? with
        | some (cont, bs) => (f cont bs).elim "-" formatNat
        | none => ""
      (s!"Round {k + 1}", rounds.map fun _ => "") ::
        cs.map (fun c => ("  " ++ name c,
          cell fun cont bs => if c ∈ cont then some (votesFor c cont bs) else none)) ++
        [("  inactive", cell fun cont bs => some (total - numActive cont bs))]
  let rows := rows ++ [("Elected", models.map fun (_, e') =>
    ", ".intercalate ((tabulate e').winners.map name))]
  let labelWidth := (rows.map (·.1.length)).foldl max 0
  let widths := models.zipIdx.map fun ((label, _), i) =>
    (rows.map fun (_, cells) => (cells[i]?.getD "").length).foldl max label.length
  IO.println ""
  IO.println <| "".pushn ' ' labelWidth ++ String.join
    ((models.zip widths).map fun ((label, _), w) => "  " ++ padLeft label w)
  for (label, cells) in rows do
    IO.println <| padRight label labelWidth ++ String.join
      ((cells.zip widths).map fun (cell, w) => "  " ++ padLeft cell w)

/-- The candidate `c` as Lean source. -/
def candSource : Cand → String
  | .regular id => s!".regular {id}"
  | .writeIn i => s!".writeIn {i}"

/-- The tree `t` as Lean source. -/
partial def treeSource : RCVTree → String
  | .winner c => s!".winner ({candSource c})"
  | .branch xs =>
    ".branch [" ++ ", ".intercalate (xs.map fun (c, t) => s!"({candSource c}, {treeSource t})") ++ "]"

/-- The candidates defeated in turn along `t` and the candidate elected, when no round of `t` has
a tie. -/
partial def treePath : RCVTree → Option (List Cand × Cand)
  | .winner c => some ([], c)
  | .branch [(d, t)] => (treePath t).map fun (ds, c) => (d :: ds, c)
  | .branch _ => none

/-- A candidate name `Last, First` as `First Last`, for each name of a ticket `A / B`. -/
def displayName (name : String) : String :=
  " / ".intercalate ((name.splitOn " / ").map fun n =>
    match n.splitOn ", " with
    | last :: first :: rest => " ".intercalate ((first :: rest) ++ [last])
    | _ => n)

/-- The words of `text` in lines of at most `width` characters, the first starting with `first`
and the others with `indent`. -/
def wrap (width : Nat) (first indent text : String) : String :=
  let words := (text.splitOn " ").filter (· != "")
  let (lines, line) := words.foldl (init := (#[], first)) fun (lines, line) w =>
    if line.length + 1 + w.length > width && line.length > indent.length then
      (lines.push line, indent ++ w)
    else if line == first then (lines, line ++ w)
    else (lines, line ++ " " ++ w)
  "\n".intercalate (lines.push line).toList

/-- What the tree `t` of `tab` says, as a sentence. -/
def treeWords (name : Cand → String) (tab : String) (t : RCVTree) : String :=
  match treePath t with
  | some ([], c) => s!"`{tab}` elects {name c} in round 1."
  | some ([d], c) => s!"`{tab}` elects {name c} over {name d}."
  | some ([d, d'], c) => s!"`{tab}` defeats {name d} and elects {name c} over {name d'}."
  | some (ds, c) =>
    s!"`{tab}` defeats {", then ".intercalate (ds.dropLast.map name)}, and elects {name c} over \
      {(ds.getLast?.map name).getD ""}."
  | none => s!"`{tab}` has a tie for the fewest votes in some round; its winners are \
      {", ".intercalate (t.winners.map name)}."

/-- A Lean file for `contest` with the ballots `ballots`, whose profile `p` is in the data file
`dataFile`: the candidates `cands`, the profile `profile` read by `profile_data%`, and theorems
giving `tabulate`, `reproductionTabulate` and, when `report` is given, `reportRounds` on every
election with these candidates and ballots with the rankings of the profile. Fails unless the
profile functions give the results of `tabulate`, `reproductionTabulate` and `reportRounds`. -/
def resultSource (command electionTitle ns : String) (dir dataFile : System.FilePath)
    (candidates : Array Candidate) (contest : Contest) (report : Option PublishedReport)
    (ballots : List Ballot) (p : Profile) : IO String := do
  let name (c : Cand) := displayName (candName candidates c)
  let e ← contestElection candidates contest ballots
  let fail (msg : String) : IO Unit := throw (IO.userError s!"contest {contest.id}: {msg}")
  let t := tabulate e
  let t' := reproductionTabulate e
  unless t == p.tabulate e.cands do fail "Profile.tabulate differs from tabulate"
  unless t' == p.toReproduction.tabulate e.cands do
    fail "Profile.tabulate after Profile.toReproduction differs from reproductionTabulate"
  let ids := report.map fun r => (r.rounds.head?.map (·.votes.map (·.1))).getD []
  if let (some r, some ids) := (report, ids) then
    unless reportRounds ids e == some r.rounds do
      fail "reportRounds differs from the published report"
    unless reportRounds ids e == p.reportRounds ids e.cands do
      fail "Profile.reportRounds differs from reportRounds"
  let mut out := "import FVDemocracy.Alaska.ProfileData\n\n/-!\n"
  out := out ++ s!"# {electionTitle}: {contest.description}\n\n"
  out := out ++ wrap 100 "" "" s!"Contest {contest.id} of the CVR export `{dir}`. `profile` is \
    `Profile.ofBallots` of its {formatNat ballots.length} ballots as `contestBallots` reads them, \
    in {formatNat p.length} entries. `profile_data%` reads it from `{dataFile}`, and writes that \
    file from the export first if it is missing. `cands` are the regular candidates of the \
    contest followed by the write-ins marked on its ballots:" ++ "\n\n"
  for c in e.cands do
    out := out ++ s!"* `{candSource c}`: {name c}\n"
  out := out ++ "\nFor every election `e` with the candidates `cands` whose ballots have the \
    rankings of `profile`:\n\n"
  out := out ++ wrap 100 "* " "  " s!"`tabulate_eq`: {treeWords name "tabulate" t}" ++ "\n"
  out := out ++ wrap 100 "* " "  "
    s!"`reproductionTabulate_eq`: {treeWords name "reproductionTabulate" t'}" ++ "\n"
  if report.isSome then
    out := out ++ "* `reportRounds_eq`: the rounds of `reproductionTabulate` are those of the \
      published report\n  (`publishedReports`).\n"
  out := out ++ s!"\nGenerated by `{command}`.\n-/\n\n"
  out := out ++ s!"namespace {ns}\n\nopen Alaska\n\n"
  out := out ++ s!"def cands : List Cand := [{", ".intercalate (e.cands.map candSource)}]\n"
  out := out ++ s!"\ndef profile : Profile :=\n  \
    profile_data% \"{dir}\" {contest.id}\n    \"{dataFile}\"\n"
  let hyps := "(e : Election) (hc : e.cands = cands)\n    (hb : profile.IsProfileOf e.ballots)"
  out := out ++ s!"
unseal Profile.tabulateRounds in
theorem profile_tabulate :
    profile.tabulate cands =
      {treeSource t} := by
  decide +kernel

unseal Profile.tabulateRounds in
theorem profile_toReproduction_tabulate :
    profile.toReproduction.tabulate cands =
      {treeSource t'} := by
  decide +kernel

{wrap 100 "/-- " "" s!"{treeWords name "tabulate" t} -/"}
theorem tabulate_eq {hyps} :
    tabulate e =
      {treeSource t} := by
  rw [tabulate_eq_profileTabulate hb, hc, profile_tabulate]

{wrap 100 "/-- " "" s!"{treeWords name "reproductionTabulate" t'} -/"}
theorem reproductionTabulate_eq {hyps} :
    reproductionTabulate e =
      {treeSource t'} := by
  rw [reproductionTabulate_eq_profileTabulate hb, hc, profile_toReproduction_tabulate]
"
  if let some ids := ids then
    let election := (report.map (·.election)).getD ""
    out := out ++ s!"
/-- The rounds of the published report. -/
def publishedRounds : Option (List PublishedRound) :=
  (publishedReports.find? fun r => r.election == \"{election}\" && r.contestId == {contest.id}).map
    (·.rounds)

unseal Profile.singlePathRounds in
theorem profile_reportRounds :
    profile.reportRounds {ids} cands = publishedRounds := by
  decide +kernel

/-- The rounds of `reproductionTabulate` are those of the published report. -/
theorem reportRounds_eq {hyps} :
    reportRounds {ids} e = publishedRounds := by
  rw [reportRounds_eq_profileReportRounds _ hb, hc, profile_reportRounds]
"
  out := out ++ s!"\nend {ns}\n"
  pure out

/-- Writes, for each ranked-choice contest `contests` of the export `dir` of `election`, the data
file `outDir/data/<Election>/<Contest>.json` of `Profile.ofBallots` of its ballots and a Lean file
`outDir/<Election>/<Contest>.lean` (`resultSource`), and a file `outDir/<Election>.lean` that
imports the Lean files. Module and namespace names follow the path of `outDir`, with
`FVDemocracy.` dropped from the namespace. -/
def writeResults (dir : System.FilePath) (election : String) (outDir : System.FilePath)
    (contests : Array Contest) : IO Unit := do
  let (year, kind) := match election.splitOn "-" with
    | [y, k] => (y, k)
    | _ => (election, "")
  let electionName := capitalize kind ++ year
  let electionTitle := s!"{year} {kind} election"
  let modulePrefix := ".".intercalate (outDir.components.filter (· != ""))
  let nsPrefix := (modulePrefix.dropPrefix "FVDemocracy.").toString
  let command := s!"lake exe alaska {dir} --results {election} {outDir}"
  let candidates ← readJsonFile (Manifest Candidate) (dir / "CandidateManifest.json")
  let ballots ← contestBallots dir contests
  let dataDir := outDir / "data" / electionName
  IO.FS.createDirAll (outDir / electionName)
  IO.FS.createDirAll dataDir
  let mut imports : Array String := #[]
  for (contest, bs) in contests.toList.zip ballots.toList do
    let cname := contestName contest.description
    let report := publishedReports.find? fun r =>
      r.election == election && r.contestId == contest.id
    let p := Profile.ofBallots bs.toList
    let dataFile := dataDir / profileFileName contest
    writeProfileData dataFile
      { contestId := contest.id, description := contest.description, profile := p }
    let src ← resultSource command electionTitle s!"{nsPrefix}.{electionName}.{cname}" dir
      dataFile candidates.list contest report bs.toList p
    IO.FS.writeFile (outDir / electionName / s!"{cname}.lean") src
    IO.println s!"{contest.description}: {electionName}/{cname}.lean"
    imports := imports.push s!"import {modulePrefix}.{electionName}.{cname}"
  IO.FS.writeFile (outDir / s!"{electionName}.lean")
    ("\n".intercalate imports.toList ++ "\n")

def usage : String :=
  "usage: lake exe alaska <export-dir> [--list | --reproduce <election> | \
    --results <election> <out-dir> | [--dropduplicates] contest-id ...]"

def main (args : List String) : IO UInt32 := do
  let dir :: rest := args
    | IO.eprintln usage; pure 1
  let dir : System.FilePath := dir
  let contests ← readJsonFile (Manifest Contest) (dir / "ContestManifest.json")
  let rcv := contests.list.filter (·.numOfRanks > 0)
  if rest == ["--list"] then
    for c in rcv do
      IO.println s!"{padLeft (toString c.id) 4}  {c.description}"
    return 0
  if let ["--reproduce", election] := rest then
    let reports := publishedReports.filter (·.election == election)
    if reports.isEmpty then
      throw (IO.userError s!"no published reports for {election}")
    let selected ← reports.toArray.mapM fun r => do
      let some c := rcv.find? (·.id == r.contestId)
        | throw (IO.userError s!"no ranked-choice contest with id {r.contestId}")
      pure c
    let candidates ← readJsonFile (Manifest Candidate) (dir / "CandidateManifest.json")
    let conditions ←
      readJsonFile (Manifest OutstackCondition) (dir / "OutstackConditionManifest.json")
    let ballots ← readBallots dir selected (notInvalidContest conditions.list) notAmbiguous
    let mut ok := true
    for ((report, contest), bs) in (reports.zip selected.toList).zip ballots.toList do
      ok := (← checkReport candidates.list contest report bs.toList) && ok
    return if ok then 0 else 1
  if let ["--results", election, outDir] := rest then
    writeResults dir election outDir rcv
    return 0
  let (dropDuplicates, rest) := match rest with
    | "--dropduplicates" :: ids => (true, ids)
    | _ => (false, rest)
  let selected ← if rest.isEmpty then pure rcv else rest.toArray.mapM fun arg => do
    let some id := arg.toNat? | throw (IO.userError s!"not a contest id: {arg}\n{usage}")
    let some c := rcv.find? (·.id == id)
      | throw (IO.userError s!"no ranked-choice contest with id {id}")
    pure c
  let candidates ← readJsonFile (Manifest Candidate) (dir / "CandidateManifest.json")
  let conditions ←
    readJsonFile (Manifest OutstackCondition) (dir / "OutstackConditionManifest.json")
  let ballots ← readBallots dir selected (notInvalidContest conditions.list) notAmbiguous
  for h : k in [0:selected.size] do
    if k > 0 then IO.println ""
    if dropDuplicates then compareDuplicates candidates.list selected[k] (ballots[k]!).toList
    else printContest candidates.list selected[k] (ballots[k]!).toList
  return 0
