import Lean.Elab.Term
import FVDemocracy.Alaska.Profile
import FVDemocracy.Alaska.ParseCVR.ParseProofs

/-!
# Profile data files

A JSON data file holds the profile of a ranked-choice contest of a CVR export, and `profile_data%`
reads it while Lean elaborates a result file. The file has the contest's id, its description and
`Profile.ofBallots` of the contest's ballots as `contestBallots` reads them. It writes a regular
candidate as its number, the write-in on line `i` as `{"writeIn": i}`, and an entry of the profile
as `[rankings, number of ballots]`.

* `fromJson_toJson_profileData`: decoding an encoded `ProfileData` gives it back.
* `profile_data% "<export dir>" <contest id> "<data file>"` elaborates to the profile of the data
  file, with both paths relative to the package root. If the file is missing, it first writes the
  data file of every ranked-choice contest of the export that has none (`writeMissingProfiles`).
-/

open Lean

namespace Alaska

open CVRExport

instance : ToJson Cand where
  toJson
    | .regular id => toJson id
    | .writeIn i => Json.mkObj [("writeIn", toJson i)]

instance : FromJson Cand where
  fromJson? j := match j.getObjValAs? Nat "writeIn" with
    | .ok i => pure (.writeIn i)
    | .error _ => .regular <$> fromJson? j

/-- A profile data file: the profile `profile` of the ballots of contest `contestId`, whose
description in the CVR export is `description`. -/
structure ProfileData where
  contestId : Nat
  description : String
  profile : Profile

instance : ToJson ProfileData where
  toJson d := Json.mkObj [
    ("contestId", toJson d.contestId), ("description", toJson d.description),
    ("profile", toJson d.profile)]

instance : FromJson ProfileData where
  fromJson? j := do
    let contestId ← j.getObjValAs? Nat "contestId"
    let description ← j.getObjValAs? String "description"
    let profile ← j.getObjValAs? Profile "profile"
    pure { contestId, description, profile }

/-! ## Round trips -/

theorem fromJson_toJson_cand (c : Cand) : fromJson? (toJson c) = Except.ok c := by
  cases c with
  | regular id => rfl
  | writeIn i =>
    simp (disch := simp only [List.map_cons, List.map_nil]; decide)
      [instToJsonCand, instFromJsonCand, Json.getObjValAs?, getObjValD_mkObj, fromJson_toJson_nat]
    rfl

theorem fromJson_toJson_list {α : Type} [FromJson α] [ToJson α]
    (h : ∀ x : α, fromJson? (toJson x) = Except.ok x) (xs : List α) :
    fromJson? (toJson xs) = Except.ok xs := by
  show (fromJson? (toJson xs.toArray) : Except String (Array α)).map Array.toList = _
  rw [fromJson_toJson_array h]
  rfl

theorem fromJson_toJson_prod {α β : Type} [FromJson α] [ToJson α] [FromJson β] [ToJson β]
    (ha : ∀ x : α, fromJson? (toJson x) = Except.ok x)
    (hb : ∀ x : β, fromJson? (toJson x) = Except.ok x) (x : α × β) :
    fromJson? (toJson x) = Except.ok x := by
  obtain ⟨a, b⟩ := x
  show (do
    let ⟨a'⟩ : ULift.{0} α := ← (fromJson? (toJson a)).map ULift.up
    let ⟨b'⟩ : ULift.{0} β := ← (fromJson? (toJson b)).map ULift.up
    return (a', b') : Except String (α × β)) = _
  rw [ha, hb]
  rfl

theorem fromJson_toJson_profile (p : Profile) : fromJson? (toJson p) = Except.ok p :=
  fromJson_toJson_list (fromJson_toJson_prod
    (fromJson_toJson_list (fromJson_toJson_list fromJson_toJson_cand)) fromJson_toJson_nat) p

theorem fromJson_toJson_profileData (d : ProfileData) : fromJson? (toJson d) = Except.ok d := by
  simp (disch := simp only [List.map_cons, List.map_nil]; decide)
    [instToJsonProfileData, instFromJsonProfileData, Json.getObjValAs?, getObjValD_mkObj,
      List.lookup_cons, fromJson_toJson_nat, fromJson_toJson_string, fromJson_toJson_profile,
      except_ok_bind]
  rfl

/-! ## Reading and writing data files -/

/-- The data file text of `d`: the JSON of `toJson d`, with each entry of the profile on its own
line. -/
def ProfileData.render (d : ProfileData) : String :=
  s!"\{\"contestId\": {d.contestId},\n \"description\": {(toJson d.description).compress},\n \
    \"profile\": [\n" ++
  ",\n".intercalate (d.profile.map fun x => "  " ++ (toJson x).pretty 1000000) ++ "]}\n"

/-- Writes `d` to the data file `path`, through a temporary file that then replaces `path`. -/
def writeProfileData (path : System.FilePath) (d : ProfileData) : IO Unit := do
  let tmp := path.addExtension "tmp"
  IO.FS.writeFile tmp d.render
  IO.FS.rename tmp path

/-- `s` with the first letter in upper case. -/
def capitalize (s : String) : String :=
  match s.toList with
  | c :: cs => String.ofList (c.toUpper :: cs)
  | [] => s

/-- The contest description `d` as a Lean name: its words, capitalized and without other
characters. -/
def contestName (d : String) : String :=
  String.join ((d.split (fun c => !c.isAlphanum)).toList.map fun w => capitalize w.toString)

/-- The name of the data file of `contest`. -/
def profileFileName (contest : Contest) : String :=
  s!"{contestName contest.description}.json"

/-- The ballots of each contest of `contests` in the export `dir`, as `readBallots` reads them: from
each session's current state, without ambiguous marks, and leaving out card contests with the
`InvalidContest` outstack condition. -/
def contestBallots (dir : System.FilePath) (contests : Array Contest) :
    IO (Array (Array Ballot)) := do
  let conditions ←
    readJsonFile (Manifest OutstackCondition) (dir / "OutstackConditionManifest.json")
  readBallots dir contests (notInvalidContest conditions.list) notAmbiguous

/-- Writes the data file `dataDir/<profileFileName>` of each ranked-choice contest of the export
`dir` that has none, reading the export once, and returns the files written. -/
def writeMissingProfiles (dir dataDir : System.FilePath) : IO (Array System.FilePath) := do
  let contests ← readJsonFile (Manifest Contest) (dir / "ContestManifest.json")
  let missing ← (contests.list.filter (·.numOfRanks > 0)).filterM fun c =>
    return !(← (dataDir / profileFileName c).pathExists)
  if missing.isEmpty then return #[]
  let ballots ← contestBallots dir missing
  IO.FS.createDirAll dataDir
  let mut written := #[]
  for (c, bs) in missing.zip ballots do
    let path := dataDir / profileFileName c
    writeProfileData path
      { contestId := c.id, description := c.description, profile := Profile.ofBallots bs.toList }
    written := written.push path
  return written

/-- The data file `file` of contest `contestId` of the export `dir`, both relative to `root`, and
the files written to produce it. If `file` is missing, `writeMissingProfiles` first writes the
missing data files of the export to the directory of `file`, under a lock on
`.lake/profile-data.lock`, so that modules elaborated in parallel write them once. -/
def loadProfileData (root dir file : System.FilePath) (contestId : Nat) :
    IO (ProfileData × Array System.FilePath) := do
  let path := root / file
  let written ← if ← path.pathExists then pure #[] else do
    IO.FS.createDirAll (root / ".lake")
    let lock ← IO.FS.Handle.mk (root / ".lake" / "profile-data.lock") .write
    lock.lock
    try
      if ← path.pathExists then pure #[]
      else
        unless ← (root / dir).pathExists do
          throw <| IO.userError s!"{file} is missing, and so is the CVR export {dir}"
        writeMissingProfiles (root / dir) (path.parent.getD root)
    finally
      lock.unlock
  unless ← path.pathExists do
    throw <| IO.userError s!"{file} is missing, and no ranked-choice contest of {dir} has a data \
      file with its name"
  let data ← readJsonFile ProfileData path
  unless data.contestId == contestId do
    throw <| IO.userError s!"{file} is the profile of contest {data.contestId}, not {contestId}"
  pure (data, written)

/-! ## The elaborator -/

open Elab Term Meta

/-- The directory of the file being elaborated, up as many levels as its module name has
components. -/
def packageRoot : CoreM System.FilePath := do
  let file : System.FilePath := ← getFileName
  let n := (← getEnv).mainModule.components.length
  pure <| (List.range n).foldl (fun p _ => p.parent.getD ".") file

def candExpr : Cand → Expr
  | .regular id => mkApp (mkConst ``Cand.regular) (mkNatLit id)
  | .writeIn i => mkApp (mkConst ``Cand.writeIn) (mkNatLit i)

/-- The list `[x₀, x₁, …]` of the terms `xs` of type `type`. -/
def listExpr (type : Expr) (xs : List Expr) : Expr :=
  xs.foldr (mkApp3 (mkConst ``List.cons [levelZero]) type)
    (mkApp (mkConst ``List.nil [levelZero]) type)

def rankingsType : Expr :=
  mkApp (mkConst ``List [levelZero]) (mkApp (mkConst ``List [levelZero]) (mkConst ``Cand))

def entryType : Expr :=
  mkApp2 (mkConst ``Prod [levelZero, levelZero]) rankingsType (mkConst ``Nat)

def entryExpr (x : List (List Cand) × Nat) : Expr :=
  mkApp4 (mkConst ``Prod.mk [levelZero, levelZero]) rankingsType (mkConst ``Nat)
    (listExpr (mkApp (mkConst ``List [levelZero]) (mkConst ``Cand))
      (x.1.map fun r => listExpr (mkConst ``Cand) (r.map candExpr)))
    (mkNatLit x.2)

/-- Adds the definitions `base.chunk0`, `base.chunk1`, … of the entries of `p`, at most `size` in
each, and returns the term `base.chunk0 ++ (base.chunk1 ++ …)`. -/
def addChunks (base : Name) (size : Nat) (p : Profile) : TermElabM Expr := do
  let chunks := (List.range ((p.length + size - 1) / size)).map fun k =>
    (p.drop (size * k)).take size
  let mut names := #[]
  for h : k in [0:chunks.length] do
    let name := base ++ Name.mkSimple s!"chunk{k}"
    let value := listExpr entryType (chunks[k].map entryExpr)
    addAndCompile <| .defnDecl {
      name, levelParams := [], type := mkConst ``Profile, value
      hints := .regular (getMaxHeight (← getEnv) value + 1), safety := .safe }
    names := names.push name
  pure <| names.foldr (fun n e => mkApp3 (mkConst ``List.append [levelZero]) entryType
    (mkConst n) e) (mkApp (mkConst ``List.nil [levelZero]) entryType)

/-- `profile_data% "<export dir>" <contest id> "<data file>"` is the profile of the data file, whose
entries it adds as definitions of at most 500 entries each, named after the declaration being
elaborated. If the data file is missing, it first writes the data files of the export that are
missing (`loadProfileData`). -/
syntax (name := profileDataElab) "profile_data% " str num str : term

@[term_elab profileDataElab] def elabProfileData : TermElab := fun stx _ => do
  let `(profile_data% $dir:str $id:num $file:str) := stx | throwUnsupportedSyntax
  let root ← packageRoot
  let task ← IO.asTask (prio := .dedicated)
    (loadProfileData root dir.getString file.getString id.getNat)
  let (data, written) ← IO.ofExcept (← IO.wait task)
  for path in written do
    logInfo m!"wrote {path} from {dir.getString}"
  addChunks ((← getDeclName?).getD `profile_data) 500 data.profile

end Alaska
