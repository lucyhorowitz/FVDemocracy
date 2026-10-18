import Lean.Data.Json
import FVDemocracy.Alaska.Statute.StatuteDefs
import FVDemocracy.Alaska.ParseCVR.Export

/-!
# Parsing the CVR export

`FromJson` and `ToJson` instances for the types in `CVRExport`, and
readers for the export's files. `CvrExport.json` is read one session at a time
with `foldJsonArrayFile`; the manifests are small and are parsed
whole. The readers check that every parsed value encodes back to the `Json` it
was parsed from.
-/

open Lean

namespace Alaska.CVRExport

/-! ## Streaming one JSON array off disk

`foldJsonArrayFile` reads a file in fixed-size chunks and parses one element of a
named top-level array at a time, so a single element is a `Json` value at any
moment. Scanning runs on bytes; the delimiters it looks for are all ASCII, so a
chunk boundary may fall at any offset.
-/

namespace JsonStream

private def quoteByte : UInt8 := 0x22
private def backslashByte : UInt8 := 0x5c
private def lbraceByte : UInt8 := 0x7b
private def rbraceByte : UInt8 := 0x7d
private def lbracketByte : UInt8 := 0x5b
private def rbracketByte : UInt8 := 0x5d
private def commaByte : UInt8 := 0x2c
private def colonByte : UInt8 := 0x3a

private def isWs (b : UInt8) : Bool :=
  b == 0x20 || b == 0x09 || b == 0x0a || b == 0x0d

/-- First index at or after `i` whose byte is not JSON whitespace. -/
def skipWs (buf : ByteArray) (i : Nat) : Nat :=
  if h : i < buf.size then
    if isWs (buf.get! i) then skipWs buf (i + 1) else i
  else i
termination_by buf.size - i
decreasing_by omega

/-- Whether `pat` occurs in `buf` starting at `off`, comparing from index `k`. -/
private def matchesFrom (buf pat : ByteArray) (off k : Nat) : Bool :=
  if h : k < pat.size then
    buf.get! (off + k) == pat.get! k && matchesFrom buf pat off (k + 1)
  else true
termination_by pat.size - k
decreasing_by omega

/-- Index just past the first occurrence of `pat` in `buf` at or after `start`. -/
def findBytes (buf pat : ByteArray) (start : Nat) : Option Nat :=
  if hp : pat.size = 0 then some start
  else if h : start + pat.size ≤ buf.size then
    if matchesFrom buf pat start 0 then some (start + pat.size)
    else findBytes buf pat (start + 1)
  else none
termination_by buf.size - start
decreasing_by omega

/-- Index just past the object, array or string beginning at `j`, or `none` when
`buf` ends first. `depth` counts unclosed brackets, `inStr` and `esc` track
string literals so that delimiters inside them are ignored. -/
private def scanFrom (buf : ByteArray) (j depth : Nat) (inStr esc : Bool) : Option Nat :=
  if h : j < buf.size then
    let b := buf.get! j
    if inStr then
      if esc then scanFrom buf (j + 1) depth true false
      else if b == backslashByte then scanFrom buf (j + 1) depth true true
      else if b == quoteByte then
        if depth == 0 then some (j + 1) else scanFrom buf (j + 1) depth false false
      else scanFrom buf (j + 1) depth true false
    else if b == quoteByte then scanFrom buf (j + 1) depth true false
    else if b == lbraceByte || b == lbracketByte then
      scanFrom buf (j + 1) (depth + 1) false false
    else if b == rbraceByte || b == rbracketByte then
      if depth ≤ 1 then some (j + 1) else scanFrom buf (j + 1) (depth - 1) false false
    else scanFrom buf (j + 1) depth false false
  else none
termination_by buf.size - j
decreasing_by all_goals omega

/-- Index of the first byte at or after `j` that ends a number, `true`, `false`
or `null`, or `none` when `buf` ends first. -/
private def scanScalar (buf : ByteArray) (j : Nat) : Option Nat :=
  if h : j < buf.size then
    let b := buf.get! j
    if b == commaByte || b == rbraceByte || b == rbracketByte || isWs b then some j
    else scanScalar buf (j + 1)
  else none
termination_by buf.size - j
decreasing_by omega

/-- Index just past the JSON value beginning at `i`, or `none` when `buf` ends
before the value closes. -/
def scanValue (buf : ByteArray) (i : Nat) : Option Nat :=
  if i < buf.size then
    let b := buf.get! i
    if b == lbraceByte || b == lbracketByte || b == quoteByte then
      scanFrom buf i 0 false false
    else scanScalar buf i
  else none

/-- An open file together with the bytes read from it but not yet consumed.
`pos` is the first unconsumed index of `buf`; `atEof` records that a read
returned nothing. -/
structure Stream where
  handle : IO.FS.Handle
  buf : ByteArray
  pos : Nat
  atEof : Bool

def chunkSize : USize := 65536

def Stream.ofFile (path : System.FilePath) : IO Stream := do
  let handle ← IO.FS.Handle.mk path IO.FS.Mode.read
  pure { handle, buf := ByteArray.empty, pos := 0, atEof := false }

/-- Drops the consumed prefix of the buffer and appends the next chunk. -/
def Stream.fill (s : Stream) : IO Stream := do
  let kept := s.buf.extract s.pos s.buf.size
  if s.atEof then
    pure { s with buf := kept, pos := 0 }
  else
    let chunk ← s.handle.read chunkSize
    pure { s with buf := kept ++ chunk, pos := 0, atEof := chunk.size == 0 }

/-- Advances the stream past the next occurrence of `"key"`. -/
partial def Stream.seekKey (s : Stream) (key : String) : IO Stream := do
  let pat := s!"\"{key}\"".toUTF8
  match findBytes s.buf pat s.pos with
  | some k => pure { s with pos := k }
  | none =>
      if s.atEof then
        throw (IO.userError s!"key \"{key}\" not found")
      else
        -- retain the bytes that could hold a prefix of the key
        let keep := s.buf.size - min s.buf.size (pat.size - 1)
        Stream.seekKey (← Stream.fill { s with pos := max s.pos keep }) key

/-- Advances the stream past the `[` that follows the key it is positioned on. -/
partial def Stream.seekArrayStart (s : Stream) : IO Stream := do
  let s := { s with pos := skipWs s.buf s.pos }
  if s.pos < s.buf.size then
    let b := s.buf.get! s.pos
    if b == lbracketByte then pure { s with pos := s.pos + 1 }
    else if b == colonByte then Stream.seekArrayStart { s with pos := s.pos + 1 }
    else throw (IO.userError "expected an array after the key")
  else if s.atEof then
    throw (IO.userError "end of file before the array started")
  else
    Stream.seekArrayStart (← Stream.fill s)

/-- Threads `a` through `step` once per element of the array the stream is
positioned inside, parsing one element at a time, and returns at the closing
`]`. -/
partial def Stream.foldArray {α : Type} [Inhabited α]
    (s : Stream) (a : α) (step : α → Json → IO α) : IO α := do
  let s := { s with pos := skipWs s.buf s.pos }
  if s.pos ≥ s.buf.size then
    if s.atEof then throw (IO.userError "end of file inside an array")
    else Stream.foldArray (← Stream.fill s) a step
  else
    let b := s.buf.get! s.pos
    if b == rbracketByte then
      pure a
    else if b == commaByte then
      Stream.foldArray { s with pos := s.pos + 1 } a step
    else
      match scanValue s.buf s.pos with
      | none =>
          if s.atEof then throw (IO.userError "end of file inside an array element")
          else Stream.foldArray (← Stream.fill s) a step
      | some k =>
          let some text := String.fromUTF8? (s.buf.extract s.pos k)
            | throw (IO.userError "array element is not valid UTF-8")
          match Json.parse text with
          | .error e => throw (IO.userError s!"JSON parse error: {e}")
          | .ok json =>
              let a ← step a json
              Stream.foldArray { s with pos := k } a step

end JsonStream

/-- Folds `step` over the elements of the top-level array named `key` in the
file at `path`, holding one element in memory at a time. -/
def foldJsonArrayFile {α : Type} [Inhabited α]
    (path : System.FilePath) (key : String) (init : α) (step : α → Json → IO α) : IO α := do
  let s ← JsonStream.Stream.ofFile path
  let s ← s.seekKey key
  let s ← s.seekArrayStart
  s.foldArray init step

instance {α : Type} [FromJson α] : FromJson (Manifest α) where
  fromJson? j := do
    let version ← j.getObjValAs? String "Version"
    let list ← j.getObjValAs? (Array α) "List"
    pure { version, list }

instance : FromJson Configuration where
  fromJson? j := do
    let includeTabulatorFilter ← j.getObjValAs? Bool "IncludeTabulatorFilter"
    let tabulatorFilterValue ← j.getObjValAs? Nat "TabulatorFilterValue"
    let includeResultContainerFilter ← j.getObjValAs? Bool "IncludeResultContainerFilter"
    let resultContainerFilterValue ← j.getObjValAs? Nat "ResultContainerFilterValue"
    let includePrecinctPortionFilter ← j.getObjValAs? Bool "IncludePrecinctPortionFilter"
    let precinctPortionFilterValue ← j.getObjValAs? Nat "PrecinctPortionFilterValue"
    let includeBallotTypeFilter ← j.getObjValAs? Bool "IncludeBallotTypeFilter"
    let ballotTypeFilterValue ← j.getObjValAs? Nat "BallotTypeFilterValue"
    let includeContestFilter ← j.getObjValAs? Bool "IncludeContestFilter"
    let contestFilterValue ← j.getObjValAs? Nat "ContestFilterValue"
    let splitFilesPerBatch ← j.getObjValAs? Bool "SplitFilesPerBatch"
    let includeOnlyPublishedResultContainers ←
      j.getObjValAs? Bool "IncludeOnlyPublishedResultContainers"
    let useTabulatorFormat ← j.getObjValAs? Bool "UseTabulatorFormat"
    pure {
      includeTabulatorFilter, tabulatorFilterValue
      includeResultContainerFilter, resultContainerFilterValue
      includePrecinctPortionFilter, precinctPortionFilterValue
      includeBallotTypeFilter, ballotTypeFilterValue
      includeContestFilter, contestFilterValue
      splitFilesPerBatch, includeOnlyPublishedResultContainers, useTabulatorFormat
    }

/-! ## Manifest entries -/

instance : FromJson BallotType where
  fromJson? j := do
    let description ← j.getObjValAs? String "Description"
    let id ← j.getObjValAs? Nat "Id"
    let externalId ← j.getObjValAs? (Option String) "ExternalId"
    pure { description, id, externalId }

instance : FromJson BallotTypeContest where
  fromJson? j := do
    let ballotTypeId ← j.getObjValAs? Nat "BallotTypeId"
    let contestId ← j.getObjValAs? Nat "ContestId"
    pure { ballotTypeId, contestId }

instance : FromJson CandidateType where
  fromJson?
    | .str "Regular" => pure .regular
    | .str "WriteIn" => pure .writeIn
    | j => throw s!"unknown candidate type: {j.compress}"

instance : FromJson Candidate where
  fromJson? j := do
    let description ← j.getObjValAs? String "Description"
    let id ← j.getObjValAs? Nat "Id"
    let externalId ← j.getObjValAs? String "ExternalId"
    let contestId ← j.getObjValAs? Nat "ContestId"
    let type ← j.getObjValAs? CandidateType "Type"
    let affiliations ← j.getObjValAs? (Option (Array Nat)) "Affiliations"
    let disabled ← j.getObjValAs? (Option Nat) "Disabled"
    pure { description, id, externalId, contestId, type, affiliations, disabled }

instance : FromJson Contest where
  fromJson? j := do
    let description ← j.getObjValAs? String "Description"
    let id ← j.getObjValAs? Nat "Id"
    let externalId ← j.getObjValAs? String "ExternalId"
    let districtId ← j.getObjValAs? Nat "DistrictId"
    let voteFor ← j.getObjValAs? Nat "VoteFor"
    let numOfRanks ← j.getObjValAs? Nat "NumOfRanks"
    let numOfWriteins ← j.getObjValAs? (Option Nat) "NumOfWriteins"
    let disabled ← j.getObjValAs? (Option Nat) "Disabled"
    let type ← j.getObjValAs? (Option String) "Type"
    pure {
      description, id, externalId, districtId, voteFor, numOfRanks, numOfWriteins, disabled
      type
    }

instance : FromJson CountingGroup where
  fromJson? j := do
    let description ← j.getObjValAs? String "Description"
    let id ← j.getObjValAs? Nat "Id"
    let externalId ← j.getObjValAs? String "ExternalId"
    pure { description, id, externalId }

instance : FromJson District where
  fromJson? j := do
    let description ← j.getObjValAs? String "Description"
    let id ← j.getObjValAs? Nat "Id"
    let districtTypeId ← j.getObjValAs? String "DistrictTypeId"
    let externalId ← j.getObjValAs? String "ExternalId"
    pure { description, id, districtTypeId, externalId }

instance : FromJson DistrictPrecinctPortion where
  fromJson? j := do
    let districtId ← j.getObjValAs? Nat "DistrictId"
    let precinctPortionId ← j.getObjValAs? Nat "PrecinctPortionId"
    pure { districtId, precinctPortionId }

instance : FromJson DistrictType where
  fromJson? j := do
    let description ← j.getObjValAs? String "Description"
    let id ← j.getObjValAs? String "Id"
    let externalId ← j.getObjValAs? String "ExternalId"
    pure { description, id, externalId }

instance : FromJson ElectionEvent where
  fromJson? j := do
    let description ← j.getObjValAs? String "Description"
    let id ← j.getObjValAs? Nat "Id"
    let externalId ← j.getObjValAs? String "ExternalId"
    let jurisdiction ← j.getObjValAs? String "Jurisdiction"
    let electionDate ← j.getObjValAs? String "ElectionDate"
    let electionSignature ← j.getObjValAs? (Array Nat) "ElectionSignature"
    pure { description, id, externalId, jurisdiction, electionDate, electionSignature }

instance : FromJson OutstackCondition where
  fromJson? j := do
    let description ← j.getObjValAs? String "Description"
    let id ← j.getObjValAs? Nat "Id"
    pure { description, id }

instance : FromJson Party where
  fromJson? j := do
    let description ← j.getObjValAs? String "Description"
    let id ← j.getObjValAs? Nat "Id"
    let externalId ← j.getObjValAs? String "ExternalId"
    pure { description, id, externalId }

instance : FromJson Precinct where
  fromJson? j := do
    let description ← j.getObjValAs? String "Description"
    let id ← j.getObjValAs? Nat "Id"
    let externalId ← j.getObjValAs? String "ExternalId"
    pure { description, id, externalId }

instance : FromJson PrecinctPortion where
  fromJson? j := do
    let description ← j.getObjValAs? String "Description"
    let id ← j.getObjValAs? Nat "Id"
    let externalId ← j.getObjValAs? String "ExternalId"
    let precinctId ← j.getObjValAs? Nat "PrecinctId"
    pure { description, id, externalId, precinctId }

instance : FromJson TabulatorType where
  fromJson?
    | .str "ImagecastCentral" => pure .imagecastCentral
    | .str "ImagecastEvolution" => pure .imagecastEvolution
    | .str "ImagecastX" => pure .imagecastX
    | .str "InternetVoting" => pure .internetVoting
    | j => throw s!"unknown tabulator type: {j.compress}"

instance : FromJson Tabulator where
  fromJson? j := do
    let description ← j.getObjValAs? String "Description"
    let id ← j.getObjValAs? Nat "Id"
    let votingLocationNumber ← j.getObjValAs? Nat "VotingLocationNumber"
    let votingLocationName ← j.getObjValAs? String "VotingLocationName"
    let externalId ← j.getObjValAs? String "ExternalId"
    let type ← j.getObjValAs? TabulatorType "Type"
    let thresholdMin ← j.getObjValAs? Nat "ThresholdMin"
    let thresholdMax ← j.getObjValAs? Nat "ThresholdMax"
    let writeThresholdMin ← j.getObjValAs? Nat "WriteThresholdMin"
    let writeThresholdMax ← j.getObjValAs? Nat "WriteThresholdMax"
    pure {
      description, id, votingLocationNumber, votingLocationName, externalId, type
      thresholdMin, thresholdMax, writeThresholdMin, writeThresholdMax
    }

/-! ## CvrExport.json -/

instance : FromJson Mark where
  fromJson? j := do
    let candidateId ← j.getObjValAs? Nat "CandidateId"
    let manifestationId ← j.getObjValAs? Nat "ManifestationId"
    let partyId ← j.getObjValAs? (Option Nat) "PartyId"
    let rank ← j.getObjValAs? Nat "Rank"
    let writeinIndex ← j.getObjValAs? (Option Nat) "WriteinIndex"
    let markDensity ← j.getObjValAs? Nat "MarkDensity"
    let writeinDensity ← j.getObjValAs? (Option Nat) "WriteinDensity"
    let isAmbiguous ← j.getObjValAs? Bool "IsAmbiguous"
    let isVote ← j.getObjValAs? Bool "IsVote"
    let outstackConditionIds ← j.getObjValAs? (Array Nat) "OutstackConditionIds"
    pure {
      candidateId, manifestationId, partyId, rank, writeinIndex, markDensity
      writeinDensity, isAmbiguous, isVote, outstackConditionIds
    }

instance : FromJson CardContest where
  fromJson? j := do
    let id ← j.getObjValAs? Nat "Id"
    let manifestationId ← j.getObjValAs? Nat "ManifestationId"
    let undervotes ← j.getObjValAs? Nat "Undervotes"
    let overvotes ← j.getObjValAs? Nat "Overvotes"
    let outstackConditionIds ← j.getObjValAs? (Array Nat) "OutstackConditionIds"
    let marks ← j.getObjValAs? (Array Mark) "Marks"
    pure { id, manifestationId, undervotes, overvotes, outstackConditionIds, marks }

instance : FromJson Card where
  fromJson? j := do
    let id ← j.getObjValAs? Nat "Id"
    let keyInId ← j.getObjValAs? (Option Nat) "KeyInId"
    let paperIndex ← j.getObjValAs? Nat "PaperIndex"
    let contests ← j.getObjValAs? (Array CardContest) "Contests"
    let outstackConditionIds ← j.getObjValAs? (Array Nat) "OutstackConditionIds"
    pure { id, keyInId, paperIndex, contests, outstackConditionIds }

instance : FromJson SessionState where
  fromJson? j := do
    let precinctPortionId ← j.getObjValAs? Nat "PrecinctPortionId"
    let ballotTypeId ← j.getObjValAs? Nat "BallotTypeId"
    let isCurrent ← j.getObjValAs? Bool "IsCurrent"
    let cards ← j.getObjValAs? (Array Card) "Cards"
    pure { precinctPortionId, ballotTypeId, isCurrent, cards }

instance : FromJson SessionType where
  fromJson?
    | .str "DreVote" => pure .dreVote
    | .str "QRVote" => pure .qrVote
    | .str "ScannedVote" => pure .scannedVote
    | j => throw s!"unknown session type: {j.compress}"

instance : FromJson Session where
  fromJson? j := do
    let tabulatorId ← j.getObjValAs? Nat "TabulatorId"
    let batchId ← j.getObjValAs? Nat "BatchId"
    let recordId ← j.getObjValAs? Nat "RecordId"
    let countingGroupId ← j.getObjValAs? Nat "CountingGroupId"
    let imageMask ← j.getObjValAs? String "ImageMask"
    let sessionType ← j.getObjValAs? SessionType "SessionType"
    let votingSessionIdentifier ← j.getObjValAs? String "VotingSessionIdentifier"
    let uniqueVotingIdentifier ← j.getObjValAs? String "UniqueVotingIdentifier"
    let original ← j.getObjValAs? SessionState "Original"
    let modified ← j.getObjValAs? (Option SessionState) "Modified"
    pure {
      tabulatorId, batchId, recordId, countingGroupId, imageMask, sessionType
      votingSessionIdentifier, uniqueVotingIdentifier, original, modified
    }

/-! ## Encoding

`ToJson` instances that write each type back with the keys it was read from,
omitting the keys of `Option` fields that are `none`. -/

instance {α : Type} [ToJson α] : ToJson (Manifest α) where
  toJson m := Json.mkObj [("Version", toJson m.version), ("List", toJson m.list)]

instance : ToJson Configuration where
  toJson c := Json.mkObj [
    ("IncludeTabulatorFilter", toJson c.includeTabulatorFilter),
    ("TabulatorFilterValue", toJson c.tabulatorFilterValue),
    ("IncludeResultContainerFilter", toJson c.includeResultContainerFilter),
    ("ResultContainerFilterValue", toJson c.resultContainerFilterValue),
    ("IncludePrecinctPortionFilter", toJson c.includePrecinctPortionFilter),
    ("PrecinctPortionFilterValue", toJson c.precinctPortionFilterValue),
    ("IncludeBallotTypeFilter", toJson c.includeBallotTypeFilter),
    ("BallotTypeFilterValue", toJson c.ballotTypeFilterValue),
    ("IncludeContestFilter", toJson c.includeContestFilter),
    ("ContestFilterValue", toJson c.contestFilterValue),
    ("SplitFilesPerBatch", toJson c.splitFilesPerBatch),
    ("IncludeOnlyPublishedResultContainers", toJson c.includeOnlyPublishedResultContainers),
    ("UseTabulatorFormat", toJson c.useTabulatorFormat)]

instance : ToJson BallotType where
  toJson b := Json.mkObj <|
    [("Description", toJson b.description), ("Id", toJson b.id)] ++
    Json.opt "ExternalId" b.externalId

instance : ToJson BallotTypeContest where
  toJson b := Json.mkObj [
    ("BallotTypeId", toJson b.ballotTypeId), ("ContestId", toJson b.contestId)]

instance : ToJson CandidateType where
  toJson
    | .regular => "Regular"
    | .writeIn => "WriteIn"

instance : ToJson Candidate where
  toJson c := Json.mkObj <|
    [("Description", toJson c.description), ("Id", toJson c.id),
     ("ExternalId", toJson c.externalId), ("ContestId", toJson c.contestId),
     ("Type", toJson c.type)] ++
    Json.opt "Affiliations" c.affiliations ++
    Json.opt "Disabled" c.disabled

instance : ToJson Contest where
  toJson c := Json.mkObj <|
    [("Description", toJson c.description), ("Id", toJson c.id),
     ("ExternalId", toJson c.externalId), ("DistrictId", toJson c.districtId),
     ("VoteFor", toJson c.voteFor), ("NumOfRanks", toJson c.numOfRanks)] ++
    Json.opt "NumOfWriteins" c.numOfWriteins ++
    Json.opt "Disabled" c.disabled ++
    Json.opt "Type" c.type

instance : ToJson CountingGroup where
  toJson c := Json.mkObj [
    ("Description", toJson c.description), ("Id", toJson c.id),
    ("ExternalId", toJson c.externalId)]

instance : ToJson District where
  toJson d := Json.mkObj [
    ("Description", toJson d.description), ("Id", toJson d.id),
    ("DistrictTypeId", toJson d.districtTypeId), ("ExternalId", toJson d.externalId)]

instance : ToJson DistrictPrecinctPortion where
  toJson d := Json.mkObj [
    ("DistrictId", toJson d.districtId), ("PrecinctPortionId", toJson d.precinctPortionId)]

instance : ToJson DistrictType where
  toJson d := Json.mkObj [
    ("Description", toJson d.description), ("Id", toJson d.id),
    ("ExternalId", toJson d.externalId)]

instance : ToJson ElectionEvent where
  toJson e := Json.mkObj [
    ("Description", toJson e.description), ("Id", toJson e.id),
    ("ExternalId", toJson e.externalId), ("Jurisdiction", toJson e.jurisdiction),
    ("ElectionDate", toJson e.electionDate),
    ("ElectionSignature", toJson e.electionSignature)]

instance : ToJson OutstackCondition where
  toJson o := Json.mkObj [("Description", toJson o.description), ("Id", toJson o.id)]

instance : ToJson Party where
  toJson p := Json.mkObj [
    ("Description", toJson p.description), ("Id", toJson p.id),
    ("ExternalId", toJson p.externalId)]

instance : ToJson Precinct where
  toJson p := Json.mkObj [
    ("Description", toJson p.description), ("Id", toJson p.id),
    ("ExternalId", toJson p.externalId)]

instance : ToJson PrecinctPortion where
  toJson p := Json.mkObj [
    ("Description", toJson p.description), ("Id", toJson p.id),
    ("ExternalId", toJson p.externalId), ("PrecinctId", toJson p.precinctId)]

instance : ToJson TabulatorType where
  toJson
    | .imagecastCentral => "ImagecastCentral"
    | .imagecastEvolution => "ImagecastEvolution"
    | .imagecastX => "ImagecastX"
    | .internetVoting => "InternetVoting"

instance : ToJson Tabulator where
  toJson t := Json.mkObj [
    ("Description", toJson t.description), ("Id", toJson t.id),
    ("VotingLocationNumber", toJson t.votingLocationNumber),
    ("VotingLocationName", toJson t.votingLocationName),
    ("ExternalId", toJson t.externalId), ("Type", toJson t.type),
    ("ThresholdMin", toJson t.thresholdMin), ("ThresholdMax", toJson t.thresholdMax),
    ("WriteThresholdMin", toJson t.writeThresholdMin),
    ("WriteThresholdMax", toJson t.writeThresholdMax)]

instance : ToJson Mark where
  toJson m := Json.mkObj <|
    [("CandidateId", toJson m.candidateId), ("ManifestationId", toJson m.manifestationId)] ++
    Json.opt "PartyId" m.partyId ++
    [("Rank", toJson m.rank)] ++
    Json.opt "WriteinIndex" m.writeinIndex ++
    [("MarkDensity", toJson m.markDensity)] ++
    Json.opt "WriteinDensity" m.writeinDensity ++
    [("IsAmbiguous", toJson m.isAmbiguous), ("IsVote", toJson m.isVote),
     ("OutstackConditionIds", toJson m.outstackConditionIds)]

instance : ToJson CardContest where
  toJson c := Json.mkObj [
    ("Id", toJson c.id), ("ManifestationId", toJson c.manifestationId),
    ("Undervotes", toJson c.undervotes), ("Overvotes", toJson c.overvotes),
    ("OutstackConditionIds", toJson c.outstackConditionIds), ("Marks", toJson c.marks)]

instance : ToJson Card where
  toJson c := Json.mkObj <|
    [("Id", toJson c.id)] ++
    Json.opt "KeyInId" c.keyInId ++
    [("PaperIndex", toJson c.paperIndex), ("Contests", toJson c.contests),
     ("OutstackConditionIds", toJson c.outstackConditionIds)]

instance : ToJson SessionState where
  toJson s := Json.mkObj [
    ("PrecinctPortionId", toJson s.precinctPortionId), ("BallotTypeId", toJson s.ballotTypeId),
    ("IsCurrent", toJson s.isCurrent), ("Cards", toJson s.cards)]

instance : ToJson SessionType where
  toJson
    | .dreVote => "DreVote"
    | .qrVote => "QRVote"
    | .scannedVote => "ScannedVote"

instance : ToJson Session where
  toJson s := Json.mkObj <|
    [("TabulatorId", toJson s.tabulatorId), ("BatchId", toJson s.batchId),
     ("RecordId", toJson s.recordId), ("CountingGroupId", toJson s.countingGroupId),
     ("ImageMask", toJson s.imageMask), ("SessionType", toJson s.sessionType),
     ("VotingSessionIdentifier", toJson s.votingSessionIdentifier),
     ("UniqueVotingIdentifier", toJson s.uniqueVotingIdentifier),
     ("Original", toJson s.original)] ++
    Json.opt "Modified" s.modified

/-! ## Reading the files -/

/-- Parses the whole file at `path` as an `α`, failing unless the result encodes
back to the file's `Json`. -/
def readJsonFile (α : Type) [FromJson α] [ToJson α] (path : System.FilePath) : IO α := do
  let text ← IO.FS.readFile path
  let j ← match Json.parse text with
    | .ok j => pure j
    | .error e => throw (IO.userError s!"{path}: {e}")
  match fromJson? j with
  | .ok a =>
      if toJson a == j then pure a
      else throw (IO.userError s!"{path}: parsed value does not encode back to the file")
  | .error e => throw (IO.userError s!"{path}: {e}")

/-- The value of the first occurrence of key `key` in the file at `path`,
parsed without reading the rest of the file. -/
partial def readTopLevelValue (path : System.FilePath) (key : String) : IO Json := do
  let s ← (← JsonStream.Stream.ofFile path).seekKey key
  let rec go (s : JsonStream.Stream) : IO Json := do
    let i := JsonStream.skipWs s.buf s.pos
    if i < s.buf.size && s.buf.get! i == ':'.toUInt8 then
      go { s with pos := i + 1 }
    else match JsonStream.scanValue s.buf i with
      | some k =>
          let some text := String.fromUTF8? (s.buf.extract i k)
            | throw (IO.userError s!"{path}: value of \"{key}\" is not valid UTF-8")
          IO.ofExcept (Json.parse text)
      | none =>
          if s.atEof then throw (IO.userError s!"{path}: end of file in \"{key}\"")
          else go (← s.fill)
  go s

/-- Folds `step` over the sessions of the `CvrExport` file at `path`, parsing
one session at a time and failing on a session that does not encode back to its
`Json`. -/
def foldSessions {α : Type} [Inhabited α] (path : System.FilePath) (init : α)
    (step : α → Session → IO α) : IO α :=
  foldJsonArrayFile path "Sessions" (init, 0) (fun (a, i) j =>
    match fromJson? (α := Session) j with
    | .ok session =>
        if toJson session == j then return (← step a session, i + 1)
        else throw (IO.userError s!"{path}: session {i} does not encode back to its JSON")
    | .error e => throw (IO.userError s!"{path}: session {i}: {e}"))
  |>.map (·.1)

def readCvrExport (path : System.FilePath) : IO CvrExport := do
  let version ← IO.ofExcept (fromJson? (← readTopLevelValue path "Version"))
  let electionId ← IO.ofExcept (fromJson? (← readTopLevelValue path "ElectionId"))
  let sessions ← foldSessions path #[] fun acc s => pure (acc.push s)
  pure { version, electionId, sessions }

/-- Reads the export directory `dir`. -/
def readExport (dir : System.FilePath) : IO Export := do
  pure {
    configuration := ← readJsonFile _ (dir / "Configuration.json")
    ballotTypes := ← readJsonFile _ (dir / "BallotTypeManifest.json")
    ballotTypeContests := ← readJsonFile _ (dir / "BallotTypeContestManifest.json")
    candidates := ← readJsonFile _ (dir / "CandidateManifest.json")
    contests := ← readJsonFile _ (dir / "ContestManifest.json")
    countingGroups := ← readJsonFile _ (dir / "CountingGroupManifest.json")
    districts := ← readJsonFile _ (dir / "DistrictManifest.json")
    districtPrecinctPortions := ← readJsonFile _ (dir / "DistrictPrecinctPortionManifest.json")
    districtTypes := ← readJsonFile _ (dir / "DistrictTypeManifest.json")
    electionEvents := ← readJsonFile _ (dir / "ElectionEventManifest.json")
    outstackConditions := ← readJsonFile _ (dir / "OutstackConditionManifest.json")
    parties := ← readJsonFile _ (dir / "PartyManifest.json")
    precincts := ← readJsonFile _ (dir / "PrecinctManifest.json")
    precinctPortions := ← readJsonFile _ (dir / "PrecinctPortionManifest.json")
    tabulators := ← readJsonFile _ (dir / "TabulatorManifest.json")
    cvrExport := ← readCvrExport (dir / "CvrExport.json")
  }

/-! ## Ballots for one contest -/

/-- The session's `Modified` state if it has one, `Original` otherwise. -/
def Session.current (s : Session) : SessionState :=
  s.modified.getD s.original

/-- The marks of contest `contestId` in `state`, `none` when no card of `state`
carries the contest. -/
def SessionState.contestMarks? (state : SessionState) (contestId : Nat) :
    Option (Array Mark) :=
  state.cards.findSome? fun c => (c.contests.find? (·.id == contestId)).map (·.marks)

def notAmbiguous (m : Mark) : Bool :=
  !m.isAmbiguous

/-- Whether card contest `cc` has no outstack condition that `conditions`
describes as `InvalidContest`. -/
def notInvalidContest (conditions : Array OutstackCondition) (cc : CardContest) : Bool :=
  !cc.outstackConditionIds.any fun id =>
    conditions.any fun o => o.id == id && o.description == "InvalidContest"

/-- The candidate a mark is for: the write-in line `i` when the mark has
`writeinIndex = some i`, otherwise its `candidateId`. -/
def Mark.cand (m : Mark) : Cand :=
  match m.writeinIndex with
  | some i => .writeIn i
  | none => .regular m.candidateId

/-- The ballot for contest `contestId` in the current state of session `s`, or
`none` when the contest is not on it. Entry `r` of `ranks` holds, in file order,
the `Mark.cand` of the marks with rank `r + 1` that satisfy `keep`; there are
`numOfRanks` entries. Fails if a mark's rank is outside `1 … numOfRanks`, or if
some entry lists a candidate more than once. -/
def Session.toBallot? (keep : Mark → Bool) (contestId numOfRanks ballotIndex : Nat)
    (s : Session) : Except String (Option Ballot) := do
  let some marks := s.current.contestMarks? contestId | pure none
  if let some m := marks.find? (fun m => m.rank == 0 || m.rank > numOfRanks) then
    throw s!"session {ballotIndex}: mark with rank {m.rank} in contest {contestId}"
  let ranks := (List.range numOfRanks).map fun r =>
    (marks.filter (fun m => keep m && m.rank == r + 1)).toList.map Mark.cand
  if let some r := ranks.findIdx? (fun l => !l.Nodup) then
    throw s!"session {ballotIndex}: candidate repeated at rank {r + 1} in contest {contestId}"
  pure (some { ballotIndex, ranks })

/-- The card contest `contestId` in `state`, `none` when no card of `state`
carries the contest. -/
def SessionState.cardContest? (state : SessionState) (contestId : Nat) :
    Option CardContest :=
  state.cards.findSome? fun c => c.contests.find? (·.id == contestId)

/-- The `CvrExport` files of the export directory `dir`: `CvrExport.json` when
it exists, otherwise the files `CvrExport_<n>.json` in increasing order of `n`. -/
def cvrExportFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  if ← (dir / "CvrExport.json").pathExists then
    return #[dir / "CvrExport.json"]
  let numbered := (← dir.readDir).filterMap fun entry =>
    let name := entry.fileName
    if name.startsWith "CvrExport_" && name.endsWith ".json" then
      ((name.dropPrefix "CvrExport_").dropSuffix ".json").toNat?.map (·, entry.path)
    else none
  if numbered.isEmpty then
    throw (IO.userError s!"{dir}: no CvrExport.json or CvrExport_<n>.json files")
  return (numbered.qsort (·.1 < ·.1)).map (·.2)

/-- The ballots for each contest of `contests` in the export directory `dir`,
read in one pass over the files of `cvrExportFiles`. Entry `k` holds one ballot
per session whose current state carries contest `contests[k]` as a card contest
satisfying `keepContest`, with `ballotIndex` the session's position across the
files. Only marks satisfying `keep` are included. -/
def readBallots (dir : System.FilePath) (contests : Array Contest)
    (keepContest : CardContest → Bool) (keep : Mark → Bool) :
    IO (Array (Array Ballot)) := do
  let mut acc := (contests.map fun _ => (#[] : Array Ballot), 0)
  for path in ← cvrExportFiles dir do
    acc ← foldSessions path acc fun (ballots, i) s => do
      let mut ballots := ballots
      for h : k in [0:contests.size] do
        let contest := contests[k]
        if (s.current.cardContest? contest.id).any keepContest then
          match s.toBallot? keep contest.id contest.numOfRanks i with
          | .ok (some b) => ballots := ballots.modify k (·.push b)
          | .ok none => pure ()
          | .error e => throw (IO.userError s!"{path}: {e}")
      pure (ballots, i + 1)
  pure acc.1

end Alaska.CVRExport
