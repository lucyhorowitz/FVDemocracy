/-!
# CVR export

The JSON files of the Division of Elections CVR exports: the 2022 Primary
Election and Special General (`cvr/2022-special`) and the 2022 General
(`cvr/2022-general`), EMS version 5.5.52.6, and the 2024 General
(`cvr/2024-general`), EMS version 5.17.18.1. The `Option` fields marked
5.17 occur only in the 2024 export. Field names are the JSON keys with the first
letter lowercased. Every file except
`Configuration.json` has a top-level `Version`; the manifests hold their
entries in a top-level `List`.
-/

namespace Alaska.CVRExport

/-- A manifest file: `Version` and `List`. -/
structure Manifest (α : Type) where
  version : String
  list : Array α
deriving Repr

/-! ## Configuration.json -/

structure Configuration where
  includeTabulatorFilter : Bool
  tabulatorFilterValue : Nat
  includeResultContainerFilter : Bool
  resultContainerFilterValue : Nat
  includePrecinctPortionFilter : Bool
  precinctPortionFilterValue : Nat
  includeBallotTypeFilter : Bool
  ballotTypeFilterValue : Nat
  includeContestFilter : Bool
  contestFilterValue : Nat
  splitFilesPerBatch : Bool
  includeOnlyPublishedResultContainers : Bool
  useTabulatorFormat : Bool
deriving Repr

/-! ## Manifest entries -/

/-- `BallotTypeManifest.json` entry. -/
structure BallotType where
  description : String -- name of the ballot type
  id : Nat -- internal machine id
  externalId : Option String -- optional external identifier
deriving Repr

/-- `BallotTypeContestManifest.json` entry: contest `contestId` appears on
ballot type `ballotTypeId`. -/
structure BallotTypeContest where
  ballotTypeId : Nat
  contestId : Nat
deriving Repr

/-- The `Type` of a `CandidateManifest.json` entry: `"Regular"` or
`"WriteIn"`. -/
inductive CandidateType where
  | regular
  | writeIn
deriving Repr, DecidableEq

/-- `CandidateManifest.json` entry. -/
structure Candidate where
  description : String
  id : Nat
  externalId : String
  contestId : Nat
  type : CandidateType
  affiliations : Option (Array Nat) -- 5.17: party ids
  disabled : Option Nat -- 5.17
deriving Repr

/-- `ContestManifest.json` entry. `numOfRanks` is `0` for a contest that is not
ranked-choice. -/
structure Contest where
  description : String
  id : Nat
  externalId : String
  districtId : Nat
  voteFor : Nat
  numOfRanks : Nat
  numOfWriteins : Option Nat -- 5.17
  disabled : Option Nat -- 5.17
  type : Option String -- 5.17: `"Candidacy"` or `"Measure"`
deriving Repr

/-- `CountingGroupManifest.json` entry. -/
structure CountingGroup where
  description : String
  id : Nat
  externalId : String
deriving Repr

/-- `DistrictManifest.json` entry. `districtTypeId` is a `DistrictType` id. -/
structure District where
  description : String
  id : Nat
  districtTypeId : String
  externalId : String
deriving Repr

/-- `DistrictPrecinctPortionManifest.json` entry: precinct portion
`precinctPortionId` belongs to district `districtId`. -/
structure DistrictPrecinctPortion where
  districtId : Nat
  precinctPortionId : Nat
deriving Repr

/-- `DistrictTypeManifest.json` entry. The id is a UUID string. -/
structure DistrictType where
  description : String
  id : String
  externalId : String
deriving Repr

/-- `ElectionEventManifest.json` entry. `electionDate` is `YYYYMMDD`;
`electionSignature` is 32 integers. -/
structure ElectionEvent where
  description : String
  id : Nat
  externalId : String
  jurisdiction : String
  electionDate : String
  electionSignature : Array Nat
deriving Repr

/-- `OutstackConditionManifest.json` entry. -/
structure OutstackCondition where
  description : String
  id : Nat
deriving Repr

/-- `PartyManifest.json` entry. -/
structure Party where
  description : String
  id : Nat
  externalId : String
deriving Repr

/-- `PrecinctManifest.json` entry. -/
structure Precinct where
  description : String
  id : Nat
  externalId : String
deriving Repr

/-- `PrecinctPortionManifest.json` entry. -/
structure PrecinctPortion where
  description : String
  id : Nat
  externalId : String
  precinctId : Nat
deriving Repr

/-- The `Type` of a `TabulatorManifest.json` entry. -/
inductive TabulatorType where
  | imagecastCentral
  | imagecastEvolution
  | imagecastX
  | internetVoting
deriving Repr, DecidableEq

/-- `TabulatorManifest.json` entry. -/
structure Tabulator where
  description : String
  id : Nat
  votingLocationNumber : Nat
  votingLocationName : String
  externalId : String
  type : TabulatorType
  thresholdMin : Nat
  thresholdMax : Nat
  writeThresholdMin : Nat
  writeThresholdMax : Nat
deriving Repr

/-! ## CvrExport.json -/

/-- One filled oval. `partyId` is absent exactly on write-in marks, which
instead have `writeinIndex` and `writeinDensity`. -/
structure Mark where
  candidateId : Nat
  manifestationId : Nat
  partyId : Option Nat
  rank : Nat
  writeinIndex : Option Nat
  markDensity : Nat
  writeinDensity : Option Nat
  isAmbiguous : Bool
  isVote : Bool
  outstackConditionIds : Array Nat
deriving Repr

/-- One contest on a card. -/
structure CardContest where
  id : Nat
  manifestationId : Nat
  undervotes : Nat
  overvotes : Nat
  outstackConditionIds : Array Nat
  marks : Array Mark
deriving Repr

structure Card where
  id : Nat
  keyInId : Option Nat -- 5.17
  paperIndex : Nat
  contests : Array CardContest
  outstackConditionIds : Array Nat
deriving Repr

/-- The `Original` or `Modified` state of a session. -/
structure SessionState where
  precinctPortionId : Nat
  ballotTypeId : Nat
  isCurrent : Bool
  cards : Array Card
deriving Repr

/-- The `SessionType` of a session. -/
inductive SessionType where
  | dreVote
  | qrVote
  | scannedVote
deriving Repr, DecidableEq

/-- One ballot. -/
structure Session where
  tabulatorId : Nat
  batchId : Nat
  recordId : Nat
  countingGroupId : Nat
  imageMask : String
  sessionType : SessionType
  votingSessionIdentifier : String
  uniqueVotingIdentifier : String
  original : SessionState
  modified : Option SessionState
deriving Repr

structure CvrExport where
  version : String
  electionId : String
  sessions : Array Session
deriving Repr

/-! ## The export directory -/

structure Export where
  configuration : Configuration
  ballotTypes : Manifest BallotType
  ballotTypeContests : Manifest BallotTypeContest
  candidates : Manifest Candidate
  contests : Manifest Contest
  countingGroups : Manifest CountingGroup
  districts : Manifest District
  districtPrecinctPortions : Manifest DistrictPrecinctPortion
  districtTypes : Manifest DistrictType
  electionEvents : Manifest ElectionEvent
  outstackConditions : Manifest OutstackCondition
  parties : Manifest Party
  precincts : Manifest Precinct
  precinctPortions : Manifest PrecinctPortion
  tabulators : Manifest Tabulator
  cvrExport : CvrExport
deriving Repr

end Alaska.CVRExport
