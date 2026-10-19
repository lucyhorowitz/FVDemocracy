/-!
# The published round-by-round results

`publishedReports` holds the rounds of every RCV report the Division of Elections published for a
contest that went past round 1. It leaves out the recount reports, which include the corrections
of the hand recount. The reports are at:

* 2022 special general: <https://www.elections.alaska.gov/results/22SSPG/RcvDetailedReport.pdf>;
* 2022 general: `https://www.elections.alaska.gov/results/22GENR/<contest>.txt`;
* 2024 general: `https://www.elections.alaska.gov/results/24GENR/RCV-<contest>.pdf`.

A candidate appears as their id in the `CandidateManifest.json` of the election's CVR export.
-/

namespace Alaska

/-- One round of a published report. `votes` lists each candidate of the report, by id, with
their votes; a defeated candidate has 0. `blanks` counts the ballots inactive in round 1,
`exhausted` the other ballots inactive in this round without reaching an overvote, and
`overvotes` the ballots that have reached an overvote. -/
structure PublishedRound where
  votes : List (Nat × Nat)
  blanks : Nat
  exhausted : Nat
  overvotes : Nat
deriving DecidableEq

/-- A published report: the rounds of the contest `contestId` of `election`, which is
`"2022-special"`, `"2022-general"` or `"2024-general"`. -/
structure PublishedReport where
  election : String
  contestId : Nat
  rounds : List PublishedRound

def publishedReports : List PublishedReport := [
  -- U.S. Representative (Special General)
  { election := "2022-special", contestId := 69, rounds := [
    { votes := [(215, 53810), (217, 58973), (218, 75799)],
      blanks := 3412, exhausted := 0, overvotes := 295 },
    { votes := [(215, 0), (217, 86026), (218, 91266)],
      blanks := 3412, exhausted := 11243, overvotes := 342 }] },
  -- U.S. Senator
  { election := "2022-general", contestId := 3, rounds := [
    { votes := [(271, 28233), (272, 8575), (273, 114118), (274, 112101)],
      blanks := 3271, exhausted := 0, overvotes := 499 },
    { votes := [(271, 29134), (272, 0), (273, 115759), (274, 115310)],
      blanks := 3271, exhausted := 2806, overvotes := 517 },
    { votes := [(271, 0), (272, 0), (273, 136330), (274, 117534)],
      blanks := 3271, exhausted := 9107, overvotes := 555 }] },
  -- U.S. Representative
  { election := "2022-general", contestId := 4, rounds := [
    { votes := [(263, 62505), (279, 4999), (264, 68330), (265, 128755)],
      blanks := 1775, exhausted := 0, overvotes := 433 },
    { votes := [(263, 64499), (279, 0), (264, 69399), (265, 129786)],
      blanks := 1775, exhausted := 902, overvotes := 436 },
    { votes := [(263, 0), (279, 0), (264, 112471), (265, 137263)],
      blanks := 1775, exhausted := 14796, overvotes := 492 }] },
  -- Senate District D
  { election := "2022-general", contestId := 9, rounds := [
    { votes := [(132, 6331), (133, 7072), (134, 1787)],
      blanks := 1031, exhausted := 0, overvotes := 15 },
    { votes := [(132, 6594), (133, 7604), (134, 0)],
      blanks := 1031, exhausted := 990, overvotes := 17 }] },
  -- Senate District E
  { election := "2022-general", contestId := 10, rounds := [
    { votes := [(129, 5532), (130, 5652), (131, 5518)],
      blanks := 731, exhausted := 0, overvotes := 4 },
    { votes := [(129, 5949), (130, 7881), (131, 0)],
      blanks := 731, exhausted := 2871, overvotes := 5 }] },
  -- Senate District N
  { election := "2022-general", contestId := 19, rounds := [
    { votes := [(106, 2977), (107, 5170), (108, 3385)],
      blanks := 2226, exhausted := 0, overvotes := 18 },
    { votes := [(106, 0), (107, 6124), (108, 4311)],
      blanks := 2226, exhausted := 1093, overvotes := 22 }] },
  -- House District 11
  { election := "2022-general", contestId := 35, rounds := [
    { votes := [(69, 3484), (70, 1186), (71, 3001)],
      blanks := 516, exhausted := 0, overvotes := 3 },
    { votes := [(69, 3565), (70, 0), (71, 3677)],
      blanks := 516, exhausted := 429, overvotes := 3 }] },
  -- House District 15
  { election := "2022-general", contestId := 39, rounds := [
    { votes := [(59, 3384), (60, 1039), (61, 2839)],
      blanks := 442, exhausted := 0, overvotes := 5 },
    { votes := [(59, 3476), (60, 0), (61, 3483)],
      blanks := 442, exhausted := 303, overvotes := 5 }] },
  -- House District 18
  { election := "2022-general", contestId := 42, rounds := [
    { votes := [(50, 444), (51, 927), (52, 746)],
      blanks := 178, exhausted := 0, overvotes := 2 },
    { votes := [(50, 0), (51, 968), (52, 1045)],
      blanks := 178, exhausted := 104, overvotes := 2 }] },
  -- House District 28
  { election := "2022-general", contestId := 52, rounds := [
    { votes := [(23, 1287), (24, 2217), (25, 863), (26, 1575)],
      blanks := 1143, exhausted := 0, overvotes := 13 },
    { votes := [(23, 1491), (24, 2418), (25, 0), (26, 1721)],
      blanks := 1143, exhausted := 311, overvotes := 14 },
    { votes := [(23, 0), (24, 3120), (25, 0), (26, 1936)],
      blanks := 1143, exhausted := 884, overvotes := 15 }] },
  -- House District 30
  { election := "2022-general", contestId := 54, rounds := [
    { votes := [(18, 2608), (19, 3394), (20, 1517)],
      blanks := 603, exhausted := 0, overvotes := 13 },
    { votes := [(18, 2884), (19, 3662), (20, 0)],
      blanks := 603, exhausted := 973, overvotes := 13 }] },
  -- House District 31
  { election := "2022-general", contestId := 55, rounds := [
    { votes := [(15, 1092), (16, 2478), (17, 1492)],
      blanks := 259, exhausted := 0, overvotes := 9 },
    { votes := [(15, 0), (16, 2589), (17, 2074)],
      blanks := 259, exhausted := 399, overvotes := 9 }] },
  -- House District 34
  { election := "2022-general", contestId := 58, rounds := [
    { votes := [(8, 3175), (9, 3615), (10, 586)],
      blanks := 310, exhausted := 0, overvotes := 7 },
    { votes := [(8, 3200), (9, 4013), (10, 0)],
      blanks := 310, exhausted := 162, overvotes := 8 }] },
  -- U.S. Representative
  { election := "2024-general", contestId := 7, rounds := [
    { votes := [(517, 159777), (552, 3558), (520, 13210), (518, 152948)],
      blanks := 5788, exhausted := 0, overvotes := 572 },
    { votes := [(517, 160044), (552, 0), (520, 13871), (518, 154261)],
      blanks := 5788, exhausted := 1300, overvotes := 589 },
    { votes := [(517, 164861), (552, 0), (520, 0), (518, 156985)],
      blanks := 5788, exhausted := 7595, overvotes := 624 }] },
  -- Senate District D
  { election := "2024-general", contestId := 11, rounds := [
    { votes := [(362, 7865), (364, 2196), (365, 9257)],
      blanks := 803, exhausted := 0, overvotes := 17 },
    { votes := [(362, 8114), (364, 0), (365, 9802)],
      blanks := 803, exhausted := 1399, overvotes := 20 }] },
  -- Senate District F
  { election := "2024-general", contestId := 13, rounds := [
    { votes := [(366, 8180), (367, 7657), (368, 1184)],
      blanks := 935, exhausted := 0, overvotes := 11 },
    { votes := [(366, 8678), (367, 7744), (368, 0)],
      blanks := 935, exhausted := 599, overvotes := 11 }] },
  -- Senate District L
  { election := "2024-general", contestId := 19, rounds := [
    { votes := [(537, 7698), (536, 9092), (551, 2770)],
      blanks := 761, exhausted := 0, overvotes := 19 },
    { votes := [(537, 7939), (536, 9892), (551, 0)],
      blanks := 761, exhausted := 1728, overvotes := 20 }] },
  -- House District 6
  { election := "2024-general", contestId := 33, rounds := [
    { votes := [(391, 5363), (392, 4965), (393, 1078)],
      blanks := 376, exhausted := 0, overvotes := 16 },
    { votes := [(391, 5638), (392, 5150), (393, 0)],
      blanks := 376, exhausted := 618, overvotes := 16 }] },
  -- House District 28
  { election := "2024-general", contestId := 55, rounds := [
    { votes := [(437, 2014), (438, 2787), (439, 2929)],
      blanks := 1177, exhausted := 0, overvotes := 8 },
    { votes := [(437, 0), (438, 3231), (439, 3243)],
      blanks := 1177, exhausted := 1255, overvotes := 9 }] },
  -- House District 36
  { election := "2024-general", contestId := 63, rounds := [
    { votes := [(548, 2291), (538, 2953), (553, 498), (539, 3189)],
      blanks := 431, exhausted := 0, overvotes := 20 },
    { votes := [(548, 2362), (538, 3022), (553, 0), (539, 3282)],
      blanks := 431, exhausted := 264, overvotes := 21 },
    { votes := [(548, 0), (538, 3155), (553, 0), (539, 4070)],
      blanks := 431, exhausted := 1698, overvotes := 28 }] },
  -- House District 38
  { election := "2024-general", contestId := 65, rounds := [
    { votes := [(457, 932), (458, 1166), (459, 1295), (460, 184)],
      blanks := 95, exhausted := 0, overvotes := 35 },
    { votes := [(457, 959), (458, 1200), (459, 1351), (460, 0)],
      blanks := 95, exhausted := 65, overvotes := 37 },
    { votes := [(457, 0), (458, 1411), (459, 1548), (460, 0)],
      blanks := 95, exhausted := 608, overvotes := 45 }] },
  -- House District 40
  { election := "2024-general", contestId := 67, rounds := [
    { votes := [(463, 874), (464, 743), (465, 1425)],
      blanks := 117, exhausted := 0, overvotes := 11 },
    { votes := [(463, 1008), (464, 0), (465, 1541)],
      blanks := 117, exhausted := 489, overvotes := 15 }] }
  ]

end Alaska
