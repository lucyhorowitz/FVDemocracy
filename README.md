# FVDemocracy

Lean 4 formalization of Alaska's ranked-choice tabulation statute and of the
cast vote record (CVR) export.

The statute next to its formalization: https://lucyhorowitz.github.io/FVDemocracy/

The Lean project has no dependencies beyond Lean core and `Std` (no Mathlib).

## Layout

- `FVDemocracy/Alaska/Statute/` — Lean formalization of the statute:
  - `StatuteDefs.lean` — definitions from AS 15.15.350(g) (overvote, skipped
    ranking, inactive ballot, highest continuing candidate) and results about
    ballot outcomes.
  - `Tallies.lean` — vote totals per candidate, active ballots, and the majority winner.
  - `WriteIns.lean` — the write-in qualification test of AS 15.15.365(a).
  - `Spec.lean` — the outcomes the tabulation procedure of AS 15.15.350(d)
    allows, stated without reference to the implementation.
  - `Rounds.lean` — single rounds in which a candidate is defeated, the final round,
    and the tree of possible round sequences.
  - `Tabulate.lean` — the full tabulation and its properties.
  - `Correctness.lean` — a proof that the tabulation gives exactly the outcomes
    `Spec.lean` allows.
  - `SpecProperties.lean` — properties of the outcomes `Spec.lean` allows: a
    candidate is always elected, only candidates are elected, the outcome is
    determined when there are no ties, and in every round the votes add up to
    the ballots tabulated.
  - `Simplifications.lean` — the rounds without a separate final round, and proofs
    that neither the majority test of the initial tabulation nor the separate final
    round changes which candidates can be elected.
  - `ReadBallot.lean` — reading a ballot ranking by ranking as AS 15.15.350(d),
    (e)(1) and (e)(2) describe, and a proof that this gives the same result as
    the definitions from (g)(2).
  - `Examples/Overvote.lean` — a ballot with an overvote at rank 2, tabulated under
    two orders of defeat: one in which the overvote is never encountered and one in
    which it is.
  - `Examples/Duplicates.lean` — ballots with duplicate rankings (6 AAC 25.072) on
    which `resultOf`, `resultOf` after removing duplicates, and the reproduction
    give different results.
- `FVDemocracy/Alaska/Reproduction/` — the tabulation that reproduces the published results,
  built on `Statute/`:
  - `Tabulate.lean` — reading a ballot by the rules that reproduce the published
    reports, a proof that this is the statute's reading of the ballot cut at its
    first overvote with repeated candidates removed, the tabulation
    `reproductionTabulate`, and an election in which it elects a candidate the
    statute does not allow (`not_reproductionTabulate_correct`).
  - `PublishedReports.lean` — the round-by-round totals of every published
    multi-round report of the 2022 special, 2022 general and 2024 general
    elections, except the recounts.
  - `Report.lean` — `reportRounds`, the rounds of `reproductionTabulate` in the
    form of a published report.
- `FVDemocracy/Alaska/Duplicates.lean` — removing duplicate rankings (6 AAC 25.072)
  from the ballots before the tabulation, and proofs that this changes nothing on
  ballots without a duplicate ranking and that on ballots without an overvote the
  reproduction is the tabulation with duplicates removed.
- `FVDemocracy/Alaska/Profile.lean` — ballot profiles (each distinct list of
  rankings with its number of ballots), `Profile.ofBallots`, which computes the
  profile of a list of ballots, the tabulation of a profile, and proofs that
  `Profile.ofBallots` gives a profile of the ballots and that on a profile of an
  election's ballots the tabulation gives the results of `tabulate`,
  `reproductionTabulate` and `reportRounds`.
- `FVDemocracy/Alaska/ProfileData.lean` — the JSON data files of profiles, with
  round-trip proofs, and the `profile_data%` elaborator, which reads a data file
  while a result file is built and writes the missing data files of a CVR export
  first (see Results below).
- `FVDemocracy/Alaska/Results/` — the results of every ranked-choice contest of
  the three elections (see Results below):
  - `data/<Election>/<Contest>.json` — the profile of the contest's ballots,
    generated from the CVR export.
  - `<Election>/<Contest>.lean` — theorems giving the results of `tabulate` and
    `reproductionTabulate` and, for a contest with a published report, that the
    rounds of `reproductionTabulate` are those of the report, for every election
    with the ballots of the profile.
  - `<Election>.lean` — imports the result files of the election.
- `FVDemocracy/Alaska/ParseCVR/` — the CVR export:
  - `Export.lean` — types for the export files.
  - `Parse.lean` — JSON parsing of the export, including streaming
    `CvrExport.json` one session at a time.
  - `ParseProofs.lean` — round-trip proofs for the parsers.
- `FVDemocracy/Util/List.lean` — lemmas about `List.eraseDups` that Lean core does not
  provide.
- `Main.lean` — the `alaska` executable, which tabulates the contests of a CVR
  export (see below).
- `scripts/download_cvr.py` — downloads the CVR exports (see Data below).
- `site/` — a static website that shows the statute text next to the Lean
  formalization (see below).

## Building

Requires [elan](https://github.com/leanprover/elan); the toolchain is pinned in
`lean-toolchain`.

```bash
lake build
```

This builds the library and the `alaska` executable. The `lean` workflow runs
`lake build` on every push to `main` and on every pull request.

## Tabulating an export

```bash
lake exe alaska <export-dir> --list               # the ranked-choice contests
lake exe alaska <export-dir> [contest-id ...]     # tabulate these contests, or all of them
```

For example, `lake exe alaska cvr/2022-special 69` tabulates the 2022 special
general election and `lake exe alaska cvr/2024-general 7` the 2024 U.S.
House race. The export directory holds either one `CvrExport.json` or files
`CvrExport_<n>.json`. Each contest's rounds are printed with candidate names,
vote totals and percentages of active ballots, following every branch of a tie;
the program fails if the winners it prints differ from those of `tabulate`.

Ballots use each session's `Modified` state where present, ambiguous marks are
dropped, and a contest marked `InvalidContest` on a card is left out of that
ballot. Reading a general-election export takes about 90 seconds.

## Reproducing the published results

```bash
lake exe alaska cvr/2022-special --reproduce 2022-special
lake exe alaska cvr/2022-general --reproduce 2022-general
lake exe alaska cvr/2024-general --reproduce 2024-general
```

Each command tabulates the contests of `publishedReports` for that election with
`reproductionTabulate`. In every round, it compares each candidate's votes and the
Blanks, Exhausted and Overvotes counts with the published report. It prints one
line per contest and exits with status 1 if any number differs.

## Results

```bash
lake exe alaska cvr/2022-general --results 2022-general FVDemocracy/Alaska/Results
lake build Results
```

`--results <election> <out-dir>` writes two files for each ranked-choice contest
of the export: the data file `<out-dir>/data/<Election>/<Contest>.json` and the
Lean file `<out-dir>/<Election>/<Contest>.lean`. The data file holds
`Profile.ofBallots` of the contest's ballots, which `ofBallots_isProfileOf`
proves is a profile of them. The Lean file defines the candidates `cands` and the
profile `profile` of the contest, and proves theorems giving the results of
`tabulate` and `reproductionTabulate` and, for the contests of
`publishedReports`, that `reportRounds` gives the published rounds. Before
writing, the program checks natively that the profile tabulation gives these
results on the ballots.

`profile` is `profile_data% "<export-dir>" <contest-id> "<data-file>"`, with
paths relative to the package root. While the Lean file is built, this reads the
data file, checks that it encodes back to the JSON it was read from, and
elaborates to its profile. If the data file is missing, it first reads the
export and writes the data file of every ranked-choice contest of the export
that has none. This runs in the interpreter and takes about 75 seconds for the
2022 special export and about 5 minutes for a general-election export. The result
files are in the `Results` library, which `needs` the data directory, so Lake
rebuilds them when a data file changes.

The theorems take as hypotheses that an election has the candidates `cands` and
that `profile` is a profile of its ballots. From the export to these:

- proved: `Session.toBallot?` (one session's ballot for a contest) meets its
  specification, `Profile.ofBallots` gives a profile of the ballots, and the
  JSON of the export and of the data files decodes to what was encoded;
- not proved: reading the export files (`readBallots`), and that `profile_data%`
  turns the data file's profile into the term `profile`.

`decide +kernel` checks the theorems, without `native_decide`. `Results` is not
a default target, so `lake build` and the `lean` workflow do not check them. `lake build Results` builds all 115 result files in about 75 seconds with
parallel jobs; the 2024 presidential contest alone takes about that long.

## Comparing readings of duplicate rankings

```bash
lake exe alaska <export-dir> --dropduplicates [contest-id ...]
```

This tabulates the given contests, or all of them, five ways: with `tabulate`,
with `tabulate` after `Election.dropDuplicates`, with `reproductionTabulate`, with
`truncateTabulate`, and with `truncateTabulate` after `Election.dropDuplicates`.
For each contest it prints the number of ballots with a duplicate ranking, then each
round's votes and inactive ballots under the five side by side, and the winners.

## Data

The CVR exports are not tracked. `python3 scripts/download_cvr.py` downloads them
from the Division of Elections into `cvr/2022-special/`,
`cvr/2022-general/` and `cvr/2024-general/`, skipping any that are
already there; pass election names such as `2024-general` to fetch only those.
It needs only the Python standard library.

## Statute site

`site/` is a static page showing AS 15.15.350 and AS 15.15.365, published at
https://lucyhorowitz.github.io/FVDemocracy/. Clicking a phrase
of the statute shows the Lean declarations that formalize it in a panel beside the
text; clicking a clause number shows everything for that clause. Defined
terms and citations in the statute text link to the clauses they refer to, and names
in the Lean link to their declarations. Theorems are shown without their proofs. There is no build step:
open `site/index.html` directly. Fonts load from Google Fonts.

`site/content.js` holds the statute text and, for each clause, the names of the Lean
declarations shown under it (`decls`) and of those shown elsewhere that it also
corresponds to (`refs`), and under `phrases` the declarations for each marked
phrase. `python3 site/extract.py` reads those names, copies each
declaration's source from `FVDemocracy/Alaska/Statute/*.lean` and
`FVDemocracy/Alaska/Statute/Examples/*.lean` into `site/lean.js`, and fails
if a name is not declared exactly once. Run it after changing the Lean or the lists
in `content.js`; `python3 site/extract.py --check` exits with an error if `lean.js`
is out of date.

`python3 site/serve.py` serves the page at `http://localhost:8000/` (`--port` to
change). Served this way, the panel of a selected clause or phrase has an Edit note
or Add note button, which writes the note to `content.js`; saving an empty note
removes it. `python3 -m unittest discover -s site/tests` runs its tests.

The `site` workflow runs on every push to `main`, checks that `lean.js` is up to
date, and publishes the page (`index.html`, `style.css`, `content.js`, `lean.js`,
`app.js`) to GitHub Pages. It can also be run by hand, with `deploy` checked to
publish.
