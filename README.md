# FVDemocracy

This repository formalizes Alaska's ranked-choice voting law in Lean 4 and uses
it to check the results of every ranked-choice contest in Alaska's 2022 special,
2022 general and 2024 general elections. It accompanies the paper *Counting by
the Book: Verifying Alaska's Ranked-Choice Elections*.

There are two models of the tabulation:

- The **statutory model** is our reading of AS 15.15.350 and 6 AAC 25.072. We
  state which outcomes the statute allows, write a tabulator, and prove that the
  tabulator computes exactly those outcomes (`tabulate_correct`).
- The **reproduction model** is a variant that exactly matches the Division of
  Elections' published round-by-round reports. It handles overvotes and repeated
  rankings differently from the statutory model.

For each of the 115 contests we prove what both models return, and for the 22
contests that went past the first round we prove that the reproduction model's
rounds match the published report.

You can read the statute side by side with the Lean at
https://lucyhorowitz.github.io/FVDemocracy/.

The project depends only on Lean core and `Std`, not Mathlib.

## Building

You need [elan](https://github.com/leanprover/elan). The Lean version is pinned
in `lean-toolchain`.

```bash
lake build           # the library and the `alaska` executable
lake build Results   # the per-contest result proofs, about 3 minutes
```

CI (the `lean` workflow) runs `lake build` on every push to `main` and on pull
requests. `Results` isn't a default target, so CI doesn't build it; run
`lake build Results` yourself to check those proofs. Most of its time goes to
the 2024 presidential contest.

## Getting the data

The cast vote records (CVRs) aren't checked in. To download them from the
Division of Elections:

```bash
python3 scripts/download_cvr.py                # all three elections
python3 scripts/download_cvr.py 2024-general   # just one
```

They go into `cvr/2022-special/`, `cvr/2022-general/` and `cvr/2024-general/`,
and exports you already have are skipped. The script only needs the Python
standard library.

## Running the tabulator

```bash
lake exe alaska <export-dir> --list            # list the ranked-choice contests
lake exe alaska <export-dir> [contest-id ...]  # tabulate some contests, or all of them
```

For example, `lake exe alaska cvr/2022-special 69` tabulates the 2022 special
election for U.S. House, and `lake exe alaska cvr/2024-general 7` tabulates the
2024 U.S. House race. The export directory can hold a single `CvrExport.json` or
several `CvrExport_<n>.json` files. The program prints each round with candidate
names, vote totals and percentages of active ballots, and follows every branch
when there is a tie. It fails if the winners it prints aren't the winners of
`tabulate`.

When reading a ballot we use its adjudicated (`Modified`) version if there is
one, drop ambiguous marks, and leave out a contest that is marked
`InvalidContest` on a card. Reading a general-election export takes about a
minute and a half.

### Checking against the published reports

```bash
lake exe alaska cvr/2022-special --reproduce 2022-special
lake exe alaska cvr/2022-general --reproduce 2022-general
lake exe alaska cvr/2024-general --reproduce 2024-general
```

This runs the reproduction model on every contest with a published multi-round
report and compares each round: every candidate's votes, plus the Blanks,
Exhausted and Overvotes counts. It prints one line per contest and exits with
status 1 if any number differs.

### Comparing ways of handling repeated rankings

```bash
lake exe alaska <export-dir> --dropduplicates [contest-id ...]
```

This tabulates each contest five ways: `tabulate`, `tabulate` with repeated
rankings removed first, `reproductionTabulate`, `truncateTabulate`, and
`truncateTabulate` with repeated rankings removed first. For each contest it
prints how many ballots have a repeated ranking, then each round's votes and
inactive ballots under all five side by side, and the winners.

## The per-contest results

The files in `FVDemocracy/Alaska/Results/` are generated, one election at a
time:

```bash
lake exe alaska cvr/2022-general --results 2022-general FVDemocracy/Alaska/Results
```

For each ranked-choice contest this writes a data file,
`data/<Election>/<Contest>.json`, and a Lean file, `<Election>/<Contest>.lean`.
Before writing them, the program runs the tabulation natively to check that the
profile gives the expected results on the ballots.

To keep the proofs tractable, the data file stores the contest's *profile*
rather than its ballots: each distinct list of rankings, with the number of
ballots that have it. The 2022 special election, for example, has 192,289
ballots but only 691 distinct lists of rankings. We prove that
`Profile.ofBallots` produces a profile of the ballots (`ofBallots_isProfileOf`),
and that tabulating a profile gives the same results as tabulating the ballots.

Each Lean file defines the contest's candidates `cands` and its profile
`profile`. It then proves what `tabulate` and `reproductionTabulate` return
and, for contests with a published report, that `reportRounds` gives the
published rounds. The theorems hold for any election with those candidates
whose ballots have that profile. They are checked with `decide +kernel`; nothing
uses `native_decide`.

`profile` is defined as `profile_data% "<export-dir>" <contest-id> "<data-file>"`,
with paths relative to the repository root. When Lean builds the file, this
reads the data file, checks that it encodes back to the same JSON, and turns it
into the profile term. If the data file is missing, it first reads the CVR
export and writes a data file for every contest that doesn't have one yet. This
runs in the interpreter and takes about 75 seconds for the 2022 special
election and about 5 minutes for a general election. The result files live in
the `Results` library, which depends on the data directory, so Lake rebuilds
them whenever a data file changes.

Between the raw CVR export and these theorems, some steps are proved and some
aren't:

- Proved: `Session.toBallot?`, which reads one session's ballot for one contest,
  meets its specification; `Profile.ofBallots` gives a profile of the ballots;
  and the JSON of the export and of the data files decodes to what was encoded.
- Not proved: reading the export files (`readBallots`), and that `profile_data%`
  turns the data file into the right `profile` term.

## Layout

The statutory model is in `FVDemocracy/Alaska/Statute/`:

- `StatuteDefs.lean`: the definitions from AS 15.15.350(g) (overvote, skipped
  ranking, inactive ballot, highest continuing ranking) and results about how a
  single ballot is counted.
- `Tallies.lean`: vote totals for each candidate, active ballots, and the
  majority winner.
- `WriteIns.lean`: the write-in qualification test of AS 15.15.365(a).
- `Spec.lean`: the outcomes the procedure in AS 15.15.350(d) allows, stated
  without reference to the implementation.
- `Rounds.lean`: a single round in which a candidate is defeated, the final
  round, and the tree of possible sequences of rounds.
- `Tabulate.lean`: the tabulator and its basic properties.
- `Correctness.lean`: the proof that the tabulator gives exactly the outcomes
  `Spec.lean` allows.
- `SpecProperties.lean`: properties of the allowed outcomes. Someone is always
  elected, only candidates are elected, the outcome is unique when there are no
  ties, and in every round the votes add up to the number of ballots counted.
- `Simplifications.lean`: a version of the rounds without a separate final
  round, and proofs that neither the first-round majority check nor the separate
  final round changes who can be elected.
- `ReadBallot.lean`: reading a ballot one ranking at a time, the way (d), (e)(1)
  and (e)(2) describe, and a proof that this agrees with the definitions in
  (g)(2).
- `Examples/Overvote.lean`: a ballot with an overvote at rank 2, tabulated under
  two defeat orders. In one the overvote is never reached; in the other it is.
- `Examples/Duplicates.lean`: ballots with repeated rankings (6 AAC 25.072) on
  which `resultOf`, `resultOf` with repeats removed, and the reproduction model
  disagree.

The reproduction model is in `FVDemocracy/Alaska/Reproduction/`, built on top of
`Statute/`:

- `Tabulate.lean`: the reproduction model's ballot reading and its tabulator,
  `reproductionTabulate`. It includes a proof that this reading is the statute's
  reading of the ballot cut off at its first overvote with repeated candidates
  removed, and an election in which it elects a candidate the statute doesn't
  allow (`not_reproductionTabulate_correct`).
- `PublishedReports.lean`: the round-by-round totals from every published
  multi-round report of the three elections, not including recounts.
- `Report.lean`: `reportRounds`, which puts the rounds of `reproductionTabulate`
  in the same form as a published report.
- `Examples/House2022.lean`: real ballots from the 2022 general-election U.S.
  House race and how each model counts them in each round. They include an
  overvote above the highest continuing ranking, a ballot that stays inactive,
  a repeated ranking, and ballots both models count the same way.

Everything else:

- `FVDemocracy/Alaska/Duplicates.lean`: removing repeated rankings before
  tabulating. It proves that this changes nothing on ballots without a repeated
  ranking, and that on ballots without an overvote the reproduction model is
  the same as tabulating with repeats removed.
- `FVDemocracy/Alaska/Profile.lean`: ballot profiles, `Profile.ofBallots`, and
  the proofs that on a profile of an election's ballots, tabulating gives the
  results of `tabulate`, `reproductionTabulate` and `reportRounds`.
- `FVDemocracy/Alaska/ProfileData.lean`: the JSON format for profiles, with
  round-trip proofs, and the `profile_data%` elaborator.
- `FVDemocracy/Alaska/Results/`: the generated per-contest results described
  above. `<Election>.lean` imports all the contests of one election.
- `FVDemocracy/Alaska/ParseCVR/`: types for the CVR export files
  (`Export.lean`), a JSON parser that can stream `CvrExport.json` one session at
  a time (`Parse.lean`), and round-trip proofs for the parsers
  (`ParseProofs.lean`).
- `FVDemocracy/Util/List.lean`: lemmas about `List.eraseDups` that Lean core
  doesn't have.
- `Main.lean`: the `alaska` executable.
- `scripts/download_cvr.py`: downloads the CVRs.
- `site/`: the statute website.

## The statute website

`site/` is a static page that shows AS 15.15.350 and AS 15.15.365 next to the
Lean that formalizes them. It's published at
https://lucyhorowitz.github.io/FVDemocracy/. Click a phrase in the statute to
see the Lean declarations for it, or a clause number to see everything for that
clause. Defined terms and cross-references in the statute link to the clauses
they refer to, and names in the Lean link to their declarations. Proofs aren't
shown. There's no build step, so you can just open `site/index.html`. Fonts load
from Google Fonts.

The statute text lives in `site/content.js`, along with the Lean declarations
that go with each clause. `decls` lists the declarations shown under a clause,
`refs` lists ones shown elsewhere that also relate to it, and `phrases` gives
the declarations for each marked phrase. `python3 site/extract.py` copies the
source of each named declaration from `FVDemocracy/Alaska/Statute/*.lean` and
`FVDemocracy/Alaska/Statute/Examples/*.lean` into `site/lean.js`, and fails if a
name isn't declared exactly once. Rerun it after changing the Lean or
`content.js`. With `--check`, it exits with an error if `lean.js` is out of
date.

To edit the notes on the page, run `python3 site/serve.py` and open
`http://localhost:8000/` (use `--port` to change the port). The panel for a
clause or phrase then has an Edit note or Add note button, which saves the note
to `content.js`. Saving an empty note deletes it. To run the site's tests:
`python3 -m unittest discover -s site/tests`.

On every push to `main`, the `site` workflow checks that `lean.js` is up to date
and publishes `index.html`, `style.css`, `content.js`, `lean.js` and `app.js` to
GitHub Pages. You can also run it by hand and check `deploy` to publish.

---

*This README was written by Claude.*
