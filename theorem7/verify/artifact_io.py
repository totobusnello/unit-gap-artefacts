"""Atomic, gated CSV writing for result artefacts — the structural fix for E37 and its relatives.

WHY THIS EXISTS. On 2026-08-11 the same defect produced a bad artefact FOUR times in one day:

  1. `atlas_n4_forced.py` saved only inside the compute branch, so a retry run truncated the CSV to 188
     of 222 rows — cutting a family class — while its summary printed the complete table from memory.
  2. Running `tree_chain_n5.py` on the Mac overwrote the CSV harvested from the VPS (same OUT path).
  3. A `git add -A` committed `formula_mode_validation.csv` while it was still being written, so a file
     recording spurious FAILs entered the tree and the history.
  4. The same validation run died at 134 of 159 when its shell went away, leaving a silent prefix. The
     completeness gate could not fire: gates run AFTER the loop, and a killed process has no after.

The first fix (write again at the end, `sys.exit(3)` on a short file) addresses only case 1. Cases 2-4
are the same shape from other directions, and the pattern is that **a partial file is indistinguishable
from a finished one**. So make it distinguishable by construction:

    write  ->  <name>.partial      (never a valid artefact name; gitignored)
    gate   ->  row count, and any caller-supplied invariant
    rename ->  <name>              (atomic on POSIX; the final name appears only when valid)

A killed process leaves `<name>.partial`, which no script reads, no claim cites and git will not stage.
There is no window in which the real filename holds incomplete content, because `os.replace` is atomic:
readers see either the old file or the new one, never a half-written one.

This also fixes case 2 for free: `write_csv_atomic` refuses to overwrite a file whose content it did not
produce in this run unless `overwrite_ok=True` is passed explicitly, so a local smoke test cannot
silently clobber a harvested result.
"""
import csv
import os
import sys


class ArtefactIncomplete(Exception):
    """Raised when the gate rejects a would-be artefact. The .partial file is left on disk for triage."""


def write_csv_atomic(path, fieldnames, rows, expected_rows=None, invariant=None,
                     overwrite_ok=True, quiet=False):
    """Write `rows` to `path` atomically, only if the gate passes.

    path          final artefact path. Content is written to `path + '.partial'` first.
    expected_rows if given, len(rows) must equal it — the completeness gate.
    invariant     optional callable(rows) -> None|str. Return a string to REJECT with that reason.
                  Use for the checks only the caller knows: distinct-class counts, no-timeout-as-verdict,
                  every expected key present.
    overwrite_ok  False refuses to replace an existing file — the guard for case 2, a local run
                  clobbering a harvested artefact.

    Returns the final path. Raises ArtefactIncomplete without touching the final path if the gate fails.
    """
    tmp = path + ".partial"
    with open(tmp, "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=fieldnames)
        w.writeheader()
        w.writerows(rows)
        fh.flush()
        os.fsync(fh.fileno())

    problems = []
    if expected_rows is not None and len(rows) != expected_rows:
        problems.append(f"{len(rows)} rows written, {expected_rows} expected — this is a PREFIX")
    if invariant is not None:
        msg = invariant(rows)
        if msg:
            problems.append(msg)
    if not overwrite_ok and os.path.exists(path):
        problems.append(f"{os.path.basename(path)} already exists and overwrite_ok=False — refusing to "
                        f"clobber a file this run did not produce (it may be a harvested result)")

    if problems:
        raise ArtefactIncomplete(
            f"artefact REJECTED, final file not written. Left at {os.path.basename(tmp)} for triage:\n"
            + "\n".join(f"  - {p}" for p in problems))

    os.replace(tmp, path)   # atomic: readers see the old file or the new one, never a partial
    if not quiet:
        print(f"    artefact written atomically: {os.path.relpath(path)} ({len(rows)} rows)", flush=True)
    return path


def checkpoint_csv(path, fieldnames, rows):
    """Mid-run progress dump for a long job, written ONLY to the .partial name.

    Long runs want their progress on disk in case of a crash, which is what motivated the
    write-after-every-item pattern that caused case 1. Keep the habit, but never let progress land on the
    real filename: that is precisely what made a prefix look like a result. Call this in the loop and
    `write_csv_atomic` once at the end.
    """
    with open(path + ".partial", "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=fieldnames)
        w.writeheader()
        w.writerows(rows)


def fail(exc):
    """Print an ArtefactIncomplete and exit 3 — the code the harvest tooling already treats as 'do not
    harvest'. Kept here so every producer script reports the same way."""
    print(f"\n  *** {exc} ***\n"
          f"  *** Do not harvest, commit or cite anything from this run. ***", flush=True)
    sys.exit(3)
