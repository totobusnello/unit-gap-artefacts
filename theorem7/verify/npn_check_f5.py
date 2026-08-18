"""F5 with BOTH lift directions — the count was low because the script only lifted by AND.

Found by Kirill Krinkin, 2026-08-11, reading the artefacts without a solver: "your lemma covers the
OR-lifts, npn_check_f5.py lifts only by AND". He is right. `npn_check_f5.py` builds its lift set as
`{z << 16 for z in F4}`, which is `z AND x4` and nothing else, while the Lift Lemma (claim 0036)
proves the statement for `z AND x_new` **and** `z OR x_new`. So the published count of 10 undercounted
its own closure.

This script counts both directions. It is pure Python over the full NPN group of n=5 (all
5!*2^5*2 = 7680 transforms) — no solver, so anyone can re-run it in seconds and the result depends on
no certificate.

RESULT (2026-08-11): **F5 >= 15**, not 10. Decomposed:
  * 6 AND-lifts  -> 6 distinct classes
  * 6 OR-lifts   -> 6 distinct classes
  * exactly ONE collision between the two sets, so the lift closure is **11** classes, not 6
  * 4 non-lift witnesses, pairwise distinct and distinct from all lifts
  => 11 + 4 = 15

WHY EXACTLY ONE COLLISION, and it is not a coincidence. Under NPN of the 5-variable function,
`OR-lift(z) = 0xFFFF0000 | z` maps to `AND-lift(~z)`: negate the output, then negate x4. The output
negation of the 5-variable function is spent doing that, so two AND-lifts coincide only under the
subgroup that fixes x4 — permutations and INPUT negations of the four original variables, without
output negation. Therefore

    OR-lift(z) ~ AND-lift(z)   <=>   ~z is NP-equivalent to z   (NP = perms + input negations only)
                               <=>   z is NP-self-complementary.

Of the six n=4 classes exactly one, `0x178e`, is NP-self-complementary — checked below — and it is
exactly the one whose two lifts collide. The check prints the per-class verdict so the explanation is
falsifiable rather than decorative.

RECONCILIATION with the number in Krinkin's letter. He wrote "F_5 >= 14, not 9". 14 = 11 lifts + 3
non-lifts: he had the three witnesses from the directed sweep, not the fourth (`0x09c50800`, promoted
2026-08-10, after the letter he was answering). Our 15 = 11 + 4. The two computations agree exactly;
his arithmetic also requires exactly one AND/OR collision, which is independent confirmation of the
structural fact above.

Usage: python3 npn_check_f5.py
"""
from collections import defaultdict
from itertools import permutations

N5, N4 = 5, 4
R5, R4 = 1 << N5, 1 << N4
M5, M4 = (1 << R5) - 1, (1 << R4) - 1
P5, P4 = list(permutations(range(N5))), list(permutations(range(N4)))

F4 = [0x0358, 0x0359, 0x03DE, 0x06B5, 0x07BC, 0x178E]
NONLIFTS = {
    "0x03de0154": 0x03DE0154,   # directed sweep, no-SB certificate
    "0xabfe03de": 0xABFE03DE,   # directed sweep, gate_order_b
    "0x57df03de": 0x57DF03DE,   # directed sweep, gate_order_b
    "0x09c50800": 0x09C50800,   # random census, no-SB certificate
    # Acrescentadas 2026-08-14 pelo lote k=9 (`law_forced_multi_k9_vps.csv`). Vieram da construção
    # `beside`, NÃO do lift — logo estão fora do fecho das seis sementes de n=4, e é por isso que
    # entram aqui e não em F4. Ambas com amo-shared UNSAT em k=opt=9, DRAT `s VERIFIED`, sem
    # symmetry breaking. Note que as DUAS saem da mesma semente `0x07bc` por operadores diferentes:
    # é o dado que sustenta a hipótese de que a forçosidade sob `beside` é propriedade da semente.
    "0x07bc0514": 0x07BC0514,   # beside `z and (~x0 or x4)`, no-SB certificate, 3869s
    "0x57fd07bc": 0x57FD07BC,   # beside `z or (~x0 and x4)`, no-SB certificate, 3159s
}


def apply_t(tt, perm, neg, n):
    rows, out = 1 << n, 0
    for a in range(rows):
        b = 0
        for i in range(n):
            if (a >> i) & 1:
                b |= 1 << perm[i]
        b ^= neg
        if (tt >> b) & 1:
            out |= 1 << a
    return out


def npn_canon(tt, n=N5):
    perms = P5 if n == N5 else P4
    mask = M5 if n == N5 else M4
    best = None
    for p in perms:
        for neg in range(1 << n):
            g = apply_t(tt, p, neg, n)
            for x in (g, (~g) & mask):
                if best is None or x < best:
                    best = x
    return best


def np_orbit_no_output_neg(tt):
    """Perms + INPUT negations only. Output negation is deliberately excluded — see the docstring."""
    return {apply_t(tt, p, neg, N4) for p in P4 for neg in range(1 << N4)}


def and_lift(z):
    return z << 16            # z AND x4 : high half = z, low half = 0


def or_lift(z):
    return z | (0xFFFF << 16)  # z OR x4 : low half = z, high half = all ones


# The two lift formulas must reproduce the witnesses already in the ledger (claim 0035), or the
# convention is wrong and every count below is wrong with it.
assert and_lift(0x03DE) == 0x03DE0000, hex(and_lift(0x03DE))
assert or_lift(0x03DE) == 0xFFFF03DE, hex(or_lift(0x03DE))
print("convention check OK: and_lift(0x03de)=0x03de0000, or_lift(0x03de)=0xffff03de (claim 0035)\n")

objs = {}
for z in F4:
    objs[f"AND(0x{z:04x})"] = and_lift(z)
    objs[f"OR(0x{z:04x})"] = or_lift(z)
objs.update(NONLIFTS)

canon = {k: npn_canon(v) for k, v in objs.items()}
groups = defaultdict(list)
for k, v in canon.items():
    groups[v].append(k)

and_c = {canon[f"AND(0x{z:04x})"] for z in F4}
or_c = {canon[f"OR(0x{z:04x})"] for z in F4}
nl_c = {canon[k] for k in NONLIFTS}
lift_c = and_c | or_c
total = len(lift_c | nl_c)

print(f"{len(objs)} functions -> {len(groups)} distinct NPN classes")
print(f"  AND-lifts: {len(and_c)} classes | OR-lifts: {len(or_c)} classes | "
      f"lift closure: {len(lift_c)} classes")
print(f"  collisions between the two lift sets: {len(and_c & or_c)}")
print(f"  non-lifts: {len(nl_c)} classes, overlap with lifts: {len(nl_c & lift_c)}")
for v, ks in groups.items():
    if len(ks) > 1:
        print(f"  COLLIDING: {' == '.join(sorted(ks))}")

print("\nNP-self-complementary (perms + input negations, NO output negation):")
predicted = []
for z in F4:
    selfc = ((~z) & M4) in np_orbit_no_output_neg(z)
    collides = canon[f"AND(0x{z:04x})"] == canon[f"OR(0x{z:04x})"]
    flag = "OK" if selfc == collides else "MISMATCH"
    if selfc:
        predicted.append(z)
    print(f"  0x{z:04x}: self-complementary={selfc!s:5} lifts collide={collides!s:5}  [{flag}]")
    assert selfc == collides, f"explanation refuted at 0x{z:04x}"

print(f"\nexplanation holds on all six: collisions are exactly the NP-self-complementary classes "
      f"({', '.join(f'0x{z:04x}' for z in predicted)})")
print(f"\n*** F5 >= {total}  ({len(lift_c)} lifts + {len(nl_c)} non-lifts) — "
      f"supersedes the earlier count of 10, which came from a counter that lifted only by AND ***")
print("Krinkin's letter says 14 = 11 lifts + the 3 non-lifts he had; the fourth was promoted after it.")

# ── THE RESULT AS A COMMITTED ARTEFACT, not a print ────────────────────────────────────────────────
# Codex REV-0109 blocked on this and was right: the project's own rule is that a number in a claim
# traces to a committed artefact, and until now `F5 >= 15` traced to this script's stdout plus the
# answer restated in its own docstring. A script that prints is not an artefact — that exact phrase is
# in the workspace lessons. The CSV below is the artefact; one row per object, with its canonical form,
# so a reader can recount the classes with `cut`/`sort -u` and never take the summary line on trust.
# Written unconditionally at the end (the E37 discipline: no incremental-only write).
import os  # noqa: E402
import sys  # noqa: E402

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from artifact_io import ArtefactIncomplete, fail, write_csv_atomic  # noqa: E402

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "f5_classes.csv")
rows = []
for name in sorted(objs):
    c = canon[name]
    if name in NONLIFTS:
        kind, seed = "non-lift", ""
    else:
        kind = "AND-lift" if name.startswith("AND(") else "OR-lift"
        seed = name[name.index("(") + 1:-1]
    rows.append({
        "object": name,
        "kind": kind,
        "seed_z_n4": seed,
        "tt_hex_n5": f"0x{objs[name]:08x}",
        "npn_canon_n5": f"0x{c:08x}",
        "class_members": len(groups[c]),
    })
# Gate on the artefact itself, enforced by the atomic writer: the row count must match the 16 objects,
# and the number of DISTINCT canonical forms in the file must equal the count the summary printed. If
# they disagree the file is a prefix or the grouping drifted, and the final filename never appears.
distinct_in_file = len({r["npn_canon_n5"] for r in rows})


def _invariant(rs):
    d = len({r["npn_canon_n5"] for r in rs})
    if d != total:
        return f"{d} distinct canonical forms in the file against a printed count of {total}"
    return None


try:
    write_csv_atomic(OUT, ["object", "kind", "seed_z_n4", "tt_hex_n5", "npn_canon_n5", "class_members"],
                     rows, expected_rows=len(objs), invariant=_invariant, quiet=True)
except ArtefactIncomplete as e:
    fail(e)
print(f"\nartefact written: {os.path.relpath(OUT)} — {len(rows)} objects, "
      f"{distinct_in_file} distinct NPN classes (recount with: "
      f"tail -n +2 f5_classes.csv | cut -d, -f5 | sort -u | wc -l)")
