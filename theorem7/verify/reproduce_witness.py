"""Regenerate and machine-recheck a forced-multiple-reconvergence witness FROM SCRATCH.

Default target: the seventh, non-lift class at n=5, f = 0x03de & (~x0 | x4) = 0x03de0154.
The two other non-lift n=5 witnesses and the n=4 base of the Lift Theorem are reproducible
by passing their truth table and opt on the command line:

    python3 reproduce_witness.py                      # 0x03de0154 (default), n=5, opt=8
    python3 reproduce_witness.py 0xabfe03de 8          # 2nd non-lift n=5 witness
    python3 reproduce_witness.py 0x57df03de 8          # 3rd non-lift n=5 witness
    python3 reproduce_witness.py 0x03de 6              # n=4 base of the Lift Theorem
    python3 reproduce_witness.py 0x03de 6 --full       # ...also its forced-multi certificate

Add --full to also regenerate the forced-multi certificate (a large DRAT for n=5, ~minutes).

Repo-relative and machine-independent (no hardcoded paths, no python-version assumption).
Prerequisites on PATH: python3, kissat, drat-trim  (see ../VERIFY.md for a one-line setup).

What each leg establishes for f (on n variables, inferred from the truth table):
  opt = OPT      : circuit UNSAT at k=1..OPT-1 (DRAT, drat-trim VERIFIED) + a k=OPT SAT model that
                   verify_circuit confirms computes f. => opt(f) = OPT.
  tree <= OPT+1  : a fan-out-1 formula of OPT+1 gates computes f (SAT model, verify_circuit). [self-certifying]
  forced-multi   : "some optimum has <=1 reconvergent gate" is UNSAT at k=OPT. With tree>=OPT+1
                   forced by this, tree = OPT+1, so gap = 1. The encoding adds NO gate-ordering
                   symmetry break beyond the base encoder's WLOG normalizations (operand order a<b,
                   no duplicate gate, no dead gate, output-last) — all sound at a proven optimum.
  canalizing?    : reported (a variable with a constant cofactor => f is an AND/OR-lift). The three
                   n=5 witnesses are non-canalizing (not lifts); the n=4 base 0x03de may be canalizing.
Portability: a CNF's SHA is deterministic from the encoder (pinned for the default witness). A DRAT's
bytes depend on the solver build, so the portable acceptance test is "drat-trim VERIFIED against the
regenerated CNF" — not equality of DRAT bytes.
"""
import os, sys, argparse

HERE = os.path.dirname(os.path.abspath(__file__))
ENC = os.path.normpath(os.path.join(HERE, "..", "encoder"))
sys.path.insert(0, ENC)   # aig_exact (canonical, with formula mode), n5_forced_test, zc_certify
from aig_exact import AIGEncoder, verify_circuit             # noqa: E402
from n5_forced_test import build_amo_shared                  # noqa: E402
from zc_certify import write_cnf, kissat, drat_verify, sha16 # noqa: E402

# pinned, encoder-deterministic CNF SHA of the default witness's forced-multi instance
PINNED_FORCED_CNF = {0x03de0154: "ed3b8350f72f8078"}
# regenerated artifacts go here (gitignored); the committed read-only spot-check samples are in sample_certs/
OUT = os.path.join(HERE, "_generated")


def infer_n(tt):
    n = 1
    while (1 << (1 << n)) <= tt:
        n += 1
    return n


def is_canalizing(tt, n):
    for i in range(n):
        for val in (0, 1):
            bits = [(tt >> a) & 1 for a in range(1 << n) if ((a >> i) & 1) == val]
            if all(b == 0 for b in bits) or all(b == 1 for b in bits):
                return True
    return False


def leg_optlb(tt, n, opt):
    print(f"\n[opt-LB] circuit UNSAT for k=1..{opt-1} (=> opt >= {opt})")
    allok = True
    for k in range(1, opt):
        enc = AIGEncoder(n, k, tt).build()
        if any(len(cl) == 0 for cl in enc.clauses):
            print(f"  k={k}: UNSAT (syntactic)"); continue
        cnf = os.path.join(OUT, f"n{n}_{tt:#x}_opt_k{k}.cnf"); write_cnf(enc.nvars, enc.clauses, cnf)
        drat = os.path.join(OUT, f"n{n}_{tt:#x}_opt_k{k}.drat")
        rc, _ = kissat(cnf, drat)
        if rc != 20:
            print(f"  k={k}: expected UNSAT(20), got {rc} — ABORT"); return False
        ok = drat_verify(cnf, drat); allok = allok and ok
        print(f"  k={k}: UNSAT  cnf={sha16(cnf)}  drat-trim={'VERIFIED' if ok else 'FAIL'}")
    return allok


def leg_optwitness(tt, n, opt):
    enc = AIGEncoder(n, opt, tt).build()
    cnf = os.path.join(OUT, f"n{n}_{tt:#x}_opt_k{opt}.cnf"); write_cnf(enc.nvars, enc.clauses, cnf)
    rc, model = kissat(cnf)
    if rc != 10:
        print(f"\n[opt witness] k={opt} expected SAT(10), got {rc} — ABORT"); return False
    gates, op = enc.decode(model); ok = verify_circuit(n, tt, gates, op)
    print(f"\n[opt witness] k={opt} SAT  cnf={sha16(cnf)}  verify_circuit={ok}  => opt = {opt}")
    return ok


def leg_tree(tt, n, opt):
    enc = AIGEncoder(n, opt + 1, tt, formula=True).build()
    cnf = os.path.join(OUT, f"n{n}_{tt:#x}_tree_k{opt+1}.cnf"); write_cnf(enc.nvars, enc.clauses, cnf)
    rc, model = kissat(cnf)
    if rc != 10:
        print(f"\n[tree] formula k={opt+1} expected SAT(10), got {rc} — ABORT"); return False
    gates, op = enc.decode(model); ok = verify_circuit(n, tt, gates, op)
    print(f"\n[tree] fan-out-1 formula k={opt+1} SAT  cnf={sha16(cnf)}  verify_circuit={ok}  => tree <= {opt+1} (self-certifying)")
    return ok


def leg_forced(tt, n, opt):
    print(f"\n[forced-multi] amo-shared UNSAT at k={opt}, no gate-ordering symmetry break")
    nv, cl = build_amo_shared(tt, opt, n=n, gate_order_b=False)
    cnf = os.path.join(OUT, f"n{n}_{tt:#x}_amo1shared_nosb.cnf"); write_cnf(nv, cl, cnf)
    csha = sha16(cnf); ok_sha = True
    exp = PINNED_FORCED_CNF.get(tt)
    if exp:
        ok_sha = (csha == exp)
        print(f"  cnf sha16={csha}  (pinned {exp}: {'MATCH' if ok_sha else 'MISMATCH!'})")
    else:
        print(f"  cnf sha16={csha}  (not pinned for this tt)")
    drat = os.path.join(OUT, f"n{n}_{tt:#x}_amo1shared_nosb.drat")
    rc, _ = kissat(cnf, drat)
    if rc != 20:
        print(f"  expected UNSAT(20), got {rc} — ABORT"); return False
    ok = drat_verify(cnf, drat)
    print(f"  UNSAT  drat-trim={'VERIFIED' if ok else 'FAIL'}  => every optimum has >=2 reconvergences")
    return ok and ok_sha


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("tt", nargs="?", default="0x03de0154", help="truth table (hex), default 0x03de0154")
    ap.add_argument("opt", nargs="?", type=int, default=8, help="opt(f), default 8")
    ap.add_argument("--n", type=int, default=None, help="number of variables (default: inferred)")
    ap.add_argument("--full", action="store_true", help="also regenerate the forced-multi certificate")
    args = ap.parse_args()
    tt = int(args.tt, 16); opt = args.opt
    n = args.n if args.n is not None else infer_n(tt)
    os.makedirs(OUT, exist_ok=True)
    print(f"=== reproduce witness {tt:#x}  (n={n}, opt={opt}) ===")
    res = {
        f"opt-LB (k=1..{opt-1} UNSAT)": leg_optlb(tt, n, opt),
        f"opt witness (k={opt} SAT)": leg_optwitness(tt, n, opt),
        f"tree<= {opt+1} (formula witness)": leg_tree(tt, n, opt),
    }
    if args.full:
        res["forced-multi (no gate-ordering SB)"] = leg_forced(tt, n, opt)
    can = is_canalizing(tt, n)
    print(f"\n[canalizing?] {can}  => {'IS an AND/OR-lift' if can else 'non-canalizing: NOT a lift'}")
    print("\n=== SUMMARY ===")
    for k, v in res.items():
        print(f"  [{'PASS' if v else 'FAIL'}] {k}")
    print(f"  [info] canalizing={can}")
    print("\nClass count (>=9 distinct NPN classes among the 3 non-lift witnesses + 6 lifts): "
          "run  python3 npn_check_bk5.py")
    sys.exit(0 if all(res.values()) else 1)


if __name__ == "__main__":
    main()
