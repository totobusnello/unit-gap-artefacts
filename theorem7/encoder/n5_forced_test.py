"""EXP-AIG-N5 forced-multi test — does claim 0034's Z phenomenon (forced multiple
reconvergence) generalize to n=5? Given a gap=1 n=5 function, certify by SAT+DRAT whether
EVERY size-optimal AIG has >=2 fan-out->=2 gates.

Reuses the at-most-one-shared encoding from zc_certify.py (there hardcoded N=4), generalized
to arbitrary N. Chain per function:
  (1) opt(f) = OPT : circuit UNSAT k=1..OPT-1 (DRAT) + witness k=OPT (verify_circuit).
  (2) tree(f) = OPT+1 (gap=1): formula UNSAT k=OPT (DRAT) + witness k=OPT+1.
  (3) forced-multi : "exists opt-gate AIG with <=1 fan-out->=2 gate" is UNSAT (DRAT).
UNSAT in (3) ==> Z-like at n=5 (single reconvergence impossible) ==> 0034 generalizes.

Usage: python3 n5_forced_test.py <tt_int> <opt>
"""
import sys
import os
from itertools import combinations

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "exp_gate_0001"))
from aig_exact import AIGEncoder, verify_circuit  # noqa: E402
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from zc_certify import write_cnf, kissat, drat_verify, sha16, CERTS  # noqa: E402

N = 5


def build_amo_shared(tt, opt, gate_order_sb=False, gate_order_b=False, n=None):
    """Base circuit encoder (k=opt) + at-most-one-shared. Sound direction: fan-out>=2 => z.

    `n=None` cai no global do MÓDULO, que é 5. Isso era uma armadilha silenciosa entre módulos, achada
    por Codex REV-0100: `reproduce_witness.py` passou a definir seu próprio `N` por testemunha (para
    servir a base n=4), mas mudar `reproduce_witness.N` não altera o `N` DESTE módulo — de modo que
    `reproduce_witness.py 0x03de --full` construiria uma instância de CINCO variáveis, rotulada `n4`, e
    o leg poderia dar PASS sobre o objeto errado. O `main` daqui já sobrescrevia via `globals()["N"]`
    (linha ~103), o que funciona para execução direta e não para import — a pior combinação, porque
    parece resolvido. Agora `n` é parâmetro; quem importa deve passá-lo explicitamente.

    gate_order_sb (default False = byte-identical to the vetted path):
    *** UNSOUND — DO NOT USE FOR CERTIFICATION. Kept only for the record. ***
    This adds a gate-ordering symmetry break (order NON-OUTPUT gates 1..k-1 by operand 4-tuple
    (a,pa,b,pb) via adjacent-pair clauses, output gate exempt). It was CONJECTURED WLOG (Kimi
    REV-0082) and wrongly confirmed by Grok REV-0083, but Codex REV-0085 found a concrete
    counterexample (tt=0x80008000: an optimal fan-out-1 circuit g1=x2&x3 (2,0,3,0) -> g2=x1&g1
    (1,0,6,0) whose topology forces a DECREASING tuple, so the SB forbids a valid circuit). Lex
    order on `a` is incompatible with the topological constraint (a just-placed node enters the
    next gate as its LARGER operand b). Hence gate_order_sb=True can turn a truly-SAT amo-shared
    instance UNSAT => it does NOT certify forced-multi. A topology-compatible ordering (by the
    larger operand b) is a possible repair, but needs independent-family panel vetting BEFORE
    any reliance. Empirical validation on known instances is necessary but NOT sufficient."""
    nn = N if n is None else n
    enc = AIGEncoder(nn, opt, tt).build()
    nvars = enc.nvars
    clauses = list(enc.clauses)
    k = opt
    if gate_order_sb:
        for i in range(1, k - 1):            # adjacent pairs (i,i+1), both <= k-1 (non-output)
            for (a, pa, b, pb, s) in enc.options[i]:
                ti = (a, pa, b, pb)
                for (a2, pa2, b2, pb2, s2) in enc.options[i + 1]:
                    if (a2, pa2, b2, pb2) < ti:   # tuple(i) > tuple(i+1): forbid this pairing
                        clauses.append([-s, -s2])
    if gate_order_b:
        # REPAIR candidate (Codex REV-0085 diagnosis): order NON-OUTPUT gates by the LARGER
        # operand b FIRST (key = (b,a,pa,pb)) instead of by a. Rationale: a gate that becomes
        # available only after some node j is placed uses j as its larger operand b, so b tracks
        # topological depth => ordering by non-decreasing b is compatible with the topological
        # constraint (unlike ordering by a). This ADMITS Codex's counterexample circuit. Whether
        # it is truly WLOG is UNDER PANEL REVIEW — do NOT rely on a verdict from it until an
        # independent family proves it sound. Output gate k exempt.
        for i in range(1, k - 1):
            for (a, pa, b, pb, s) in enc.options[i]:
                ki = (b, a, pa, pb)
                for (a2, pa2, b2, pb2, s2) in enc.options[i + 1]:
                    if (b2, a2, pa2, pb2) < ki:   # key(i) > key(i+1): forbid
                        clauses.append([-s, -s2])

    def newvar():
        nonlocal nvars
        nvars += 1
        return nvars

    u = {}
    for i in range(1, k):
        node = nn + i
        users = []
        for j in range(i + 1, k + 1):
            refs = [o[4] for o in enc.options[j] if o[0] == node or o[2] == node]
            if not refs:
                continue
            uij = newvar()
            u[(i, j)] = uij
            for s in refs:
                clauses.append([-s, uij])
            users.append(j)
        zi = newvar()
        u[("z", i)] = zi
        for j1, j2 in combinations(users, 2):
            clauses.append([zi, -u[(i, j1)], -u[(i, j2)]])
    zs = [u[("z", i)] for i in range(1, k)]
    for a, b in combinations(zs, 2):
        clauses.append([-a, -b])
    return nvars, clauses


def cnf_of(enc, path):
    write_cnf(enc.nvars, enc.clauses, path)


def main():
    tt = int(sys.argv[1], 0)
    opt = int(sys.argv[2])
    if len(sys.argv) > 3:
        globals()["N"] = int(sys.argv[3])
    tag = f"{tt:#010x}"
    print(f"[{tag}] n={N}, opt hint={opt}")

    # (1) opt lower bound: UNSAT k=1..opt-1 (DRAT)
    ok_lb = True
    for kk in range(1, opt):
        enc = AIGEncoder(N, kk, tt).build()
        cnf = os.path.join(CERTS, f"n5_{tt:#010x}_opt_k{kk}.cnf")
        if any(len(cl) == 0 for cl in enc.clauses):
            print(f"  opt-LB k={kk}: UNSAT (syntactic)"); continue
        cnf_of(enc, cnf)
        drat = os.path.join(CERTS, f"n5_{tt:#010x}_opt_k{kk}.drat")
        rc, _ = kissat(cnf, drat)
        if rc == 10:
            print(f"  !!! opt-LB k={kk} SAT — opt<{opt}. ABORT."); return 1
        ver = drat_verify(cnf, drat); ok_lb = ok_lb and ver
        print(f"  opt-LB k={kk}: UNSAT drat-trim={'VERIFIED' if ver else 'FAIL'}")

    # (1b) opt witness k=opt
    enc = AIGEncoder(N, opt, tt).build()
    cnf = os.path.join(CERTS, f"n5_{tt:#010x}_opt_k{opt}.cnf"); cnf_of(enc, cnf)
    rc, model = kissat(cnf)
    if rc != 10:
        print(f"  !!! k={opt} not SAT — opt>{opt}. ABORT."); return 1
    gates, op = enc.decode(model)
    vc = verify_circuit(N, tt, gates, op)
    print(f"  opt-UB k={opt}: SAT verify_circuit={vc}")
    if not vc:
        # REV-0004 exists precisely so a False here cannot slide by as printed text (Kimi
        # REV-0097 finding 6a: verify_circuit results were reported, never asserted).
        print(f"  !!! witness does not compute tt — k={opt} leg NOT established. ABORT.")
        return 1

    # (2) tree: formula UNSAT k=opt (=> tree>=opt+1) + witness k=opt+1
    enc = AIGEncoder(N, opt, tt, formula=True).build()
    cnf = os.path.join(CERTS, f"n5_{tt:#010x}_tree_k{opt}.cnf"); cnf_of(enc, cnf)
    drat = os.path.join(CERTS, f"n5_{tt:#010x}_tree_k{opt}.drat")
    rc, _ = kissat(cnf, drat)
    tree_ok = False
    if rc == 20:
        ver = drat_verify(cnf, drat)
        encw = AIGEncoder(N, opt + 1, tt, formula=True).build()
        cnfw = os.path.join(CERTS, f"n5_{tt:#010x}_tree_k{opt+1}.cnf"); cnf_of(encw, cnfw)
        rcw, mw = kissat(cnfw)
        tree_ok = ver and rcw == 10
        print(f"  tree: formula UNSAT k={opt} (drat-trim={'VERIFIED' if ver else 'FAIL'}) + "
              f"formula SAT k={opt+1} ({rcw==10}) => tree={opt+1}, gap=1: {tree_ok}")
    else:
        print(f"  tree: formula k={opt} rc={rc} (SAT => tree<=opt => gap<=0, not gap=1)")

    # (3) forced-multi: at-most-one-shared UNSAT at k=opt
    nvars, clauses = build_amo_shared(tt, opt)
    cnf = os.path.join(CERTS, f"n5_{tt:#010x}_amo1shared.cnf")
    write_cnf(nvars, clauses, cnf)
    drat = os.path.join(CERTS, f"n5_{tt:#010x}_amo1shared.drat")
    rc, _ = kissat(cnf, drat)
    if rc == 10:
        print(f"  forced-multi: at-most-1-shared SAT => a single-reconvergence optimum EXISTS "
              f"(NOT forced-multi; conforming like most n=4 gap=1).")
        print(f"\n  VERDICT [{tag}]: gap=1 but NOT Z-like (single reconvergence possible).")
        return 0
    if rc != 20:
        print(f"  forced-multi: kissat rc={rc} (neither SAT nor UNSAT — timeout/error). INCONCLUSIVE.")
        return 1
    ver = drat_verify(cnf, drat)
    print(f"  forced-multi: at-most-1-shared UNSAT (drat-trim={'VERIFIED' if ver else 'FAIL'}) "
          f"cnf_sha={sha16(cnf)} drat_sha={sha16(drat)}")
    print(f"\n  *** VERDICT [{tag}]: FORCED MULTIPLE RECONVERGENCE at n={N} — Z-like. "
          f"Claim 0034's phenomenon GENERALIZES (opt LB DRAT={ok_lb}, tree gap=1={tree_ok}, "
          f"forced-multi DRAT={ver}). ***")
    return 0


if __name__ == "__main__":
    sys.exit(main())
