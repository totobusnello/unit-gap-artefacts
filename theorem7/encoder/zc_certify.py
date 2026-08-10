"""EXP-KRINKIN-THM7-Z / B2 — per-function DRAT certification of the Z family.

For each "zero-conforming" function f (gap=1, n=4), certifies via SAT+DRAT that EVERY
size-optimal AIG has >=2 gates with fan-out>=2 (forced DOUBLE reconvergence) — without
relying on the completeness of the enumerator (thm7_check). Per-function chain:

  (1) opt(f) >= OPT   : circuit UNSAT for k=1..OPT-1 (DRAT, drat-trim s VERIFIED).
  (2) opt(f) <= OPT   : witness (circuit SAT at k=OPT, verify_circuit).
  (3) >=2 shared      : "there exists an AIG of OPT gates with <=1 gate of fan-out>=2" is
                        UNSAT (DRAT). At-most-one-shared encoding:
                          u[i,j]  : gate j (j>i) selects an option that references gate i
                                    (clause  ¬s_o ∨ u[i,j]  for every option o of j that uses n+i)
                          z[i]    : gate i has fan-out>=2
                                    (clause  z[i] ∨ ¬u[i,j] ∨ ¬u[i,j']  for all j<j' users of i)
                          amo(z)  : ¬z[i] ∨ ¬z[i']   (at most one shared)
                        UNSAT ⟹ no optimum has <=1 shared ⟹ all have >=2.

Soundness: the base encoder's dedup/all-used are WLOG at k=OPT (an optimal circuit has no
duplicate or useless gate — that would shrink the size). The direction "fan-out>=2 ⟹ z" is
the only one needed for the UNSAT to be sound (a spurious z only tightens the amo; the
solver zeroes it out).
REV-0004: witness (2) is verified by simulation; DRAT certifies the CNF.
Remaining confidence gaps: encoder→CNF (G3) + drat-trim — the same as claims 0024/0033.
"""
import sys
import os
import subprocess
import hashlib
import json
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "exp_gate_0001"))
from aig_exact import AIGEncoder, verify_circuit, trivial_opt  # noqa: E402

N = 4
CERTS = os.path.join(HERE, "certs")
os.makedirs(CERTS, exist_ok=True)

# (tt, opt) of the 6 zero-conforming functions (opt from the census, cross-checked in thm7_check)
ZC = [(0x0358, 7), (0x0359, 7), (0x03de, 6), (0x06b5, 8), (0x07bc, 7), (0x178e, 8)]


def sha16(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()[:16]


def write_cnf(nvars, clauses, path):
    with open(path, "w") as f:
        f.write(f"p cnf {nvars} {len(clauses)}\n")
        for cl in clauses:
            f.write(" ".join(map(str, cl)) + " 0\n")


def kissat(cnf, drat=None):
    args = ["kissat", "-q", cnf] + ([drat] if drat else [])
    p = subprocess.run(args, capture_output=True, text=True)
    model = []
    if p.returncode == 10:
        for line in p.stdout.splitlines():
            if line.startswith("v "):
                model += [int(x) for x in line[2:].split() if x != "0"]
    return p.returncode, model


def drat_verify(cnf, drat):
    """True iff drat-trim actually verified the proof. See tools/check_drat.sh for the shell twin.

    The `s ` prefix is load-bearing and must stay: `"VERIFIED" in stdout` — which decide_pending.py
    used until Codex REV-0096 reproduced the failure — is also true of `s NOT VERIFIED`, so it
    passes a FAILED proof. This function was never affected (`"s VERIFIED" in "s NOT VERIFIED"` is
    False), which is why the seven opt legs it validated are sound. Exit code added for parity with
    check_drat.sh: a checker that dies after printing the status line should not count as evidence.
    """
    v = subprocess.run(["drat-trim", cnf, drat], capture_output=True, text=True)
    return "s VERIFIED" in v.stdout and v.returncode == 0


def build_amo_shared(tt, opt):
    """Builds the CNF of the base encoder (circuit, k=opt) + at-most-one-shared constraint.
    Returns (nvars, clauses, enc)."""
    enc = AIGEncoder(N, opt, tt).build()
    nvars = enc.nvars
    clauses = list(enc.clauses)
    k = opt

    def newvar():
        nonlocal nvars
        nvars += 1
        return nvars

    # users of each gate i (i<k): list of (j, sel_vars of the option referencing i)
    # u[i][j] var
    u = {}
    for i in range(1, k):          # gate i, node = N+i
        node = N + i
        user_gates = []
        for j in range(i + 1, k + 1):
            ref_sels = [o[4] for o in enc.options[j] if o[0] == node or o[2] == node]
            if not ref_sels:
                continue
            uij = newvar()
            u[(i, j)] = uij
            for s in ref_sels:
                clauses.append([-s, uij])   # referencing option selected ⟹ u
            user_gates.append(j)
        # z[i]: fan-out>=2 ⟹ z[i]
        zi = newvar()
        u[("z", i)] = zi
        for j1, j2 in combinations(user_gates, 2):
            clauses.append([zi, -u[(i, j1)], -u[(i, j2)]])
    # amo(z): at most one shared
    zs = [u[("z", i)] for i in range(1, k)]
    for a, b in combinations(zs, 2):
        clauses.append([-a, -b])
    return nvars, clauses, enc


def certify_one(tt, opt):
    tag = f"{tt:#06x}"
    print(f"\n{'='*66}\n[{tag}] opt={opt} — certificação zero-conforme (DRAT)\n{'='*66}")
    res = {"tt_hex": tag, "opt": opt}

    # (1) opt >= OPT : UNSAT for k=1..OPT-1
    lb = []
    ok_lb = True
    for kk in range(1, opt):
        enc = AIGEncoder(N, kk, tt).build()
        cnf = os.path.join(CERTS, f"zc_{tt:#06x}_opt_k{kk}.cnf")
        if any(len(cl) == 0 for cl in enc.clauses):
            print(f"  opt-LB k={kk}: UNSAT (sintático)")
            lb.append({"k": kk, "result": "UNSAT_SYN"})
            continue
        write_cnf(enc.nvars, enc.clauses, cnf)
        drat = os.path.join(CERTS, f"zc_{tt:#06x}_opt_k{kk}.drat")
        rc, _ = kissat(cnf, drat)
        if rc == 10:
            print(f"  !!! opt-LB k={kk} SAT — opt<{opt}. ABORTA {tag}.")
            res["error"] = f"opt LB falhou em k={kk}"
            return res
        ver = drat_verify(cnf, drat)
        ok_lb = ok_lb and ver
        print(f"  opt-LB k={kk}: UNSAT drat={os.path.getsize(drat)}B "
              f"cnf_sha={sha16(cnf)} drat-trim={'VERIFIED' if ver else 'FALHOU'}")
        lb.append({"k": kk, "result": "UNSAT", "cnf_sha": sha16(cnf),
                   "drat_sha": sha16(drat), "drat_trim_verified": ver})
    res["opt_lower_bound_drat"] = lb
    res["opt_lb_all_verified"] = ok_lb

    # (2) opt <= OPT : witness SAT at k=OPT
    enc = AIGEncoder(N, opt, tt).build()
    cnf_w = os.path.join(CERTS, f"zc_{tt:#06x}_opt_k{opt}.cnf")
    write_cnf(enc.nvars, enc.clauses, cnf_w)
    rc, model = kissat(cnf_w)
    if rc != 10:
        print(f"  !!! opt k={opt} não-SAT (rc={rc}) — opt>{opt}? ABORTA.")
        res["error"] = "sem testemunha em k=opt"
        return res
    gates, op = enc.decode(model)
    ok_sim = verify_circuit(N, tt, gates, op)
    print(f"  opt-UB k={opt}: SAT testemunha verify_circuit={ok_sim}")
    res["opt_witness"] = {"gates": gates, "op": op, "verify_circuit": ok_sim}

    # (3) >=2 shared : at-most-one-shared UNSAT at k=OPT
    nvars, clauses, _ = build_amo_shared(tt, opt)
    cnf = os.path.join(CERTS, f"zc_{tt:#06x}_amo1shared.cnf")
    write_cnf(nvars, clauses, cnf)
    drat = os.path.join(CERTS, f"zc_{tt:#06x}_amo1shared.drat")
    rc, _ = kissat(cnf, drat)
    if rc == 10:
        print(f"  !!! at-most-1-shared SAT — existe ótimo conforme! NÃO é zero-conforme. ABORTA.")
        res["error"] = "at-most-1-shared SAT (não zero-conforme)"
        res["forced_ge2_shared"] = False
        return res
    ver = drat_verify(cnf, drat)
    print(f"  >=2-shared: at-most-1-shared UNSAT drat={os.path.getsize(drat)}B "
          f"cnf_sha={sha16(cnf)} drat-trim={'VERIFIED' if ver else 'FALHOU'}")
    res["amo1shared_unsat_drat"] = {"result": "UNSAT", "cnf_sha": sha16(cnf),
                                    "drat_sha": sha16(drat), "drat_trim_verified": ver}
    res["forced_ge2_shared"] = ver
    res["certified"] = ok_lb and ok_sim and ver
    print(f"  [{tag}] zero-conforme DRAT-certificado: {res['certified']}")
    return res


def main():
    only = os.environ.get("ZC_ONLY")  # e.g. "0x03de"
    targets = ZC if not only else [(tt, o) for tt, o in ZC if f"{tt:#06x}" == only]
    out = []
    for tt, opt in targets:
        out.append(certify_one(tt, opt))
    allok = all(r.get("certified") for r in out)
    path = os.path.join(HERE, "zc_forced_witness.json")
    json.dump({"n": len(out), "all_certified": allok, "results": out}, open(path, "w"), indent=2)
    print(f"\n[SAVE] {path}\nTODAS as {len(out)} ZC DRAT-certificadas (reconvergência-dupla forçada)? {allok}")
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main())
