"""CNF / DRAT helper functions for the reproduction scripts.

- write_cnf : dump (nvars, clauses) to a DIMACS CNF file.
- kissat    : run kissat, returning (return_code, model); pass a drat path to emit a DRAT proof.
- drat_verify : run drat-trim and report whether it prints "s VERIFIED".
- sha16     : first 16 hex chars of the SHA-256 of a file (used to pin the encoder-deterministic
              CNF identity; DRAT bytes are solver-version-dependent and are checked by drat-trim,
              not by hash).

Requires `kissat` and `drat-trim` on PATH. A SAT witness is always re-checked by simulation
(`verify_circuit` in aig_exact.py); DRAT certifies the CNF. The one confidence gap is the
encoder->CNF translation itself, which is outside DRAT — mitigated by cross-validation against
independent enumeration and by the per-circuit verify_circuit check.
"""
import os
import subprocess
import hashlib

HERE = os.path.dirname(os.path.abspath(__file__))
CERTS = os.path.join(HERE, "certs")   # default scratch dir for generated certificates (created lazily)


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
    v = subprocess.run(["drat-trim", cnf, drat], capture_output=True, text=True)
    return "s VERIFIED" in v.stdout
