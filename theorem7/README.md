# unit-gap-verify

Reproducible, machine-checkable artifacts for the unit-gap / forced-reconvergence results in
And-Inverter-Graph exact synthesis: the refutation of Theorem 7 of *The Unit Gap*
(arXiv:2603.08033) and the positive structure that replaces it — a family of gap = 1 functions
whose *every* size-optimal circuit is forced to reconverge (the **forced-reconvergence family**).

**Start with [`VERIFY.md`](VERIFY.md)** — setup, one-command reproduction, and a zero-setup
`drat-trim` spot check.

- [`proofs/`](proofs/) — the Lift Theorem (full proof) and the synthesis note (refutation →
  positive structure → non-lift classes), with honest scope.
- [`encoder/`](encoder/) — the AIG exact-synthesis SAT encoder + an independent `verify_circuit`.
- [`verify/`](verify/) — reproduction scripts, the certificate manifest (CNF SHAs), and tiny
  sample certificates.

The core witnesses regenerate from scratch (the n=5 seventh-class witness, the other two non-lift
witnesses, and the n=4 Lift base); a few larger enumerations (the n=4 census, n=6 corroboration)
are cited from the full development rather than re-run here — `VERIFY.md` says exactly which is
which. Not an asymptotic or lower-bound result — a structural result and its machine-checked
certificates.
