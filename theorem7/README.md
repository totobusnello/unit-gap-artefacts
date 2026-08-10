# unit-gap-verify

Reproducible, machine-checkable artifacts for the unit-gap / forced-reconvergence results in
And-Inverter-Graph exact synthesis: the refutation of Theorem 7 of *The Unit Gap*
(arXiv:2603.08033) and the positive structure that replaces it — a family of gap = 1 functions
whose *every* size-optimal circuit is forced to reconverge (the **forced-reconvergence family**).

**Start with [`VERIFY.md`](VERIFY.md)** — setup, one-command reproduction, and a zero-setup
`drat-trim` spot check.

- [`proofs/`](proofs/) — the Lift Theorem (full proof), the synthesis note (refutation → positive
  structure → non-lift classes), and four technotes, all with honest scope.
- [`encoder/`](encoder/) — the AIG exact-synthesis SAT encoder + an independent `verify_circuit`.
- [`verify/`](verify/) — reproduction scripts, the certificate manifest (CNF SHAs), tiny sample
  certificates, and the raw CSVs behind the sampling measurement quoted in `VERIFY.md`.

At n = 5 the family is counted at **at least ten distinct NPN classes**: six AND-lifts of the n = 4
base, three found by a directed sweep on one family, and **one that fell out of a random census** of
14,466 truth tables. That last provenance is the point of the count, not the number — existence by
construction and existence by accident are evidence of different kinds. `verify/npn_check_f5.py`
prints the count decomposed that way, over the full 7680-element NPN group, with no solver involved.

Every core witness regenerates from scratch (`verify/reproduce_witness.py`): the four non-lift n = 5
witnesses and the n = 4 Lift base, each as `opt` lower bound by DRAT plus a self-certifying witness.
A few larger enumerations (the n = 4 census, the n = 6 corroboration) are cited from the full
development rather than re-run here — `VERIFY.md` says exactly which is which, and states where the
evidence is a paper proof rather than a certificate.

Not an asymptotic or lower-bound result — a structural result and its machine-checked certificates.
The sampling rate quoted for the census is a **yield under a declared, deliberately biased sampler**,
not a density; `VERIFY.md` gives the measurement and the limitation side by side.
