"""Regenerate and machine-recheck the headline result FROM SCRATCH: the seventh, non-lift
forced-reconvergence class at n=5, witness f = 0x03de & (~x0 | x4) = 0x03de0154.

Naming: this file is part of the bundle copied to the PUBLIC artefact repo, where the family is
`forced-reconvergence family` / `F_n` and never the eponym — that enters only after Kirill accepts
co-authorship. The strip used to happen by hand at publication time, which is the step where it can
silently fail; keeping the public-facing files neutral AT THE SOURCE makes publishing a copy instead
of an edit. `tools/audit.sh` check 6 fails if the eponym reappears here.

Repo-relative and machine-independent (no hardcoded paths, no python-version assumption).
Prerequisites on PATH: python3, kissat, drat-trim  (see ../VERIFY.md for a one-line setup).

    python3 reproduce_witness.py           # quick: opt-LB + witnesses + non-canalizing (~seconds)
    python3 reproduce_witness.py --full     # also the forced-multi no-SB certificate (247 MB, ~minutes)

What each leg establishes for f (n=5):
  opt = 8      : circuit UNSAT at k=1..7 (DRAT, drat-trim VERIFIED) + a k=8 SAT model that
                 verify_circuit confirms computes f. => opt(f) = 8.
  tree <= 9    : a fan-out-1 formula of 9 gates computes f (SAT model, verify_circuit).  [self-certifying]
  forced-multi : "some optimum has <=1 reconvergent gate" is UNSAT at k=8 with ZERO symmetry
                 breaking (the vetted encoder) -> every 8-gate optimum has >=2 reconvergences.
                 With tree>=opt+1 forced by this, tree = 9, so gap = tree - opt = 1.
  non-canalizing : no variable has a constant cofactor => f is not an AND/OR-lift.
Portability note: a CNF's SHA is deterministic from the encoder (machine-independent, pinned here);
a DRAT's bytes depend on the solver build, so the portable check is "drat-trim VERIFIED", not a DRAT SHA.
"""
import os, sys, argparse

HERE = os.path.dirname(os.path.abspath(__file__))
EXP = os.path.normpath(os.path.join(HERE, "..", "encoder"))  # layout achatado do bundle
sys.path.insert(0, EXP)      # aig_exact (canonical, with formula mode)
   # zc_certify, n5_forced_test
from aig_exact import AIGEncoder, verify_circuit             # noqa: E402
from n5_forced_test import build_amo_shared                  # noqa: E402
from zc_certify import write_cnf, kissat, drat_verify, sha16 # noqa: E402

# Witnesses this script can regenerate. `forced_cnf_sha16` pins the forced-multi CNF hash, which is
# encoder-deterministic and therefore machine-independent (DRAT bytes are not — they depend on the
# solver build, so the portable acceptance test is "drat-trim VERIFIED").
#
# WHY THIS TABLE HOLDS ALL FIVE, and not the two it held before. The public artefact repo carried a
# FORK of this script with a more general CLI (`<tt> <opt> --n`) and its VERIFY.md documented five
# commands — the three directed-sweep witnesses, the n=4 base, and the census witness. The private
# copy was later tightened to pin SHAs per witness, which was right, but it dropped to two entries and
# stopped accepting the other three. So the public bundle documented commands its own script could no
# longer serve, and the two copies drifted apart in BOTH capability and rigour. Same failure mode as
# the divergent module forks (see the archived-forks note in the private tree), except here the
# fork is what strangers execute. The fix is one table that serves every documented command, so the
# public bundle can be GENERATED from this tree rather than maintained beside it (tools/export_public.sh).
#
# Every witness here now carries a no-SB `forced_cnf_sha16`. Until 2026-08-12 two of them did not, and
# this comment explained why: they had been certified through the `gate_order_b` WLOG-ordering, so no
# no-SB CNF existed to pin. That was honest then and became a lie the moment the certificates landed —
# the manifest pinned the two new hashes and named THIS script as their regenerator while the table
# below still said the hashes did not exist and the code below forced `match = True` without comparing.
# Three independent reviewers found it in the same hour (Codex REV-0114, DeepSeek REV-0115, Kimi
# REV-0116), which is what a broken promise in the one file strangers execute deserves.
#
# So: `forced_cnf_sha16: None` is no longer a state any n=5 witness is allowed to be in. If a witness
# ever legitimately lacks a pin, the `None` branch below still handles it and says so out loud — but
# check the manifest first, because a manifest row that names this script and a `None` here cannot both
# be right.
WITNESSES = {
    0x03DE0154: {"n": 5, "opt": 8, "forced_cnf_sha16": "ed3b8350f72f8078",
                 "desc": "0x03de & (~x0 | x4) — 7th class, found by directed sweep"},
    0xABFE03DE: {"n": 5, "opt": 8, "forced_cnf_sha16": "39d9bd8db8daeb8b",
                 "desc": "0x03de | (x0 & x4) — 8th class, directed sweep (forced-multi certified with NO symmetry breaking, 2026-08-12)"},
    0x57DF03DE: {"n": 5, "opt": 8, "forced_cnf_sha16": "378fa46181ed496b",
                 "desc": "0x03de | (~x0 & x4) — 9th class, directed sweep (forced-multi certified with NO symmetry breaking, 2026-08-12)"},
    0x03DE:     {"n": 4, "opt": 6, "forced_cnf_sha16": None,
                 "desc": "the n=4 base of the Lift Theorem — flagship class 0x03de"},
    0x09C50800: {"n": 5, "opt": 8, "forced_cnf_sha16": "8949334bf9baa8ca",
                 "desc": "10th class — found by random census, not by construction"},
}
DEFAULT_TT = 0x03DE0154
# `_generated/`, NOT `sample_certs/`. Codex asked for exactly this in REV-0094 ("reproduce sobrescreve
# sample_certs") and the call log records it as applied — but the line was never changed, and the drift
# between the ledger and the code stayed invisible until the cost showed up as 535 MB of untracked
# files sitting in the versioned tree, one DRAT of them 443 MB. A regenerator must never write into
# the directory it is supposed to reproduce: it destroys the reference it is being checked against.
# `_generated/` is gitignored, so running the verify leaves `git status` clean.
OUT = os.path.join(HERE, "_generated")
os.makedirs(OUT, exist_ok=True)

# Set by main() from argv; module-level so the leg_* helpers keep their current shape. `N` joins them
# because the n=4 base is one of the witnesses — it used to be a hardcoded `N = 5`, which is precisely
# why the private copy could not serve the `0x03de 6` command the public VERIFY.md documents.
TT = DEFAULT_TT
N = WITNESSES[DEFAULT_TT]["n"]
OPT = WITNESSES[DEFAULT_TT]["opt"]
EXPECT_FORCED_CNF_SHA16 = WITNESSES[DEFAULT_TT]["forced_cnf_sha16"]


def is_canalizing(tt, n=None):
    """`n=None` e não `n=N`: o default de um parâmetro é avaliado UMA VEZ, na definição da função, de
    modo que `n=N` congelava o 5 de então e ignorava o `N` que o main passa a definir por testemunha.
    Efeito observado no primeiro teste da base n=4: `0x03de` foi julgada como função de 5 variáveis,
    onde x4 tem cofator constante, e o script reportou `canalizing=True` contra o `canal=0` do atlas —
    um leg VERMELHO por late binding, não por matemática. Bug que eu introduzi ao tornar `N` dinâmico
    e que só apareceu porque a primeira coisa que fiz foi rodar a testemunha nova."""
    n = N if n is None else n
    for i in range(n):
        for val in (0, 1):
            bits = [(tt >> a) & 1 for a in range(1 << n) if ((a >> i) & 1) == val]
            if all(b == 0 for b in bits) or all(b == 1 for b in bits):
                return True
    return False


def leg_optlb():
    print(f"\n[opt-LB] circuit UNSAT for k=1..{OPT-1} (=> opt >= {OPT})")
    allok = True
    for k in range(1, OPT):
        enc = AIGEncoder(N, k, TT).build()
        if any(len(cl) == 0 for cl in enc.clauses):
            print(f"  k={k}: UNSAT (syntactic)"); continue
        cnf = os.path.join(OUT, f"n5_{TT:#010x}_opt_k{k}.cnf"); write_cnf(enc.nvars, enc.clauses, cnf)
        drat = os.path.join(OUT, f"n5_{TT:#010x}_opt_k{k}.drat")
        rc, _ = kissat(cnf, drat)
        assert rc == 20, f"k={k} expected UNSAT(20), got {rc}"
        ok = drat_verify(cnf, drat); allok = allok and ok
        print(f"  k={k}: UNSAT  cnf={sha16(cnf)}  drat-trim={'VERIFIED' if ok else 'FAIL'}")
    return allok


def leg_optwitness():
    enc = AIGEncoder(N, OPT, TT).build()
    cnf = os.path.join(OUT, f"n5_{TT:#010x}_opt_k{OPT}.cnf"); write_cnf(enc.nvars, enc.clauses, cnf)
    rc, model = kissat(cnf)
    assert rc == 10, f"k={OPT} expected SAT(10), got {rc}"
    gates, op = enc.decode(model); ok = verify_circuit(N, TT, gates, op)
    print(f"\n[opt witness] k={OPT} SAT, verify_circuit={ok}  => opt = {OPT}")
    return ok


def leg_tree():
    enc = AIGEncoder(N, OPT + 1, TT, formula=True).build()
    cnf = os.path.join(OUT, f"n5_{TT:#010x}_tree_k{OPT+1}.cnf"); write_cnf(enc.nvars, enc.clauses, cnf)
    rc, model = kissat(cnf)
    assert rc == 10, f"formula k={OPT+1} expected SAT(10), got {rc}"
    gates, op = enc.decode(model); ok = verify_circuit(N, TT, gates, op)

    # FAN-OUT CONTADO POR PORTA, e não confiado ao `formula=True` do encoder. O VERIFY.md afirmava
    # "per-gate fan-out is counted" e o manifest repetia a afirmação, mas este leg só chamava
    # `verify_circuit`, que compara a truth table e nada diz sobre estrutura (Codex REV-0100). Uma
    # regressão no modo `formula` passaria como "árvore self-certifying" sem que nada checasse a
    # propriedade que dá o nome ao leg. Agora a asserção existe: numa fórmula, todo nó interno é
    # consumido no máximo uma vez, contando a saída como consumidor.
    consumers = {}
    for gi, (a, _pa, b, _pb) in enumerate(gates, start=1):
        for operand in (a, b):
            if operand > N:                       # > N = nó interno (entradas podem ter fan-out livre)
                consumers[operand] = consumers.get(operand, 0) + 1
    # A SAÍDA é o nó `N + len(gates)` — a última porta, por construção do encoder (ver `simulate()`,
    # que lê `vals[n + len(gates)]`). O segundo valor de `decode()` é a POLARIDADE da saída, um bool,
    # não um nó: minha primeira versão fazia `abs(op)` e comparava com N, o que em Python calcula
    # `abs(True) = 1` — porque `bool` é subclasse de `int` — e portanto nunca contava nada, enquanto o
    # comentário afirmava "contando a saída como consumidor". Erro achado ao ler o `decode()` antes de
    # os revisores o fazerem. Na prática o veredicto não muda (a última porta não pode ser operando de
    # ninguém, logo tem 0 consumidores internos), mas um comentário que descreve o que o código NÃO faz
    # é a mesma falha que o Codex apontou no leg inteiro — afirmar mais do que se executa.
    out_node = N + len(gates)
    consumers[out_node] = consumers.get(out_node, 0) + 1
    max_fanout = max(consumers.values()) if consumers else 0
    shared = {k: v for k, v in consumers.items() if v > 1}
    fanout_ok = not shared
    print(f"\n[tree] fan-out-1 formula k={OPT+1} SAT, verify_circuit={ok}, "
          f"max fan-out interno={max_fanout} (contado por porta, {len(consumers)} nós internos)")
    if shared:
        print(f"  !!! nós com fan-out>1: {shared} — NÃO é fórmula fan-out-1; o leg FALHA")
    print(f"  => tree <= {OPT+1} (self-certifying: truth table + estrutura fan-out-1)")
    return ok and fanout_ok


def leg_tree_chain():
    """A cadeia de LOWER BOUND do tree: formula UNSAT em k=1..opt, uma perna por k, com DRAT.

    Esta perna existe porque o `manifest.csv` pina `b922fe75b9c3508e` para ela e nomeava, até
    2026-08-12, um script PRIVADO como regenerador — promessa que um leitor externo não podia cumprir.
    Depois eu a troquei por uma DESCRIÇÃO (`aig_exact.py (AIGEncoder(...) for k=1..8)`), que também não
    se cola num shell. DeepSeek REV-0115 pegou as duas formas. Um comando que existe é a única correção.

    Compara o SHA de cada k contra `tree_chain_n5.csv` quando esse artefato viaja no bundle; quando não
    viaja, ainda imprime os SHAs para conferência manual, e diz qual é o caso — em vez de calar.
    """
    import csv as _csv
    # O CSV de referência é procurado ao LADO do script e no diretório de experimentos que o layout
    # privado usa. O nome do diretório privado NÃO é escrito aqui: o export tem um gate que proíbe path
    # do layout privado neste arquivo, e ele pegou a primeira versão desta função. Então o caminho de
    # fora vem por variável de ambiente, e a ausência dele é um caso tratado, não um erro.
    ref = {}
    cands = [os.path.join(HERE, "tree_chain_n5.csv")]
    if os.environ.get("TREE_CHAIN_CSV"):
        cands.append(os.environ["TREE_CHAIN_CSV"])
    for cand in cands:
        if os.path.exists(cand):
            for r in _csv.DictReader(open(cand)):
                if r.get("mode") == "formula" and r.get("tt_hex", "").lower() == f"{TT:#010x}":
                    ref[int(r["k"])] = r["cnf_sha16"]
            break
    print(f"\n[tree chain] formula-mode UNSAT k=1..{OPT}  "
          f"({'comparando contra tree_chain_n5.csv' if ref else 'sem CSV de referencia no bundle: SHAs impressos para conferencia'})")
    allok = True
    for k in range(1, OPT + 1):
        enc = AIGEncoder(N, k, TT, formula=True).build()
        if any(len(cl) == 0 for cl in enc.clauses):
            print(f"  k={k}: UNSAT (syntactic)")
            continue
        cnf = os.path.join(OUT, f"n{N}_{TT:#010x}_tree_k{k}.cnf")
        write_cnf(enc.nvars, enc.clauses, cnf)
        got = sha16(cnf)
        drat = os.path.join(OUT, f"n{N}_{TT:#010x}_tree_k{k}.drat")
        rc, _ = kissat(cnf, drat)
        assert rc == 20, f"formula k={k} expected UNSAT(20), got {rc}"
        dok = drat_verify(cnf, drat)
        if k in ref:
            m = (got == ref[k])
            allok = allok and dok and m
            print(f"  k={k}: UNSAT  cnf={got} ({'MATCH' if m else 'MISMATCH vs ' + ref[k]})  "
                  f"drat-trim={'VERIFIED' if dok else 'FAIL'}")
        else:
            allok = allok and dok
            print(f"  k={k}: UNSAT  cnf={got}  drat-trim={'VERIFIED' if dok else 'FAIL'}")
    return allok


def leg_canalizing():
    c = is_canalizing(TT)
    print(f"\n[non-canalizing] canalizing={c}  => {'NOT a lift (independent class)' if not c else 'IS a lift'}")
    return not c


def leg_forced():
    print(f"\n[forced-multi] amo-shared UNSAT at k={OPT}, ZERO symmetry break (247 MB DRAT, ~minutes)")
    # `n=N` EXPLÍCITO: sem isto, `build_amo_shared` usa o `N=5` do módulo n5_forced_test e a base n=4
    # seria certificada como instância de cinco variáveis, com o arquivo rotulado `n4` (Codex REV-0100).
    nv, cl = build_amo_shared(TT, OPT, gate_order_b=False, n=N)
    cnf = os.path.join(OUT, f"n{N}_{TT:#010x}_amo1shared_nosb.cnf"); write_cnf(nv, cl, cnf)
    csha = sha16(cnf)
    if EXPECT_FORCED_CNF_SHA16 is None:
        # Sem pin: o veredicto ainda é checado, a byte-identidade não pode ser. Dizer isso em voz alta
        # é o ponto — um "OK" que silenciosamente pula a comparação é pior que a comparação ausente.
        match = True
        print(f"  cnf sha16={csha}  (nenhum pin no-SB para esta testemunha — ver WITNESSES; veredicto ainda é verificado)")
    else:
        match = (csha == EXPECT_FORCED_CNF_SHA16)
        print(f"  cnf sha16={csha}  (expected {EXPECT_FORCED_CNF_SHA16}: {'MATCH' if match else 'MISMATCH!'})")
    drat = os.path.join(OUT, f"n{N}_{TT:#010x}_amo1shared_nosb.drat")
    rc, _ = kissat(cnf, drat)
    assert rc == 20, f"forced-multi expected UNSAT(20), got {rc}"
    ok = drat_verify(cnf, drat)
    print(f"  UNSAT  drat-trim={'VERIFIED' if ok else 'FAIL'}  => every optimum has >=2 reconvergences")
    return ok and match


def main():
    global TT, N, OPT, EXPECT_FORCED_CNF_SHA16
    ap = argparse.ArgumentParser(description="Regenerate and machine-recheck a forced-reconvergence witness chain.")
    ap.add_argument("tt", nargs="?", default=f"{DEFAULT_TT:#010x}",
                    help="truth table in hex (default: the 7th-class witness 0x03de0154)")
    ap.add_argument("--full", action="store_true", help="also regenerate the forced-multi no-SB certificate")
    ap.add_argument("--tree-chain", action="store_true",
                    help="also regenerate the tree lower-bound chain (formula UNSAT k=1..opt, per-leg SHAs)")
    args = ap.parse_args()
    tt = int(args.tt, 16)
    if tt not in WITNESSES:
        known = ", ".join(f"{k:#010x}" for k in WITNESSES)
        sys.exit(f"unknown witness {tt:#010x} — this script pins CNF SHAs, so it only serves: {known}")
    TT, N, OPT = tt, WITNESSES[tt]["n"], WITNESSES[tt]["opt"]
    EXPECT_FORCED_CNF_SHA16 = WITNESSES[tt]["forced_cnf_sha16"]
    print(f"=== reproduce witness {TT:#010x} — {WITNESSES[tt]['desc']}  (n={N}, opt={OPT}) ===")
    res = {
        "opt-LB (k=1..7 UNSAT)": leg_optlb(),
        f"opt witness (k={OPT} SAT)": leg_optwitness(),
        f"tree<= {OPT+1} (formula witness)": leg_tree(),
        "non-canalizing": leg_canalizing(),
    }
    if args.tree_chain:
        res[f"tree chain (formula UNSAT k=1..{OPT})"] = leg_tree_chain()
    if args.full:
        res["forced-multi (no-SB UNSAT)"] = leg_forced()
    print("\n=== SUMMARY ===")
    for k, v in res.items():
        print(f"  [{'PASS' if v else 'FAIL'}] {k}")
    # "established vs candidate" era o texto de quando a décima classe estava pendente; a claim 0038
    # a promoveu e a contagem passou a sair decomposta por PROVENIÊNCIA, que é o que interessa.
    print("\nFor the NPN class count (decomposed by provenance: lifts / directed sweep / random census): run  "
          "python3 ./npn_check_f5.py")
    sys.exit(0 if all(res.values()) else 1)


if __name__ == "__main__":
    main()
