"""
EXP-GATE-0001 — Encoder de exact synthesis AIG via SAT (gate de qualificação da FASE 5).

Pergunta codificada: "existe circuito AIG com exatamente k portas AND que computa f?"
Modelo AIG (convenção do catálogo SRC-0019/0027): portas AND de 2 entradas,
inversões livres em qualquer aresta e na saída; tamanho = número de portas AND.

Semântica do encoding (validada no G3 contra enumeração independente):
- Nós: entradas 1..n (valores fixos por linha da truth table), portas n+1..n+k.
- Cada porta i escolhe (one-hot) uma opção (a, pa, b, pb): operandos a < b
  dentre nós anteriores, com polaridades pa, pb.
- v[i][t] = valor da porta i na linha t; cláusulas condicionais impõem
  v[i][t] <-> (val(a,t) xor pa) AND (val(b,t) xor pb).
- Saída = porta k com polaridade livre op: v[k][t] <-> (f(t) xor op).
- Quebra de simetria (sound): toda porta i < k precisa ser usada por alguma
  porta posterior.
- k=0 tratado fora do SAT (f constante ou literal).

REGRA REV-0004: prova DRAT certifica a CNF, não o encoding — por isso o G3
(enumeração cruzada) e a verificação por simulação de todo circuito SAT.

═══════════════════════════════════════════════════════════════════════════════
`relax=` — ESTE ENCODER RODA FORA DO PRÓPRIO ESPAÇO CANÔNICO, E ISSO SERVE A
QUALQUER CLAIM QUE DEPENDA DE UM WLOG DELE
═══════════════════════════════════════════════════════════════════════════════

Todo claim de síntese exata deste programa atravessa os constraints estruturais
listados acima, e até 2026-08-11 a defesa deles era PROSA: o paper enumerava os
constraints, argumentava que cada um é sem perda de generalidade em `k = opt`, e
pedia ao leitor que aceitasse a análise. Era o elo mais fraco do P1 e está
nomeado como tal no §4.2.

Parte disso não precisa de argumento. Os constraints se dividem em dois tipos,
e a diferença é OPERACIONAL, não estilística:

  RELAXÁVEIS — proíbem objetos que existem no problema mas são redundantes.
    'dup'    duas portas com a MESMA (a, pa, b, pb)
    'aeqb'   a == b, admitindo `x ∧ x` (buffer) e `x ∧ ¬x` (constante 0)
    'const'  a constante livre do §2.1 como operando (nunca era oferecida)
  DESLIGUE E RODE DE NOVO. Se o veredicto SOBREVIVE, o constraint não sustentava
  o resultado: ele sai do argumento e o leitor não precisa aceitar nada sobre
  ele. Se MUDA, era load-bearing — e agora se sabe com número, não por suposição.

  DEFINICIONAIS — codificam o que a pergunta significa.
    toda porta i<k alimenta uma posterior  ·  a saída é a porta k
  NÃO relaxe. Porta morta significa circuito estritamente MENOR, o que contradiz
  `opt = k`; relaxar troca a pergunta por "existe circuito de ≤ k portas com
  pouca reconvergência", cuja resposta é trivialmente sim e nada diz sobre
  ótimos. Aqui o argumento é irredutível — mas fica pequeno e quase
  tautológico, do tipo que só se recusa recusando a definição de ótimo.

VALIDE O INSTRUMENTO ANTES DE USÁ-LO, por uma propriedade que TEM de valer:
relaxar só admite circuitos que NÃO SÃO MELHORES, logo o `opt` medido não pode
mudar — UNSAT em `k = opt−1`, SAT em `k = opt`. Se mudar, o relaxamento está
errado e nada medido depois vale. Sem esse passo, um relaxamento com bug produz
UNSAT fácil e PARECE confirmar o resultado.

O QUE `relax` NÃO ALCANÇA: que a truth table, a semântica do Tseitin e a noção
de fan-out no CNF correspondam ao objeto matemático. Relaxamento audita QUAIS
OBJETOS o encoder admite; não audita O QUE ELE SIGNIFICA. Fechar isso é
formalização (Lean), não mais solving. Um claim que diga "os WLOGs foram
testados" e sugira que a ponte semântica está certificada é overclaim.

Procedimento completo, com o status de lastro: `13_WRITEUP_STANDARD.md`,
seção *Auditoria da ponte semântica por RELAXAMENTO*. Instância que originou
isto: claim 0043 e P1 §4.2.1 — cinco constraints, três testados, dois
definicionais. Molde de script: `exp_krinkin_cor6/audit_wlog_42.py` (copie com
nome próprio por claim; script que serve a duas claims é onde os escopos se
confundem).

`relax` é para AUDITAR argumento, NUNCA para produzir claim: o caminho de
confiança de qualquer resultado é o encoder no default (`relax=()`).
"""

from itertools import combinations, combinations_with_replacement, product


def tt_bit(tt, t):
    return (tt >> t) & 1


class AIGEncoder:
    # Nó-fonte CONSTANTE, usado só sob relax='const'. Vale 1; a polaridade do operando dá o 0. Índice 0
    # está livre porque entradas são 1..n e portas são n+i.
    CONST_NODE = 0

    def __init__(self, n, k, tt, formula=False, relax=()):
        """`relax` desliga WLOGs para AUDITAR o argumento do §4.2, nunca para produzir claim.

        O §4.2 sustenta que os constraints estruturais do encoder são WLOG em k=opt e que nenhum muda
        fan-out — e essa é a única passagem do paper onde prosa substitui certificado. Três deles podem
        ser TESTADOS em vez de argumentados: se o UNSAT do amo-shared sobrevive com o constraint
        RELAXADO, ele não estava sustentando o resultado e sai do argumento.

          'dup'   permite duas portas com a MESMA (a,pa,b,pb)
          'aeqb'  permite a == b  (AND(x,x)=x buffer; AND(x,~x)=0 constante)
          'const' admite 0 e 1 como operandos (o §2.1 admite constante livre; o encoder não)
          'order' admite (a,b) E (b,a) — relaxa a ORDENAÇÃO `a < b`, que é simetria por comutatividade
                  do AND. ATENÇÃO: `aeqb` sozinho NÃO relaxa a ordenação (Kimi REV-0113) —
                  `combinations_with_replacement` devolve pares ordenados, só admitindo a==b

        Os outros dois — toda porta alimenta uma posterior, e a saída é a porta k — NÃO são relaxáveis:
        porta morta significa circuito menor, logo eles não são simetria, são a DEFINIÇÃO de "ótimo com
        k portas". Relaxá-los tornaria a pergunta outra.
        """
        """n entradas, k portas AND, tt = truth table como inteiro de 2^n bits.
        formula=True: modo FÓRMULA (fan-out 1) — cada porta não-saída é usada por
        EXATAMENTE uma posterior (árvore). SAT em k => tree(f) <= k. Idêntico ao
        modo formula do XAGEncoder; a restrição adicional é só a de fan-out."""
        self.n, self.k, self.tt, self.formula = n, k, tt, formula
        self.relax = set(relax)
        self.rows = 1 << n
        self.nvars = 0
        self.clauses = []
        # v[i][t] para portas i=1..k
        self.v = {(i, t): self._new() for i in range(1, k + 1) for t in range(self.rows)}
        # opções de cada porta: (a, pa, b, pb), nós 1..n são entradas, n+j é a porta j
        self.options = {}
        for i in range(1, k + 1):
            opts = []
            nodes = list(range(1, self.n + i))  # nós disponíveis (< n+i)
            if "const" in self.relax:
                nodes = [self.CONST_NODE] + nodes   # 0/1 via polaridade sobre uma fonte constante
            # 'order' relaxa a ORDENAÇÃO de operandos (`a < b`), que é simetria por comutatividade do
            # AND. Kimi REV-0113 pegou que `combinations_with_replacement` ainda devolve pares
            # ORDENADOS: ela relaxa `a != b`, não `a < b`. Sem `order`, a ordenação seguia em vigor e a
            # contagem "três dos cinco relaxados" era falsa — dois dos cinco, mais o sexto silencioso.
            if "order" in self.relax:
                pairs = product(nodes, repeat=2)          # (a,b) E (b,a); inclui a==b
            elif "aeqb" in self.relax:
                pairs = combinations_with_replacement(nodes, 2)   # a <= b
            else:
                pairs = combinations(nodes, 2)                    # a < b
            for a, b in pairs:
                for pa in (0, 1):
                    for pb in (0, 1):
                        opts.append((a, pa, b, pb, self._new()))
            self.options[i] = opts
        self.out_pol = self._new()

    def _new(self):
        self.nvars += 1
        return self.nvars

    def _node_val(self, node, t):
        """Valor do nó na linha t: (const, None) p/ entradas; (None, var) p/ portas."""
        if node == self.CONST_NODE:
            return (1, None)          # fonte constante 1; ~1 = 0 pela polaridade
        if node <= self.n:
            return ((t >> (node - 1)) & 1, None)
        return (None, self.v[(node - self.n, t)])

    def build(self):
        c = self.clauses
        for i in range(1, self.k + 1):
            svars = [o[4] for o in self.options[i]]
            c.append(svars)  # at-least-one
            c.extend([-x, -y] for x, y in combinations(svars, 2))  # at-most-one
            for a, pa, b, pb, s in self.options[i]:
                for t in range(self.rows):
                    x = self.v[(i, t)]
                    # BUGFIX (pego pelo G1-verify na 1ª execução): constantes 0/1
                    # colidiam com literais DIMACS ±1 — agora tipos separados.
                    ka, la = self._lit(a, pa, t)  # ('const', 0|1) ou ('lit', ±var)
                    kb, lb = self._lit(b, pb, t)
                    # x <-> la AND lb, condicionado a s
                    if (ka == "const" and la == 0) or (kb == "const" and lb == 0):
                        c.append([-s, -x])           # AND com falso => x falso
                    elif ka == "const" and kb == "const":  # ambos true
                        c.append([-s, x])
                    elif ka == "const":              # la=true: x <-> lb
                        c.append([-s, -x, lb]); c.append([-s, x, -lb])
                    elif kb == "const":              # lb=true: x <-> la
                        c.append([-s, -x, la]); c.append([-s, x, -la])
                    else:
                        c.append([-s, -x, la]); c.append([-s, -x, lb])
                        c.append([-s, x, -la, -lb])
        # QUEBRA DE SIMETRIA (sound p/ a pergunta "opt = k?"): duas portas nunca
        # selecionam a MESMA opção (a,pa,b,pb) — um circuito MÍNIMO nunca tem
        # portas duplicadas (remover a duplicata daria circuito menor). Como a
        # sonda pergunta k=9 com opt ∈ {9,10} (catálogo), toda solução relevante
        # é mínima, logo livre de duplicatas. [EXP-PROBE-0001 v2]
        # QUEBRA DE SIMETRIA — só no modo CIRCUITO. Num modo FÓRMULA (árvore), uma
        # subárvore pode aparecer DUPLICADA (é a razão de tree>opt); proibir
        # duplicatas excluiria fórmulas mínimas válidas e daria UNSAT FALSO
        # (lower bound de tree errado). Por isso o dedup é desligado se formula.
        if not self.formula and "dup" not in self.relax:
            by_tuple = {}
            for i in range(1, self.k + 1):
                for a, pa, b, pb, s in self.options[i]:
                    by_tuple.setdefault((a, pa, b, pb), []).append(s)
            for svars in by_tuple.values():
                if len(svars) > 1:
                    c.extend([-x, -y] for x, y in combinations(svars, 2))
        # toda porta i < k é usada por porta(s) posterior(es).
        # circuito: AO MENOS uma (fan-out >= 1). fórmula: EXATAMENTE uma (fan-out 1).
        for i in range(1, self.k):
            users = [o[4] for j in range(i + 1, self.k + 1)
                     for o in self.options[j] if o[0] == self.n + i or o[2] == self.n + i]
            if users:
                self.clauses.append(users)                       # at-least-one
                if self.formula:
                    c.extend([-x, -y] for x, y in combinations(users, 2))  # at-most-one => fan-out 1
            else:  # sem usuários possíveis => k inviável nessa forma
                self.clauses.append([])
        # saída: v[k][t] <-> (f(t) xor op)
        op = self.out_pol
        for t in range(self.rows):
            x = self.v[(self.k, t)]
            if tt_bit(self.tt, t):   # op=0 -> x=1 ; op=1 -> x=0
                self.clauses.append([op, x]); self.clauses.append([-op, -x])
            else:
                self.clauses.append([op, -x]); self.clauses.append([-op, x])
        return self

    def _lit(self, node, pol, t):
        """Retorna ('const', 0|1) para entradas, ('lit', ±var) para portas."""
        const, var = self._node_val(node, t)
        if var is None:
            return ("const", const ^ pol)
        return ("lit", -var if pol else var)

    def to_dimacs(self, path):
        with open(path, "w") as f:
            f.write(f"p cnf {self.nvars} {len(self.clauses)}\n")
            for cl in self.clauses:
                f.write(" ".join(map(str, cl)) + " 0\n")

    def decode(self, model):
        """model = lista de ints (pysat) ou set de literais verdadeiros. Retorna circuito."""
        pos = {abs(l) for l in model if l > 0}
        gates = []
        for i in range(1, self.k + 1):
            sel = [o for o in self.options[i] if o[4] in pos]
            assert len(sel) == 1, f"porta {i}: seleção não única ({len(sel)})"
            a, pa, b, pb, _ = sel[0]
            gates.append((a, pa, b, pb))
        return gates, (self.out_pol in pos)


def simulate(n, gates, out_pol, t):
    """Simulação independente do circuito decodificado, linha t."""
    vals = {j: (t >> (j - 1)) & 1 for j in range(1, n + 1)}
    for idx, (a, pa, b, pb) in enumerate(gates, start=1):
        vals[n + idx] = (vals[a] ^ pa) & (vals[b] ^ pb)
    return vals[n + len(gates)] ^ (1 if out_pol else 0)


def verify_circuit(n, tt, gates, out_pol):
    """VERIFICAÇÃO SEMÂNTICA (regra REV-0004): circuito bate com a truth table inteira?"""
    return all(simulate(n, gates, out_pol, t) == tt_bit(tt, t) for t in range(1 << n))


def trivial_opt(n, tt):
    """opt=0: constantes e literais (com polaridade)."""
    rows = 1 << n
    if tt in (0, (1 << rows) - 1):
        return True
    for j in range(1, n + 1):
        lit = sum(((t >> (j - 1)) & 1) << t for t in range(rows))
        if tt == lit or tt == ((1 << rows) - 1) ^ lit:
            return True
    return False


def solve_k(n, tt, k, return_circuit=False):
    """SAT check com pysat/Glucose4. Retorna (bool, circuito|None)."""
    from pysat.solvers import Glucose4
    enc = AIGEncoder(n, k, tt).build()
    if any(len(cl) == 0 for cl in enc.clauses):
        return False, None
    with Glucose4(bootstrap_with=enc.clauses) as s:
        if not s.solve():
            return False, None
        model = s.get_model()
    gates, op = enc.decode(model)
    assert verify_circuit(n, tt, gates, op), "REPROVADO: circuito não bate com truth table"
    return True, (gates, op) if return_circuit else None


def opt_via_sat(n, tt, kmax=12):
    """Menor k com solução (0 = trivial)."""
    if trivial_opt(n, tt):
        return 0
    for k in range(1, kmax + 1):
        sat, _ = solve_k(n, tt, k)
        if sat:
            return k
    return None
