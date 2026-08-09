"""
Encoder de exact synthesis AIG via SAT.

Pergunta codificada: "existe circuito AIG com exatamente k portas AND que computa f?"
Modelo AIG: portas AND de 2 entradas,
inversões livres em qualquer aresta e na saída; tamanho = número de portas AND.

Semântica do encoding (validada contra enumeração independente):
- Nós: entradas 1..n (valores fixos por linha da truth table), portas n+1..n+k.
- Cada porta i escolhe (one-hot) uma opção (a, pa, b, pb): operandos a < b
  dentre nós anteriores, com polaridades pa, pb.
- v[i][t] = valor da porta i na linha t; cláusulas condicionais impõem
  v[i][t] <-> (val(a,t) xor pa) AND (val(b,t) xor pb).
- Saída = porta k com polaridade livre op: v[k][t] <-> (f(t) xor op).
- Quebra de simetria (sound): toda porta i < k precisa ser usada por alguma
  porta posterior.
- k=0 tratado fora do SAT (f constante ou literal).

NOTE: a DRAT proof certifies the CNF, not the encoding — hence the independent
cross-enumeration check and the per-circuit simulation (verify_circuit) of every SAT model.
"""

from itertools import combinations


def tt_bit(tt, t):
    return (tt >> t) & 1


class AIGEncoder:
    def __init__(self, n, k, tt, formula=False):
        """n entradas, k portas AND, tt = truth table como inteiro de 2^n bits.
        formula=True: modo FÓRMULA (fan-out 1) — cada porta não-saída é usada por
        EXATAMENTE uma posterior (árvore). SAT em k => tree(f) <= k. Idêntico ao
        modo formula do XAGEncoder; a restrição adicional é só a de fan-out."""
        self.n, self.k, self.tt, self.formula = n, k, tt, formula
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
            for a, b in combinations(nodes, 2):
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
                    # constantes 0/1 e literais DIMACS ±1 são tipos separados (evita colisão).
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
        # QUEBRA DE SIMETRIA (WLOG em k=opt): duas portas nunca selecionam a MESMA
        # opção (a,pa,b,pb) — um circuito MÍNIMO nunca tem portas duplicadas (remover
        # a duplicata daria um circuito menor), logo toda solução relevante é livre de duplicatas.
        # QUEBRA DE SIMETRIA — só no modo CIRCUITO. Num modo FÓRMULA (árvore), uma
        # subárvore pode aparecer DUPLICADA (é a razão de tree>opt); proibir
        # duplicatas excluiria fórmulas mínimas válidas e daria UNSAT FALSO
        # (lower bound de tree errado). Por isso o dedup é desligado se formula.
        if not self.formula:
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
    """VERIFICAÇÃO SEMÂNTICA: circuito bate com a truth table inteira?"""
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
