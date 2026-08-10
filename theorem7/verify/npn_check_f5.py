"""Independent NPN-class check for F5 >= 10 (claim 0037 ressalva 1; 10th class by claim 0038).

Gold-standard canonicalization: brute-force over the FULL NPN group for n=5
(5! input perms x 2^5 input negations x 2 output negation = 7680 elements),
taking the lexicographically-minimum 32-bit truth table as the canonical form.
No hand-rolled heuristic. Two functions are in the same NPN class iff they have
the same canonical form.

Confirms: the 3 non-canalizing forced-multi gap=1 winners are pairwise NPN-distinct
AND distinct from the 6 AND-lifts of the F4 classes, and that the census witness
`0x09c50800` is distinct from all nine  =>  F5 >= 10.
Also independently re-verifies canalizing status (lifts canalizing; winners not).

The count is printed DECOMPOSED BY PROVENANCE (lifts / directed sweep / random census), because
that split is the actual argument of §6 of the paper: the family has two independent origins, and
a bare "10" hides the one number a referee cares about — how many appeared without anyone knowing
where to look.
"""
from itertools import permutations

N = 5
ROWS = 1 << N
MASK = (1 << ROWS) - 1


def apply_transform(tt, perm, negmask):
    """g(a2) = f(a), where a2 is a with inputs negated (negmask) then permuted (perm[i]=dest bit)."""
    new = 0
    for a in range(ROWS):
        a2 = 0
        for i in range(N):
            bit = (a >> i) & 1
            if (negmask >> i) & 1:
                bit ^= 1
            a2 |= bit << perm[i]
        if (tt >> a) & 1:
            new |= 1 << a2
    return new


def npn_canon(tt):
    best = None
    perms = list(permutations(range(N)))
    for perm in perms:
        for negmask in range(1 << N):
            g = apply_transform(tt, perm, negmask)
            for out in (g, (~g) & MASK):
                if best is None or out < best:
                    best = out
    return best


def is_canalizing(tt):
    """Some variable has a constant cofactor (=> AND/OR-lift direction). NPN-invariant property."""
    for i in range(N):
        for val in (0, 1):
            bits = [(tt >> a) & 1 for a in range(ROWS) if ((a >> i) & 1) == val]
            if all(b == 0 for b in bits) or all(b == 1 for b in bits):
                return True
    return False


winners = {
    "0x03de0154": 0x03de0154,   # 0x03de & (~x0 | x4)
    "0xabfe03de": 0xabfe03de,   # 0x03de | (x0 & x4)
    "0x57df03de": 0x57df03de,   # 0x03de | (~x0 & x4)
}
# 6 F4 classes lifted by AND x4  (z & x4  ==  z << 16 as a 32-bit tt; x4 is the MSB, bit 4)
f4 = [0x0358, 0x0359, 0x03de, 0x06b5, 0x07bc, 0x178e]
lifts = {f"lift(0x{z:04x})": (z << 16) for z in f4}
# The 10th class, PROMOTED 2026-08-10 (claim 0038): first forced-reconvergence witness found by random sampling rather
# than by a directed sweep on the flagship family. Chain certified no-SB — forced-multi UNSAT +
# drat-trim (decide_pending.py), opt=8 by UNSAT k=1..7 + SAT witness, tree=9 by fan-out-1 formula
# witness (cert_chain.py) — and passed the 3-family panel 3/3 GO (REV-0096/0097/0098). Listed here so
# its NPN distinctness is a re-runnable artifact rather than a literal quoted in a note (Kimi REV-0097
# finding 5a).
#
# It sat in `candidates` while awaiting the promotion rule, and this dict stayed behind after the rule
# was satisfied: the script kept printing "F5 >= 9 established" plus "10 if the candidate chains
# hold" for a day after the chains had held and the claim was VERIFIED. The separation was right
# BEFORE promotion and became stale the moment it happened — the lesson being that a "pending" bucket
# needs an owner, or it silently understates the result.
promoted_2026_08_10 = {
    "0x09c50800": 0x09C50800,
}
# Nothing is awaiting promotion right now. New witnesses go here first, and move up once the panel
# clears them — keeping the printed count honest in both directions.
candidates = {}

ALL = {**winners, **lifts, **promoted_2026_08_10, **candidates}

print("=== canalizing re-check ===")
for name, tt in ALL.items():
    print(f"  {name}: canalizing={is_canalizing(tt)}")

print("\n=== NPN canonical forms (exhaustive 7680-element group) ===")
canon = {}
for name, tt in ALL.items():
    c = npn_canon(tt)
    canon[name] = c
    print(f"  {name:16s} -> {c:#010x}")

classes = {}
for name, c in canon.items():
    classes.setdefault(c, []).append(name)
print(f"\n=== distinct NPN classes among the {len(canon)} functions: {len(classes)} ===")
for c, names in classes.items():
    print(f"  {c:#010x}: {names}")

winner_canons = {canon[n] for n in winners}
lift_canons = {canon[n] for n in lifts}
census_canons = {canon[n] for n in promoted_2026_08_10}
cand_canons = {canon[n] for n in candidates}
print(f"\nwinners pairwise-distinct: {len(winner_canons)==len(winners)} ({len(winner_canons)}/3)")
print(f"winners disjoint from lifts: {winner_canons.isdisjoint(lift_canons)}")
print(f"lifts pairwise-distinct: {len(lift_canons)==len(lifts)} ({len(lift_canons)}/6)")
print(f"census witness disjoint from all above: "
      f"{census_canons.isdisjoint(winner_canons | lift_canons)}")
established = winner_canons | lift_canons | census_canons
# A contagem sai decomposta POR PROVENIÊNCIA, não só como total. O argumento do §6 do P1 é que a
# família tem duas origens independentes — construção dirigida e censo aleatório — e um total de 10
# esconde exatamente isso. O número que interessa a um referee é "quantas apareceram sem que se
# soubesse onde olhar", e a resposta é uma, explicitamente.
print(f"\n*** F5 >= {len(established)}  (established: {len(lift_canons)} lifts + "
      f"{len(winner_canons)} by directed sweep + {len(census_canons)} by random census) ***")

if candidates:
    print("\n=== candidates (certified chain, pending promotion) ===")
    for name in candidates:
        c = canon[name]
        clash = [n for n, cc in canon.items() if cc == c and n != name]
        print(f"  {name}: canon={c:#010x} canalizing={is_canalizing(candidates[name])} "
              f"{'COLLIDES with ' + str(clash) if clash else 'NPN-distinct from all established'}")
    fresh = cand_canons - established
    print(f"  distinct new classes: {len(fresh)}  =>  F5 >= {len(established | cand_canons)} "
          f"if the candidate chains hold")
