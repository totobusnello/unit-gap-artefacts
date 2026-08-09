"""Independent NPN-class check for BK5 >= 9.

Gold-standard canonicalization: brute-force over the FULL NPN group for n=5
(5! input perms x 2^5 input negations x 2 output negation = 7680 elements),
taking the lexicographically-minimum 32-bit truth table as the canonical form.
No hand-rolled heuristic. Two functions are in the same NPN class iff they have
the same canonical form.

Confirms: the 3 non-canalizing forced-multi gap=1 winners are pairwise NPN-distinct
AND distinct from the 6 AND-lifts of the BK4 classes  =>  BK5 >= 9.
Also independently re-verifies canalizing status (lifts canalizing; winners not).
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
# 6 BK4 classes lifted by AND x4  (z & x4  ==  z << 16 as a 32-bit tt; x4 is the MSB, bit 4)
bk4 = [0x0358, 0x0359, 0x03de, 0x06b5, 0x07bc, 0x178e]
lifts = {f"lift(0x{z:04x})": (z << 16) for z in bk4}

print("=== canalizing re-check ===")
for name, tt in {**winners, **lifts}.items():
    print(f"  {name}: canalizing={is_canalizing(tt)}")

print("\n=== NPN canonical forms (exhaustive 7680-element group) ===")
canon = {}
for name, tt in {**winners, **lifts}.items():
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
print(f"\nwinners pairwise-distinct: {len(winner_canons)==len(winners)} ({len(winner_canons)}/3)")
print(f"winners disjoint from lifts: {winner_canons.isdisjoint(lift_canons)}")
print(f"lifts pairwise-distinct: {len(lift_canons)==len(lifts)} ({len(lift_canons)}/6)")
total = len(winner_canons | lift_canons)
print(f"\n*** BK5 >= {total}  (distinct NPN classes: {len(lift_canons)} lifts + {len(winner_canons)} independent winners) ***")
