#!/usr/bin/env python3
"""Random request streams for the differential test (plan v2 Phase 5, item 2).

One request per line: `O <id> <account> <side> <type> <stp> <price> <qty>` or
`C <id>`. Ids are mostly fresh, sometimes reused (duplicate ids, cancels of
live, cancelled or never-used ids); types include an unsupported code (5); STP
modes include an invalid code (7); prices and quantities include 0, and
quantities include values above Qmax for the capacity. With a small capacity
the store fills, so full-store rejections and post-only orders at a full
store occur. Profile `noqmax` leaves out quantities above Qmax (the one
invalid class the handwritten engine has no rule for), so the handwritten
engine can be compared for longer.
Usage: gen_stream.py <seed> <length> <capacity> [full|noqmax]
"""
import random, sys

def main():
    seed, n, cap = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    noqmax = len(sys.argv) > 4 and sys.argv[4] == "noqmax"
    rng = random.Random(seed)
    qmax = (2**64 - 1) // (cap + 1)
    next_id = 1
    for _ in range(n):
        if rng.random() < 0.18:
            # cancel: a recent id (often resting), an old one (often gone), or never used
            r = rng.random()
            if next_id == 1 or r >= 0.9: i = next_id + rng.randrange(0, 4)
            elif r < 0.7: i = max(1, next_id - rng.randrange(1, 12))
            else: i = rng.randrange(1, next_id)
            print(f"C {i}"); continue
        if rng.random() < 0.12 and next_id > 1:
            i = rng.choice([max(1, next_id - rng.randrange(1, 12)), rng.randrange(1, next_id)])
        else:
            i = next_id; next_id += 1
        t = rng.choices([0, 1, 2, 3, 5], [9, 3, 3, 4, 1])[0]
        stp = rng.choices([0, 1, 2, 3, 4, 7], [8, 2, 2, 2, 2, 1])[0]
        acct = rng.randrange(3)
        side = rng.choices([0, 1, 2], [10, 10, 1])[0]
        price = 0 if rng.random() < 0.03 else 95 + rng.randrange(11)
        r = rng.random()
        qty = 0 if r < 0.02 else (qmax + rng.randrange(1, 3) if r < 0.04 and not noqmax else 1 + rng.randrange(9))
        print(f"O {i} {acct} {side} {t} {stp} {price} {qty}")

main()
