#!/usr/bin/env python3
"""
Write a scenario (examples/core/README.md) of N entries for artifact/bench.sh.

Usage:
    python3 artifact/bench_trace.py invoice|sequence N SEED > OUT.scn

The entries are drawn from random.Random(SEED) with its method random() only,
whose sequence for a given seed Python keeps the same from version to version
(the documentation of the module random says so of random(), not of randrange
or choice); so the scenario depends only on the three arguments. bench.sh lists
the SHA-256 of every scenario it writes. Entry 0 activates the specification at
2026-11-02T09:00:00Z; every later entry is 1 to 30 seconds after the one before
it.

invoice   examples/core/core_invoice_agent.triel. Each later entry is a tick
          (45%), an arrival of the quote amount_eur (45%) or a payment of the
          supplier by the agent (10%). Each entry gives limit_eur 1000.00, the
          quote amount_eur, a Decimal from 100.00 to 999.99 (absent before the
          first arrival), and owner_approved true, false or absent (a third
          each). The quote never exceeds the limit, so the prohibition is never
          breached, and each payment is checked against it.
sequence  examples/core/core_sequence.triel, whose three terms are composite.
          Each later entry is a tick (60%), a payment by alice (30%) or a leak
          by bob (10%), and gives amount, a Decimal from 0.00 to 999.99, or
          leaves it absent (a fifth of the entries).
"""
import random
import sys

START = 1793610000  # 2026-11-02T09:00:00Z


def iso(t: int) -> str:
    days, rem = divmod(t, 86400)
    # Civil date from days since 1970-01-01 (proleptic Gregorian calendar).
    z = days + 719468
    era = z // 146097
    doe = z - era * 146097
    yoe = (doe - doe // 1460 + doe // 36524 - doe // 146096) // 365
    doy = doe - (365 * yoe + yoe // 4 - yoe // 100)
    mp = (5 * doy + 2) // 153
    d = doy - (153 * mp + 2) // 5 + 1
    m = mp + 3 if mp < 10 else mp - 9
    y = yoe + era * 400 + (1 if m <= 2 else 0)
    return f"{y:04d}-{m:02d}-{d:02d}T{rem // 3600:02d}:{rem % 3600 // 60:02d}:{rem % 60:02d}Z"


def below(rng: random.Random, n: int) -> int:
    """An integer from 0 to n - 1, from one call of random()."""
    return int(rng.random() * n)


def dec(cents: int) -> str:
    return f"(dec {cents // 100}.{cents % 100:02d})"


def invoice(n: int, rng: random.Random):
    yield '(scenario bench_invoice\n  (spec "examples/core/core_invoice_agent.triel")'
    t = START
    yield f'  (entry "{iso(t)}" (activate) (data (limit_eur (dec 1000.00))))'
    quote = None
    for _ in range(n - 1):
        t += 1 + below(rng, 30)
        r = below(rng, 100)
        if r < 45:
            ev = "(tick)"
        elif r < 90:
            ev = "(arrive amount_eur)"
            quote = 10000 + below(rng, 90000)
        else:
            ev = "(act agent (pay (name supplier)) must)"
        data = ["(limit_eur (dec 1000.00))"]
        if quote is not None:
            data.append(f"(amount_eur {dec(quote)})")
        approved = ["true", "false", None][below(rng, 3)]
        if approved is not None:
            data.append(f"(owner_approved (bool {approved}))")
        yield f'  (entry "{iso(t)}" {ev} (data {" ".join(data)}))'
    yield ")"


def sequence(n: int, rng: random.Random):
    yield '(scenario bench_sequence\n  (spec "examples/core/core_sequence.triel")'
    t = START
    yield f'  (entry "{iso(t)}" (activate) (data))'
    for _ in range(n - 1):
        t += 1 + below(rng, 30)
        r = below(rng, 100)
        if r < 60:
            ev = "(tick)"
        elif r < 90:
            ev = "(act alice pay must)"
        else:
            ev = "(act bob leak must_not)"
        data = "" if below(rng, 5) == 0 else f" (amount {dec(below(rng, 100000))})"
        yield f'  (entry "{iso(t)}" {ev} (data{data}))'
    yield ")"


def main() -> int:
    if len(sys.argv) != 4 or sys.argv[1] not in ("invoice", "sequence") \
            or not sys.argv[2].isdigit() or int(sys.argv[2]) < 1 or not sys.argv[3].isdigit():
        print(__doc__, file=sys.stderr)
        return 2
    gen = invoice if sys.argv[1] == "invoice" else sequence
    out = sys.stdout
    for line in gen(int(sys.argv[2]), random.Random(int(sys.argv[3]))):
        out.write(line + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
