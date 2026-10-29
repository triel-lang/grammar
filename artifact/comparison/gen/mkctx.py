import json, os, sys
out = sys.argv[1]; os.makedirs(out, exist_ok=True)
def dt(s): return {"__extn": {"fn": "datetime", "arg": s}}
def dec(s): return {"__extn": {"fn": "decimal", "arg": s}}
def ctx(now, amount=None, quoted="2026-11-02T09:30:00Z", approved=None):
    c = {"now": dt(now), "activated_at": dt("2026-11-02T09:00:00Z"), "limit_eur": dec("1000.00")}
    if amount is not None: c["amount_eur"] = dec(amount)
    if quoted is not None: c["quoted_at"] = dt(quoted)
    if approved is not None: c["owner_approved"] = approved
    return c
cases = {
 "within_limit":     ("agent", ctx("2026-11-02T10:00:00Z", "800.00", approved=False)),
 "over_limit":       ("agent", ctx("2026-11-02T10:00:00Z", "1500.00", approved=False)),
 "approved":         ("agent", ctx("2026-11-02T10:00:00Z", "1500.00", approved=True)),
 "approval_missing": ("agent", ctx("2026-11-02T10:00:00Z", "1500.00")),
 "stale_quote":      ("agent", ctx("2026-11-02T11:00:00Z", "1500.00", approved=False)),
 "owner_fallback":   ("owner", ctx("2026-11-06T10:00:00Z", "1500.00", approved=False)),
 "owner_early":      ("owner", ctx("2026-11-02T10:00:00Z", "1500.00", approved=False)),
 "owner_after_5d":   ("owner", ctx("2026-11-07T12:00:00Z", "1500.00", approved=False)),
 "no_amount":        ("agent", ctx("2026-11-02T10:00:00Z", None, quoted=None, approved=False)),
 "no_amount_approved": ("agent", ctx("2026-11-02T10:00:00Z", None, quoted=None, approved=True)),
}
for name, (who, c) in cases.items():
    req = {"principal": f'Inv::{"Agent" if who=="agent" else "Owner"}::"{who}"',
           "action": 'Inv::Action::"Pay"', "resource": 'Inv::Supplier::"supplier"', "context": c}
    json.dump(req, open(os.path.join(out, name + ".json"), "w"), indent=1)
print("ok")
