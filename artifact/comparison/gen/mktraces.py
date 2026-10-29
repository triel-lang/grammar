import sys, os
out = sys.argv[1]
T0 = 1793610000  # 2026-11-02T09:00:00Z
H = 3600; D = 86400
SUP = 'Inv::Supplier::"supplier"'
n = [0]
def ev(ts, ptype, pid, action, kind, inp, output=None):
    n[0] += 1
    p = f'Inv::{ptype}::"{pid}"'
    fields = f'input: {inp}'
    if output: fields += f', output: {output}'
    return (f'@{ts} scope(principal: {p}, resource: {SUP}) request_context(input: {inp}) '
            f'Inv::Action::"{action}"::{kind}({fields}, callerPrincipal: {p}, callerResource: {SUP}, requestId: "r{n[0]}")')
INV = '{ invoice: "inv1" }'
def activate(): return ev(T0, 'Owner', 'owner', 'Activate', 'response', INV)
def quote(ts, cents): return ev(ts, 'Oracle', 'fx_oracle', 'Quote', 'response', INV, f'{{ amount_cents: {cents} }}')
def approve(ts): return ev(ts, 'Owner', 'owner', 'Approve', 'response', INV)
def pay(ts, who, amount=None, approved=None):
    parts = ['invoice: "inv1"', 'limit_cents: 100000', 'limit_eur: 1000.00']
    if amount is not None: parts.append(f'amount_eur: {amount}')
    if approved is not None: parts.append(f'owner_approved: {approved}')
    ptype = 'Agent' if who == 'agent' else 'Owner'
    return ev(ts, ptype, who, 'Pay', 'request', '{ ' + ', '.join(parts) + ' }')
t930 = T0 + 1800; t1000 = T0 + H
traces = {
 'within_limit':     [activate(), quote(t930, 80000), pay(t1000, 'agent', '800.00', 'false')],
 'over_limit':       [activate(), quote(t930, 150000), pay(t1000, 'agent', '1500.00', 'false')],
 'approved':         [activate(), quote(t930, 150000), approve(t930 + 60), pay(t1000, 'agent', '1500.00', 'true')],
 'approval_missing': [activate(), quote(t930, 150000), pay(t1000, 'agent', '1500.00', None)],
 'stale_quote':      [activate(), quote(t930, 150000), pay(T0 + 2*H, 'agent', '1500.00', 'false')],
 'owner_fallback':   [activate(), quote(t930, 150000), pay(T0 + 4*D + H, 'owner', '1500.00', 'false')],
 'owner_late':       [activate(), quote(t930, 150000)],
 'no_amount':        [activate(), pay(t1000, 'agent', None, 'false')],
 'owner_early':      [activate(), quote(t930, 150000), pay(t1000, 'owner', '1500.00', 'false')],
 'owner_after_5d':   [activate(), quote(t930, 150000), pay(T0 + 5*D + 3*H, 'owner', '1500.00', 'false')],
}
os.makedirs(out, exist_ok=True)
for name, lines in traces.items():
    with open(os.path.join(out, name + '.log'), 'w') as f:
        f.write('\n'.join(lines) + '\n')
print('written', len(traces))
