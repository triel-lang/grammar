// Pure Cedar rendering of core_invoice_agent.triel with the limit written as a
// condition of the permit, not as a forbid. The agent may pay only if the amount
// is known, its quote is at most one hour old (as MAX_AGE 1 HOURS ON_STALE BLOCK
// in TRIEL) and it is not over the limit, or if the approval is known and true.
// A request that satisfies no permit is denied by default, so a missing amount,
// quote or approval denies. Every optional attribute is read behind `has`, so the
// policy validates. There is no forbid.
@id("agent_may_pay_within_limit")
permit (principal == Inv::Agent::"agent", action == Inv::Action::"Pay", resource)
when {
  (context has amount_eur && context has quoted_at &&
   context.now.durationSince(context.quoted_at) <= duration("1h") &&
   !context.amount_eur.greaterThan(context.limit_eur)) ||
  (context has owner_approved && context.owner_approved)
};

@id("owner_may_pay_in_fallback_window")
permit (principal == Inv::Owner::"owner", action == Inv::Action::"Pay", resource)
when {
  context.now > context.activated_at.offset(duration("3d")) &&
  context.now <= context.activated_at.offset(duration("5d"))
};
