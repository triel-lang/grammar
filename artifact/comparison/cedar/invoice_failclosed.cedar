// Pure Cedar rendering of core_invoice_agent.triel written as the TRIEL monitor
// reads the prohibition: the forbid holds unless its condition
// `amount_eur > limit_eur AND NOT owner_approved` is known to be false in strong
// Kleene logic, that is, unless the amount is known and not over the limit, or
// the approval is known and true. As in TRIEL (MAX_AGE 1 HOURS ON_STALE BLOCK),
// the amount counts as known only while its quote is at most one hour old. Every
// optional attribute is read behind `has`, so the policy validates.
@id("agent_may_pay")
permit (principal == Inv::Agent::"agent", action == Inv::Action::"Pay", resource);

@id("owner_may_pay_in_fallback_window")
permit (principal == Inv::Owner::"owner", action == Inv::Action::"Pay", resource)
when {
  context.now > context.activated_at.offset(duration("3d")) &&
  context.now <= context.activated_at.offset(duration("5d"))
};

@id("over_limit_without_approval")
forbid (principal == Inv::Agent::"agent", action == Inv::Action::"Pay", resource)
when {
  !((context has amount_eur && context has quoted_at &&
     context.now.durationSince(context.quoted_at) <= duration("1h") &&
     !context.amount_eur.greaterThan(context.limit_eur)) ||
    (context has owner_approved && context.owner_approved))
};
