// Pure Cedar rendering of core_invoice_agent.triel with the guards that the
// validator asks for: every optional attribute is tested with `has` on the left
// of a short-circuiting &&. An absent attribute makes the forbid false.
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
  context has amount_eur && context has owner_approved &&
  context.amount_eur.greaterThan(context.limit_eur) && !context.owner_approved
};

@id("block_stale_quote")
forbid (principal == Inv::Agent::"agent", action == Inv::Action::"Pay", resource)
when { context has quoted_at && context.now.durationSince(context.quoted_at) > duration("1h") };
