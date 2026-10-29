// Pure Cedar rendering of core_invoice_agent.triel, as far as it goes.
@id("agent_may_pay")
permit (principal == Inv::Agent::"agent", action == Inv::Action::"Pay", resource);

// Attempted encoding of the ELSE branch: the owner may pay in (activated+3d, activated+5d].
@id("owner_may_pay_in_fallback_window")
permit (principal == Inv::Owner::"owner", action == Inv::Action::"Pay", resource)
when {
  context.now > context.activated_at.offset(duration("3d")) &&
  context.now <= context.activated_at.offset(duration("5d"))
};

// MUST_NOT pay WHEN amount_eur > limit_eur AND NOT owner_approved (no `has` guards).
@id("over_limit_without_approval")
forbid (principal == Inv::Agent::"agent", action == Inv::Action::"Pay", resource)
when { context.amount_eur.greaterThan(context.limit_eur) && !context.owner_approved };

// MAX_AGE 1 HOURS ON_STALE BLOCK, as a comparison of request attributes.
@id("block_stale_quote")
forbid (principal == Inv::Agent::"agent", action == Inv::Action::"Pay", resource)
when { context.now.durationSince(context.quoted_at) > duration("1h") };
