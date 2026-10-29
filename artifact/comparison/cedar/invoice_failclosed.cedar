// Pure Cedar rendering of core_invoice_agent.triel written to fail closed: a
// forbid holds unless its condition is known to be false, as the TRIEL monitor
// blocks unless the condition is known to be false. Guarded with if ... then ...
// else true, which the validator accepts.
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
  if context has amount_eur
  then context.amount_eur.greaterThan(context.limit_eur) &&
       (if context has owner_approved then !context.owner_approved else true)
  else true
};

@id("block_stale_quote")
forbid (principal == Inv::Agent::"agent", action == Inv::Action::"Pay", resource)
when {
  if context has quoted_at
  then context.now.durationSince(context.quoted_at) > duration("1h")
  else true
};
