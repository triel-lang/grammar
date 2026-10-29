@id("allow_pay")
permit (principal, action == Inv::Action::"Pay", resource);

@id("forbid_unapproved")
forbid (principal, action == Inv::Action::"Pay", resource)
when { if context has owner_approved then !context.owner_approved else true };
