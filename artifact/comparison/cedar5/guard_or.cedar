@id("allow_pay")
permit (principal, action == Inv::Action::"Pay", resource);

@id("forbid_unapproved")
forbid (principal, action == Inv::Action::"Pay", resource)
when { !(context has owner_approved) || !context.owner_approved };
