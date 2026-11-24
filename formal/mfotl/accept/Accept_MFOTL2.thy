(*  Title:      Accept_MFOTL2.thy
    Acceptance of part 2 of the bridge from the TRIEL core to MFOTL: norms and deadlines.
    Written by the maintainers, not by the stage; the stage may not change this file (its
    SHA-256 is checked in CI). It has four parts.
    (1) The formulas. For each constant of the bridge that is a formula (and for rel_lo,
    the lower bound of a window) a lemma writes it out in the constructors of the AFP
    theory Formula, the constants of part 1 and the constants written out before it, and
    proves it by the definition of the stage alone. A formula is built from the parameters
    of the norm and the activation time, an integer: no constant takes a trace.
    (2) The theorems. Each lemma restates a theorem of the session TRIEL_MFOTL exactly and
    proves it by that theorem alone. Every type variable carries its sort, so a bridge
    whose constants or theorems need a narrower type or a further class does not parse or
    is not proved here.
    (3) Probes. What the formulas of (1) say at an entry is derived from the satisfaction
    relation of MFOTL alone, without a lemma or theorem of the bridge, and checked on
    concrete entries: an action exactly at the deadline fulfils, one time unit later the
    obligation is breached; FROM is inclusive; a condition is read at the entry before the
    action; an undefined condition blocks and is not a breach. The probes are about the
    formulas as (1) writes them out: (1) ties the definitions of the stage to them.
    (4) The ML block at the end fails if a lemma uses a constant that is neither of the
    core, of the AFP theory Formula (with its ancestors) nor one of the constants of the
    bridge named there; if a lemma does not use the constants it is about; or if a lemma
    depends on an oracle (an unfinished proof is one).
    The satisfaction relation is written Formula.sat, without notation: the AFP switches
    its notation off at the end of the theory Formula.
*)

theory Accept_MFOTL2
  imports TRIEL_Core.TRIEL_Breach TRIEL_MFOTL.TRIEL_MFOTL_Norm TRIEL_MFOTL.TRIEL_MFOTL_Future
begin

section \<open>The formulas\<close>

text \<open>Time since the activation entry. \<open>First\<close> holds at entry 0 only; \<open>At I\<close> holds
  at an entry whose distance from entry 0 is in \<open>I\<close>. The window \<open>(lo, d]\<close> of the core,
  with the activation time \<open>\<tau>\<^sub>0\<close>: its times are \<open>InWin\<close>, the times after \<open>lo\<close> are
  \<open>AfterLo\<close>, the times strictly after \<open>d\<close> are \<open>Passed\<close>.\<close>

lemma accept_def_First:
  "(First :: (string, ('n :: type, 'v :: type, 's :: type, 'a :: type) TRIEL_MFOTL_Enc.mval) Formula.formula) =
     formula.Neg (formula.Prev Interval.all formula.TT)"
  by (rule First_def)

lemma accept_def_At:
  "(At (I :: Interval.\<I>) :: (string, ('n :: type, 'v :: type, 's :: type, 'a :: type) TRIEL_MFOTL_Enc.mval) Formula.formula) =
     formula.Once I First"
  by (rule At_def)

lemma accept_def_rel_lo:
  "rel_lo (\<tau>\<^sub>0 :: int) (lo :: int option) = (case lo of None \<Rightarrow> (0 :: nat) | Some l \<Rightarrow> nat (l + 1 - \<tau>\<^sub>0))"
  by (rule rel_lo_def)

lemma accept_def_InWin:
  "(InWin (\<tau>\<^sub>0 :: int) (lo :: int option) (d :: int) :: (string, ('n :: type, 'v :: type, 's :: type, 'a :: type) TRIEL_MFOTL_Enc.mval) Formula.formula) =
     (if d < \<tau>\<^sub>0 \<or> nat (d - \<tau>\<^sub>0) < rel_lo \<tau>\<^sub>0 lo then formula.FF
      else At (Interval.interval (rel_lo \<tau>\<^sub>0 lo) (enat (nat (d - \<tau>\<^sub>0)))))"
  by (rule InWin_def)

lemma accept_def_AfterLo:
  "(AfterLo (\<tau>\<^sub>0 :: int) (lo :: int option) :: (string, ('n :: type, 'v :: type, 's :: type, 'a :: type) TRIEL_MFOTL_Enc.mval) Formula.formula) =
     At (Interval.interval (rel_lo \<tau>\<^sub>0 lo) \<infinity>)"
  by (rule AfterLo_def)

lemma accept_def_Passed:
  "(Passed (\<tau>\<^sub>0 :: int) (d :: int) :: (string, ('n :: type, 'v :: type, 's :: type, 'a :: type) TRIEL_MFOTL_Enc.mval) Formula.formula) =
     (if d < \<tau>\<^sub>0 then formula.TT else At (Interval.interval (Suc (nat (d - \<tau>\<^sub>0))) \<infinity>))"
  by (rule Passed_def)

text \<open>Obligations: the action \<open>a\<close> of \<open>s\<close> is the fact \<open>act\<close> of the encoding of part 1.\<close>

lemma accept_def_Act:
  "(Act (s :: 's :: type) (a :: 'a :: type) :: (string, ('n :: type, 'v :: type, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.formula) =
     formula.Pred ''act'' [trm.Const (MS s), trm.Const (MA a)]"
  by (rule Act_def)

lemma accept_def_Acted:
  "(Acted (\<tau>\<^sub>0 :: int) (s :: 's :: type) (a :: 'a :: type) (lo :: int option) (d :: int) :: (string, ('n :: type, 'v :: type, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.formula) =
     formula.Once Interval.all (formula.And (Act s a) (InWin \<tau>\<^sub>0 lo d))"
  by (rule Acted_def)

lemma accept_def_ObBre:
  "(ObBre (\<tau>\<^sub>0 :: int) (s :: 's :: type) (a :: 'a :: type) (lo :: int option) (d :: int) :: (string, ('n :: type, 'v :: type, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.formula) =
     formula.And (formula.Neg (Acted \<tau>\<^sub>0 s a lo d)) (Passed \<tau>\<^sub>0 d)"
  by (rule ObBre_def)

lemma accept_def_ActedN:
  "(ActedN (\<tau>\<^sub>0 :: int) (s :: 's :: type) (a :: 'a :: type) (lo :: int option) :: (string, ('n :: type, 'v :: type, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.formula) =
     formula.Once Interval.all (formula.And (Act s a) (AfterLo \<tau>\<^sub>0 lo))"
  by (rule ActedN_def)

text \<open>Prohibitions: the condition is the formula \<open>Pc\<close> (true) or \<open>Nc\<close> (false) of part 1,
  read at the entry before the action.\<close>

lemma accept_def_Forb:
  "(Forb (s :: 's :: type) (a :: 'a :: type) (c :: ('n :: type, 'v :: type) TRIEL_Core.expr) :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.formula) =
     formula.And (Act s a) (formula.Prev Interval.all (Pc c))"
  by (rule Forb_def)

lemma accept_def_PrBre:
  "(PrBre (s :: 's :: type) (a :: 'a :: type) (c :: ('n :: type, 'v :: type) TRIEL_Core.expr) :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.formula) =
     formula.Once Interval.all (Forb s a c)"
  by (rule PrBre_def)

lemma accept_def_PrFirst:
  "(PrFirst (s :: 's :: type) (a :: 'a :: type) (c :: ('n :: type, 'v :: type) TRIEL_Core.expr) :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.formula) =
     formula.And (Forb s a c) (formula.Neg (formula.Prev Interval.all (PrBre s a c)))"
  by (rule PrFirst_def)

lemma accept_def_Blk:
  "(Blk (s :: 's :: type) (a :: 'a :: type) (c :: ('n :: type, 'v :: type) TRIEL_Core.expr) :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.formula) =
     formula.And (Act s a) (formula.Prev Interval.all (formula.Neg (Nc c)))"
  by (rule Blk_def)

text \<open>A fresh factor, the fallback in force, and the obligation as a formula of bounded
  future.\<close>

lemma accept_def_Fresh:
  "(Fresh (m :: int) (x :: 'n :: type) :: (string, ('n, 'v :: type, 's :: type, 'a :: type) TRIEL_MFOTL_Enc.mval) Formula.formula) =
     formula.Once (Interval.interval 0 (enat (nat m))) (formula.Pred ''arr'' [trm.Const (MN x)])"
  by (rule Fresh_def)

lemma accept_def_ElseIn:
  "(ElseIn (\<tau>\<^sub>0 :: int) (s :: 's :: type) (a :: 'a :: type) (d :: int) :: (string, ('n :: type, 'v :: type, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.formula) =
     formula.And (formula.Neg (Acted \<tau>\<^sub>0 s a None d)) (Passed \<tau>\<^sub>0 d)"
  by (rule ElseIn_def)

lemma accept_def_ObFut:
  "(ObFut (n :: nat) (s :: 's :: type) (a :: 'a :: type) :: (string, ('n :: type, 'v :: type, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.formula) =
     formula.Eventually (Interval.interval 0 (enat n)) (Act s a)"
  by (rule ObFut_def)


section \<open>The theorems\<close>

text \<open>An obligation with the window \<open>(lo, d]\<close> (WITHIN, BY, FROM): the verdict on the
  prefix up to entry \<open>j\<close> is read at entry \<open>j\<close>; "pending" is neither formula.\<close>

lemma accept_window_fulfilled:
  "\<lbrakk>is_trace (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace); enc_pre C \<pi> (\<sigma> :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.trace); j < length \<pi>\<rbrakk>
   \<Longrightarrow> window s a lo d (pre \<pi> j) = Fulfilled \<longleftrightarrow> Formula.sat \<sigma> v j (Acted (time \<pi> 0) s a lo d)"
  by (rule bridge_window_fulfilled)

lemma accept_window_breached:
  "\<lbrakk>is_trace (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace); enc_pre C \<pi> (\<sigma> :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.trace); j < length \<pi>\<rbrakk>
   \<Longrightarrow> window s a lo d (pre \<pi> j) = Breached t \<longleftrightarrow> t = d \<and> Formula.sat \<sigma> v j (ObBre (time \<pi> 0) s a lo d)"
  by (rule bridge_window_breached)

lemma accept_window_pending:
  "\<lbrakk>is_trace (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace); enc_pre C \<pi> (\<sigma> :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.trace); j < length \<pi>\<rbrakk>
   \<Longrightarrow> window s a lo d (pre \<pi> j) = Pending \<longleftrightarrow>
       \<not> Formula.sat \<sigma> v j (Acted (time \<pi> 0) s a lo d) \<and> \<not> Formula.sat \<sigma> v j (ObBre (time \<pi> 0) s a lo d)"
  by (rule bridge_window_pending)

text \<open>An obligation without a deadline is fulfilled or pending.\<close>

lemma accept_ob_no_deadline:
  "\<lbrakk>is_trace (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace); enc_pre C \<pi> (\<sigma> :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.trace); j < length \<pi>\<rbrakk>
   \<Longrightarrow> ob_verdict s a lo None (pre \<pi> j) =
       (if Formula.sat \<sigma> v j (ActedN (time \<pi> 0) s a lo) then Fulfilled else Pending)"
  by (rule bridge_ob_no_deadline)

text \<open>A prohibition is breached or pending; the time of the breach is the time of the
  entry of the first forbidden action.\<close>

lemma accept_pr_breached:
  "\<lbrakk>is_trace (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace); enc_pre C \<pi> (\<sigma> :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.trace); j < length \<pi>; econsts c \<subseteq> C\<rbrakk>
   \<Longrightarrow> (\<exists>t. pr_verdict s a c (pre \<pi> j) = Breached t) \<longleftrightarrow> Formula.sat \<sigma> v j (PrBre s a c)"
  by (rule bridge_pr_breached)

lemma accept_pr_pending:
  "\<lbrakk>is_trace (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace); enc_pre C \<pi> (\<sigma> :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.trace); j < length \<pi>; econsts c \<subseteq> C\<rbrakk>
   \<Longrightarrow> pr_verdict s a c (pre \<pi> j) = Pending \<longleftrightarrow> \<not> Formula.sat \<sigma> v j (PrBre s a c)"
  by (rule bridge_pr_pending)

lemma accept_pr_time:
  "\<lbrakk>is_trace (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace); enc_pre C \<pi> (\<sigma> :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.trace); j < length \<pi>; econsts c \<subseteq> C\<rbrakk>
   \<Longrightarrow> pr_verdict s a c (pre \<pi> j) = Breached t \<longleftrightarrow>
       (\<exists>k \<le> j. Formula.sat \<sigma> v k (PrFirst s a c) \<and> time \<pi> k = t)"
  by (rule bridge_pr_time)

text \<open>The decision of the fail-closed monitor at one entry, a permission, and a fresh
  factor (MAX_AGE).\<close>

lemma accept_blocked_action:
  "\<lbrakk>is_trace (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace); enc_pre C \<pi> (\<sigma> :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.trace); j < length \<pi>; econsts c \<subseteq> C\<rbrakk>
   \<Longrightarrow> blocked_action s a c \<pi> j \<longleftrightarrow> Formula.sat \<sigma> v j (Blk s a c)"
  by (rule bridge_blocked_action)

lemma accept_may:
  "\<lbrakk>is_trace (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace); enc_pre C \<pi> (\<sigma> :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.trace); j < length \<pi>; econsts c \<subseteq> C\<rbrakk>
   \<Longrightarrow> may_verdict s a c (pre \<pi> j) = Fulfilled \<longleftrightarrow> Formula.sat \<sigma> v j (PrBre s a c)"
  by (rule bridge_may)

lemma accept_fresh:
  "\<lbrakk>is_trace (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace); enc_pre C \<pi> (\<sigma> :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.trace); j < length \<pi>; 0 \<le> m\<rbrakk>
   \<Longrightarrow> fresh m x \<pi> j \<longleftrightarrow> Formula.sat \<sigma> v j (Fresh m x)"
  by (rule bridge_fresh)

text \<open>ELSE with a deadline \<open>d'\<close> of the fallback: the four clauses of \<open>bridge_else\<close>.\<close>

lemma accept_else_fulfilled:
  "\<lbrakk>is_trace (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace); enc_pre C \<pi> (\<sigma> :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.trace); j < length \<pi>\<rbrakk>
   \<Longrightarrow> else_verdict s a d s' a' (Some d') (pre \<pi> j) = EFulfilled \<longleftrightarrow>
       Formula.sat \<sigma> v j (Acted (time \<pi> 0) s a None d)"
  by (rule bridge_else(1))

lemma accept_else_alt_fulfilled:
  "\<lbrakk>is_trace (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace); enc_pre C \<pi> (\<sigma> :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.trace); j < length \<pi>\<rbrakk>
   \<Longrightarrow> else_verdict s a d s' a' (Some d') (pre \<pi> j) = EElse d Fulfilled \<longleftrightarrow>
       Formula.sat \<sigma> v j (formula.And (ElseIn (time \<pi> 0) s a d) (Acted (time \<pi> 0) s' a' (Some d) d'))"
  by (rule bridge_else(2))

lemma accept_else_alt_breached:
  "\<lbrakk>is_trace (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace); enc_pre C \<pi> (\<sigma> :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.trace); j < length \<pi>\<rbrakk>
   \<Longrightarrow> else_verdict s a d s' a' (Some d') (pre \<pi> j) = EElse d (Breached d') \<longleftrightarrow>
       Formula.sat \<sigma> v j (formula.And (ElseIn (time \<pi> 0) s a d) (ObBre (time \<pi> 0) s' a' (Some d) d'))"
  by (rule bridge_else(3))

lemma accept_else_pending:
  "\<lbrakk>is_trace (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace); enc_pre C \<pi> (\<sigma> :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.trace); j < length \<pi>\<rbrakk>
   \<Longrightarrow> else_verdict s a d s' a' (Some d') (pre \<pi> j) = EPending \<longleftrightarrow>
       \<not> Formula.sat \<sigma> v j (Acted (time \<pi> 0) s a None d) \<and> \<not> Formula.sat \<sigma> v j (Passed (time \<pi> 0) d)"
  by (rule bridge_else(4))

text \<open>ON_BREACH with CURE_BY \<open>k\<close>: the three clauses of \<open>bridge_cure\<close>. \<open>b\<close> is the start
  of the obligation, the first argument of \<open>handle_breach\<close>.\<close>

lemma accept_cure_fulfilled:
  "\<lbrakk>is_trace (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace); enc_pre C \<pi> (\<sigma> :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.trace); j < length \<pi>;
     cont_of (acts :: ('s, 'p :: type) TRIEL_Breach.baction list) = Some (CureBy k)\<rbrakk>
   \<Longrightarrow> handle_breach b lo s a d acts (pre \<pi> j) = SBreached d (Cure Fulfilled) \<longleftrightarrow>
       Formula.sat \<sigma> v j (formula.And (ObBre (time \<pi> 0) s a lo d) (Acted (time \<pi> 0) s a (Some d) (d + k)))"
  by (rule bridge_cure(1))

lemma accept_cure_breached:
  "\<lbrakk>is_trace (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace); enc_pre C \<pi> (\<sigma> :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.trace); j < length \<pi>;
     cont_of (acts :: ('s, 'p :: type) TRIEL_Breach.baction list) = Some (CureBy k)\<rbrakk>
   \<Longrightarrow> handle_breach b lo s a d acts (pre \<pi> j) = SBreached d (Cure (Breached (d + k))) \<longleftrightarrow>
       Formula.sat \<sigma> v j (formula.And (ObBre (time \<pi> 0) s a lo d) (ObBre (time \<pi> 0) s a (Some d) (d + k)))"
  by (rule bridge_cure(2))

lemma accept_cure_base_fulfilled:
  "\<lbrakk>is_trace (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace); enc_pre C \<pi> (\<sigma> :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.trace); j < length \<pi>;
     cont_of (acts :: ('s, 'p :: type) TRIEL_Breach.baction list) = Some (CureBy k)\<rbrakk>
   \<Longrightarrow> handle_breach b lo s a d acts (pre \<pi> j) = SFulfilled \<longleftrightarrow>
       Formula.sat \<sigma> v j (Acted (time \<pi> 0) s a lo d)"
  by (rule bridge_cure(3))

text \<open>ON_BREACH with ESCALATE_TO \<open>s'\<close>: the two clauses of \<open>bridge_escalate\<close>.\<close>

lemma accept_escalate_fulfilled:
  "\<lbrakk>is_trace (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace); enc_pre C \<pi> (\<sigma> :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.trace); j < length \<pi>;
     cont_of (acts :: ('s, 'p :: type) TRIEL_Breach.baction list) = Some (EscalateTo s')\<rbrakk>
   \<Longrightarrow> handle_breach b lo s a d acts (pre \<pi> j) = SBreached d (Escalated s' Fulfilled) \<longleftrightarrow>
       Formula.sat \<sigma> v j (formula.And (ObBre (time \<pi> 0) s a lo d) (Acted (time \<pi> 0) s' a (Some d) (d + (d - b))))"
  by (rule bridge_escalate(1))

lemma accept_escalate_breached:
  "\<lbrakk>is_trace (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace); enc_pre C \<pi> (\<sigma> :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.trace); j < length \<pi>;
     cont_of (acts :: ('s, 'p :: type) TRIEL_Breach.baction list) = Some (EscalateTo s')\<rbrakk>
   \<Longrightarrow> handle_breach b lo s a d acts (pre \<pi> j) = SBreached d (Escalated s' (Breached (d + (d - b)))) \<longleftrightarrow>
       Formula.sat \<sigma> v j (formula.And (ObBre (time \<pi> 0) s a lo d) (ObBre (time \<pi> 0) s' a (Some d) (d + (d - b))))"
  by (rule bridge_escalate(2))

text \<open>The window without FROM and the formula of bounded future at entry 0, over all
  traces of MFOTL that encode the trace: the two clauses of \<open>bridge_window_future\<close>.\<close>

lemma accept_future_fulfilled:
  "\<lbrakk>is_trace (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace); finite C;
     \<forall>j < length \<pi>. finite (dom (st \<pi> j)); time \<pi> 0 \<le> d\<rbrakk>
   \<Longrightarrow> window s a None d \<pi> = Fulfilled \<longleftrightarrow>
       (\<forall>\<sigma> :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.trace.
          enc_pre C \<pi> \<sigma> \<longrightarrow> Formula.sat \<sigma> v 0 (ObFut (nat (d - time \<pi> 0)) s a))"
  by (rule bridge_window_future(1))

lemma accept_future_breached:
  "\<lbrakk>is_trace (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace); finite C;
     \<forall>j < length \<pi>. finite (dom (st \<pi> j)); time \<pi> 0 \<le> d\<rbrakk>
   \<Longrightarrow> window s a None d \<pi> = Breached d \<longleftrightarrow>
       (\<forall>\<sigma> :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.trace.
          enc_pre C \<pi> \<sigma> \<longrightarrow> \<not> Formula.sat \<sigma> v 0 (ObFut (nat (d - time \<pi> 0)) s a))"
  by (rule bridge_window_future(2))


section \<open>The remaining statuses of ELSE and ON_BREACH\<close>

text \<open>The fallback in force and still open (\<open>bridge_else_alt_pending\<close>), and a fallback
  without a deadline (the four clauses of \<open>bridge_else_no_deadline\<close>).\<close>

lemma accept_else_alt_pending:
  "\<lbrakk>is_trace (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace); enc_pre C \<pi> (\<sigma> :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.trace); j < length \<pi>\<rbrakk>
   \<Longrightarrow> else_verdict s a d s' a' (Some d') (pre \<pi> j) = EElse d Pending \<longleftrightarrow>
       Formula.sat \<sigma> v j (ElseIn (time \<pi> 0) s a d)
       \<and> \<not> Formula.sat \<sigma> v j (Acted (time \<pi> 0) s' a' (Some d) d')
       \<and> \<not> Formula.sat \<sigma> v j (ObBre (time \<pi> 0) s' a' (Some d) d')"
  by (rule bridge_else_alt_pending)

lemma accept_else_nd_fulfilled:
  "\<lbrakk>is_trace (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace); enc_pre C \<pi> (\<sigma> :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.trace); j < length \<pi>\<rbrakk>
   \<Longrightarrow> else_verdict s a d s' a' None (pre \<pi> j) = EFulfilled \<longleftrightarrow>
       Formula.sat \<sigma> v j (Acted (time \<pi> 0) s a None d)"
  by (rule bridge_else_no_deadline(1))

lemma accept_else_nd_alt_fulfilled:
  "\<lbrakk>is_trace (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace); enc_pre C \<pi> (\<sigma> :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.trace); j < length \<pi>\<rbrakk>
   \<Longrightarrow> else_verdict s a d s' a' None (pre \<pi> j) = EElse d Fulfilled \<longleftrightarrow>
       Formula.sat \<sigma> v j (formula.And (ElseIn (time \<pi> 0) s a d) (ActedN (time \<pi> 0) s' a' (Some d)))"
  by (rule bridge_else_no_deadline(2))

lemma accept_else_nd_alt_pending:
  "\<lbrakk>is_trace (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace); enc_pre C \<pi> (\<sigma> :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.trace); j < length \<pi>\<rbrakk>
   \<Longrightarrow> else_verdict s a d s' a' None (pre \<pi> j) = EElse d Pending \<longleftrightarrow>
       Formula.sat \<sigma> v j (ElseIn (time \<pi> 0) s a d) \<and> \<not> Formula.sat \<sigma> v j (ActedN (time \<pi> 0) s' a' (Some d))"
  by (rule bridge_else_no_deadline(3))

lemma accept_else_nd_pending:
  "\<lbrakk>is_trace (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace); enc_pre C \<pi> (\<sigma> :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.trace); j < length \<pi>\<rbrakk>
   \<Longrightarrow> else_verdict s a d s' a' None (pre \<pi> j) = EPending \<longleftrightarrow>
       \<not> Formula.sat \<sigma> v j (Acted (time \<pi> 0) s a None d) \<and> \<not> Formula.sat \<sigma> v j (Passed (time \<pi> 0) d)"
  by (rule bridge_else_no_deadline(4))

text \<open>The status of an obligation with a handler while it is not breached, whatever the
  handler (the two clauses of \<open>bridge_handle_open\<close>); TERMINATE and a handler without a
  continuation; the second window of CURE_BY and the window of ESCALATE_TO still open.\<close>

lemma accept_handle_fulfilled:
  "\<lbrakk>is_trace (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace); enc_pre C \<pi> (\<sigma> :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.trace); j < length \<pi>\<rbrakk>
   \<Longrightarrow> handle_breach b lo s a d (acts :: ('s, 'p :: type) TRIEL_Breach.baction list) (pre \<pi> j) = SFulfilled \<longleftrightarrow>
       Formula.sat \<sigma> v j (Acted (time \<pi> 0) s a lo d)"
  by (rule bridge_handle_open(1))

lemma accept_handle_pending:
  "\<lbrakk>is_trace (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace); enc_pre C \<pi> (\<sigma> :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.trace); j < length \<pi>\<rbrakk>
   \<Longrightarrow> handle_breach b lo s a d (acts :: ('s, 'p :: type) TRIEL_Breach.baction list) (pre \<pi> j) = SPending \<longleftrightarrow>
       \<not> Formula.sat \<sigma> v j (Acted (time \<pi> 0) s a lo d) \<and> \<not> Formula.sat \<sigma> v j (ObBre (time \<pi> 0) s a lo d)"
  by (rule bridge_handle_open(2))

lemma accept_terminate:
  "\<lbrakk>is_trace (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace); enc_pre C \<pi> (\<sigma> :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.trace); j < length \<pi>;
     cont_of (acts :: ('s, 'p :: type) TRIEL_Breach.baction list) = Some Terminate\<rbrakk>
   \<Longrightarrow> handle_breach b lo s a d acts (pre \<pi> j) = SBreached d Terminated \<longleftrightarrow>
       Formula.sat \<sigma> v j (ObBre (time \<pi> 0) s a lo d)"
  by (rule bridge_terminate)

lemma accept_no_continuation:
  "\<lbrakk>is_trace (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace); enc_pre C \<pi> (\<sigma> :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.trace); j < length \<pi>;
     cont_of (acts :: ('s, 'p :: type) TRIEL_Breach.baction list) = None\<rbrakk>
   \<Longrightarrow> handle_breach b lo s a d acts (pre \<pi> j) = SBreached d NoContinuation \<longleftrightarrow>
       Formula.sat \<sigma> v j (ObBre (time \<pi> 0) s a lo d)"
  by (rule bridge_no_continuation)

lemma accept_cure_pending:
  "\<lbrakk>is_trace (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace); enc_pre C \<pi> (\<sigma> :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.trace); j < length \<pi>;
     cont_of (acts :: ('s, 'p :: type) TRIEL_Breach.baction list) = Some (CureBy k)\<rbrakk>
   \<Longrightarrow> handle_breach b lo s a d acts (pre \<pi> j) = SBreached d (Cure Pending) \<longleftrightarrow>
       Formula.sat \<sigma> v j (ObBre (time \<pi> 0) s a lo d)
       \<and> \<not> Formula.sat \<sigma> v j (Acted (time \<pi> 0) s a (Some d) (d + k))
       \<and> \<not> Formula.sat \<sigma> v j (ObBre (time \<pi> 0) s a (Some d) (d + k))"
  by (rule bridge_cure_pending)

lemma accept_escalate_pending:
  "\<lbrakk>is_trace (\<pi> :: ('n :: type, 'v :: value_order, 's :: type, 'a :: type) TRIEL_Breach.itrace); enc_pre C \<pi> (\<sigma> :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.trace); j < length \<pi>;
     cont_of (acts :: ('s, 'p :: type) TRIEL_Breach.baction list) = Some (EscalateTo s')\<rbrakk>
   \<Longrightarrow> handle_breach b lo s a d acts (pre \<pi> j) = SBreached d (Escalated s' Pending) \<longleftrightarrow>
       Formula.sat \<sigma> v j (ObBre (time \<pi> 0) s a lo d)
       \<and> \<not> Formula.sat \<sigma> v j (Acted (time \<pi> 0) s' a (Some d) (d + (d - b)))
       \<and> \<not> Formula.sat \<sigma> v j (ObBre (time \<pi> 0) s' a (Some d) (d + (d - b)))"
  by (rule bridge_escalate_pending)


section \<open>Probes\<close>

text \<open>Facts of the AFP alone, not of the bridge: the bounds of its intervals, the
  operators that the formulas use, read from the satisfaction relation, and the entries up
  to entries 0, 1 and 2.\<close>

lemma aux_all: "Interval.left Interval.all = 0" "Interval.right Interval.all = \<infinity>"
  by (transfer, simp)+

lemma aux_interval:
  "enat l \<le> r \<Longrightarrow> Interval.left (Interval.interval l r) = l"
  "enat l \<le> r \<Longrightarrow> Interval.right (Interval.interval l r) = r"
  by (simp_all add: Interval.interval_def left.rep_eq right.rep_eq Abs_\<I>_inverse)

lemma aux_and: "Formula.sat \<sigma> v j (formula.And \<phi> \<psi>) \<longleftrightarrow> Formula.sat \<sigma> v j \<phi> \<and> Formula.sat \<sigma> v j \<psi>"
  by simp

lemma aux_neg: "Formula.sat \<sigma> v j (formula.Neg \<phi>) \<longleftrightarrow> \<not> Formula.sat \<sigma> v j \<phi>"
  by simp

lemma aux_pred:
  "Formula.sat \<sigma> v j (formula.Pred r [trm.Const x]) \<longleftrightarrow> (r, [x]) \<in> \<Gamma> \<sigma> j"
  "Formula.sat \<sigma> v j (formula.Pred r [trm.Const x, trm.Const y]) \<longleftrightarrow> (r, [x, y]) \<in> \<Gamma> \<sigma> j"
  by (simp_all add: eval_trms_def)

lemma aux_once: "Formula.sat \<sigma> v j (formula.Once Interval.all \<phi>) \<longleftrightarrow> (\<exists>k\<le>j. Formula.sat \<sigma> v k \<phi>)"
  by (simp add: aux_all)

lemma aux_once_in:
  "Formula.sat \<sigma> v j (formula.Once I \<phi>) \<longleftrightarrow>
     (\<exists>k\<le>j. (Interval.left I \<le> \<tau> \<sigma> j - \<tau> \<sigma> k \<and> enat (\<tau> \<sigma> j - \<tau> \<sigma> k) \<le> Interval.right I) \<and> Formula.sat \<sigma> v k \<phi>)"
  by simp

lemma aux_eventually:
  "Formula.sat \<sigma> v 0 (formula.Eventually I \<phi>) \<longleftrightarrow>
     (\<exists>j. (Interval.left I \<le> \<tau> \<sigma> j - \<tau> \<sigma> 0 \<and> enat (\<tau> \<sigma> j - \<tau> \<sigma> 0) \<le> Interval.right I) \<and> Formula.sat \<sigma> v j \<phi>)"
  by simp

lemma aux_prev:
  "Formula.sat \<sigma> v 0 (formula.Prev Interval.all \<phi>) \<longleftrightarrow> False"
  "Formula.sat \<sigma> v 1 (formula.Prev Interval.all \<phi>) \<longleftrightarrow> Formula.sat \<sigma> v 0 \<phi>"
  "Formula.sat \<sigma> v 2 (formula.Prev Interval.all \<phi>) \<longleftrightarrow> Formula.sat \<sigma> v 1 \<phi>"
  by (simp_all add: aux_all)

lemma aux_upto:
  "(\<exists>k\<le>(0 :: nat). P k) \<longleftrightarrow> P 0"
  "(\<exists>k\<le>(1 :: nat). P k) \<longleftrightarrow> P 0 \<or> P 1"
  "(\<exists>k\<le>(2 :: nat). P k) \<longleftrightarrow> P 0 \<or> P 1 \<or> P 2"
proof -
  have 1: "k \<le> 1 \<longleftrightarrow> k = 0 \<or> k = 1" and 2: "k \<le> 2 \<longleftrightarrow> k = 0 \<or> k = 1 \<or> k = 2" for k :: nat
    by arith+
  show "(\<exists>k\<le>(0 :: nat). P k) \<longleftrightarrow> P 0" by simp
  show "(\<exists>k\<le>(1 :: nat). P k) \<longleftrightarrow> P 0 \<or> P 1" unfolding 1 by blast
  show "(\<exists>k\<le>(2 :: nat). P k) \<longleftrightarrow> P 0 \<or> P 1 \<or> P 2" unfolding 2 by blast
qed

text \<open>What each formula says at an entry, from the lemmas of section 1 and the facts above
  alone; no lemma of the stage is used, and no proof below searches: a formula written out
  wrongly in section 1 fails here at once. Time: \<open>First\<close> holds at entry 0 only, and
  \<open>At I\<close> where the timestamp, counted from entry 0, is in \<open>I\<close>.\<close>

lemma accept_probe_First:
  "Formula.sat (\<sigma> :: (string, ('n :: type, 'v :: type, 's :: type, 'a :: type) TRIEL_MFOTL_Enc.mval) Formula.trace) v k First \<longleftrightarrow> k = 0"
  unfolding accept_def_First by (cases k) (simp_all add: aux_all)

lemma accept_probe_At:
  "Formula.sat (\<sigma> :: (string, ('n :: type, 'v :: type, 's :: type, 'a :: type) TRIEL_MFOTL_Enc.mval) Formula.trace) v j (At I) \<longleftrightarrow>
     Interval.left I \<le> \<tau> \<sigma> j - \<tau> \<sigma> 0 \<and> enat (\<tau> \<sigma> j - \<tau> \<sigma> 0) \<le> Interval.right I"
  unfolding accept_def_At aux_once_in accept_probe_First by simp

text \<open>Obligations: an action is the fact \<open>act\<close> of the entry; \<open>Acted\<close> looks for an action
  at an entry up to this one whose time is in the window; \<open>ObBre\<close> is "no such action, and
  the deadline has passed".\<close>

lemma accept_probe_Act:
  "Formula.sat (\<sigma> :: (string, ('n :: type, 'v :: type, 's :: type, 'a :: type) TRIEL_MFOTL_Enc.mval) Formula.trace) v j (Act s a) \<longleftrightarrow> (''act'', [MS s, MA a]) \<in> \<Gamma> \<sigma> j"
  unfolding accept_def_Act by (rule aux_pred(2))

lemma accept_probe_Acted:
  "Formula.sat (\<sigma> :: (string, ('n :: type, 'v :: type, 's :: type, 'a :: type) TRIEL_MFOTL_Enc.mval) Formula.trace) v j (Acted \<tau>\<^sub>0 s a lo d) \<longleftrightarrow>
     (\<exists>k\<le>j. (''act'', [MS s, MA a]) \<in> \<Gamma> \<sigma> k \<and> Formula.sat \<sigma> v k (InWin \<tau>\<^sub>0 lo d))"
  unfolding accept_def_Acted aux_once aux_and accept_probe_Act by (rule refl)

lemma accept_probe_ObBre:
  "Formula.sat (\<sigma> :: (string, ('n :: type, 'v :: type, 's :: type, 'a :: type) TRIEL_MFOTL_Enc.mval) Formula.trace) v j (ObBre \<tau>\<^sub>0 s a lo d) \<longleftrightarrow>
     \<not> Formula.sat \<sigma> v j (Acted \<tau>\<^sub>0 s a lo d) \<and> Formula.sat \<sigma> v j (Passed \<tau>\<^sub>0 d)"
  unfolding accept_def_ObBre aux_and aux_neg by (rule refl)

text \<open>Prohibitions: entry 0 is never a forbidden action (the lemmas are equations, since
  they are used as rewrite rules below); a later entry is one when it is the action and the
  condition was true at the entry before it. \<open>PrBre\<close> looks for a
  forbidden action up to this entry, \<open>PrFirst\<close> holds at the first one, and \<open>Blk\<close> is the
  action after an entry where the condition was not known to be false.\<close>

lemma accept_probe_Forb:
  fixes \<sigma> :: "(string, ('n :: type, 'v :: type, 's :: type, 'a :: type) TRIEL_MFOTL_Enc.mval) Formula.trace"
  shows "Formula.sat \<sigma> v 0 (Forb s a c) \<longleftrightarrow> False"
    and "Formula.sat \<sigma> v 1 (Forb s a c) \<longleftrightarrow> (''act'', [MS s, MA a]) \<in> \<Gamma> \<sigma> 1 \<and> Formula.sat \<sigma> v 0 (Pc c)"
    and "Formula.sat \<sigma> v 2 (Forb s a c) \<longleftrightarrow> (''act'', [MS s, MA a]) \<in> \<Gamma> \<sigma> 2 \<and> Formula.sat \<sigma> v 1 (Pc c)"
  unfolding accept_def_Forb aux_and aux_prev accept_probe_Act by simp_all

lemma accept_probe_PrBre:
  "Formula.sat (\<sigma> :: (string, ('n :: type, 'v :: type, 's :: type, 'a :: type) TRIEL_MFOTL_Enc.mval) Formula.trace) v j (PrBre s a c) \<longleftrightarrow> (\<exists>k\<le>j. Formula.sat \<sigma> v k (Forb s a c))"
  unfolding accept_def_PrBre aux_once by (rule refl)

lemma accept_probe_PrFirst:
  fixes \<sigma> :: "(string, ('n :: type, 'v :: type, 's :: type, 'a :: type) TRIEL_MFOTL_Enc.mval) Formula.trace"
  shows "Formula.sat \<sigma> v 1 (PrFirst s a c) \<longleftrightarrow> Formula.sat \<sigma> v 1 (Forb s a c) \<and> \<not> Formula.sat \<sigma> v 0 (PrBre s a c)"
    and "Formula.sat \<sigma> v 2 (PrFirst s a c) \<longleftrightarrow> Formula.sat \<sigma> v 2 (Forb s a c) \<and> \<not> Formula.sat \<sigma> v 1 (PrBre s a c)"
  unfolding accept_def_PrFirst aux_and aux_neg aux_prev by (rule refl)+

lemma accept_probe_Blk:
  "Formula.sat (\<sigma> :: (string, ('n :: type, 'v :: type, 's :: type, 'a :: type) TRIEL_MFOTL_Enc.mval) Formula.trace) v 1 (Blk s a c) \<longleftrightarrow>
     (''act'', [MS s, MA a]) \<in> \<Gamma> \<sigma> 1 \<and> \<not> Formula.sat \<sigma> v 0 (Nc c)"
  unfolding accept_def_Blk aux_and aux_neg aux_prev accept_probe_Act by (rule refl)

text \<open>A fresh factor: data for \<open>x\<close> arrived at an entry at most \<open>m\<close> time units before this
  one. The formula of bounded future at entry 0: an action at an entry at most \<open>n\<close> time
  units after it.\<close>

lemma accept_probe_Fresh:
  "Formula.sat (\<sigma> :: (string, ('n :: type, 'v :: type, 's :: type, 'a :: type) TRIEL_MFOTL_Enc.mval) Formula.trace) v j (Fresh m x) \<longleftrightarrow>
     (\<exists>k\<le>j. (Interval.left (Interval.interval 0 (enat (nat m))) \<le> \<tau> \<sigma> j - \<tau> \<sigma> k
            \<and> enat (\<tau> \<sigma> j - \<tau> \<sigma> k) \<le> Interval.right (Interval.interval 0 (enat (nat m))))
          \<and> (''arr'', [MN x]) \<in> \<Gamma> \<sigma> k)"
  unfolding accept_def_Fresh aux_once_in aux_pred by (rule refl)

lemma accept_probe_ObFut:
  "Formula.sat (\<sigma> :: (string, ('n :: type, 'v :: type, 's :: type, 'a :: type) TRIEL_MFOTL_Enc.mval) Formula.trace) v 0 (ObFut n s a) \<longleftrightarrow>
     (\<exists>j. (Interval.left (Interval.interval 0 (enat n)) \<le> \<tau> \<sigma> j - \<tau> \<sigma> 0
          \<and> enat (\<tau> \<sigma> j - \<tau> \<sigma> 0) \<le> Interval.right (Interval.interval 0 (enat n)))
        \<and> (''act'', [MS s, MA a]) \<in> \<Gamma> \<sigma> j)"
  unfolding accept_def_ObFut aux_eventually accept_probe_Act by (rule refl)

text \<open>The formulas of a window with the activation time 0 and the deadline 5: the window
  is \<open>[0, 5]\<close> and "passed" is \<open>[6, \<infinity>)\<close>; with FROM 3 (the lower bound \<open>Some 2\<close> of the
  core) the window is \<open>[3, 5]\<close>; a window that starts after its deadline and a deadline
  before the activation give no interval.\<close>

lemma accept_probe_window:
  "(InWin 0 None 5 :: (string, ('n :: type, 'v :: type, 's :: type, 'a :: type) TRIEL_MFOTL_Enc.mval) Formula.formula) = At (Interval.interval 0 (enat 5))"
  "(Passed 0 5 :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.formula) = At (Interval.interval 6 \<infinity>)"
  "(InWin 0 (Some 2) 5 :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.formula) = At (Interval.interval 3 (enat 5))"
  "(InWin 0 (Some 7) 5 :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.formula) = formula.FF"
  "(InWin 0 None (- 1) :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.formula) = formula.FF"
  "(Passed 0 (- 1) :: (string, ('n, 'v, 's, 'a) TRIEL_MFOTL_Enc.mval) Formula.formula) = formula.TT"
  unfolding accept_def_InWin accept_def_Passed accept_def_rel_lo by simp_all

text \<open>Concrete entries. The activation entry is entry 0, at time 0, and an action \<open>a\<close> of
  \<open>s\<close> is at entry 1. With the deadline 5, an action at time 5 fulfils the obligation, and
  it is not breached.\<close>

lemma accept_probe_at_deadline:
  fixes \<sigma> :: "(string, ('n :: type, 'v :: type, 's :: type, 'a :: type) TRIEL_MFOTL_Enc.mval) Formula.trace"
  assumes "\<tau> \<sigma> 0 = 0" and "\<tau> \<sigma> 1 = 5"
    and "\<Gamma> \<sigma> 0 = {}" and "\<Gamma> \<sigma> 1 = {(''act'', [MS s, MA a])}"
  shows "Formula.sat \<sigma> v 1 (Acted 0 s a None 5)" and "\<not> Formula.sat \<sigma> v 1 (ObBre 0 s a None 5)"
proof -
  have i: "enat 0 \<le> enat 5" by simp
  show f: "Formula.sat \<sigma> v 1 (Acted 0 s a None 5)"
    unfolding accept_probe_Acted accept_probe_window accept_probe_At aux_upto
    using assms aux_interval[OF i] by simp
  show "\<not> Formula.sat \<sigma> v 1 (ObBre 0 s a None 5)"
    unfolding accept_probe_ObBre using f by simp
qed

text \<open>The same action at time 6 does not fulfil it, and the obligation is breached.\<close>

lemma accept_probe_after_deadline:
  fixes \<sigma> :: "(string, ('n :: type, 'v :: type, 's :: type, 'a :: type) TRIEL_MFOTL_Enc.mval) Formula.trace"
  assumes "\<tau> \<sigma> 0 = 0" and "\<tau> \<sigma> 1 = 6"
    and "\<Gamma> \<sigma> 0 = {}" and "\<Gamma> \<sigma> 1 = {(''act'', [MS s, MA a])}"
  shows "\<not> Formula.sat \<sigma> v 1 (Acted 0 s a None 5)" and "Formula.sat \<sigma> v 1 (ObBre 0 s a None 5)"
proof -
  have i: "enat 0 \<le> enat 5" and j: "enat 6 \<le> \<infinity>" by simp_all
  show n: "\<not> Formula.sat \<sigma> v 1 (Acted 0 s a None 5)"
    unfolding accept_probe_Acted accept_probe_window accept_probe_At aux_upto
    using assms aux_interval[OF i] by simp
  show "Formula.sat \<sigma> v 1 (ObBre 0 s a None 5)"
    unfolding accept_probe_ObBre accept_probe_window accept_probe_At
    using n assms aux_interval[OF j] by simp
qed

text \<open>An action in time, at time 3, and then an entry after the deadline, at time 7: the
  obligation stays fulfilled and is not breached.\<close>

lemma accept_probe_fulfilled_stays:
  fixes \<sigma> :: "(string, ('n :: type, 'v :: type, 's :: type, 'a :: type) TRIEL_MFOTL_Enc.mval) Formula.trace"
  assumes "\<tau> \<sigma> 0 = 0" and "\<tau> \<sigma> 1 = 3" and "\<tau> \<sigma> 2 = 7"
    and "\<Gamma> \<sigma> 0 = {}" and "\<Gamma> \<sigma> 1 = {(''act'', [MS s, MA a])}" and "\<Gamma> \<sigma> 2 = {}"
  shows "Formula.sat \<sigma> v 2 (Acted 0 s a None 5)" and "\<not> Formula.sat \<sigma> v 2 (ObBre 0 s a None 5)"
proof -
  have i: "enat 0 \<le> enat 5" by simp
  show f: "Formula.sat \<sigma> v 2 (Acted 0 s a None 5)"
    unfolding accept_probe_Acted accept_probe_window accept_probe_At aux_upto
    using assms aux_interval[OF i] by simp
  show "\<not> Formula.sat \<sigma> v 2 (ObBre 0 s a None 5)"
    unfolding accept_probe_ObBre using f by simp
qed

text \<open>An entry at time 5 without the action leaves the obligation open: neither formula
  holds. A breach needs an entry strictly after the deadline.\<close>

lemma accept_probe_open_at_deadline:
  fixes \<sigma> :: "(string, ('n :: type, 'v :: type, 's :: type, 'a :: type) TRIEL_MFOTL_Enc.mval) Formula.trace"
  assumes "\<tau> \<sigma> 0 = 0" and "\<tau> \<sigma> 1 = 5" and "\<Gamma> \<sigma> 0 = {}" and "\<Gamma> \<sigma> 1 = {}"
  shows "\<not> Formula.sat \<sigma> v 1 (Acted 0 s a None 5)" and "\<not> Formula.sat \<sigma> v 1 (ObBre 0 s a None 5)"
proof -
  have i: "enat 0 \<le> enat 5" and j: "enat 6 \<le> \<infinity>" by simp_all
  show "\<not> Formula.sat \<sigma> v 1 (Acted 0 s a None 5)"
    unfolding accept_probe_Acted accept_probe_window accept_probe_At aux_upto
    using assms aux_interval[OF i] by simp
  show "\<not> Formula.sat \<sigma> v 1 (ObBre 0 s a None 5)"
    unfolding accept_probe_ObBre accept_probe_window accept_probe_At
    using assms aux_interval[OF j] by simp
qed

text \<open>FROM is inclusive. With FROM 3, the lower bound \<open>Some 2\<close> of the core, an action at
  time 3 fulfils the obligation and an action at time 2 does not.\<close>

lemma accept_probe_from:
  fixes \<sigma> :: "(string, ('n :: type, 'v :: type, 's :: type, 'a :: type) TRIEL_MFOTL_Enc.mval) Formula.trace"
  assumes "\<tau> \<sigma> 0 = 0" and "\<Gamma> \<sigma> 0 = {}" and "\<Gamma> \<sigma> 1 = {(''act'', [MS s, MA a])}"
  shows "\<tau> \<sigma> 1 = 3 \<Longrightarrow> Formula.sat \<sigma> v 1 (Acted 0 s a (Some 2) 5)"
    and "\<tau> \<sigma> 1 = 2 \<Longrightarrow> \<not> Formula.sat \<sigma> v 1 (Acted 0 s a (Some 2) 5)"
proof -
  have i: "enat 3 \<le> enat 5" by simp
  show "Formula.sat \<sigma> v 1 (Acted 0 s a (Some 2) 5)" if "\<tau> \<sigma> 1 = 3"
    unfolding accept_probe_Acted accept_probe_window accept_probe_At aux_upto
    using assms that aux_interval[OF i] by simp
  show "\<not> Formula.sat \<sigma> v 1 (Acted 0 s a (Some 2) 5)" if "\<tau> \<sigma> 1 = 2"
    unfolding accept_probe_Acted accept_probe_window accept_probe_At aux_upto
    using assms that aux_interval[OF i] by simp
qed

text \<open>A prohibition reads its condition at the entry before the action. The condition
  PRESENT(x) is true at entry 0 and the action is at entry 1: the prohibition is breached,
  and entry 1 is the first forbidden action. If \<open>x\<close> gets its value only at the entry of
  the action, there is no breach.\<close>

lemma accept_probe_condition_before:
  fixes \<sigma> :: "(string, ('n :: type, 'v :: type, 's :: type, 'a :: type) TRIEL_MFOTL_Enc.mval) Formula.trace"
  assumes "\<Gamma> \<sigma> 0 = {(''val'', [MN x, MV u])}" and "\<Gamma> \<sigma> 1 = {(''act'', [MS s, MA a])}"
  shows "Formula.sat \<sigma> v 1 (PrBre s a (EPresent x))" and "Formula.sat \<sigma> v 1 (PrFirst s a (EPresent x))"
proof -
  show "Formula.sat \<sigma> v 1 (PrBre s a (EPresent x))"
    unfolding accept_probe_PrBre aux_upto accept_probe_Forb
    using assms by (simp add: eval_trms_def)
  show "Formula.sat \<sigma> v 1 (PrFirst s a (EPresent x))"
    unfolding accept_probe_PrFirst accept_probe_PrBre aux_upto accept_probe_Forb
    using assms by (simp add: eval_trms_def)
qed

lemma accept_probe_condition_late:
  fixes \<sigma> :: "(string, ('n :: type, 'v :: type, 's :: type, 'a :: type) TRIEL_MFOTL_Enc.mval) Formula.trace"
  assumes "\<Gamma> \<sigma> 0 = {}" and "\<Gamma> \<sigma> 1 = {(''act'', [MS s, MA a]), (''val'', [MN x, MV u])}"
  shows "\<not> Formula.sat \<sigma> v 1 (PrBre s a (EPresent x))"
  unfolding accept_probe_PrBre aux_upto accept_probe_Forb
  using assms by (simp add: eval_trms_def)

text \<open>Two forbidden actions, at entries 1 and 2: the second one is not the first, so the
  time of the breach is not read at entry 2.\<close>

lemma accept_probe_first_only:
  fixes \<sigma> :: "(string, ('n :: type, 'v :: type, 's :: type, 'a :: type) TRIEL_MFOTL_Enc.mval) Formula.trace"
  assumes "\<Gamma> \<sigma> 0 = {(''val'', [MN x, MV u])}"
    and "\<Gamma> \<sigma> 1 = {(''act'', [MS s, MA a]), (''val'', [MN x, MV u])}"
    and "\<Gamma> \<sigma> 2 = {(''act'', [MS s, MA a])}"
  shows "\<not> Formula.sat \<sigma> v 2 (PrFirst s a (EPresent x))"
  unfolding accept_probe_PrFirst accept_probe_PrBre aux_upto accept_probe_Forb
  using assms by (simp add: eval_trms_def)

text \<open>An undefined condition blocks and is not a breach. The condition \<open>x < u\<close> has no
  value at entry 0, where \<open>x\<close> is absent: the monitor blocks the action of entry 1, and the
  prohibition is not breached. A condition known to be false does not block.\<close>

lemma accept_probe_undefined_blocks:
  fixes \<sigma> :: "(string, ('n :: type, 'v :: type, 's :: type, 'a :: type) TRIEL_MFOTL_Enc.mval) Formula.trace"
  assumes "\<Gamma> \<sigma> 0 = {}" and "\<Gamma> \<sigma> 1 = {(''act'', [MS s, MA a])}"
  shows "Formula.sat \<sigma> v 1 (Blk s a (ELt (VName x) (VConst u)))"
    and "\<not> Formula.sat \<sigma> v 1 (PrBre s a (ELt (VName x) (VConst u)))"
proof -
  show "Formula.sat \<sigma> v 1 (Blk s a (ELt (VName x) (VConst u)))"
    unfolding accept_probe_Blk using assms by (simp add: eval_trms_def)
  show "\<not> Formula.sat \<sigma> v 1 (PrBre s a (ELt (VName x) (VConst u)))"
    unfolding accept_probe_PrBre aux_upto accept_probe_Forb
    using assms by (simp add: eval_trms_def)
qed

lemma accept_probe_false_allows:
  fixes \<sigma> :: "(string, ('n :: type, 'v :: type, 's :: type, 'a :: type) TRIEL_MFOTL_Enc.mval) Formula.trace"
  assumes "\<Gamma> \<sigma> 0 = {(''val'', [MN x, MV u])}" and "\<Gamma> \<sigma> 1 = {(''act'', [MS s, MA a])}"
  shows "\<not> Formula.sat \<sigma> v 1 (Blk s a (ENot (EPresent x)))"
  unfolding accept_probe_Blk using assms by (simp add: eval_trms_def)

text \<open>MAX_AGE: data that arrived at time 0 are fresh at time 3 for the maximum age 3 and
  stale for the maximum age 2.\<close>

lemma accept_probe_age:
  fixes \<sigma> :: "(string, ('n :: type, 'v :: type, 's :: type, 'a :: type) TRIEL_MFOTL_Enc.mval) Formula.trace"
  assumes "\<tau> \<sigma> 0 = 0" and "\<tau> \<sigma> 1 = 3" and "\<Gamma> \<sigma> 0 = {(''arr'', [MN x])}" and "\<Gamma> \<sigma> 1 = {}"
  shows "Formula.sat \<sigma> v 1 (Fresh 3 x)" and "\<not> Formula.sat \<sigma> v 1 (Fresh 2 x)"
proof -
  have i3: "enat 0 \<le> enat 3" and i2: "enat 0 \<le> enat 2" by simp_all
  show "Formula.sat \<sigma> v 1 (Fresh 3 x)"
    unfolding accept_probe_Fresh aux_upto using assms aux_interval[OF i3] by simp
  show "\<not> Formula.sat \<sigma> v 1 (Fresh 2 x)"
    unfolding accept_probe_Fresh aux_upto using assms aux_interval[OF i2] by simp
qed

text \<open>The formula of bounded future at entry 0: the only action of the trace is at entry 1,
  at time 5. "Within 5" holds and "within 4" does not.\<close>

lemma accept_probe_future:
  fixes \<sigma> :: "(string, ('n :: type, 'v :: type, 's :: type, 'a :: type) TRIEL_MFOTL_Enc.mval) Formula.trace"
  assumes "\<tau> \<sigma> 0 = 0" and "\<tau> \<sigma> 1 = 5"
    and "\<Gamma> \<sigma> 1 = {(''act'', [MS s, MA a])}" and "\<And>i. i \<noteq> 1 \<Longrightarrow> \<Gamma> \<sigma> i = {}"
  shows "Formula.sat \<sigma> v 0 (ObFut 5 s a)" and "\<not> Formula.sat \<sigma> v 0 (ObFut 4 s a)"
proof -
  have i5: "enat 0 \<le> enat 5" and i4: "enat 0 \<le> enat 4" by simp_all
  show "Formula.sat \<sigma> v 0 (ObFut 5 s a)"
    unfolding accept_probe_ObFut
    using assms(1-3) aux_interval[OF i5] by (intro exI[of _ 1]) simp
  show "\<not> Formula.sat \<sigma> v 0 (ObFut 4 s a)"
    unfolding accept_probe_ObFut
  proof (intro notI, elim exE conjE)
    fix j
    assume b: "enat (\<tau> \<sigma> j - \<tau> \<sigma> 0) \<le> Interval.right (Interval.interval 0 (enat 4))"
      and m: "(''act'', [MS s, MA a]) \<in> \<Gamma> \<sigma> j"
    have "j = 1" using m assms(4)[of j] by (cases "j = 1") simp_all
    with b assms(1,2) aux_interval(2)[OF i4] show False by simp
  qed
qed


section \<open>Constants and oracles\<close>

ML \<open>
  (* The accepted lemmas, each with the constants it is about. *)
  val H0 = ["TRIEL_Trace.is_trace", "TRIEL_MFOTL_Enc.enc_pre", "TRIEL_Trace.pre", "Formula.sat"]
  val H = H0 @ ["TRIEL_Breach.time"]
  val P = ["Formula.sat", "Trace.\<Gamma>"]
  fun F c = "Formula.formula." ^ c
  fun T c = "TRIEL_MFOTL_Time." ^ c
  fun N c = "TRIEL_MFOTL_Norm." ^ c
  fun B c = "TRIEL_Breach." ^ c
  val spec =
    [(* (1) the formulas *)
     ("accept_def_First", [T "First", F "Neg", F "Prev", F "TT", "Interval.all"]),
     ("accept_def_At", [T "At", T "First", F "Once"]),
     ("accept_def_rel_lo", [T "rel_lo"]),
     ("accept_def_InWin", [T "InWin", T "rel_lo", T "At", F "FF", "Interval.interval"]),
     ("accept_def_AfterLo", [T "AfterLo", T "rel_lo", T "At", "Interval.interval"]),
     ("accept_def_Passed", [T "Passed", T "At", F "TT", "Interval.interval"]),
     ("accept_def_Act", [N "Act", F "Pred", "Formula.trm.Const",
        "TRIEL_MFOTL_Enc.mval.MS", "TRIEL_MFOTL_Enc.mval.MA"]),
     ("accept_def_Acted", [N "Acted", N "Act", T "InWin", F "Once", F "And", "Interval.all"]),
     ("accept_def_ObBre", [N "ObBre", N "Acted", T "Passed", F "And", F "Neg"]),
     ("accept_def_ActedN", [N "ActedN", N "Act", T "AfterLo", F "Once", F "And", "Interval.all"]),
     ("accept_def_Forb", [N "Forb", N "Act", "TRIEL_MFOTL_Cond.Pc", F "And", F "Prev", "Interval.all"]),
     ("accept_def_PrBre", [N "PrBre", N "Forb", F "Once", "Interval.all"]),
     ("accept_def_PrFirst", [N "PrFirst", N "Forb", N "PrBre", F "And", F "Neg", F "Prev", "Interval.all"]),
     ("accept_def_Blk", [N "Blk", N "Act", "TRIEL_MFOTL_Cond.Nc", F "And", F "Neg", F "Prev", "Interval.all"]),
     ("accept_def_Fresh", [N "Fresh", F "Once", F "Pred", "Formula.trm.Const",
        "TRIEL_MFOTL_Enc.mval.MN", "Interval.interval"]),
     ("accept_def_ElseIn", [N "ElseIn", N "Acted", T "Passed", F "And", F "Neg"]),
     ("accept_def_ObFut", ["TRIEL_MFOTL_Future.ObFut", N "Act", F "Eventually", "Interval.interval"]),
     (* (2) the theorems *)
     ("accept_window_fulfilled", H @ [B "window", B "verdict.Fulfilled", N "Acted"]),
     ("accept_window_breached", H @ [B "window", B "verdict.Breached", N "ObBre"]),
     ("accept_window_pending", H @ [B "window", B "verdict.Pending", N "Acted", N "ObBre"]),
     ("accept_ob_no_deadline", H @ [B "ob_verdict", B "verdict.Fulfilled", B "verdict.Pending", N "ActedN"]),
     ("accept_pr_breached", H0 @ [B "pr_verdict", B "verdict.Breached", N "PrBre", "TRIEL_MFOTL_Cond.econsts"]),
     ("accept_pr_pending", H0 @ [B "pr_verdict", B "verdict.Pending", N "PrBre", "TRIEL_MFOTL_Cond.econsts"]),
     ("accept_pr_time", H @ [B "pr_verdict", B "verdict.Breached", N "PrFirst", "TRIEL_MFOTL_Cond.econsts"]),
     ("accept_blocked_action", ["TRIEL_Trace.is_trace", "TRIEL_MFOTL_Enc.enc_pre", "Formula.sat",
        B "blocked_action", N "Blk", "TRIEL_MFOTL_Cond.econsts"]),
     ("accept_may", H0 @ [B "may_verdict", B "verdict.Fulfilled", N "PrBre", "TRIEL_MFOTL_Cond.econsts"]),
     ("accept_fresh", ["TRIEL_Trace.is_trace", "TRIEL_MFOTL_Enc.enc_pre", "Formula.sat",
        B "fresh", N "Fresh"]),
     ("accept_else_fulfilled", H @ [B "else_verdict", B "else_status.EFulfilled", N "Acted"]),
     ("accept_else_alt_fulfilled", H @ [B "else_verdict", B "else_status.EElse", B "verdict.Fulfilled",
        N "ElseIn", N "Acted", F "And"]),
     ("accept_else_alt_breached", H @ [B "else_verdict", B "else_status.EElse", B "verdict.Breached",
        N "ElseIn", N "ObBre", F "And"]),
     ("accept_else_pending", H @ [B "else_verdict", B "else_status.EPending", N "Acted", T "Passed"]),
     ("accept_cure_fulfilled", H @ [B "handle_breach", B "cont_of", B "baction.CureBy", B "status.SBreached",
        B "continuation.Cure", B "verdict.Fulfilled", N "ObBre", N "Acted", F "And"]),
     ("accept_cure_breached", H @ [B "handle_breach", B "cont_of", B "baction.CureBy", B "status.SBreached",
        B "continuation.Cure", B "verdict.Breached", N "ObBre", F "And"]),
     ("accept_cure_base_fulfilled", H @ [B "handle_breach", B "cont_of", B "baction.CureBy",
        B "status.SFulfilled", N "Acted"]),
     ("accept_escalate_fulfilled", H @ [B "handle_breach", B "cont_of", B "baction.EscalateTo",
        B "status.SBreached", B "continuation.Escalated", B "verdict.Fulfilled", N "ObBre", N "Acted", F "And"]),
     ("accept_escalate_breached", H @ [B "handle_breach", B "cont_of", B "baction.EscalateTo",
        B "status.SBreached", B "continuation.Escalated", B "verdict.Breached", N "ObBre", F "And"]),
     ("accept_future_fulfilled", ["TRIEL_Trace.is_trace", "TRIEL_MFOTL_Enc.enc_pre", "TRIEL_Trace.st",
        "TRIEL_Breach.time", "Formula.sat", B "window", B "verdict.Fulfilled", "TRIEL_MFOTL_Future.ObFut"]),
     ("accept_future_breached", ["TRIEL_Trace.is_trace", "TRIEL_MFOTL_Enc.enc_pre", "TRIEL_Trace.st",
        "TRIEL_Breach.time", "Formula.sat", B "window", B "verdict.Breached", "TRIEL_MFOTL_Future.ObFut"]),
     (* (2) the remaining statuses of ELSE and ON_BREACH *)
     ("accept_else_alt_pending", H @ [B "else_verdict", B "else_status.EElse", B "verdict.Pending",
        N "ElseIn", N "Acted", N "ObBre"]),
     ("accept_else_nd_fulfilled", H @ [B "else_verdict", B "else_status.EFulfilled", N "Acted"]),
     ("accept_else_nd_alt_fulfilled", H @ [B "else_verdict", B "else_status.EElse", B "verdict.Fulfilled",
        N "ElseIn", N "ActedN", F "And"]),
     ("accept_else_nd_alt_pending", H @ [B "else_verdict", B "else_status.EElse", B "verdict.Pending",
        N "ElseIn", N "ActedN"]),
     ("accept_else_nd_pending", H @ [B "else_verdict", B "else_status.EPending", N "Acted", T "Passed"]),
     ("accept_handle_fulfilled", H @ [B "handle_breach", B "status.SFulfilled", N "Acted"]),
     ("accept_handle_pending", H @ [B "handle_breach", B "status.SPending", N "Acted", N "ObBre"]),
     ("accept_terminate", H @ [B "handle_breach", B "cont_of", B "baction.Terminate", B "status.SBreached",
        B "continuation.Terminated", N "ObBre"]),
     ("accept_no_continuation", H @ [B "handle_breach", B "cont_of", B "status.SBreached",
        B "continuation.NoContinuation", N "ObBre"]),
     ("accept_cure_pending", H @ [B "handle_breach", B "cont_of", B "baction.CureBy", B "status.SBreached",
        B "continuation.Cure", B "verdict.Pending", N "ObBre", N "Acted"]),
     ("accept_escalate_pending", H @ [B "handle_breach", B "cont_of", B "baction.EscalateTo",
        B "status.SBreached", B "continuation.Escalated", B "verdict.Pending", N "ObBre", N "Acted"]),
     (* (3) the probes: what the formulas say, and concrete entries *)
     ("accept_probe_First", ["Formula.sat", T "First"]),
     ("accept_probe_At", ["Formula.sat", T "At", "Trace.\<tau>", "Interval.left", "Interval.right"]),
     ("accept_probe_Act", P @ [N "Act", "TRIEL_MFOTL_Enc.mval.MS", "TRIEL_MFOTL_Enc.mval.MA"]),
     ("accept_probe_Acted", P @ [N "Acted", T "InWin"]),
     ("accept_probe_ObBre", ["Formula.sat", N "ObBre", N "Acted", T "Passed"]),
     ("accept_probe_Forb", P @ [N "Forb", "TRIEL_MFOTL_Cond.Pc"]),
     ("accept_probe_PrBre", ["Formula.sat", N "PrBre", N "Forb"]),
     ("accept_probe_PrFirst", ["Formula.sat", N "PrFirst", N "Forb", N "PrBre"]),
     ("accept_probe_Blk", P @ [N "Blk", "TRIEL_MFOTL_Cond.Nc"]),
     ("accept_probe_Fresh", P @ ["Trace.\<tau>", N "Fresh", "Interval.interval", "TRIEL_MFOTL_Enc.mval.MN"]),
     ("accept_probe_ObFut", P @ ["Trace.\<tau>", "TRIEL_MFOTL_Future.ObFut", "Interval.interval"]),
     ("accept_probe_window", [T "InWin", T "Passed", T "At", "Interval.interval", F "FF", F "TT"]),
     ("accept_probe_at_deadline", P @ ["Trace.\<tau>", N "Acted", N "ObBre"]),
     ("accept_probe_after_deadline", P @ ["Trace.\<tau>", N "Acted", N "ObBre"]),
     ("accept_probe_fulfilled_stays", P @ ["Trace.\<tau>", N "Acted", N "ObBre"]),
     ("accept_probe_open_at_deadline", P @ ["Trace.\<tau>", N "Acted", N "ObBre"]),
     ("accept_probe_from", P @ ["Trace.\<tau>", N "Acted"]),
     ("accept_probe_condition_before", P @ [N "PrBre", N "PrFirst", "TRIEL_Core.expr.EPresent"]),
     ("accept_probe_condition_late", P @ [N "PrBre", "TRIEL_Core.expr.EPresent"]),
     ("accept_probe_first_only", P @ [N "PrFirst", "TRIEL_Core.expr.EPresent"]),
     ("accept_probe_undefined_blocks", P @ [N "Blk", N "PrBre", "TRIEL_Core.expr.ELt"]),
     ("accept_probe_false_allows", P @ [N "Blk", "TRIEL_Core.expr.ENot", "TRIEL_Core.expr.EPresent"]),
     ("accept_probe_age", P @ ["Trace.\<tau>", N "Fresh"]),
     ("accept_probe_future", P @ ["Trace.\<tau>", "TRIEL_MFOTL_Future.ObFut"])]
  val accepted =
    map (fn (name, _) => (name, Proof_Context.get_thms @{context} ("Accept_MFOTL2." ^ name))) spec
  val n = length accepted
  val _ =
    if has_duplicates (op =) (map fst spec)
    then error "Accept_MFOTL2: a lemma is listed twice" else ()
  fun consts_of ths = fold (Term.add_const_names o Thm.prop_of) ths []

  (* (a) Every constant of a lemma is declared in the core (with HOL), in the AFP theory
     Formula (with its ancestors), or is one of the constants of the bridge: the nine of
     part 1 and the seventeen of part 2, each named with its theory. A constant that the
     bridge declares under a name of the core or of the AFP (window, pre, time, sat, ...)
     is in none of the three. An abbreviation is unfolded before this check, so the
     theories of the bridge may not declare one (step (2) of mfotl.yml). *)
  val core = @{theory TRIEL_Breach}
  val afp = @{theory Formula}
  val part1 =
    ["TRIEL_MFOTL_Enc.enc_db", "TRIEL_MFOTL_Enc.enc_pre",
     "TRIEL_MFOTL_Enc.mval.MN", "TRIEL_MFOTL_Enc.mval.MV",
     "TRIEL_MFOTL_Enc.mval.MS", "TRIEL_MFOTL_Enc.mval.MA",
     "TRIEL_MFOTL_Cond.econsts", "TRIEL_MFOTL_Cond.Pc", "TRIEL_MFOTL_Cond.Nc"]
  val part2 =
    [T "First", T "At", T "rel_lo", T "InWin", T "AfterLo", T "Passed",
     N "Act", N "Acted", N "ObBre", N "ActedN", N "Forb", N "PrBre", N "PrFirst", N "Blk",
     N "Fresh", N "ElseIn", "TRIEL_MFOTL_Future.ObFut"]
  val bridge = part1 @ part2
  fun allowed c =
    Sign.declared_const core c orelse Sign.declared_const afp c orelse member (op =) bridge c
  val bad =
    accepted
    |> maps (fn (_, ths) => consts_of ths)
    |> distinct (op =)
    |> filter_out allowed
  val _ =
    if null bad then ()
    else error ("Accept_MFOTL2: an accepted lemma uses a constant not of the core, of Formula or of the bridge: " ^ commas bad)

  (* (b) Each lemma uses the constants of the core, of the AFP and of the bridge it is
     about, and each constant of part 2 is written out by a lemma of section 1. *)
  val missing =
    spec
    |> maps (fn (name, cs) =>
        let val have = consts_of (the (AList.lookup (op =) accepted name))
        in map (fn c => name ^ ": " ^ c) (filter_out (member (op =) have) cs) end)
  val _ =
    if null missing then ()
    else error ("Accept_MFOTL2: an accepted lemma lacks a constant it is about: " ^ commas missing)
  val unwritten =
    filter_out (fn c => exists (fn (name, cs) =>
        String.isPrefix "accept_def_" name andalso (case cs of c' :: _ => c = c' | [] => false)) spec)
      part2
  val _ =
    if null unwritten then ()
    else error ("Accept_MFOTL2: a constant of part 2 is not written out by a lemma: " ^ commas unwritten)
  val _ = writeln ("Accept_MFOTL2: constants as required in " ^ string_of_int n ^ " lemmas")

  (* (c) No accepted lemma depends on an oracle. *)
  val oracles =
    distinct (op =) (map (fn ((name, _), _) => name) (Thm_Deps.all_oracles (maps snd accepted)))
  val _ =
    if null oracles then ()
    else error ("Accept_MFOTL2: an accepted lemma depends on an oracle: " ^ commas oracles)
  val _ = writeln ("Accept_MFOTL2: " ^ string_of_int n ^ " lemmas, no oracle, constants as required")
\<close>

end
