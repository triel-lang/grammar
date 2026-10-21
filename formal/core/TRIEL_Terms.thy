(*  Title:      TRIEL_Terms.thy
    Purpose:    The term language of TECHNICAL_REPORT.md section 2.5 as an inductive
                type, its denotation in the trace semantics of TRIEL_Trace, totality of
                every term, the laws of UNLESS for terms (law 3 without side condition),
                and the conditional terms IF and WHEN.
*)

theory TRIEL_Terms
  imports TRIEL_Trace
begin

section \<open>Terms\<close>

datatype ('n, 'v, 's, 'a) tm =
    TMust 's 'a                                         \<comment> \<open>subject MUST action\<close>
  | TMay 's 'a "('n, 'v) expr"                         \<comment> \<open>subject MAY action WHEN c\<close>
  | TMustNot 's 'a "('n, 'v) expr"                     \<comment> \<open>subject MUST_NOT action WHEN c\<close>
  | TThen "('n, 'v, 's, 'a) tm" "('n, 'v, 's, 'a) tm"     \<comment> \<open>t1 THEN t2\<close>
  | TOr "('n, 'v, 's, 'a) tm" "('n, 'v, 's, 'a) tm"       \<comment> \<open>t1 OR t2\<close>
  | TUnless "('n, 'v, 's, 'a) tm" "('n, 'v) expr" "('n, 'v, 's, 'a) tm"  \<comment> \<open>t1 UNLESS c DO t2\<close>
  | TAnd "('n, 'v, 's, 'a) tm" "('n, 'v, 's, 'a) tm"      \<comment> \<open>t1 AND t2\<close>
  | TIf "('n, 'v) expr" "('n, 'v, 's, 'a) tm" "('n, 'v, 's, 'a) tm"  \<comment> \<open>IF c THEN t1 ELSE t2\<close>
  | TSkip                                              \<comment> \<open>completes at once: the missing ELSE\<close>

text \<open>\<open>IF c THEN t\<close> without ELSE is \<open>TIf c t TSkip\<close>, \<open>IF c\<^sub>1 THEN t\<^sub>1 ELIF c\<^sub>2 THEN t\<^sub>2 \<dots>\<close> is
  \<open>TIf c\<^sub>1 t\<^sub>1 (TIf c\<^sub>2 t\<^sub>2 \<dots>)\<close>, and \<open>WHEN c THEN t\<close> is \<open>IF c THEN t\<close> (TECHNICAL_REPORT.md
  section 2.5).\<close>


section \<open>Denotation\<close>

text \<open>The denotation needs \<open>interleave\<close> for AND, so it is defined in an extension of
  the locale \<open>interleaving\<close> with timestamps in a linear order. Values carry the order of
  the ordering comparisons (\<open>value_order\<close> of TRIEL_Core), since guards may compare.\<close>

locale term_semantics = interleaving interleave
  for interleave ::
    "('n, 'v :: value_order, 't :: linorder, 's, 'a) trace \<Rightarrow> ('n, 'v, 't, 's, 'a) trace
       \<Rightarrow> ('n, 'v, 't, 's, 'a) trace set"
begin

primrec den :: "('n, 'v, 's, 'a) tm \<Rightarrow> ('n, 'v, 't, 's, 'a) den" where
  "den (TMust s a) = must_d s a"
| "den (TMay s a c) = may_d s a c"
| "den (TMustNot s a c) = mustnot_d s a c"
| "den (TThen t\<^sub>1 t\<^sub>2) = then_d (den t\<^sub>1) (den t\<^sub>2)"
| "den (TOr t\<^sub>1 t\<^sub>2) = or_d (den t\<^sub>1) (den t\<^sub>2)"
| "den (TUnless t\<^sub>1 c t\<^sub>2) = unless_d (den t\<^sub>1) c (den t\<^sub>2)"
| "den (TAnd t\<^sub>1 t\<^sub>2) = and_d (den t\<^sub>1) (den t\<^sub>2)"
| "den (TIf c t\<^sub>1 t\<^sub>2) = if_d c (den t\<^sub>1) (den t\<^sub>2)"
| "den TSkip = skip_d"


section \<open>Totality\<close>

text \<open>Every term can start from any entry.\<close>

theorem den_total: "total (den t)"
proof (induction t)
  case (TMust s a)
  show ?case by (simp add: total_must)
next
  case (TMay s a c)
  show ?case by (simp add: total_may)
next
  case (TMustNot s a c)
  show ?case by (simp add: total_mustnot)
next
  case (TThen t\<^sub>1 t\<^sub>2)
  then show ?case by (simp add: total_then)
next
  case (TOr t\<^sub>1 t\<^sub>2)
  then show ?case by (simp add: total_or)
next
  case (TUnless t\<^sub>1 c t\<^sub>2)
  then show ?case by (simp add: total_unless)
next
  case (TAnd t\<^sub>1 t\<^sub>2)
  then show ?case by (simp add: total_and)
next
  case (TIf c t\<^sub>1 t\<^sub>2)
  then show ?case by (simp add: total_if)
next
  case TSkip
  show ?case by (simp add: total_skip)
qed


section \<open>Laws of UNLESS for terms\<close>

(* §2.5, law 1 *)
theorem term_unless_false: "den (TUnless t EFalse e) = den t"
  by (simp add: unless_false)

(* §2.5, law 2 *)
theorem term_unless_or:
  "den (TUnless (TOr t\<^sub>1 t\<^sub>2) c e) = den (TOr (TUnless t\<^sub>1 c e) (TUnless t\<^sub>2 c e))"
  by (simp add: unless_or)

text \<open>Law 3 holds for every term, with no side condition: the totality it needs is
  a property of all terms (\<open>den_total\<close>).\<close>

(* §2.5, law 3 *)
theorem term_unless_then:
  "den (TUnless (TThen t\<^sub>1 t\<^sub>2) c e) = den (TThen (TUnless t\<^sub>1 c e) (TUnless t\<^sub>2 c e))"
  using unless_then[OF den_total[of t\<^sub>2]] by simp

(* §2.5, law 4 *)
theorem term_unless_idem: "den (TUnless (TUnless t c e) c e) = den (TUnless t c e)"
  by (simp add: unless_idem)

text \<open>UNLESS distributes over IF: the condition is read in the state where the term is
  reached, and an interrupted trace starts there too.\<close>

theorem term_unless_if:
  "den (TUnless (TIf c t e) d h) = den (TIf c (TUnless t d h) (TUnless e d h))"
  by (simp add: unless_if)


section \<open>Conditional terms\<close>

text \<open>The condition is evaluated once, in the first state of the trace, where the term is
  reached. Only T selects the THEN branch.\<close>

theorem den_if:
  "(\<pi>, r) \<in> den (TIf c t e) \<longleftrightarrow>
     \<pi> \<noteq> [] \<and> (if eval c (sta (hd \<pi>)) = Some True then (\<pi>, r) \<in> den t else (\<pi>, r) \<in> den e)"
  by (auto simp: if_d_def)

text \<open>Without ELSE, a condition that is not T completes the term at once: the one-entry
  trace, with outcome Done, like a permission that is not exercised; and no other trace
  starts there.\<close>

theorem if_no_else_not_true:
  assumes "eval c (sta x) \<noteq> Some True"
  shows "([x], Done) \<in> den (TIf c t TSkip)"
    and "(\<pi>, r) \<in> den (TIf c t TSkip) \<Longrightarrow> hd \<pi> = x \<Longrightarrow> \<pi> = [x] \<and> r = Done"
proof -
  have "([x], Done) \<in> skip_d" unfolding skip_d_def by blast
  with assms show "([x], Done) \<in> den (TIf c t TSkip)" by (simp add: if_d_def)
next
  assume "(\<pi>, r) \<in> den (TIf c t TSkip)" and "hd \<pi> = x"
  with assms show "\<pi> = [x] \<and> r = Done" by (auto simp: if_d_def skip_d_def)
qed

text \<open>An undefined condition goes the way of F.\<close>

theorem if_undefined_else:
  assumes "eval c (sta (hd \<pi>)) = None"
  shows "(\<pi>, r) \<in> den (TIf c t e) \<longleftrightarrow> \<pi> \<noteq> [] \<and> (\<pi>, r) \<in> den e"
    and "(\<pi>, r) \<in> den (TIf c t e) \<longleftrightarrow> (\<pi>, r) \<in> den (TIf EFalse t e)"
  using assms by (auto simp: if_d_def)

text \<open>Agreement with two-valued logic (T4): when the state where the term is reached
  defines every name the condition reads, the condition is never undefined, and IF is the
  two-valued IF of the classical value of the condition.\<close>

theorem if_classical:
  assumes "\<pi> \<noteq> []" and "names c \<subseteq> dom (sta (hd \<pi>))"
    and "\<forall>x \<in> dom (sta (hd \<pi>)). sta (hd \<pi>) x = Some (\<rho> x)"
  shows "eval c (sta (hd \<pi>)) \<noteq> None"
    and "(\<pi>, r) \<in> den (TIf c t e) \<longleftrightarrow>
           (if ceval c (dom (sta (hd \<pi>))) \<rho> then (\<pi>, r) \<in> den t else (\<pi>, r) \<in> den e)"
  using T4_classical[OF assms(2,3)] assms(1) den_if[of \<pi> r c t e] by simp_all

text \<open>Stability (T2): once the condition has a definite value, more data does not change
  the branch, for a condition without PRESENT and DEFAULT. If the condition is defined in
  \<open>\<sigma>\<close>, every trace that starts in an extension of \<open>\<sigma>\<close> takes the branch chosen in \<open>\<sigma>\<close>.\<close>

theorem if_branch_stable:
  assumes "present_free c" and "eval c \<sigma> \<noteq> None" and "\<sigma> \<sqsubseteq> sta (hd \<pi>)" and "\<pi> \<noteq> []"
  shows "(\<pi>, r) \<in> den (TIf c t e) \<longleftrightarrow> (\<pi>, r) \<in> den (if eval c \<sigma> = Some True then t else e)"
proof -
  from assms(2) obtain b where b: "eval c \<sigma> = Some b" by auto
  have "eval c (sta (hd \<pi>)) = Some b" by (rule T2_monotone[OF assms(1,3) b])
  with b assms(4) den_if[of \<pi> r c t e] show ?thesis by (cases b) simp_all
qed

text \<open>The branch taken on an undefined condition is not protected in this way: data that
  arrives later can make the condition true. Every rule that picks a branch on \<open>\<bottom>\<close> has
  this property.\<close>

theorem if_undefined_branch_not_stable:
  fixes x :: 'n and v :: "'v :: value_order"
  shows "present_free (EEq (VName x) (VConst v) :: ('n, 'v) expr)"
    and "(Map.empty :: ('n, 'v) state) \<sqsubseteq> [x \<mapsto> v]"
    and "eval (EEq (VName x) (VConst v)) (Map.empty :: ('n, 'v) state) = None"
    and "eval (EEq (VName x) (VConst v)) [x \<mapsto> v] = Some True"
  by (simp_all add: info_le_def)


section \<open>Actions and violations\<close>

text \<open>An obligation is discharged by an action, and an action is the event of a later entry,
  never of the entry where the obligation is reached. So two obligations in sequence need two
  actions.\<close>

theorem must_action:
  assumes "(\<pi>, r) \<in> den (TMust s a)"
  shows "r = Done" and "\<exists>j. 1 \<le> j \<and> j < length \<pi> \<and> does s a (evt (\<pi> ! j))"
proof -
  from assms have r: "r = Done" and l: "2 \<le> length \<pi>" and d: "does s a (evt (last \<pi>))"
    by (auto simp: must_d_def)
  show "r = Done" by (rule r)
  have ne: "\<pi> \<noteq> []" using l by auto
  have j: "does s a (evt (\<pi> ! (length \<pi> - 1)))" using d last_conv_nth[OF ne] by simp
  show "\<exists>j. 1 \<le> j \<and> j < length \<pi> \<and> does s a (evt (\<pi> ! j))"
  proof (intro exI[of _ "length \<pi> - 1"] conjI)
    show "1 \<le> length \<pi> - 1" using l by linarith
    show "length \<pi> - 1 < length \<pi>" using l by linarith
  qed (rule j)
qed

theorem must_one_entry: "([x], r) \<notin> den (TMust s a)"
  by (simp add: must_d_def)

theorem must_then_must_two_actions:
  "([x\<^sub>0, x\<^sub>1], r) \<notin> den (TThen (TMust s a) (TMust s a))"
proof
  assume "([x\<^sub>0, x\<^sub>1], r) \<in> den (TThen (TMust s a) (TMust s a))"
  then consider (seq) \<pi>\<^sub>1 \<pi>\<^sub>2 where "(\<pi>\<^sub>1, Done) \<in> must_d s a" "(\<pi>\<^sub>2, r) \<in> must_d s a"
      "fusable \<pi>\<^sub>1 \<pi>\<^sub>2" "[x\<^sub>0, x\<^sub>1] = fuse \<pi>\<^sub>1 \<pi>\<^sub>2"
    | (left) "([x\<^sub>0, x\<^sub>1], r) \<in> must_d s a" "r \<noteq> Done"
    unfolding den.simps then_d_iff by blast
  then show False
  proof cases
    case seq
    have "2 \<le> length \<pi>\<^sub>1" "2 \<le> length \<pi>\<^sub>2" using seq(1,2) by (auto simp: must_d_def)
    then have "3 \<le> length (fuse \<pi>\<^sub>1 \<pi>\<^sub>2)" by (simp add: fuse_def)
    moreover have "length [x\<^sub>0, x\<^sub>1] = length (fuse \<pi>\<^sub>1 \<pi>\<^sub>2)" using seq(4) by (rule arg_cong)
    ultimately show False by simp
  next
    case left
    then show False by (simp add: must_d_def)
  qed
qed

text \<open>A prohibition is violated by its first forbidden action, also inside a composite term.\<close>

theorem mustnot_violated:
  assumes "eval c \<sigma> = Some True" and "\<tau> \<le> \<tau>'"
  shows "([(\<sigma>, \<tau>, e), (\<sigma>', \<tau>', Deontic s a p)], Violated) \<in> den (TMustNot s a c)"
  using assms by (auto simp: mustnot_d_def forbidden_def is_trace_def does_def st_def)

corollary violated_reachable: "\<exists>\<pi>. (\<pi>, Violated) \<in> den (TMustNot s a ETrue)"
  using mustnot_violated[of ETrue] by fastforce

theorem then_mustnot_violated:
  assumes c: "eval c \<sigma>\<^sub>1 = Some True" and t: "\<tau>\<^sub>0 \<le> \<tau>\<^sub>1" "\<tau>\<^sub>1 \<le> \<tau>\<^sub>2"
  shows "([(\<sigma>\<^sub>0, \<tau>\<^sub>0, e), (\<sigma>\<^sub>1, \<tau>\<^sub>1, Deontic s a p), (\<sigma>\<^sub>2, \<tau>\<^sub>2, Deontic s' a' p')], Violated)
           \<in> den (TThen (TMust s a) (TMustNot s' a' c))"
proof -
  let ?x\<^sub>1 = "(\<sigma>\<^sub>1, \<tau>\<^sub>1, Deontic s a p)"
  have m: "([(\<sigma>\<^sub>0, \<tau>\<^sub>0, e), ?x\<^sub>1], Done) \<in> must_d s a"
    using t(1) by (simp add: must_d_def is_trace_def does_def)
  have n: "([?x\<^sub>1, (\<sigma>\<^sub>2, \<tau>\<^sub>2, Deontic s' a' p')], Violated) \<in> mustnot_d s' a' c"
    using mustnot_violated[OF c t(2)] by simp
  have "fusable [(\<sigma>\<^sub>0, \<tau>\<^sub>0, e), ?x\<^sub>1] [?x\<^sub>1, (\<sigma>\<^sub>2, \<tau>\<^sub>2, Deontic s' a' p')]"
    by (simp add: fusable_def)
  with m n have "(fuse [(\<sigma>\<^sub>0, \<tau>\<^sub>0, e), ?x\<^sub>1] [?x\<^sub>1, (\<sigma>\<^sub>2, \<tau>\<^sub>2, Deontic s' a' p')], Violated)
                   \<in> then_d (must_d s a) (mustnot_d s' a' c)"
    unfolding then_d_def by blast
  then show ?thesis by (simp add: fuse_def)
qed

end

text \<open>\<open>term_semantics\<close> adds no assumptions to \<open>interleaving\<close>, so it has models
  whenever \<open>interleaving\<close> does (\<open>interleaving_satisfiable\<close>).\<close>

end
