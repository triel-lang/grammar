(*  Title:      TRIEL_Penalty.thy
    Purpose:    The amount of PENALTY e CAP c (TECHNICAL_REPORT.md sections 2.6 and 2.9):
                arithmetic on numbers with +, - and *, the state in which the amount is
                computed (the state in which the breach occurs), the cap, and the
                informational actions reported after a breach.
    SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause
*)

theory TRIEL_Penalty
  imports TRIEL_Breach TRIEL_Numbers
begin

section \<open>Amount expressions\<close>

text \<open>The amount of a penalty is built from value expressions (constants, names and
  DEFAULT) with \<open>+\<close>, \<open>-\<close>, \<open>*\<close> and negation. Division is not admitted: the Decimals are
  not closed under it (\<open>not_decimal_third\<close>). The function \<open>num\<close> reads a value as a number,
  and is \<open>None\<close> on a value that is not a number. As every arithmetic operation in
  section 2.9, an amount is undefined if an operand is.\<close>

datatype ('n, 'v) pexp =
    PVal "('n, 'v) vexp"
  | PAdd "('n, 'v) pexp" "('n, 'v) pexp"
  | PSub "('n, 'v) pexp" "('n, 'v) pexp"
  | PMul "('n, 'v) pexp" "('n, 'v) pexp"
  | PNeg "('n, 'v) pexp"

fun lift2 :: "(rat \<Rightarrow> rat \<Rightarrow> rat) \<Rightarrow> rat option \<Rightarrow> rat option \<Rightarrow> rat option" where
  "lift2 f (Some x) (Some y) = Some (f x y)"
| "lift2 f _ _ = None"

primrec evalP :: "('v \<Rightarrow> rat option) \<Rightarrow> ('n, 'v) pexp \<Rightarrow> ('n, 'v) state \<Rightarrow> rat option" where
  "evalP num (PVal a) \<sigma> = Option.bind (evalV a \<sigma>) num"
| "evalP num (PAdd p q) \<sigma> = lift2 (+) (evalP num p \<sigma>) (evalP num q \<sigma>)"
| "evalP num (PSub p q) \<sigma> = lift2 (-) (evalP num p \<sigma>) (evalP num q \<sigma>)"
| "evalP num (PMul p q) \<sigma> = lift2 (*) (evalP num p \<sigma>) (evalP num q \<sigma>)"
| "evalP num (PNeg p) \<sigma> = map_option uminus (evalP num p \<sigma>)"

lemma lift2_None: "lift2 f x y = None \<longleftrightarrow> x = None \<or> y = None"
  by (cases x; cases y) simp_all

theorem evalP_strict:
  "evalP num (PAdd p q) \<sigma> = None \<longleftrightarrow> evalP num p \<sigma> = None \<or> evalP num q \<sigma> = None"
  "evalP num (PSub p q) \<sigma> = None \<longleftrightarrow> evalP num p \<sigma> = None \<or> evalP num q \<sigma> = None"
  "evalP num (PMul p q) \<sigma> = None \<longleftrightarrow> evalP num p \<sigma> = None \<or> evalP num q \<sigma> = None"
  "evalP num (PNeg p) \<sigma> = None \<longleftrightarrow> evalP num p \<sigma> = None"
  by (simp_all add: lift2_None)

primrec pdefault_free :: "('n, 'v) pexp \<Rightarrow> bool" where
  "pdefault_free (PVal a) = default_free a"
| "pdefault_free (PAdd p q) = (pdefault_free p \<and> pdefault_free q)"
| "pdefault_free (PSub p q) = (pdefault_free p \<and> pdefault_free q)"
| "pdefault_free (PMul p q) = (pdefault_free p \<and> pdefault_free q)"
| "pdefault_free (PNeg p) = pdefault_free p"

text \<open>Arithmetic without DEFAULT is monotone, like the comparisons (T2): a defined amount
  is not changed by more data.\<close>

theorem evalP_mono:
  assumes "pdefault_free e" and "\<sigma> \<sqsubseteq> \<sigma>'" and "evalP num e \<sigma> = Some q"
  shows "evalP num e \<sigma>' = Some q"
  using assms(1,3)
proof (induction e arbitrary: q)
  case (PVal a)
  then obtain v where v: "evalV a \<sigma> = Some v" "num v = Some q" by (auto split: Option.bind_splits)
  have "evalV a \<sigma> \<preceq> evalV a \<sigma>'" using PVal.prems(1) assms(2) by (simp add: evalV_mono)
  with v have "evalV a \<sigma>' = Some v" by (simp add: approx_def)
  with v show ?case by simp
next
  case (PAdd p r)
  then show ?case by (cases "evalP num p \<sigma>"; cases "evalP num r \<sigma>") auto
next
  case (PSub p r)
  then show ?case by (cases "evalP num p \<sigma>"; cases "evalP num r \<sigma>") auto
next
  case (PMul p r)
  then show ?case by (cases "evalP num p \<sigma>"; cases "evalP num r \<sigma>") auto
next
  case (PNeg p)
  then show ?case by (cases "evalP num p \<sigma>") auto
qed

text \<open>If every number a value can denote is a Decimal, so is every amount: \<open>+\<close>, \<open>-\<close> and
  \<open>*\<close> keep the Decimals.\<close>

theorem evalP_decimal:
  assumes "\<forall>v r. num v = Some r \<longrightarrow> decimal r" and "evalP num e \<sigma> = Some q"
  shows "decimal q"
  using assms(2)
proof (induction e arbitrary: q)
  case (PVal a)
  then show ?case using assms(1) by (auto split: Option.bind_splits)
next
  case (PAdd p r)
  then show ?case by (cases "evalP num p \<sigma>"; cases "evalP num r \<sigma>") (auto intro: decimal_add)
next
  case (PSub p r)
  then show ?case by (cases "evalP num p \<sigma>"; cases "evalP num r \<sigma>") (auto intro: decimal_diff)
next
  case (PMul p r)
  then show ?case by (cases "evalP num p \<sigma>"; cases "evalP num r \<sigma>") (auto intro: decimal_mult)
next
  case (PNeg p)
  then show ?case by (cases "evalP num p \<sigma>") (auto intro: decimal_uminus)
qed


section \<open>The amount of a penalty and its cap\<close>

text \<open>\<open>PENALTY e CAP c\<close> is \<open>Pen e (Some c)\<close>, and \<open>PENALTY e\<close> is \<open>Pen e None\<close>. Its amount in a
  state is undefined if \<open>e\<close> is; negative if \<open>e\<close> is negative, which violates the rule of
  section 2.9 that the amount is not negative, and is reported, not replaced by 0; and
  otherwise the value of \<open>e\<close>, or \<open>c\<close> if \<open>e\<close> exceeds the cap. The flag of \<open>PAmount\<close> records
  whether the cap was applied.\<close>

datatype ('n, 'v) pen = Pen "('n, 'v) pexp" "rat option"

datatype amount = PAmount rat bool | PUndefined | PNegative rat

fun pen_amount :: "('v \<Rightarrow> rat option) \<Rightarrow> ('n, 'v) pen \<Rightarrow> ('n, 'v) state \<Rightarrow> amount" where
  "pen_amount num (Pen e cap) \<sigma> =
     (case evalP num e \<sigma> of
        None \<Rightarrow> PUndefined
      | Some v \<Rightarrow>
          if v < 0 then PNegative v
          else (case cap of
                  None \<Rightarrow> PAmount v False
                | Some c \<Rightarrow> if c < v then PAmount c True else PAmount v False))"

theorem pen_amount_undefined: "evalP num e \<sigma> = None \<Longrightarrow> pen_amount num (Pen e cap) \<sigma> = PUndefined"
  by simp

theorem pen_amount_negative: "evalP num e \<sigma> = Some v \<Longrightarrow> v < 0 \<Longrightarrow> pen_amount num (Pen e cap) \<sigma> = PNegative v"
  by simp

theorem pen_amount_exact:
  "evalP num e \<sigma> = Some v \<Longrightarrow> 0 \<le> v \<Longrightarrow> (\<forall>c. cap = Some c \<longrightarrow> v \<le> c) \<Longrightarrow>
     pen_amount num (Pen e cap) \<sigma> = PAmount v False"
  by (cases cap) auto

theorem pen_amount_capped:
  "evalP num e \<sigma> = Some v \<Longrightarrow> c < v \<Longrightarrow> 0 \<le> c \<Longrightarrow> pen_amount num (Pen e (Some c)) \<sigma> = PAmount c True"
  by simp

text \<open>A reported amount is never negative and never exceeds the cap.\<close>

theorem pen_amount_bounds:
  assumes "pen_amount num (Pen e cap) \<sigma> = PAmount x b" and "\<forall>c. cap = Some c \<longrightarrow> 0 \<le> c"
  shows "0 \<le> x" and "\<And>c. cap = Some c \<Longrightarrow> x \<le> c"
  using assms by (auto split: option.splits if_splits)

theorem pen_amount_decimal:
  assumes "\<forall>v r. num v = Some r \<longrightarrow> decimal r" and "\<And>c. cap = Some c \<Longrightarrow> decimal c"
    and "pen_amount num (Pen e cap) \<sigma> = PAmount x b"
  shows "decimal x"
proof -
  from assms(3) obtain v where v: "evalP num e \<sigma> = Some v"
    by (cases "evalP num e \<sigma>") auto
  have "decimal v" using evalP_decimal[OF assms(1) v] .
  with v assms(2,3) show ?thesis by (auto split: option.splits if_splits)
qed

theorem pen_amount_mono:
  assumes "pdefault_free e" and "\<sigma> \<sqsubseteq> \<sigma>'" and "pen_amount num (Pen e cap) \<sigma> \<noteq> PUndefined"
  shows "pen_amount num (Pen e cap) \<sigma>' = pen_amount num (Pen e cap) \<sigma>"
proof -
  from assms(3) obtain v where "evalP num e \<sigma> = Some v" by (cases "evalP num e \<sigma>") auto
  moreover from evalP_mono[OF assms(1,2) this] have "evalP num e \<sigma>' = Some v" .
  ultimately show ?thesis by simp
qed

text \<open>With DEFAULT the amount is not monotone (decision 15): DEFAULT(x, 0) is 0 without
  \<open>x\<close> and 1 once \<open>x = 1\<close> is present.\<close>

theorem pen_default_not_mono:
  fixes x :: 'n
  defines "e \<equiv> PVal (VDefault x (VConst (0 :: rat)))"
  shows "(Map.empty :: ('n, rat) state) \<sqsubseteq> [x \<mapsto> 1]"
    and "pen_amount Some (Pen e None) Map.empty = PAmount 0 False"
    and "pen_amount Some (Pen e None) [x \<mapsto> 1] = PAmount 1 False"
  by (simp_all add: e_def info_le_def)


section \<open>The state in which a penalty is computed\<close>

text \<open>A penalty fires once, at the moment of breach, and is computed in the state in
  which the breach occurs: the state of the entry just before the entry that establishes
  the breach.
  \<^item> An obligation with deadline \<open>d\<close> is breached once the trace has an entry strictly after
    \<open>d\<close>; the first such entry is \<open>breach_entry d \<pi>\<close>, and the state before it is the last
    state not after the deadline.
  \<^item> A prohibition is breached by the first forbidden action, \<open>first_forbidden\<close>; the state
    before it is the state in which its condition is read.\<close>

definition breach_entry :: "int \<Rightarrow> ('n, 'v, 's, 'a) itrace \<Rightarrow> nat" where
  "breach_entry d \<pi> = (case find (\<lambda>j. d < time \<pi> j) [0..<length \<pi>] of Some j \<Rightarrow> j | None \<Rightarrow> length \<pi>)"

definition ob_pen_state :: "int \<Rightarrow> ('n, 'v, 's, 'a) itrace \<Rightarrow> ('n, 'v) state" where
  "ob_pen_state d \<pi> = st \<pi> (breach_entry d \<pi> - 1)"

definition first_forbidden :: "'s \<Rightarrow> 'a \<Rightarrow> ('n, 'v :: value_order) expr \<Rightarrow> ('n, 'v, 's, 'a) itrace \<Rightarrow> nat" where
  "first_forbidden s a c \<pi> =
     (case find (forbidden s a c \<pi>) [0..<length \<pi>] of Some j \<Rightarrow> j | None \<Rightarrow> length \<pi>)"

definition pr_pen_state :: "'s \<Rightarrow> 'a \<Rightarrow> ('n, 'v :: value_order) expr \<Rightarrow> ('n, 'v, 's, 'a) itrace
    \<Rightarrow> ('n, 'v) state" where
  "pr_pen_state s a c \<pi> = st \<pi> (first_forbidden s a c \<pi> - 1)"

lemma find_upt_Some_iff:
  "find P [0..<n] = Some j \<longleftrightarrow> j < n \<and> P j \<and> (\<forall>i < j. \<not> P i)"
  by (auto simp: find_Some_iff)

lemma find_upt_None_iff: "find P [0..<n] = None \<longleftrightarrow> (\<forall>j < n. \<not> P j)"
  by (auto simp: find_None_iff)

lemma breach_entry_passed:
  assumes "passed d \<pi>"
  shows "breach_entry d \<pi> < length \<pi>" and "d < time \<pi> (breach_entry d \<pi>)"
    and "\<And>i. i < breach_entry d \<pi> \<Longrightarrow> time \<pi> i \<le> d"
proof -
  have "find (\<lambda>j. d < time \<pi> j) [0..<length \<pi>] \<noteq> None"
    using assms unfolding passed_def find_upt_None_iff by auto
  then obtain j where j: "find (\<lambda>j. d < time \<pi> j) [0..<length \<pi>] = Some j" by auto
  then have b: "breach_entry d \<pi> = j" by (simp add: breach_entry_def)
  from j show "breach_entry d \<pi> < length \<pi>" and "d < time \<pi> (breach_entry d \<pi>)"
    and "\<And>i. i < breach_entry d \<pi> \<Longrightarrow> time \<pi> i \<le> d"
    unfolding b find_upt_Some_iff by (auto simp: not_less)
qed

text \<open>The penalty of an obligation is read in the last state not after the deadline,
  unless the breach is established by the activation entry itself (a deadline before
  activation), in which case it is read in the activation state.\<close>

theorem ob_pen_state_at_deadline:
  assumes "passed d \<pi>" and "0 < breach_entry d \<pi>"
  shows "ob_pen_state d \<pi> = st \<pi> (breach_entry d \<pi> - 1)" and "time \<pi> (breach_entry d \<pi> - 1) \<le> d"
    and "d < time \<pi> (breach_entry d \<pi>)"
  using breach_entry_passed[OF assms(1)] assms(2) by (simp_all add: ob_pen_state_def)

lemma breach_entry_append:
  assumes "passed d \<pi>"
  shows "breach_entry d (\<pi> @ \<rho>) = breach_entry d \<pi>"
proof -
  let ?j = "breach_entry d \<pi>"
  note b = breach_entry_passed[OF assms]
  have "find (\<lambda>j. d < time (\<pi> @ \<rho>) j) [0..<length (\<pi> @ \<rho>)] = Some ?j"
    unfolding find_upt_Some_iff using b by (auto simp: not_less)
  then show ?thesis by (simp add: breach_entry_def)
qed

text \<open>Once the obligation is breached, later entries do not change the state in which its
  penalty is computed.\<close>

theorem ob_pen_state_final:
  assumes "passed d \<pi>"
  shows "ob_pen_state d (\<pi> @ \<rho>) = ob_pen_state d \<pi>"
proof -
  have "breach_entry d \<pi> - 1 < length \<pi>"
    using breach_entry_passed(1)[OF assms] by simp
  then show ?thesis
    by (simp add: ob_pen_state_def breach_entry_append[OF assms])
qed

lemma first_forbidden_breached:
  assumes "pr_verdict s a c \<pi> \<noteq> Pending"
  shows "forbidden s a c \<pi> (first_forbidden s a c \<pi>)"
    and "\<And>i. i < first_forbidden s a c \<pi> \<Longrightarrow> \<not> forbidden s a c \<pi> i"
    and "pr_verdict s a c \<pi> = Breached (time \<pi> (first_forbidden s a c \<pi>))"
proof -
  from assms obtain j where "forbidden s a c \<pi> j" by (auto simp: pr_verdict_def split: if_splits)
  then have "find (forbidden s a c \<pi>) [0..<length \<pi>] \<noteq> None"
    using forbidden_less[of s a c \<pi> j] by (auto simp: find_upt_None_iff)
  then obtain k where k: "find (forbidden s a c \<pi>) [0..<length \<pi>] = Some k" by auto
  then have f: "first_forbidden s a c \<pi> = k" by (simp add: first_forbidden_def)
  from k have kk: "forbidden s a c \<pi> k" "\<And>i. i < k \<Longrightarrow> \<not> forbidden s a c \<pi> i"
    unfolding find_upt_Some_iff by auto
  then show "forbidden s a c \<pi> (first_forbidden s a c \<pi>)"
    and "\<And>i. i < first_forbidden s a c \<pi> \<Longrightarrow> \<not> forbidden s a c \<pi> i" by (simp_all add: f)
  have "(LEAST j. forbidden s a c \<pi> j) = k"
    by (rule Least_equality) (use kk in \<open>auto simp: not_le[symmetric]\<close>)
  with kk show "pr_verdict s a c \<pi> = Breached (time \<pi> (first_forbidden s a c \<pi>))"
    by (auto simp: pr_verdict_def f)
qed

text \<open>The penalty of a prohibition is read in the state in which its condition was true:
  the state before the forbidden action.\<close>

theorem pr_pen_state_condition:
  assumes "pr_verdict s a c \<pi> \<noteq> Pending"
  shows "eval c (pr_pen_state s a c \<pi>) = Some True"
    and "1 \<le> first_forbidden s a c \<pi>"
    and "does s a (evt (\<pi> ! first_forbidden s a c \<pi>))"
  using first_forbidden_breached(1)[OF assms] by (simp_all add: forbidden_def pr_pen_state_def)

theorem pr_pen_state_final:
  assumes "pr_verdict s a c \<pi> \<noteq> Pending"
  shows "pr_pen_state s a c (\<pi> @ \<rho>) = pr_pen_state s a c \<pi>"
proof -
  let ?k = "first_forbidden s a c \<pi>"
  have fk: "forbidden s a c \<pi> ?k" and before: "\<And>i. i < ?k \<Longrightarrow> \<not> forbidden s a c \<pi> i"
    using first_forbidden_breached[OF assms] by blast+
  have kl: "?k < length \<pi>" using fk by (rule forbidden_less)
  have "find (forbidden s a c (\<pi> @ \<rho>)) [0..<length (\<pi> @ \<rho>)] = Some ?k"
    unfolding find_upt_Some_iff using fk kl before
    by (auto simp: forbidden_append)
  then have "first_forbidden s a c (\<pi> @ \<rho>) = ?k" by (simp add: first_forbidden_def)
  with kl show ?thesis by (simp add: pr_pen_state_def)
qed


section \<open>The actions reported after a breach\<close>

text \<open>After a breach, the informational actions of the handler are reported in source
  order: NOTIFY with its subject, PENALTY with its amount in the state of the breach. The
  continuation-determining actions are reported by the status (section 2.6).\<close>

datatype 's ract = RNotify 's | RPenalty amount

fun ract_of :: "('v \<Rightarrow> rat option) \<Rightarrow> ('n, 'v) state \<Rightarrow> ('s, ('n, 'v) pen) baction \<Rightarrow> 's ract list" where
  "ract_of num \<sigma> (Notify s) = [RNotify s]"
| "ract_of num \<sigma> (Penalty p) = [RPenalty (pen_amount num p \<sigma>)]"
| "ract_of num \<sigma> _ = []"

definition report_actions ::
    "('v \<Rightarrow> rat option) \<Rightarrow> ('n, 'v) state \<Rightarrow> ('s, ('n, 'v) pen) baction list \<Rightarrow> 's ract list" where
  "report_actions num \<sigma> acts = concat (map (ract_of num \<sigma>) acts)"

lemma report_actions_informational:
  "report_actions num \<sigma> acts = report_actions num \<sigma> (filter (\<lambda>x. \<not> is_cont x) acts)"
proof (induction acts)
  case (Cons x xs)
  then show ?case by (cases x) (simp_all add: report_actions_def)
qed (simp add: report_actions_def)

text \<open>The actions reported with an obligation and with a prohibition: nothing unless it
  is breached, and then the informational actions of its handler, with the penalty
  computed in the state of the breach.\<close>

definition ob_report :: "('v \<Rightarrow> rat option) \<Rightarrow> int \<Rightarrow> 's status \<Rightarrow> ('s, ('n, 'v) pen) baction list
    \<Rightarrow> ('n, 'v, 's, 'a) itrace \<Rightarrow> 's ract list" where
  "ob_report num d sts acts \<pi> =
     (case sts of SBreached \<tau> c \<Rightarrow> report_actions num (ob_pen_state d \<pi>) acts | _ \<Rightarrow> [])"

definition pr_report :: "('v \<Rightarrow> rat option) \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> ('n, 'v :: value_order) expr
    \<Rightarrow> ('s, ('n, 'v) pen) baction list \<Rightarrow> ('n, 'v, 's, 'a) itrace \<Rightarrow> 's ract list" where
  "pr_report num s a c acts \<pi> =
     (case pr_verdict s a c \<pi> of Breached \<tau> \<Rightarrow> report_actions num (pr_pen_state s a c \<pi>) acts | _ \<Rightarrow> [])"

lemma handle_breach_breached:
  "handle_breach \<tau>\<^sub>0 lo s a d acts \<pi> = SBreached \<tau> c \<Longrightarrow> window s a lo d \<pi> = Breached d \<and> \<tau> = d"
  by (auto simp: handle_breach_def window_def split: verdict.splits if_splits)

lemma window_breached_passed: "window s a lo d \<pi> = Breached d \<Longrightarrow> passed d \<pi>"
  by (auto simp: window_def split: if_splits)

text \<open>The reported actions are final: once the norm is breached, later entries change
  neither the actions nor the amounts of its penalties.\<close>

theorem pr_report_final:
  assumes "pr_verdict s a c \<pi> \<noteq> Pending"
  shows "pr_report num s a c acts (\<pi> @ \<rho>) = pr_report num s a c acts \<pi>"
  by (simp add: pr_report_def pr_verdict_final[OF assms] pr_pen_state_final[OF assms]
      split: verdict.split)

theorem ob_report_final:
  assumes "is_trace (\<pi> @ \<rho>)" and "handle_breach \<tau>\<^sub>0 lo s a d acts \<pi> = SBreached \<tau> c"
  shows "ob_report num d (handle_breach \<tau>\<^sub>0 lo s a d acts (\<pi> @ \<rho>)) acts (\<pi> @ \<rho>)
           = ob_report num d (handle_breach \<tau>\<^sub>0 lo s a d acts \<pi>) acts \<pi>"
proof -
  from handle_breach_breached[OF assms(2)] have w: "window s a lo d \<pi> = Breached d" by simp
  have w': "window s a lo d (\<pi> @ \<rho>) = Breached d"
    using window_final[OF assms(1)] w by simp
  have "\<exists>c'. handle_breach \<tau>\<^sub>0 lo s a d acts (\<pi> @ \<rho>) = SBreached d c'"
    using w' by (simp add: handle_breach_def)
  then obtain c' where h: "handle_breach \<tau>\<^sub>0 lo s a d acts (\<pi> @ \<rho>) = SBreached d c'" by blast
  have p: "passed d \<pi>" using w by (rule window_breached_passed)
  show ?thesis
    using assms(2) h ob_pen_state_final[OF p] by (simp add: ob_report_def)
qed

end
