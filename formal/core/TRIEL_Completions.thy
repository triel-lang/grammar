(*  Title:      TRIEL_Completions.thy
    Purpose:    Completions of incomplete data: the total valuations that agree with a
                state wherever it is defined. What the fail-closed monitor of TRIEL_Breach
                allows, and a condition known to be true, stay so in every completion;
                reading an undefined condition as "skip the policy", or a comparison with
                an absent operand as false, does not; and strong Kleene evaluation is not
                complete with respect to completions.
    SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause
*)

theory TRIEL_Completions
  imports TRIEL_Breach
begin

section \<open>Completions\<close>

text \<open>A completion of a state \<open>\<sigma>\<close> is a total valuation that agrees with \<open>\<sigma>\<close> wherever
  \<open>\<sigma>\<close> is defined: one of the ways in which the data missing from \<open>\<sigma>\<close> may turn out.\<close>

definition completion :: "('n, 'v) state \<Rightarrow> ('n, 'v) state \<Rightarrow> bool" where
  "completion \<sigma> \<sigma>' \<longleftrightarrow> \<sigma> \<sqsubseteq> \<sigma>' \<and> dom \<sigma>' = UNIV"

text \<open>Every state has a completion, so the theorems below that hold for every completion
  are not vacuous.\<close>

lemma completion_exists: "\<exists>\<sigma>'. completion \<sigma> \<sigma>'"
proof
  show "completion \<sigma> ((\<lambda>_. Some undefined) ++ \<sigma>)"
    by (auto simp: completion_def info_le_def)
qed

lemma total_name: "dom \<sigma> = UNIV \<Longrightarrow> \<exists>v. \<sigma> x = Some v"
  by (metis UNIV_I domD)

lemma evalV_total: "dom \<sigma> = UNIV \<Longrightarrow> \<exists>v. evalV a \<sigma> = Some v"
  by (induction a) (auto simp: total_name split: option.splits)


section \<open>Two readings of an undefined condition\<close>

text \<open>The reading ``skip the policy if its evaluation fails'': the action is allowed unless
  the condition is known to be true, so an undefined condition allows it.\<close>

definition skip_allows :: "('n, 'v :: value_order) expr \<Rightarrow> ('n, 'v) state \<Rightarrow> bool" where
  "skip_allows c \<sigma> \<longleftrightarrow> eval c \<sigma> \<noteq> Some True"

text \<open>The reading ``absent means false'': a two-valued evaluation in which a comparison with
  an operand that has no value is false, and the connectives are the classical ones.\<close>

primrec eval_af :: "('n, 'v :: value_order) expr \<Rightarrow> ('n, 'v) state \<Rightarrow> bool" where
  "eval_af ETrue \<sigma> = True"
| "eval_af EFalse \<sigma> = False"
| "eval_af (EEq a b) \<sigma> =
     (case evalV a \<sigma> of
        None \<Rightarrow> False
      | Some u \<Rightarrow> (case evalV b \<sigma> of None \<Rightarrow> False | Some w \<Rightarrow> u = w))"
| "eval_af (ELt a b) \<sigma> =
     (case evalV a \<sigma> of
        None \<Rightarrow> False
      | Some u \<Rightarrow> (case evalV b \<sigma> of None \<Rightarrow> False | Some w \<Rightarrow> vless u w))"
| "eval_af (ELe a b) \<sigma> =
     (case evalV a \<sigma> of
        None \<Rightarrow> False
      | Some u \<Rightarrow> (case evalV b \<sigma> of None \<Rightarrow> False | Some w \<Rightarrow> vleq u w))"
| "eval_af (ENot e) \<sigma> = (\<not> eval_af e \<sigma>)"
| "eval_af (EAnd e\<^sub>1 e\<^sub>2) \<sigma> = (eval_af e\<^sub>1 \<sigma> \<and> eval_af e\<^sub>2 \<sigma>)"
| "eval_af (EOr e\<^sub>1 e\<^sub>2) \<sigma> = (eval_af e\<^sub>1 \<sigma> \<or> eval_af e\<^sub>2 \<sigma>)"
| "eval_af (EImp e\<^sub>1 e\<^sub>2) \<sigma> = (eval_af e\<^sub>1 \<sigma> \<longrightarrow> eval_af e\<^sub>2 \<sigma>)"
| "eval_af (EPresent x) \<sigma> = (x \<in> dom \<sigma>)"

text \<open>On a total valuation the two evaluations agree: there every condition is defined,
  and its value is the one of \<open>eval_af\<close>. The readings differ only on incomplete data.\<close>

theorem eval_af_total: "dom \<sigma> = UNIV \<Longrightarrow> eval c \<sigma> = Some (eval_af c \<sigma>)"
proof (induction c)
  case (EEq a b)
  then show ?case using evalV_total[of \<sigma> a] evalV_total[of \<sigma> b] by auto
next
  case (ELt a b)
  then show ?case using evalV_total[of \<sigma> a] evalV_total[of \<sigma> b] by auto
next
  case (ELe a b)
  then show ?case using evalV_total[of \<sigma> a] evalV_total[of \<sigma> b] by auto
qed simp_all

text \<open>In particular every condition, PRESENT-free or not, is defined in every completion.\<close>

corollary completion_defined: "completion \<sigma> \<sigma>' \<Longrightarrow> eval c \<sigma>' \<noteq> None"
  by (simp add: completion_def eval_af_total)


section \<open>Soundness of the monitor and of the verdict\<close>

text \<open>If the fail-closed monitor does not block, the condition is false in every completion:
  the action is allowed only when it is allowed however the missing data turn out.\<close>

theorem monitor_sound_completions:
  assumes "present_free c" and "\<not> blocks c \<sigma>" and "completion \<sigma> \<sigma>'"
  shows "eval c \<sigma>' = Some False"
proof -
  have "eval c \<sigma> = Some False" using assms(2) by (simp add: blocks_def)
  moreover have "\<sigma> \<sqsubseteq> \<sigma>'" using assms(3) by (simp add: completion_def)
  ultimately show ?thesis using T2_monotone[OF assms(1)] by blast
qed

text \<open>If the condition is true, it is true in every completion: the condition of a breach
  recorded on incomplete data holds however the missing data turn out.\<close>

theorem breach_certain_completions:
  assumes "present_free c" and "eval c \<sigma> = Some True" and "completion \<sigma> \<sigma>'"
  shows "eval c \<sigma>' = Some True"
proof -
  have "\<sigma> \<sqsubseteq> \<sigma>'" using assms(3) by (simp add: completion_def)
  then show ?thesis using T2_monotone[OF assms(1)] assms(2) by blast
qed


section \<open>The two other readings are unsound\<close>

text \<open>A comparison \<open>x = v\<close> whose operand \<open>x\<close> has no value: both readings allow the action,
  the monitor blocks it, and the completion that gives \<open>x\<close> the value \<open>v\<close> makes the
  comparison true.\<close>

lemma absent_comparison:
  fixes v :: "'v :: value_order"
  assumes "x \<notin> dom \<sigma>"
  shows "present_free (EEq (VName x) (VConst v))"
    and "eval (EEq (VName x) (VConst v)) \<sigma> = None"
    and "skip_allows (EEq (VName x) (VConst v)) \<sigma>"
    and "eval_af (EEq (VName x) (VConst v)) \<sigma> = False"
    and "blocks (EEq (VName x) (VConst v)) \<sigma>"
    and "completion \<sigma> ((\<lambda>_. Some v) ++ \<sigma>)"
    and "eval (EEq (VName x) (VConst v)) ((\<lambda>_. Some v) ++ \<sigma>) = Some True"
  using assms
  by (auto simp: skip_allows_def blocks_def completion_def info_le_def domIff map_add_def
      split: option.splits)

text \<open>The witness of the next two theorems is, like the prohibition of
  \<open>core_invoice_agent.triel\<close> when its quote is stale, a comparison one of whose operands has no
  value yet.\<close>

theorem skip_reading_unsound:
  "\<exists>(c :: ('n, 'v :: value_order) expr) \<sigma> \<sigma>'.
     present_free c \<and> skip_allows c \<sigma> \<and> blocks c \<sigma> \<and> completion \<sigma> \<sigma>' \<and> eval c \<sigma>' = Some True"
proof -
  fix x :: 'n and v :: 'v
  have "x \<notin> dom (Map.empty :: ('n, 'v) state)" by simp
  from absent_comparison[OF this, where v = v] show ?thesis by blast
qed

theorem absent_false_unsound:
  "\<exists>(c :: ('n, 'v :: value_order) expr) \<sigma> \<sigma>'.
     present_free c \<and> eval_af c \<sigma> = False \<and> blocks c \<sigma> \<and> completion \<sigma> \<sigma>' \<and> eval c \<sigma>' = Some True"
proof -
  fix x :: 'n and v :: 'v
  have "x \<notin> dom (Map.empty :: ('n, 'v) state)" by simp
  from absent_comparison[OF this, where v = v] show ?thesis by blast
qed

text \<open>The comparison of that prohibition is \<open>amount_eur > limit_eur\<close>, an ordering comparison.
  The witness above is \<open>=\<close> because the class \<open>value_order\<close> assumes nothing about \<open><\<close>; for
  an order with a pair \<open>l < a\<close>, the comparison \<open>limit < amount\<close> with the limit known and the
  amount absent behaves in the same way.\<close>

lemma stale_quote_completion:
  fixes limit amount :: 'n and l a :: "'v :: value_order"
  assumes "amount \<noteq> limit" and "vless l a"
  defines "c \<equiv> ELt (VName limit) (VName amount)"
    and "\<sigma> \<equiv> [limit \<mapsto> l]"
    and "\<sigma>' \<equiv> (\<lambda>_. Some a)(limit \<mapsto> l)"
  shows "present_free c" and "skip_allows c \<sigma>" and "eval_af c \<sigma> = False" and "blocks c \<sigma>"
    and "completion \<sigma> \<sigma>'" and "eval c \<sigma>' = Some True"
  using assms by (simp_all add: skip_allows_def blocks_def completion_def info_le_def)


section \<open>Strong Kleene evaluation is not complete\<close>

text \<open>A condition can be undefined although every completion gives it the same value:
  \<open>x = v AND NOT (x = v)\<close> with \<open>x\<close> absent is false in every completion, but strong Kleene
  evaluation does not see it, and the monitor blocks.\<close>

lemma absent_contradiction:
  fixes v :: "'v :: value_order"
  assumes "x \<notin> dom \<sigma>"
  shows "present_free (EAnd (EEq (VName x) (VConst v)) (ENot (EEq (VName x) (VConst v))))"
    and "eval (EAnd (EEq (VName x) (VConst v)) (ENot (EEq (VName x) (VConst v)))) \<sigma> = None"
    and "completion \<sigma> \<sigma>' \<Longrightarrow>
         eval (EAnd (EEq (VName x) (VConst v)) (ENot (EEq (VName x) (VConst v)))) \<sigma>' = Some False"
proof -
  show "present_free (EAnd (EEq (VName x) (VConst v)) (ENot (EEq (VName x) (VConst v))))"
    by simp
  show "eval (EAnd (EEq (VName x) (VConst v)) (ENot (EEq (VName x) (VConst v)))) \<sigma> = None"
    using assms by (simp add: domIff kand_def)
  assume completion: "completion \<sigma> \<sigma>'"
  obtain u where "\<sigma>' x = Some u"
    using completion total_name[of \<sigma>' x] by (auto simp: completion_def)
  then show "eval (EAnd (EEq (VName x) (VConst v)) (ENot (EEq (VName x) (VConst v)))) \<sigma>' = Some False"
    by simp
qed

theorem kleene_not_complete:
  "\<exists>(c :: ('n, 'v :: value_order) expr) \<sigma>.
     present_free c \<and> eval c \<sigma> = None \<and> (\<forall>\<sigma>'. completion \<sigma> \<sigma>' \<longrightarrow> eval c \<sigma>' = Some False)"
proof -
  fix x :: 'n and v :: 'v
  have "x \<notin> dom (Map.empty :: ('n, 'v) state)" by simp
  from absent_contradiction[OF this, where v = v] show ?thesis by blast
qed

end
