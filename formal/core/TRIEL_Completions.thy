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

section \<open>Strong Kleene evaluation is the best sound compositional evaluation\<close>

text \<open>A compositional evaluation reads the atoms as \<open>eval\<close> does and combines the values of
  the parts by four connectives on \<^typ>\<open>bool option\<close>, \<open>G = (gnot, gand, gor, gimp)\<close>.\<close>

type_synonym connectives =
  "(bool option \<Rightarrow> bool option) \<times> (bool option \<Rightarrow> bool option \<Rightarrow> bool option)
   \<times> (bool option \<Rightarrow> bool option \<Rightarrow> bool option) \<times> (bool option \<Rightarrow> bool option \<Rightarrow> bool option)"

fun gnot :: "connectives \<Rightarrow> bool option \<Rightarrow> bool option" where
  "gnot (cn, ca, co, ci) = cn"

fun gand :: "connectives \<Rightarrow> bool option \<Rightarrow> bool option \<Rightarrow> bool option" where
  "gand (cn, ca, co, ci) = ca"

fun gor :: "connectives \<Rightarrow> bool option \<Rightarrow> bool option \<Rightarrow> bool option" where
  "gor (cn, ca, co, ci) = co"

fun gimp :: "connectives \<Rightarrow> bool option \<Rightarrow> bool option \<Rightarrow> bool option" where
  "gimp (cn, ca, co, ci) = ci"

primrec evalG :: "connectives \<Rightarrow> ('n, 'v :: value_order) expr \<Rightarrow> ('n, 'v) state \<Rightarrow> bool option" where
  "evalG G ETrue \<sigma> = eval ETrue \<sigma>"
| "evalG G EFalse \<sigma> = eval EFalse \<sigma>"
| "evalG G (EEq a b) \<sigma> = eval (EEq a b) \<sigma>"
| "evalG G (ELt a b) \<sigma> = eval (ELt a b) \<sigma>"
| "evalG G (ELe a b) \<sigma> = eval (ELe a b) \<sigma>"
| "evalG G (ENot e) \<sigma> = gnot G (evalG G e \<sigma>)"
| "evalG G (EAnd e\<^sub>1 e\<^sub>2) \<sigma> = gand G (evalG G e\<^sub>1 \<sigma>) (evalG G e\<^sub>2 \<sigma>)"
| "evalG G (EOr e\<^sub>1 e\<^sub>2) \<sigma> = gor G (evalG G e\<^sub>1 \<sigma>) (evalG G e\<^sub>2 \<sigma>)"
| "evalG G (EImp e\<^sub>1 e\<^sub>2) \<sigma> = gimp G (evalG G e\<^sub>1 \<sigma>) (evalG G e\<^sub>2 \<sigma>)"
| "evalG G (EPresent x) \<sigma> = eval (EPresent x) \<sigma>"

text \<open>\<open>G\<close> is sound if, on every PRESENT-free condition, a value it gives on incomplete data is
  the value of the condition in every completion. Soundness quantifies over the conditions of
  one type of names and values, which is therefore an argument of \<open>sound_conn\<close>.\<close>

definition sound_conn :: "('n, 'v :: value_order) expr itself \<Rightarrow> connectives \<Rightarrow> bool" where
  "sound_conn T G \<longleftrightarrow>
     (\<forall>(e :: ('n, 'v) expr) \<sigma> \<sigma>'. present_free e \<longrightarrow> completion \<sigma> \<sigma>' \<longrightarrow> evalG G e \<sigma> \<preceq> eval e \<sigma>')"

lemma sound_connD:
  assumes "sound_conn TYPE(('n, 'v :: value_order) expr) G" and "present_free (e :: ('n, 'v) expr)"
    and "completion \<sigma> \<sigma>'"
  shows "evalG G e \<sigma> \<preceq> eval e \<sigma>'"
  using assms unfolding sound_conn_def by simp

lemma approx_trans: "p \<preceq> q \<Longrightarrow> q \<preceq> r \<Longrightarrow> p \<preceq> r"
  by (auto simp: approx_def)

lemma evalG_kleene: "evalG (knot, kand, kor, kimp) e \<sigma> = eval e \<sigma>"
  by (induction e) simp_all

theorem kleene_sound_conn: "sound_conn TYPE(('n, 'v :: value_order) expr) (knot, kand, kor, kimp)"
  unfolding sound_conn_def evalG_kleene by (auto simp: completion_def intro: eval_mono)

text \<open>Every truth value is the value of a PRESENT-free condition in the state \<open>\<emptyset>\<close>: true,
  false, and a comparison \<open>x = v\<close>, which is undefined there.\<close>

definition truth_witness :: "'n \<Rightarrow> 'v \<Rightarrow> bool option \<Rightarrow> ('n, 'v) expr" where
  "truth_witness x v p = (case p of None \<Rightarrow> EEq (VName x) (VConst v) | Some b \<Rightarrow> if b then ETrue else EFalse)"

lemma truth_witness_present_free: "present_free (truth_witness x v p)"
  by (simp add: truth_witness_def split: option.split)

lemma evalG_truth_witness: "evalG G (truth_witness x v p) Map.empty = p"
  by (simp add: truth_witness_def split: option.split)

text \<open>In the completion that gives every name the value \<open>u\<close>, the witness of an undefined
  value becomes \<open>u = v\<close>, and the others keep their value.\<close>

definition refine :: "bool option \<Rightarrow> bool \<Rightarrow> bool option" where
  "refine p c = (case p of None \<Rightarrow> Some c | Some b \<Rightarrow> Some b)"

lemma approx_refine: "p \<preceq> refine p c"
  by (cases p) (simp_all add: refine_def approx_iff)

lemma eval_truth_witness: "eval (truth_witness x v p) (\<lambda>_. Some u) = refine p (u = v)"
  by (simp add: truth_witness_def refine_def split: option.split)

lemma completion_const: "completion Map.empty (\<lambda>_. Some u)"
  by (simp add: completion_def info_le_def)

text \<open>With two different values, the soundness of \<open>G\<close> on these conditions makes each
  connective of \<open>G\<close> below the strong Kleene one. Where the strong Kleene connective is
  defined, its value is the value in the completion that gives \<open>x\<close> the value \<open>v\<close>; where it
  is undefined, two completions, which give \<open>x\<close> the values \<open>v\<close> and \<open>w\<close>, give the
  condition different values.\<close>

lemma sound_conn_kleene_le:
  fixes v w :: "'v :: value_order"
  assumes sound: "sound_conn TYPE(('n, 'v) expr) G" and vw: "v \<noteq> w"
  shows "gnot G p \<preceq> knot p" and "gand G p q \<preceq> kand p q"
    and "gor G p q \<preceq> kor p q" and "gimp G p q \<preceq> kimp p q"
proof -
  fix x :: 'n
  let ?W = "truth_witness x"
  have S: "evalG G e Map.empty \<preceq> eval e (\<lambda>_. Some u)" if "present_free (e :: ('n, 'v) expr)" for e u
    using sound_connD[OF sound that completion_const] .
  have N: "gnot G p \<preceq> knot (refine p (u = v))" for u
  proof -
    have "evalG G (ENot (?W v p)) Map.empty \<preceq> eval (ENot (?W v p)) (\<lambda>_. Some u)"
      by (rule S) (simp add: truth_witness_present_free)
    then show ?thesis by (simp only: evalG.simps eval.simps evalG_truth_witness eval_truth_witness)
  qed
  have A: "gand G p q \<preceq> kand (refine p (u = v1)) (refine q (u = v2))" for u v1 v2 :: 'v
  proof -
    have "evalG G (EAnd (?W v1 p) (?W v2 q)) Map.empty \<preceq> eval (EAnd (?W v1 p) (?W v2 q)) (\<lambda>_. Some u)"
      by (rule S) (simp add: truth_witness_present_free)
    then show ?thesis by (simp only: evalG.simps eval.simps evalG_truth_witness eval_truth_witness)
  qed
  have O: "gor G p q \<preceq> kor (refine p (u = v1)) (refine q (u = v2))" for u v1 v2 :: 'v
  proof -
    have "evalG G (EOr (?W v1 p) (?W v2 q)) Map.empty \<preceq> eval (EOr (?W v1 p) (?W v2 q)) (\<lambda>_. Some u)"
      by (rule S) (simp add: truth_witness_present_free)
    then show ?thesis by (simp only: evalG.simps eval.simps evalG_truth_witness eval_truth_witness)
  qed
  have I: "gimp G p q \<preceq> kimp (refine p (u = v1)) (refine q (u = v2))" for u v1 v2 :: 'v
  proof -
    have "evalG G (EImp (?W v1 p) (?W v2 q)) Map.empty \<preceq> eval (EImp (?W v1 p) (?W v2 q)) (\<lambda>_. Some u)"
      by (rule S) (simp add: truth_witness_present_free)
    then show ?thesis by (simp only: evalG.simps eval.simps evalG_truth_witness eval_truth_witness)
  qed
  have vv: "(v = v) = True" and wv: "(w = v) = False" and vw': "(v = w) = False"
    using vw by simp_all
  show "gnot G p \<preceq> knot p"
  proof (cases p)
    case None
    then show ?thesis using N[of v] N[of w] by (auto simp: vv wv refine_def approx_iff)
  next
    case (Some b)
    then show ?thesis using N[of v] by (simp add: refine_def)
  qed
  show "gand G p q \<preceq> kand p q"
  proof (cases "kand p q")
    case None
    then have "kand (refine p True) (refine q True) = Some True"
      and "kand (refine p False) (refine q False) = Some False"
      using bool_option_cases[of p] bool_option_cases[of q] by (auto simp: kand_def refine_def)
    then show ?thesis using A[of v v v] A[of w v v] None by (auto simp: vv wv approx_iff)
  next
    case (Some b)
    moreover have "kand p q \<preceq> kand (refine p (v = v)) (refine q (v = v))"
      by (rule kand_mono[OF approx_refine approx_refine])
    ultimately show ?thesis using A[of v v v] by (simp add: approx_iff)
  qed
  show "gor G p q \<preceq> kor p q"
  proof (cases "kor p q")
    case None
    then have "kor (refine p True) (refine q True) = Some True"
      and "kor (refine p False) (refine q False) = Some False"
      using bool_option_cases[of p] bool_option_cases[of q] by (auto simp: kor_def refine_def)
    then show ?thesis using O[of v v v] O[of w v v] None by (auto simp: vv wv approx_iff)
  next
    case (Some b)
    moreover have "kor p q \<preceq> kor (refine p (v = v)) (refine q (v = v))"
      by (rule kor_mono[OF approx_refine approx_refine])
    ultimately show ?thesis using O[of v v v] by (simp add: approx_iff)
  qed
  show "gimp G p q \<preceq> kimp p q"
  proof (cases "kimp p q")
    case None
    then have "kimp (refine p True) (refine q False) = Some False"
      and "kimp (refine p False) (refine q True) = Some True"
      using bool_option_cases[of p] bool_option_cases[of q] by (auto simp: kimp_def refine_def)
    then show ?thesis using I[of v v w] I[of w v w] None by (auto simp: vv wv vw' approx_iff)
  next
    case (Some b)
    moreover have "kimp p q \<preceq> kimp (refine p (v = v)) (refine q (v = v))"
      by (rule kimp_mono[OF approx_refine approx_refine])
    ultimately show ?thesis using I[of v v v] by (simp add: approx_iff)
  qed
qed

text \<open>So strong Kleene evaluation is the most defined sound compositional evaluation: on a
  PRESENT-free condition every sound one is below it. This is a classical fact about the
  logic of Kleene, proved here with respect to the completions of the data.\<close>

theorem kleene_optimal:
  assumes "sound_conn TYPE(('n, 'v :: value_order) expr) G" and "present_free (e :: ('n, 'v) expr)"
    and "\<exists>v w :: 'v. v \<noteq> w"
  shows "evalG G e \<sigma> \<preceq> eval e \<sigma>"
proof -
  from assms(3) obtain v w :: 'v where vw: "v \<noteq> w" by blast
  note le = sound_conn_kleene_le[OF assms(1) vw]
  from assms(2) show ?thesis
  proof (induction e)
    case (ENot e)
    then show ?case using le(1) knot_mono approx_trans by fastforce
  next
    case (EAnd e\<^sub>1 e\<^sub>2)
    then show ?case using le(2) kand_mono approx_trans by fastforce
  next
    case (EOr e\<^sub>1 e\<^sub>2)
    then show ?case using le(3) kor_mono approx_trans by fastforce
  next
    case (EImp e\<^sub>1 e\<^sub>2)
    then show ?case using le(4) kimp_mono approx_trans by fastforce
  qed simp_all
qed

text \<open>And no sound compositional evaluation is complete: the witness of
  \<open>kleene_not_complete\<close> is undefined for every one of them.\<close>

theorem compositional_incomplete:
  assumes "sound_conn TYPE(('n, 'v :: value_order) expr) G" and "\<exists>v w :: 'v. v \<noteq> w"
  shows "\<exists>(e :: ('n, 'v) expr) \<sigma>. present_free e \<and> (\<forall>\<sigma>'. completion \<sigma> \<sigma>' \<longrightarrow> eval e \<sigma>' = Some False)
           \<and> evalG G e \<sigma> = None"
proof -
  fix x :: 'n and v :: 'v
  let ?e = "EAnd (EEq (VName x) (VConst v)) (ENot (EEq (VName x) (VConst v))) :: ('n, 'v) expr"
  have x: "x \<notin> dom (Map.empty :: ('n, 'v) state)" by simp
  note c = absent_contradiction[OF x, where v = v]
  have "evalG G ?e Map.empty \<preceq> eval ?e Map.empty"
    by (rule kleene_optimal[OF assms(1) c(1) assms(2)])
  then have "evalG G ?e Map.empty = None" using c(2) by (simp add: approx_iff)
  with c show ?thesis by blast
qed

end
