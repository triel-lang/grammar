(*  Title:      TRIEL_MFOTL_Cond.thy
    Purpose:    The bridge from the TRIEL core to MFOTL, part 1: a condition of the core
                as a pair of MFOTL formulas, Pc for "true" and Nc for "false", with no
                premise on the completeness of the data.
    SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause
*)

theory TRIEL_MFOTL_Cond
  imports TRIEL_MFOTL_Enc
begin

section \<open>The constants of a condition\<close>

primrec vconsts :: "('n, 'v) vexp \<Rightarrow> 'v set" where
  "vconsts (VConst u) = {u}"
| "vconsts (VName x) = {}"
| "vconsts (VDefault x a) = vconsts a"

primrec econsts :: "('n, 'v) expr \<Rightarrow> 'v set" where
  "econsts ETrue = {}"
| "econsts EFalse = {}"
| "econsts (EEq a b) = vconsts a \<union> vconsts b"
| "econsts (ELt a b) = vconsts a \<union> vconsts b"
| "econsts (ELe a b) = vconsts a \<union> vconsts b"
| "econsts (ENot e) = econsts e"
| "econsts (EAnd e\<^sub>1 e\<^sub>2) = econsts e\<^sub>1 \<union> econsts e\<^sub>2"
| "econsts (EOr e\<^sub>1 e\<^sub>2) = econsts e\<^sub>1 \<union> econsts e\<^sub>2"
| "econsts (EImp e\<^sub>1 e\<^sub>2) = econsts e\<^sub>1 \<union> econsts e\<^sub>2"
| "econsts (EPresent x) = {}"

lemma vconsts_finite: "finite (vconsts a)"
  by (induction a) simp_all

lemma econsts_finite: "finite (econsts c)"
  by (induction c) (simp_all add: vconsts_finite)


section \<open>Values\<close>

text \<open>\<open>V a y\<close> holds when the variable \<open>y\<close> is the value of \<open>a\<close> in the state. It has no
  free variable but \<open>y\<close> and binds no other variable: the test that \<open>x\<close> has no value,
  inside DEFAULT, binds \<open>y\<close> again.\<close>

primrec V :: "('n, 'v) vexp \<Rightarrow> string \<Rightarrow> (string, ('n, 'v, 's, 'a) mval) Formula.formula" where
  "V (VConst u) y = formula.Eq_Const y (MV u)"
| "V (VName x) y = formula.Pred ''val'' [trm.Const (MN x), trm.Var y]"
| "V (VDefault x a) y =
     formula.Or (formula.Pred ''val'' [trm.Const (MN x), trm.Var y])
       (formula.And (formula.Neg (formula.Exists y (formula.Pred ''val'' [trm.Const (MN x), trm.Var y])))
          (V a y))"

text \<open>A value of an expression is a value of the state or a constant of the expression.\<close>

lemma evalV_ran: "evalV a \<sigma> = Some u \<Longrightarrow> u \<in> ran \<sigma> \<union> vconsts a"
  by (induction a) (auto intro: ranI split: option.splits)

text \<open>The variable \<open>y\<close> is the value of \<open>a\<close>: in a general form, which reads the value of
  \<open>y\<close> in the valuation, and in the form with \<open>y\<close> bound to \<open>z\<close>.\<close>

lemma sat_V:
  assumes "enc_pre C \<pi> \<sigma>" and "j < length \<pi>"
  shows "Formula.sat \<sigma> v j (V a y) \<longleftrightarrow> (\<exists>u. v y = MV u \<and> evalV a (st \<pi> j) = Some u)"
proof -
  have db: "\<Gamma> \<sigma> j = enc_db C \<pi> j"
    using assms by (simp add: enc_pre_def)
  show ?thesis
    by (induction a) (auto simp: db enc_db_val eval_trms_def split: option.splits)
qed

lemma fv_V: "Formula.fv (V a y) \<subseteq> {y}"
  by (induction a) auto

lemma fv_V_sub: "y \<in> A \<Longrightarrow> Formula.fv (V a y) \<subseteq> A"
  using fv_V by blast

lemma sat_V_upd:
  assumes "enc_pre C \<pi> \<sigma>" and "j < length \<pi>"
  shows "Formula.sat \<sigma> (v(y := z)) j (V a y) \<longleftrightarrow> (\<exists>u. z = MV u \<and> evalV a (st \<pi> j) = Some u)"
  using sat_V[OF assms, of "v(y := z)" a y] by simp


section \<open>Conditions\<close>

text \<open>\<open>Pc c\<close> holds when \<open>c\<close> is true, \<open>Nc c\<close> when \<open>c\<close> is false. A comparison binds its
  two operands to the variables x1 and x2 (an equality only to x1); every formula
  \<open>Pc c\<close> and \<open>Nc c\<close> is closed, so these names are never captured. MFOTL has no
  comparison of two variables: an equality is true when one variable is the value of
  both operands, and false when both operands have a value and no variable is the value
  of both.\<close>

fun Pc :: "('n, 'v) expr \<Rightarrow> (string, ('n, 'v, 's, 'a) mval) Formula.formula"
and Nc :: "('n, 'v) expr \<Rightarrow> (string, ('n, 'v, 's, 'a) mval) Formula.formula" where
  "Pc ETrue = formula.TT"
| "Pc EFalse = formula.FF"
| "Pc (EEq a b) = formula.Exists ''x1'' (formula.And (V a ''x1'') (V b ''x1''))"
| "Pc (ELt a b) =
     formula.Exists ''x1'' (formula.Exists ''x2''
       (formula.And (formula.And (V a ''x1'') (V b ''x2''))
          (formula.Pred ''lt'' [trm.Var ''x1'', trm.Var ''x2''])))"
| "Pc (ELe a b) =
     formula.Exists ''x1'' (formula.Exists ''x2''
       (formula.And (formula.And (V a ''x1'') (V b ''x2''))
          (formula.Pred ''le'' [trm.Var ''x1'', trm.Var ''x2''])))"
| "Pc (ENot e) = Nc e"
| "Pc (EAnd e\<^sub>1 e\<^sub>2) = formula.And (Pc e\<^sub>1) (Pc e\<^sub>2)"
| "Pc (EOr e\<^sub>1 e\<^sub>2) = formula.Or (Pc e\<^sub>1) (Pc e\<^sub>2)"
| "Pc (EImp e\<^sub>1 e\<^sub>2) = formula.Or (Nc e\<^sub>1) (Pc e\<^sub>2)"
| "Pc (EPresent x) = formula.Exists ''x1'' (formula.Pred ''val'' [trm.Const (MN x), trm.Var ''x1''])"
| "Nc ETrue = formula.FF"
| "Nc EFalse = formula.TT"
| "Nc (EEq a b) =
     formula.And (formula.And (formula.Exists ''x1'' (V a ''x1'')) (formula.Exists ''x1'' (V b ''x1'')))
       (formula.Neg (formula.Exists ''x1'' (formula.And (V a ''x1'') (V b ''x1''))))"
| "Nc (ELt a b) =
     formula.Exists ''x1'' (formula.Exists ''x2''
       (formula.And (formula.And (V a ''x1'') (V b ''x2''))
          (formula.Neg (formula.Pred ''lt'' [trm.Var ''x1'', trm.Var ''x2'']))))"
| "Nc (ELe a b) =
     formula.Exists ''x1'' (formula.Exists ''x2''
       (formula.And (formula.And (V a ''x1'') (V b ''x2''))
          (formula.Neg (formula.Pred ''le'' [trm.Var ''x1'', trm.Var ''x2'']))))"
| "Nc (ENot e) = Pc e"
| "Nc (EAnd e\<^sub>1 e\<^sub>2) = formula.Or (Nc e\<^sub>1) (Nc e\<^sub>2)"
| "Nc (EOr e\<^sub>1 e\<^sub>2) = formula.And (Nc e\<^sub>1) (Nc e\<^sub>2)"
| "Nc (EImp e\<^sub>1 e\<^sub>2) = formula.And (Pc e\<^sub>1) (Nc e\<^sub>2)"
| "Nc (EPresent x) = formula.Neg (formula.Exists ''x1'' (formula.Pred ''val'' [trm.Const (MN x), trm.Var ''x1'']))"


text \<open>The formulas \<open>Pc c\<close> and \<open>Nc c\<close> are closed.\<close>

lemma fv_Pc_Nc:
  "Formula.fv (Pc c :: (string, ('n, 'v, 's, 'a) mval) Formula.formula) = {}
   \<and> Formula.fv (Nc c :: (string, ('n, 'v, 's, 'a) mval) Formula.formula) = {}"
  by (induction c) (simp_all add: Diff_eq_empty_iff Diff_subset_conv fv_V_sub)


section \<open>The condition is a pair of formulas\<close>

text \<open>The strong Kleene connectives, read for "true" and for "false".\<close>

lemma knot_Some_iff: "knot p = Some b \<longleftrightarrow> p = Some (\<not> b)"
  by (cases p) auto

lemma kand_True_iff: "kand p q = Some True \<longleftrightarrow> p = Some True \<and> q = Some True"
  by (auto simp: kand_def)

lemma kand_False_iff: "kand p q = Some False \<longleftrightarrow> p = Some False \<or> q = Some False"
  by (auto simp: kand_def)

lemma kor_True_iff: "kor p q = Some True \<longleftrightarrow> p = Some True \<or> q = Some True"
  by (auto simp: kor_def)

lemma kor_False_iff: "kor p q = Some False \<longleftrightarrow> p = Some False \<and> q = Some False"
  by (auto simp: kor_def)

lemma kimp_True_iff: "kimp p q = Some True \<longleftrightarrow> p = Some False \<or> q = Some True"
  by (auto simp: kimp_def)

lemma kimp_False_iff: "kimp p q = Some False \<longleftrightarrow> p = Some True \<and> q = Some False"
  by (auto simp: kimp_def)

text \<open>Both formulas at once, by induction on the condition.\<close>

lemma bridge_cond:
  assumes "enc_pre C \<pi> \<sigma>" and "j < length \<pi>" and "econsts c \<subseteq> C"
  shows "(eval c (st \<pi> j) = Some True \<longleftrightarrow> Formula.sat \<sigma> v j (Pc c))
       \<and> (eval c (st \<pi> j) = Some False \<longleftrightarrow> Formula.sat \<sigma> v j (Nc c))"
  using assms(3)
proof (induction c)
  case ETrue
  then show ?case by simp
next
  case EFalse
  then show ?case by simp
next
  case (EEq a b)
  show ?case
    by (auto simp: sat_V[OF assms(1,2)] split: option.splits)
next
  case (ELt a b)
  let ?s = "st \<pi> j"
  have db: "\<Gamma> \<sigma> j = enc_db C \<pi> j"
    using assms(1,2) by (simp add: enc_pre_def)
  have lt: "(''lt'', [MV u, MV w]) \<in> enc_db C \<pi> j \<longleftrightarrow> vless u w"
    if "evalV a ?s = Some u" and "evalV b ?s = Some w" for u w
  proof (rule enc_db_lt)
    show "u \<in> ran ?s \<union> C"
      using evalV_ran[OF that(1)] ELt.prems by auto
    show "w \<in> ran ?s \<union> C"
      using evalV_ran[OF that(2)] ELt.prems by auto
  qed
  have P: "Formula.sat \<sigma> v j (Pc (ELt a b))
      \<longleftrightarrow> (\<exists>u w. evalV a ?s = Some u \<and> evalV b ?s = Some w \<and> vless u w)"
    using lt by (auto simp: sat_V[OF assms(1,2)] db eval_trms_def)
  have N: "Formula.sat \<sigma> v j (Nc (ELt a b))
      \<longleftrightarrow> (\<exists>u w. evalV a ?s = Some u \<and> evalV b ?s = Some w \<and> \<not> vless u w)"
    using lt by (auto simp: sat_V[OF assms(1,2)] db eval_trms_def)
  show ?case
    unfolding P N by (auto split: option.splits)
next
  case (ELe a b)
  let ?s = "st \<pi> j"
  have db: "\<Gamma> \<sigma> j = enc_db C \<pi> j"
    using assms(1,2) by (simp add: enc_pre_def)
  have le: "(''le'', [MV u, MV w]) \<in> enc_db C \<pi> j \<longleftrightarrow> vleq u w"
    if "evalV a ?s = Some u" and "evalV b ?s = Some w" for u w
  proof (rule enc_db_le)
    show "u \<in> ran ?s \<union> C"
      using evalV_ran[OF that(1)] ELe.prems by auto
    show "w \<in> ran ?s \<union> C"
      using evalV_ran[OF that(2)] ELe.prems by auto
  qed
  have P: "Formula.sat \<sigma> v j (Pc (ELe a b))
      \<longleftrightarrow> (\<exists>u w. evalV a ?s = Some u \<and> evalV b ?s = Some w \<and> vleq u w)"
    using le by (auto simp: sat_V[OF assms(1,2)] db eval_trms_def)
  have N: "Formula.sat \<sigma> v j (Nc (ELe a b))
      \<longleftrightarrow> (\<exists>u w. evalV a ?s = Some u \<and> evalV b ?s = Some w \<and> \<not> vleq u w)"
    using le by (auto simp: sat_V[OF assms(1,2)] db eval_trms_def)
  show ?case
    unfolding P N by (auto split: option.splits)
next
  case (ENot e)
  then show ?case
    by (simp add: knot_Some_iff)
next
  case (EAnd e\<^sub>1 e\<^sub>2)
  then show ?case
    by (simp add: kand_True_iff kand_False_iff)
next
  case (EOr e\<^sub>1 e\<^sub>2)
  then show ?case
    by (simp add: kor_True_iff kor_False_iff)
next
  case (EImp e\<^sub>1 e\<^sub>2)
  then show ?case
    by (simp add: kimp_True_iff kimp_False_iff)
next
  case (EPresent x)
  have db: "\<Gamma> \<sigma> j = enc_db C \<pi> j"
    using assms(1,2) by (simp add: enc_pre_def)
  show ?case
    by (auto simp: db enc_db_val eval_trms_def)
qed

theorem bridge_true:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>" and "j < length \<pi>" and "econsts c \<subseteq> C"
  shows "eval c (st \<pi> j) = Some True \<longleftrightarrow> Formula.sat \<sigma> v j (Pc c)"
  using bridge_cond[OF assms(2-4)] by blast

theorem bridge_false:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>" and "j < length \<pi>" and "econsts c \<subseteq> C"
  shows "eval c (st \<pi> j) = Some False \<longleftrightarrow> Formula.sat \<sigma> v j (Nc c)"
  using bridge_cond[OF assms(2-4)] by blast

text \<open>Unknown blocks: a prohibition blocks unless its condition is known to be false.\<close>

theorem bridge_blocks_cond:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>" and "j < length \<pi>" and "econsts c \<subseteq> C"
  shows "blocks c (st \<pi> j) \<longleftrightarrow> \<not> Formula.sat \<sigma> v j (Nc c)"
  unfolding blocks_def using bridge_false[OF assms] by simp

text \<open>With complete data (T4) the condition is defined and is the truth of \<open>Pc c\<close>.\<close>

theorem bridge_complete_cond:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>" and "j < length \<pi>" and "econsts c \<subseteq> C"
    and "names c \<subseteq> dom (st \<pi> j)"
  shows "eval c (st \<pi> j) = Some (Formula.sat \<sigma> v j (Pc c))"
proof -
  have "eval c (st \<pi> j) = Some (ceval c (dom (st \<pi> j)) (\<lambda>x. the (st \<pi> j x)))"
    by (rule T4_classical_the[OF assms(5)])
  then obtain b where b: "eval c (st \<pi> j) = Some b"
    by blast
  then show ?thesis
    using bridge_true[OF assms(1-4), of v] by (cases b) simp_all
qed

end
