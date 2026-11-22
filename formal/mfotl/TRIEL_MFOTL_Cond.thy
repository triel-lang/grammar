(*  Title:      TRIEL_MFOTL_Cond.thy
    Purpose:    The bridge from the TRIEL core to MFOTL, part 1: a condition of the core
                as a pair of MFOTL formulas, Pc for "true" and Nc for "false", with no
                premise on the completeness of the data.
    SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause
*)

theory TRIEL_MFOTL_Cond
  imports TRIEL_MFOTL_Enc
begin

declare [[quick_and_dirty]]

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
  sorry

lemma econsts_finite: "finite (econsts c)"
  sorry


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
  sorry

text \<open>Lemma 2: the variable is the value of \<open>a\<close>. The general form reads the value of
  the variable in the environment, the form after it binds the variable.\<close>

lemma sat_V:
  assumes "enc_pre C \<pi> \<sigma>" and "j < length \<pi>"
  shows "Formula.sat \<sigma> v j (V a y) \<longleftrightarrow> (\<exists>u. v y = MV u \<and> evalV a (st \<pi> j) = Some u)"
  sorry

lemma sat_V_upd:
  assumes "enc_pre C \<pi> \<sigma>" and "j < length \<pi>"
  shows "Formula.sat \<sigma> (v(y := z)) j (V a y) \<longleftrightarrow> (\<exists>u. z = MV u \<and> evalV a (st \<pi> j) = Some u)"
  sorry


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


section \<open>The condition is a pair of formulas\<close>

theorem bridge_true:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>" and "j < length \<pi>" and "econsts c \<subseteq> C"
  shows "eval c (st \<pi> j) = Some True \<longleftrightarrow> Formula.sat \<sigma> v j (Pc c)"
  sorry

theorem bridge_false:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>" and "j < length \<pi>" and "econsts c \<subseteq> C"
  shows "eval c (st \<pi> j) = Some False \<longleftrightarrow> Formula.sat \<sigma> v j (Nc c)"
  sorry

text \<open>Unknown blocks: a prohibition blocks unless its condition is known to be false.\<close>

theorem bridge_blocks_cond:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>" and "j < length \<pi>" and "econsts c \<subseteq> C"
  shows "blocks c (st \<pi> j) \<longleftrightarrow> \<not> Formula.sat \<sigma> v j (Nc c)"
  sorry

text \<open>With complete data (T4) the condition is defined and is the truth of \<open>Pc c\<close>.\<close>

theorem bridge_complete_cond:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>" and "j < length \<pi>" and "econsts c \<subseteq> C"
    and "names c \<subseteq> dom (st \<pi> j)"
  shows "eval c (st \<pi> j) = Some (Formula.sat \<sigma> v j (Pc c))"
  sorry

end
