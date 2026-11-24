(*  Title:      TRIEL_Evidence.thy
    Purpose:    The theorems of the evidence of the value of a condition in one state:
                a defined value stays the same on any data that agree on the read values
                and keep the read absences; an undefined value names the absent names it
                waits for; a set of names that supports a value can be checked by eval
                alone; the decisions of the monitor with their evidence are those of
                monitor_decisions, final and stable.
    SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause
*)

theory TRIEL_Evidence imports TRIEL_Evidence_Def begin

section \<open>Auxiliary facts\<close>

subsection \<open>Connectives and comparisons\<close>

lemma knot_None: "knot p = None \<longleftrightarrow> p = None"
  by (cases p) simp_all

lemma knot_Some: "knot p = Some b \<longleftrightarrow> p = Some (\<not> b)"
  by (cases p) auto

lemma kand_not_None: "p \<noteq> None \<Longrightarrow> q \<noteq> None \<Longrightarrow> kand p q \<noteq> None"
  by (cases p; cases q) simp_all

lemma kor_not_None: "p \<noteq> None \<Longrightarrow> q \<noteq> None \<Longrightarrow> kor p q \<noteq> None"
  by (cases p; cases q) simp_all

lemma kimp_not_None: "p \<noteq> None \<Longrightarrow> q \<noteq> None \<Longrightarrow> kimp p q \<noteq> None"
  by (cases p; cases q) simp_all

lemma cmp_None:
  "eval (EEq a1 a2) \<sigma> = None \<longleftrightarrow> evalV a1 \<sigma> = None \<or> evalV a2 \<sigma> = None"
  "eval (ELt a1 a2) \<sigma> = None \<longleftrightarrow> evalV a1 \<sigma> = None \<or> evalV a2 \<sigma> = None"
  "eval (ELe a1 a2) \<sigma> = None \<longleftrightarrow> evalV a1 \<sigma> = None \<or> evalV a2 \<sigma> = None"
  by (auto split: option.splits)

subsection \<open>Joined evidence\<close>

lemma ejoin_parts:
  assumes "ejoin E1 E2 = (X, A, U)"
  obtains X1 A1 U1 X2 A2 U2 where "E1 = (X1, A1, U1)" and "E2 = (X2, A2, U2)"
    and "X = X1 @ X2" and "A = A1 @ A2" and "U = U1 @ U2"
proof -
  obtain X1 A1 U1 where ev1: "E1 = (X1, A1, U1)" by (metis prod_cases3)
  obtain X2 A2 U2 where ev2: "E2 = (X2, A2, U2)" by (metis prod_cases3)
  have "X = X1 @ X2" "A = A1 @ A2" "U = U1 @ U2"
    using assms by (simp_all add: ev1 ev2)
  with ev1 ev2 show ?thesis by (rule that)
qed

subsection \<open>Operands\<close>

lemma evidV_VDefault_cases [consumes 1, case_names Present Undef Def]:
  assumes "evidV (VDefault x a) \<sigma> = (X, A, U)"
  obtains (Present) v where "\<sigma> x = Some v" and "X = [x]" and "A = []" and "U = []"
  | (Undef) U' where "\<sigma> x = None" and "evalV a \<sigma> = None" and "evidV a \<sigma> = (X, A, U')"
      and "U = x # U'"
  | (Def) A' v where "\<sigma> x = None" and "evalV a \<sigma> = Some v" and "evidV a \<sigma> = (X, A', U)"
      and "A = x # A'"
proof (cases "\<sigma> x")
  case (Some v)
  from Some assms have "X = [x]" "A = []" "U = []" by simp_all
  with Some show ?thesis by (rule Present)
next
  case None
  note nx = this
  obtain X' A' U' where ev: "evidV a \<sigma> = (X', A', U')" by (metis prod_cases3)
  show ?thesis
  proof (cases "evalV a \<sigma>")
    case None
    from nx None ev assms have XAU: "X = X'" "A = A'" "U = x # U'" by simp_all
    from ev XAU(1,2) have ev': "evidV a \<sigma> = (X, A, U')" by simp
    from nx None ev' XAU(3) show ?thesis by (rule Undef)
  next
    case (Some v)
    from nx Some ev assms have XAU: "X = X'" "A = x # A'" "U = U'" by simp_all
    from ev XAU(1,3) have ev': "evidV a \<sigma> = (X, A', U)" by simp
    from nx Some ev' XAU(2) show ?thesis by (rule Def)
  qed
qed

lemma evidV_names:
  "evidV a \<sigma> = (X, A, U) \<Longrightarrow> set X \<union> set A \<union> set U \<subseteq> vnames a \<union> vpnames a"
proof (induction a arbitrary: X A U)
  case (VDefault x a)
  from VDefault.prems show ?case
  proof (cases rule: evidV_VDefault_cases)
    case (Present v)
    then show ?thesis by simp
  next
    case (Undef U')
    from VDefault.IH[OF Undef(3)] Undef(4) show ?thesis by auto
  next
    case (Def A' v)
    from VDefault.IH[OF Def(3)] Def(4) show ?thesis by auto
  qed
qed (auto split: option.splits)

lemma evidV_shape:
  "evidV a \<sigma> = (X, A, U) \<Longrightarrow> set X \<subseteq> dom \<sigma> \<and> set A \<inter> dom \<sigma> = {} \<and> set U \<inter> dom \<sigma> = {}"
proof (induction a arbitrary: X A U)
  case (VDefault x a)
  from VDefault.prems show ?case
  proof (cases rule: evidV_VDefault_cases)
    case (Present v)
    then show ?thesis by (auto simp: domIff)
  next
    case (Undef U')
    from VDefault.IH[OF Undef(3)] Undef(1,4) show ?thesis by (auto simp: domIff)
  next
    case (Def A' v)
    from VDefault.IH[OF Def(3)] Def(1,4) show ?thesis by (auto simp: domIff)
  qed
qed (auto simp: domIff split: option.splits)

lemma evidV_default_free:
  "default_free a \<Longrightarrow> evidV a \<sigma> = (X, A, U) \<Longrightarrow> A = []"
  by (cases a) (auto split: option.splits)

lemma evidV_U:
  "evidV a \<sigma> = (X, A, U) \<Longrightarrow> evalV a \<sigma> = None \<longleftrightarrow> U \<noteq> []"
proof (induction a arbitrary: X A U)
  case (VDefault x a)
  from VDefault.prems show ?case
  proof (cases rule: evidV_VDefault_cases)
    case (Present v)
    then show ?thesis by simp
  next
    case (Undef U')
    then show ?thesis by simp
  next
    case (Def A' v)
    from Def VDefault.IH[OF Def(3)] show ?thesis by auto
  qed
qed (auto split: option.splits)

lemma evidV_definite:
  "evidV a \<sigma> = (X, A, U) \<Longrightarrow> evalV a \<sigma> = Some v \<Longrightarrow> \<forall>x \<in> set X. \<sigma>' x = \<sigma> x
   \<Longrightarrow> \<forall>x \<in> set A. \<sigma>' x = None \<Longrightarrow> evalV a \<sigma>' = Some v"
proof (induction a arbitrary: X A U v)
  case (VDefault x a)
  from VDefault.prems(1) show ?case
  proof (cases rule: evidV_VDefault_cases)
    case (Present w)
    from Present VDefault.prems(2,3) show ?thesis by auto
  next
    case (Undef U')
    from Undef VDefault.prems(2) show ?thesis by simp
  next
    case (Def A' w)
    have hx: "\<forall>y \<in> set X. \<sigma>' y = \<sigma> y" and ha: "\<forall>y \<in> set A'. \<sigma>' y = None"
      and hn: "\<sigma>' x = None"
      using VDefault.prems(3,4) Def(4) by auto
    from VDefault.IH[OF Def(3) Def(2) hx ha] have "evalV a \<sigma>' = Some w" .
    with hn Def(1,2) VDefault.prems(2) show ?thesis by auto
  qed
qed (auto split: option.splits)

lemma evidV_stays:
  "evidV a \<sigma> = (X, A, U) \<Longrightarrow> evalV a \<sigma> = None \<Longrightarrow> \<forall>x \<in> set X. \<sigma>' x = \<sigma> x
   \<Longrightarrow> \<forall>x \<in> set A \<union> set U. \<sigma>' x = None \<Longrightarrow> evalV a \<sigma>' = None"
proof (induction a arbitrary: X A U)
  case (VDefault x a)
  from VDefault.prems(1) show ?case
  proof (cases rule: evidV_VDefault_cases)
    case (Present w)
    from Present VDefault.prems(2) show ?thesis by simp
  next
    case (Undef U')
    have hx: "\<forall>y \<in> set X. \<sigma>' y = \<sigma> y" and hau: "\<forall>y \<in> set A \<union> set U'. \<sigma>' y = None"
      and hn: "\<sigma>' x = None"
      using VDefault.prems(3,4) Undef(4) by auto
    from VDefault.IH[OF Undef(3) Undef(2) hx hau] hn show ?thesis by simp
  next
    case (Def A' w)
    from Def VDefault.prems(2) show ?thesis by simp
  qed
qed (auto split: option.splits)

lemma evidV_resolved:
  "evidV a \<sigma> = (X, A, U) \<Longrightarrow> evalV a \<sigma> = None \<Longrightarrow> set U \<subseteq> dom \<sigma>' \<Longrightarrow> evalV a \<sigma>' \<noteq> None"
proof (induction a arbitrary: X A U)
  case (VDefault x a)
  from VDefault.prems(1) show ?case
  proof (cases rule: evidV_VDefault_cases)
    case (Present w)
    from Present VDefault.prems(2) show ?thesis by simp
  next
    case (Undef U')
    from Undef(4) VDefault.prems(3) show ?thesis by (auto simp: domIff split: option.splits)
  next
    case (Def A' w)
    from Def VDefault.prems(2) show ?thesis by simp
  qed
qed (auto simp: domIff split: option.splits)

lemma evidV_defined:
  assumes ev: "evidV a \<sigma> = (X, A, U)" and hx: "\<forall>x \<in> set X. \<sigma>' x = \<sigma> x"
    and ha: "\<forall>x \<in> set A. \<sigma>' x = None" and hu: "set U \<subseteq> dom \<sigma>'"
  shows "evalV a \<sigma>' \<noteq> None"
proof (cases "evalV a \<sigma>")
  case None
  from evidV_resolved[OF ev None hu] show ?thesis .
next
  case (Some v)
  from evidV_definite[OF ev Some hx ha] show ?thesis by simp
qed

subsection \<open>The two operands of a comparison\<close>

lemma pair_names:
  assumes "ejoin (evidV a1 \<sigma>) (evidV a2 \<sigma>) = (X, A, U)"
  shows "set X \<union> set A \<union> set U \<subseteq> (vnames a1 \<union> vnames a2) \<union> (vpnames a1 \<union> vpnames a2)"
proof -
  from assms obtain X1 A1 U1 X2 A2 U2 where ev1: "evidV a1 \<sigma> = (X1, A1, U1)"
    and ev2: "evidV a2 \<sigma> = (X2, A2, U2)" and j: "X = X1 @ X2" "A = A1 @ A2" "U = U1 @ U2"
    by (rule ejoin_parts)
  from evidV_names[OF ev1] evidV_names[OF ev2] j show ?thesis by auto
qed

lemma pair_shape:
  assumes "ejoin (evidV a1 \<sigma>) (evidV a2 \<sigma>) = (X, A, U)"
  shows "set X \<subseteq> dom \<sigma> \<and> set A \<inter> dom \<sigma> = {} \<and> set U \<inter> dom \<sigma> = {}"
proof -
  from assms obtain X1 A1 U1 X2 A2 U2 where ev1: "evidV a1 \<sigma> = (X1, A1, U1)"
    and ev2: "evidV a2 \<sigma> = (X2, A2, U2)" and j: "X = X1 @ X2" "A = A1 @ A2" "U = U1 @ U2"
    by (rule ejoin_parts)
  from evidV_shape[OF ev1] evidV_shape[OF ev2] j show ?thesis by auto
qed

lemma pair_default_free:
  assumes "default_free a1" and "default_free a2"
    and "ejoin (evidV a1 \<sigma>) (evidV a2 \<sigma>) = (X, A, U)"
  shows "A = []"
proof -
  from assms(3) obtain X1 A1 U1 X2 A2 U2 where ev1: "evidV a1 \<sigma> = (X1, A1, U1)"
    and ev2: "evidV a2 \<sigma> = (X2, A2, U2)" and j: "X = X1 @ X2" "A = A1 @ A2" "U = U1 @ U2"
    by (rule ejoin_parts)
  from evidV_default_free[OF assms(1) ev1] evidV_default_free[OF assms(2) ev2] j(2)
  show ?thesis by simp
qed

lemma pair_U:
  assumes "ejoin (evidV a1 \<sigma>) (evidV a2 \<sigma>) = (X, A, U)"
  shows "(evalV a1 \<sigma> = None \<or> evalV a2 \<sigma> = None) \<longleftrightarrow> U \<noteq> []"
proof -
  from assms obtain X1 A1 U1 X2 A2 U2 where ev1: "evidV a1 \<sigma> = (X1, A1, U1)"
    and ev2: "evidV a2 \<sigma> = (X2, A2, U2)" and j: "X = X1 @ X2" "A = A1 @ A2" "U = U1 @ U2"
    by (rule ejoin_parts)
  from evidV_U[OF ev1] evidV_U[OF ev2] j(3) show ?thesis by auto
qed

lemma pair_definite:
  assumes "ejoin (evidV a1 \<sigma>) (evidV a2 \<sigma>) = (X, A, U)"
    and v1: "evalV a1 \<sigma> = Some v1" and v2: "evalV a2 \<sigma> = Some v2"
    and "\<forall>x \<in> set X. \<sigma>' x = \<sigma> x" and "\<forall>x \<in> set A. \<sigma>' x = None"
  shows "evalV a1 \<sigma>' = Some v1 \<and> evalV a2 \<sigma>' = Some v2"
proof -
  from assms(1) obtain X1 A1 U1 X2 A2 U2 where ev1: "evidV a1 \<sigma> = (X1, A1, U1)"
    and ev2: "evidV a2 \<sigma> = (X2, A2, U2)" and j: "X = X1 @ X2" "A = A1 @ A2" "U = U1 @ U2"
    by (rule ejoin_parts)
  have h: "\<forall>x \<in> set X1. \<sigma>' x = \<sigma> x" "\<forall>x \<in> set A1. \<sigma>' x = None"
    "\<forall>x \<in> set X2. \<sigma>' x = \<sigma> x" "\<forall>x \<in> set A2. \<sigma>' x = None"
    using assms(4,5) j by auto
  from evidV_definite[OF ev1 v1 h(1,2)] evidV_definite[OF ev2 v2 h(3,4)] show ?thesis by simp
qed

lemma pair_stays:
  assumes "ejoin (evidV a1 \<sigma>) (evidV a2 \<sigma>) = (X, A, U)"
    and n: "evalV a1 \<sigma> = None \<or> evalV a2 \<sigma> = None"
    and "\<forall>x \<in> set X. \<sigma>' x = \<sigma> x" and "\<forall>x \<in> set A \<union> set U. \<sigma>' x = None"
  shows "evalV a1 \<sigma>' = None \<or> evalV a2 \<sigma>' = None"
proof -
  from assms(1) obtain X1 A1 U1 X2 A2 U2 where ev1: "evidV a1 \<sigma> = (X1, A1, U1)"
    and ev2: "evidV a2 \<sigma> = (X2, A2, U2)" and j: "X = X1 @ X2" "A = A1 @ A2" "U = U1 @ U2"
    by (rule ejoin_parts)
  have h: "\<forall>x \<in> set X1. \<sigma>' x = \<sigma> x" "\<forall>x \<in> set A1 \<union> set U1. \<sigma>' x = None"
    "\<forall>x \<in> set X2. \<sigma>' x = \<sigma> x" "\<forall>x \<in> set A2 \<union> set U2. \<sigma>' x = None"
    using assms(3,4) j by auto
  from n show ?thesis
  proof
    assume "evalV a1 \<sigma> = None"
    from evidV_stays[OF ev1 this h(1,2)] show ?thesis by simp
  next
    assume "evalV a2 \<sigma> = None"
    from evidV_stays[OF ev2 this h(3,4)] show ?thesis by simp
  qed
qed

lemma pair_resolved:
  assumes "ejoin (evidV a1 \<sigma>) (evidV a2 \<sigma>) = (X, A, U)"
    and "\<forall>x \<in> set X. \<sigma>' x = \<sigma> x" and "\<forall>x \<in> set A. \<sigma>' x = None" and "set U \<subseteq> dom \<sigma>'"
  shows "evalV a1 \<sigma>' \<noteq> None \<and> evalV a2 \<sigma>' \<noteq> None"
proof -
  from assms(1) obtain X1 A1 U1 X2 A2 U2 where ev1: "evidV a1 \<sigma> = (X1, A1, U1)"
    and ev2: "evidV a2 \<sigma> = (X2, A2, U2)" and j: "X = X1 @ X2" "A = A1 @ A2" "U = U1 @ U2"
    by (rule ejoin_parts)
  have h: "\<forall>x \<in> set X1. \<sigma>' x = \<sigma> x" "\<forall>x \<in> set A1. \<sigma>' x = None" "set U1 \<subseteq> dom \<sigma>'"
    "\<forall>x \<in> set X2. \<sigma>' x = \<sigma> x" "\<forall>x \<in> set A2. \<sigma>' x = None" "set U2 \<subseteq> dom \<sigma>'"
    using assms(2,3,4) j by auto
  from evidV_defined[OF ev1 h(1-3)] evidV_defined[OF ev2 h(4-6)] show ?thesis by simp
qed

subsection \<open>The three connectives with two operands\<close>

lemma evidence_EAnd_cases [consumes 1, case_names L R J]:
  assumes "evidence (EAnd e1 e2) \<sigma> = (X, A, U)"
  obtains (L) "eval e1 \<sigma> = Some False" and "evidence e1 \<sigma> = (X, A, U)"
  | (R) "eval e1 \<sigma> \<noteq> Some False" and "eval e2 \<sigma> = Some False" and "evidence e2 \<sigma> = (X, A, U)"
  | (J) X1 A1 U1 X2 A2 U2 where "eval e1 \<sigma> \<noteq> Some False" and "eval e2 \<sigma> \<noteq> Some False"
      and "evidence e1 \<sigma> = (X1, A1, U1)" and "evidence e2 \<sigma> = (X2, A2, U2)"
      and "X = X1 @ X2" and "A = A1 @ A2" and "U = U1 @ U2"
proof (cases "eval e1 \<sigma> = Some False")
  case True
  from True assms have "evidence e1 \<sigma> = (X, A, U)" by simp
  with True show ?thesis by (rule L)
next
  case False
  note n1 = this
  show ?thesis
  proof (cases "eval e2 \<sigma> = Some False")
    case True
    from n1 True assms have "evidence e2 \<sigma> = (X, A, U)" by simp
    with n1 True show ?thesis by (rule R)
  next
    case False
    note n2 = this
    from n1 n2 assms have "ejoin (evidence e1 \<sigma>) (evidence e2 \<sigma>) = (X, A, U)" by simp
    then obtain X1 A1 U1 X2 A2 U2 where "evidence e1 \<sigma> = (X1, A1, U1)"
      and "evidence e2 \<sigma> = (X2, A2, U2)" and "X = X1 @ X2" and "A = A1 @ A2" and "U = U1 @ U2"
      by (rule ejoin_parts)
    with n1 n2 show ?thesis by (rule J)
  qed
qed

lemma evidence_EOr_cases [consumes 1, case_names L R J]:
  assumes "evidence (EOr e1 e2) \<sigma> = (X, A, U)"
  obtains (L) "eval e1 \<sigma> = Some True" and "evidence e1 \<sigma> = (X, A, U)"
  | (R) "eval e1 \<sigma> \<noteq> Some True" and "eval e2 \<sigma> = Some True" and "evidence e2 \<sigma> = (X, A, U)"
  | (J) X1 A1 U1 X2 A2 U2 where "eval e1 \<sigma> \<noteq> Some True" and "eval e2 \<sigma> \<noteq> Some True"
      and "evidence e1 \<sigma> = (X1, A1, U1)" and "evidence e2 \<sigma> = (X2, A2, U2)"
      and "X = X1 @ X2" and "A = A1 @ A2" and "U = U1 @ U2"
proof (cases "eval e1 \<sigma> = Some True")
  case True
  from True assms have "evidence e1 \<sigma> = (X, A, U)" by simp
  with True show ?thesis by (rule L)
next
  case False
  note n1 = this
  show ?thesis
  proof (cases "eval e2 \<sigma> = Some True")
    case True
    from n1 True assms have "evidence e2 \<sigma> = (X, A, U)" by simp
    with n1 True show ?thesis by (rule R)
  next
    case False
    note n2 = this
    from n1 n2 assms have "ejoin (evidence e1 \<sigma>) (evidence e2 \<sigma>) = (X, A, U)" by simp
    then obtain X1 A1 U1 X2 A2 U2 where "evidence e1 \<sigma> = (X1, A1, U1)"
      and "evidence e2 \<sigma> = (X2, A2, U2)" and "X = X1 @ X2" and "A = A1 @ A2" and "U = U1 @ U2"
      by (rule ejoin_parts)
    with n1 n2 show ?thesis by (rule J)
  qed
qed

lemma evidence_EImp_cases [consumes 1, case_names L R J]:
  assumes "evidence (EImp e1 e2) \<sigma> = (X, A, U)"
  obtains (L) "eval e1 \<sigma> = Some False" and "evidence e1 \<sigma> = (X, A, U)"
  | (R) "eval e1 \<sigma> \<noteq> Some False" and "eval e2 \<sigma> = Some True" and "evidence e2 \<sigma> = (X, A, U)"
  | (J) X1 A1 U1 X2 A2 U2 where "eval e1 \<sigma> \<noteq> Some False" and "eval e2 \<sigma> \<noteq> Some True"
      and "evidence e1 \<sigma> = (X1, A1, U1)" and "evidence e2 \<sigma> = (X2, A2, U2)"
      and "X = X1 @ X2" and "A = A1 @ A2" and "U = U1 @ U2"
proof (cases "eval e1 \<sigma> = Some False")
  case True
  from True assms have "evidence e1 \<sigma> = (X, A, U)" by simp
  with True show ?thesis by (rule L)
next
  case False
  note n1 = this
  show ?thesis
  proof (cases "eval e2 \<sigma> = Some True")
    case True
    from n1 True assms have "evidence e2 \<sigma> = (X, A, U)" by simp
    with n1 True show ?thesis by (rule R)
  next
    case False
    note n2 = this
    from n1 n2 assms have "ejoin (evidence e1 \<sigma>) (evidence e2 \<sigma>) = (X, A, U)" by simp
    then obtain X1 A1 U1 X2 A2 U2 where "evidence e1 \<sigma> = (X1, A1, U1)"
      and "evidence e2 \<sigma> = (X2, A2, U2)" and "X = X1 @ X2" and "A = A1 @ A2" and "U = U1 @ U2"
      by (rule ejoin_parts)
    with n1 n2 show ?thesis by (rule J)
  qed
qed


section \<open>The shape of the evidence\<close>

lemma evidence_names:
  "evidence c \<sigma> = (X, A, U) \<Longrightarrow> set X \<union> set A \<union> set U \<subseteq> names c \<union> pnames c"
proof (induction c arbitrary: X A U)
  case (EEq a1 a2)
  then have "ejoin (evidV a1 \<sigma>) (evidV a2 \<sigma>) = (X, A, U)" by simp
  from pair_names[OF this] show ?case by auto
next
  case (ELt a1 a2)
  then have "ejoin (evidV a1 \<sigma>) (evidV a2 \<sigma>) = (X, A, U)" by simp
  from pair_names[OF this] show ?case by auto
next
  case (ELe a1 a2)
  then have "ejoin (evidV a1 \<sigma>) (evidV a2 \<sigma>) = (X, A, U)" by simp
  from pair_names[OF this] show ?case by auto
next
  case (ENot e)
  from ENot.prems have "evidence e \<sigma> = (X, A, U)" by simp
  from ENot.IH[OF this] show ?case by simp
next
  case (EAnd e1 e2)
  from EAnd.prems show ?case
  proof (cases rule: evidence_EAnd_cases)
    case L
    from EAnd.IH(1)[OF L(2)] show ?thesis by auto
  next
    case R
    from EAnd.IH(2)[OF R(3)] show ?thesis by auto
  next
    case (J X1 A1 U1 X2 A2 U2)
    from EAnd.IH(1)[OF J(3)] EAnd.IH(2)[OF J(4)] J(5-7) show ?thesis by auto
  qed
next
  case (EOr e1 e2)
  from EOr.prems show ?case
  proof (cases rule: evidence_EOr_cases)
    case L
    from EOr.IH(1)[OF L(2)] show ?thesis by auto
  next
    case R
    from EOr.IH(2)[OF R(3)] show ?thesis by auto
  next
    case (J X1 A1 U1 X2 A2 U2)
    from EOr.IH(1)[OF J(3)] EOr.IH(2)[OF J(4)] J(5-7) show ?thesis by auto
  qed
next
  case (EImp e1 e2)
  from EImp.prems show ?case
  proof (cases rule: evidence_EImp_cases)
    case L
    from EImp.IH(1)[OF L(2)] show ?thesis by auto
  next
    case R
    from EImp.IH(2)[OF R(3)] show ?thesis by auto
  next
    case (J X1 A1 U1 X2 A2 U2)
    from EImp.IH(1)[OF J(3)] EImp.IH(2)[OF J(4)] J(5-7) show ?thesis by auto
  qed
qed (auto split: option.splits)

lemma evidence_shape:
  "evidence c \<sigma> = (X, A, U) \<Longrightarrow> set X \<subseteq> dom \<sigma> \<and> set A \<inter> dom \<sigma> = {} \<and> set U \<inter> dom \<sigma> = {}"
proof (induction c arbitrary: X A U)
  case (EEq a1 a2)
  then have "ejoin (evidV a1 \<sigma>) (evidV a2 \<sigma>) = (X, A, U)" by simp
  from pair_shape[OF this] show ?case .
next
  case (ELt a1 a2)
  then have "ejoin (evidV a1 \<sigma>) (evidV a2 \<sigma>) = (X, A, U)" by simp
  from pair_shape[OF this] show ?case .
next
  case (ELe a1 a2)
  then have "ejoin (evidV a1 \<sigma>) (evidV a2 \<sigma>) = (X, A, U)" by simp
  from pair_shape[OF this] show ?case .
next
  case (ENot e)
  from ENot.prems have "evidence e \<sigma> = (X, A, U)" by simp
  from ENot.IH[OF this] show ?case .
next
  case (EAnd e1 e2)
  from EAnd.prems show ?case
  proof (cases rule: evidence_EAnd_cases)
    case L
    from EAnd.IH(1)[OF L(2)] show ?thesis .
  next
    case R
    from EAnd.IH(2)[OF R(3)] show ?thesis .
  next
    case (J X1 A1 U1 X2 A2 U2)
    from EAnd.IH(1)[OF J(3)] EAnd.IH(2)[OF J(4)] J(5-7) show ?thesis by auto
  qed
next
  case (EOr e1 e2)
  from EOr.prems show ?case
  proof (cases rule: evidence_EOr_cases)
    case L
    from EOr.IH(1)[OF L(2)] show ?thesis .
  next
    case R
    from EOr.IH(2)[OF R(3)] show ?thesis .
  next
    case (J X1 A1 U1 X2 A2 U2)
    from EOr.IH(1)[OF J(3)] EOr.IH(2)[OF J(4)] J(5-7) show ?thesis by auto
  qed
next
  case (EImp e1 e2)
  from EImp.prems show ?case
  proof (cases rule: evidence_EImp_cases)
    case L
    from EImp.IH(1)[OF L(2)] show ?thesis .
  next
    case R
    from EImp.IH(2)[OF R(3)] show ?thesis .
  next
    case (J X1 A1 U1 X2 A2 U2)
    from EImp.IH(1)[OF J(3)] EImp.IH(2)[OF J(4)] J(5-7) show ?thesis by auto
  qed
qed (auto simp: domIff split: option.splits)

lemma evidence_present_free:
  "present_free c \<Longrightarrow> evidence c \<sigma> = (X, A, U) \<Longrightarrow> A = []"
proof (induction c arbitrary: X A U)
  case (EEq a1 a2)
  from EEq.prems(1) have "default_free a1" "default_free a2" by simp_all
  moreover from EEq.prems(2) have "ejoin (evidV a1 \<sigma>) (evidV a2 \<sigma>) = (X, A, U)" by simp
  ultimately show ?case by (rule pair_default_free)
next
  case (ELt a1 a2)
  from ELt.prems(1) have "default_free a1" "default_free a2" by simp_all
  moreover from ELt.prems(2) have "ejoin (evidV a1 \<sigma>) (evidV a2 \<sigma>) = (X, A, U)" by simp
  ultimately show ?case by (rule pair_default_free)
next
  case (ELe a1 a2)
  from ELe.prems(1) have "default_free a1" "default_free a2" by simp_all
  moreover from ELe.prems(2) have "ejoin (evidV a1 \<sigma>) (evidV a2 \<sigma>) = (X, A, U)" by simp
  ultimately show ?case by (rule pair_default_free)
next
  case (ENot e)
  from ENot.prems have "present_free e" "evidence e \<sigma> = (X, A, U)" by simp_all
  from ENot.IH[OF this] show ?case .
next
  case (EAnd e1 e2)
  from EAnd.prems(1) have p: "present_free e1" "present_free e2" by simp_all
  from EAnd.prems(2) show ?case
  proof (cases rule: evidence_EAnd_cases)
    case L
    from EAnd.IH(1)[OF p(1) L(2)] show ?thesis .
  next
    case R
    from EAnd.IH(2)[OF p(2) R(3)] show ?thesis .
  next
    case (J X1 A1 U1 X2 A2 U2)
    from EAnd.IH(1)[OF p(1) J(3)] EAnd.IH(2)[OF p(2) J(4)] J(6) show ?thesis by simp
  qed
next
  case (EOr e1 e2)
  from EOr.prems(1) have p: "present_free e1" "present_free e2" by simp_all
  from EOr.prems(2) show ?case
  proof (cases rule: evidence_EOr_cases)
    case L
    from EOr.IH(1)[OF p(1) L(2)] show ?thesis .
  next
    case R
    from EOr.IH(2)[OF p(2) R(3)] show ?thesis .
  next
    case (J X1 A1 U1 X2 A2 U2)
    from EOr.IH(1)[OF p(1) J(3)] EOr.IH(2)[OF p(2) J(4)] J(6) show ?thesis by simp
  qed
next
  case (EImp e1 e2)
  from EImp.prems(1) have p: "present_free e1" "present_free e2" by simp_all
  from EImp.prems(2) show ?case
  proof (cases rule: evidence_EImp_cases)
    case L
    from EImp.IH(1)[OF p(1) L(2)] show ?thesis .
  next
    case R
    from EImp.IH(2)[OF p(2) R(3)] show ?thesis .
  next
    case (J X1 A1 U1 X2 A2 U2)
    from EImp.IH(1)[OF p(1) J(3)] EImp.IH(2)[OF p(2) J(4)] J(6) show ?thesis by simp
  qed
qed (auto split: option.splits)


section \<open>Missing names and definedness\<close>

text \<open>The value is undefined exactly when the evidence waits for some name.\<close>

lemma evidence_U:
  "evidence c \<sigma> = (X, A, U) \<Longrightarrow> eval c \<sigma> = None \<longleftrightarrow> U \<noteq> []"
proof (induction c arbitrary: X A U)
  case (EEq a1 a2)
  then have j: "ejoin (evidV a1 \<sigma>) (evidV a2 \<sigma>) = (X, A, U)" by simp
  show ?case unfolding cmp_None by (rule pair_U[OF j])
next
  case (ELt a1 a2)
  then have j: "ejoin (evidV a1 \<sigma>) (evidV a2 \<sigma>) = (X, A, U)" by simp
  show ?case unfolding cmp_None by (rule pair_U[OF j])
next
  case (ELe a1 a2)
  then have j: "ejoin (evidV a1 \<sigma>) (evidV a2 \<sigma>) = (X, A, U)" by simp
  show ?case unfolding cmp_None by (rule pair_U[OF j])
next
  case (ENot e)
  from ENot.prems have "evidence e \<sigma> = (X, A, U)" by simp
  from ENot.IH[OF this] show ?case by (simp add: knot_None)
next
  case (EAnd e1 e2)
  from EAnd.prems show ?case
  proof (cases rule: evidence_EAnd_cases)
    case L
    from L(1) EAnd.IH(1)[OF L(2)] show ?thesis by (simp add: kand_def)
  next
    case R
    from R(1,2) EAnd.IH(2)[OF R(3)] show ?thesis by (simp add: kand_def)
  next
    case (J X1 A1 U1 X2 A2 U2)
    show ?thesis
      using J(1,2,7) EAnd.IH(1)[OF J(3)] EAnd.IH(2)[OF J(4)]
        bool_option_cases[of "eval e1 \<sigma>"] bool_option_cases[of "eval e2 \<sigma>"]
      by (auto simp: kand_def)
  qed
next
  case (EOr e1 e2)
  from EOr.prems show ?case
  proof (cases rule: evidence_EOr_cases)
    case L
    from L(1) EOr.IH(1)[OF L(2)] show ?thesis by (simp add: kor_def)
  next
    case R
    from R(1,2) EOr.IH(2)[OF R(3)] show ?thesis by (simp add: kor_def)
  next
    case (J X1 A1 U1 X2 A2 U2)
    show ?thesis
      using J(1,2,7) EOr.IH(1)[OF J(3)] EOr.IH(2)[OF J(4)]
        bool_option_cases[of "eval e1 \<sigma>"] bool_option_cases[of "eval e2 \<sigma>"]
      by (auto simp: kor_def)
  qed
next
  case (EImp e1 e2)
  from EImp.prems show ?case
  proof (cases rule: evidence_EImp_cases)
    case L
    from L(1) EImp.IH(1)[OF L(2)] show ?thesis by (simp add: kimp_def)
  next
    case R
    from R(1,2) EImp.IH(2)[OF R(3)] show ?thesis by (simp add: kimp_def)
  next
    case (J X1 A1 U1 X2 A2 U2)
    show ?thesis
      using J(1,2,7) EImp.IH(1)[OF J(3)] EImp.IH(2)[OF J(4)]
        bool_option_cases[of "eval e1 \<sigma>"] bool_option_cases[of "eval e2 \<sigma>"]
      by (auto simp: kimp_def)
  qed
qed (auto split: option.splits)


section \<open>(a) A defined value\<close>

lemma evidence_definite_U:
  "\<lbrakk>evidence c \<sigma> = (X, A, U); eval c \<sigma> = Some b\<rbrakk> \<Longrightarrow> U = []"
  by (drule evidence_U) auto

lemma evidence_definite:
  "\<lbrakk>evidence c \<sigma> = (X, A, U); eval c \<sigma> = Some b; \<forall>x \<in> set X. \<sigma>' x = \<sigma> x; \<forall>x \<in> set A. \<sigma>' x = None\<rbrakk>
   \<Longrightarrow> eval c \<sigma>' = Some b"
proof (induction c arbitrary: X A U b)
  case (EEq a1 a2)
  from EEq.prems(1) have j: "ejoin (evidV a1 \<sigma>) (evidV a2 \<sigma>) = (X, A, U)" by simp
  from EEq.prems(2) obtain v1 v2 where v1: "evalV a1 \<sigma> = Some v1" and v2: "evalV a2 \<sigma> = Some v2"
    by (auto split: option.splits)
  from pair_definite[OF j v1 v2 EEq.prems(3,4)]
  have "evalV a1 \<sigma>' = Some v1" "evalV a2 \<sigma>' = Some v2" by simp_all
  with v1 v2 EEq.prems(2) show ?case by simp
next
  case (ELt a1 a2)
  from ELt.prems(1) have j: "ejoin (evidV a1 \<sigma>) (evidV a2 \<sigma>) = (X, A, U)" by simp
  from ELt.prems(2) obtain v1 v2 where v1: "evalV a1 \<sigma> = Some v1" and v2: "evalV a2 \<sigma> = Some v2"
    by (auto split: option.splits)
  from pair_definite[OF j v1 v2 ELt.prems(3,4)]
  have "evalV a1 \<sigma>' = Some v1" "evalV a2 \<sigma>' = Some v2" by simp_all
  with v1 v2 ELt.prems(2) show ?case by simp
next
  case (ELe a1 a2)
  from ELe.prems(1) have j: "ejoin (evidV a1 \<sigma>) (evidV a2 \<sigma>) = (X, A, U)" by simp
  from ELe.prems(2) obtain v1 v2 where v1: "evalV a1 \<sigma> = Some v1" and v2: "evalV a2 \<sigma> = Some v2"
    by (auto split: option.splits)
  from pair_definite[OF j v1 v2 ELe.prems(3,4)]
  have "evalV a1 \<sigma>' = Some v1" "evalV a2 \<sigma>' = Some v2" by simp_all
  with v1 v2 ELe.prems(2) show ?case by simp
next
  case (ENot e)
  from ENot.prems(1) have ev: "evidence e \<sigma> = (X, A, U)" by simp
  from ENot.prems(2) have "eval e \<sigma> = Some (\<not> b)" by (simp add: knot_Some)
  from ENot.IH[OF ev this ENot.prems(3,4)] show ?case by simp
next
  case (EAnd e1 e2)
  from EAnd.prems(1) show ?case
  proof (cases rule: evidence_EAnd_cases)
    case L
    from EAnd.IH(1)[OF L(2) L(1) EAnd.prems(3,4)] have "eval e1 \<sigma>' = Some False" .
    with L(1) EAnd.prems(2) show ?thesis by (simp add: kand_def)
  next
    case R
    from EAnd.IH(2)[OF R(3) R(2) EAnd.prems(3,4)] have "eval e2 \<sigma>' = Some False" .
    with R(2) EAnd.prems(2) show ?thesis by (simp add: kand_def)
  next
    case (J X1 A1 U1 X2 A2 U2)
    have t: "eval e1 \<sigma> = Some True" "eval e2 \<sigma> = Some True" "b"
      using J(1,2) EAnd.prems(2) bool_option_cases[of "eval e1 \<sigma>"] bool_option_cases[of "eval e2 \<sigma>"]
      by (auto simp: kand_def)
    have h: "\<forall>x \<in> set X1. \<sigma>' x = \<sigma> x" "\<forall>x \<in> set A1. \<sigma>' x = None"
      "\<forall>x \<in> set X2. \<sigma>' x = \<sigma> x" "\<forall>x \<in> set A2. \<sigma>' x = None"
      using EAnd.prems(3,4) J(5,6) by auto
    from EAnd.IH(1)[OF J(3) t(1) h(1,2)] EAnd.IH(2)[OF J(4) t(2) h(3,4)] t(3)
    show ?thesis by simp
  qed
next
  case (EOr e1 e2)
  from EOr.prems(1) show ?case
  proof (cases rule: evidence_EOr_cases)
    case L
    from EOr.IH(1)[OF L(2) L(1) EOr.prems(3,4)] have "eval e1 \<sigma>' = Some True" .
    with L(1) EOr.prems(2) show ?thesis by (simp add: kor_def)
  next
    case R
    from EOr.IH(2)[OF R(3) R(2) EOr.prems(3,4)] have "eval e2 \<sigma>' = Some True" .
    with R(2) EOr.prems(2) show ?thesis by (simp add: kor_def)
  next
    case (J X1 A1 U1 X2 A2 U2)
    have t: "eval e1 \<sigma> = Some False" "eval e2 \<sigma> = Some False" "\<not> b"
      using J(1,2) EOr.prems(2) bool_option_cases[of "eval e1 \<sigma>"] bool_option_cases[of "eval e2 \<sigma>"]
      by (auto simp: kor_def)
    have h: "\<forall>x \<in> set X1. \<sigma>' x = \<sigma> x" "\<forall>x \<in> set A1. \<sigma>' x = None"
      "\<forall>x \<in> set X2. \<sigma>' x = \<sigma> x" "\<forall>x \<in> set A2. \<sigma>' x = None"
      using EOr.prems(3,4) J(5,6) by auto
    from EOr.IH(1)[OF J(3) t(1) h(1,2)] EOr.IH(2)[OF J(4) t(2) h(3,4)] t(3)
    show ?thesis by simp
  qed
next
  case (EImp e1 e2)
  from EImp.prems(1) show ?case
  proof (cases rule: evidence_EImp_cases)
    case L
    from EImp.IH(1)[OF L(2) L(1) EImp.prems(3,4)] have "eval e1 \<sigma>' = Some False" .
    with L(1) EImp.prems(2) show ?thesis by (simp add: kimp_def)
  next
    case R
    from EImp.IH(2)[OF R(3) R(2) EImp.prems(3,4)] have "eval e2 \<sigma>' = Some True" .
    with R(2) EImp.prems(2) show ?thesis by (simp add: kimp_def)
  next
    case (J X1 A1 U1 X2 A2 U2)
    have t: "eval e1 \<sigma> = Some True" "eval e2 \<sigma> = Some False" "\<not> b"
      using J(1,2) EImp.prems(2) bool_option_cases[of "eval e1 \<sigma>"] bool_option_cases[of "eval e2 \<sigma>"]
      by (auto simp: kimp_def)
    have h: "\<forall>x \<in> set X1. \<sigma>' x = \<sigma> x" "\<forall>x \<in> set A1. \<sigma>' x = None"
      "\<forall>x \<in> set X2. \<sigma>' x = \<sigma> x" "\<forall>x \<in> set A2. \<sigma>' x = None"
      using EImp.prems(3,4) J(5,6) by auto
    from EImp.IH(1)[OF J(3) t(1) h(1,2)] EImp.IH(2)[OF J(4) t(2) h(3,4)] t(3)
    show ?thesis by simp
  qed
qed (auto simp: domIff split: option.splits)

lemma evidence_definite_pf:
  assumes "present_free c" and "evidence c \<sigma> = (X, A, U)" and "eval c \<sigma> = Some b"
    and "\<forall>x \<in> set X. \<sigma>' x = \<sigma> x"
  shows "eval c \<sigma>' = Some b"
proof -
  from evidence_present_free[OF assms(1,2)] have "\<forall>x \<in> set A. \<sigma>' x = None" by simp
  from evidence_definite[OF assms(2,3,4) this] show ?thesis .
qed

lemma evidence_completions:
  assumes "present_free c" and "evidence c \<sigma> = (X, A, U)" and "eval c \<sigma> = Some b"
    and "completion (\<sigma> |` set X) \<sigma>'"
  shows "eval c \<sigma>' = Some b"
proof -
  have le: "\<sigma> |` set X \<sqsubseteq> \<sigma>'" using assms(4) unfolding completion_def by blast
  have dx: "set X \<subseteq> dom \<sigma>" using evidence_shape[OF assms(2)] by blast
  have "\<forall>x \<in> set X. \<sigma>' x = \<sigma> x"
  proof
    fix x assume x: "x \<in> set X"
    with dx have "x \<in> dom \<sigma>" by blast
    from domD[OF this] obtain v where v: "\<sigma> x = Some v" by blast
    from x v have "(\<sigma> |` set X) x = Some v" by simp
    from info_leD[OF le this] v show "\<sigma>' x = \<sigma> x" by simp
  qed
  from evidence_definite_pf[OF assms(1,2,3) this] show ?thesis .
qed


section \<open>(b) An undefined value\<close>

lemma evidence_undefined_U:
  "\<lbrakk>evidence c \<sigma> = (X, A, U); eval c \<sigma> = None\<rbrakk> \<Longrightarrow> U \<noteq> []"
  by (drule evidence_U) auto

lemma evidence_undefined_absent:
  "\<lbrakk>evidence c \<sigma> = (X, A, U); eval c \<sigma> = None\<rbrakk> \<Longrightarrow> \<forall>x \<in> set U. \<sigma> x = None"
  by (drule evidence_shape) (auto simp: domIff)

lemma evidence_undefined_stays:
  "\<lbrakk>evidence c \<sigma> = (X, A, U); eval c \<sigma> = None; \<forall>x \<in> set X. \<sigma>' x = \<sigma> x;
    \<forall>x \<in> set A \<union> set U. \<sigma>' x = None\<rbrakk> \<Longrightarrow> eval c \<sigma>' = None"
proof (induction c arbitrary: X A U)
  case (EEq a1 a2)
  from EEq.prems(1) have j: "ejoin (evidV a1 \<sigma>) (evidV a2 \<sigma>) = (X, A, U)" by simp
  from EEq.prems(2) have "evalV a1 \<sigma> = None \<or> evalV a2 \<sigma> = None" by (auto split: option.splits)
  from pair_stays[OF j this EEq.prems(3,4)] show ?case by (auto split: option.splits)
next
  case (ELt a1 a2)
  from ELt.prems(1) have j: "ejoin (evidV a1 \<sigma>) (evidV a2 \<sigma>) = (X, A, U)" by simp
  from ELt.prems(2) have "evalV a1 \<sigma> = None \<or> evalV a2 \<sigma> = None" by (auto split: option.splits)
  from pair_stays[OF j this ELt.prems(3,4)] show ?case by (auto split: option.splits)
next
  case (ELe a1 a2)
  from ELe.prems(1) have j: "ejoin (evidV a1 \<sigma>) (evidV a2 \<sigma>) = (X, A, U)" by simp
  from ELe.prems(2) have "evalV a1 \<sigma> = None \<or> evalV a2 \<sigma> = None" by (auto split: option.splits)
  from pair_stays[OF j this ELe.prems(3,4)] show ?case by (auto split: option.splits)
next
  case (ENot e)
  from ENot.prems(1) have ev: "evidence e \<sigma> = (X, A, U)" by simp
  from ENot.prems(2) have "eval e \<sigma> = None" by (simp add: knot_None)
  from ENot.IH[OF ev this ENot.prems(3,4)] show ?case by simp
next
  case (EAnd e1 e2)
  from EAnd.prems(1) show ?case
  proof (cases rule: evidence_EAnd_cases)
    case L
    from L(1) EAnd.prems(2) show ?thesis by (simp add: kand_def)
  next
    case R
    from R(2) EAnd.prems(2) show ?thesis by (simp add: kand_def)
  next
    case (J X1 A1 U1 X2 A2 U2)
    have h: "\<forall>x \<in> set X1. \<sigma>' x = \<sigma> x" "\<forall>x \<in> set A1 \<union> set U1. \<sigma>' x = None"
      "\<forall>x \<in> set X2. \<sigma>' x = \<sigma> x" "\<forall>x \<in> set A2 \<union> set U2. \<sigma>' x = None"
      using EAnd.prems(3,4) J(5-7) by auto
    have s1: "eval e1 \<sigma>' = eval e1 \<sigma>"
    proof (cases "eval e1 \<sigma>")
      case None
      from EAnd.IH(1)[OF J(3) None h(1,2)] None show ?thesis by simp
    next
      case (Some v)
      have "\<forall>x \<in> set A1. \<sigma>' x = None" using h(2) by auto
      from evidence_definite[OF J(3) Some h(1) this] Some show ?thesis by simp
    qed
    have s2: "eval e2 \<sigma>' = eval e2 \<sigma>"
    proof (cases "eval e2 \<sigma>")
      case None
      from EAnd.IH(2)[OF J(4) None h(3,4)] None show ?thesis by simp
    next
      case (Some v)
      have "\<forall>x \<in> set A2. \<sigma>' x = None" using h(4) by auto
      from evidence_definite[OF J(4) Some h(3) this] Some show ?thesis by simp
    qed
    from EAnd.prems(2) s1 s2 show ?thesis by simp
  qed
next
  case (EOr e1 e2)
  from EOr.prems(1) show ?case
  proof (cases rule: evidence_EOr_cases)
    case L
    from L(1) EOr.prems(2) show ?thesis by (simp add: kor_def)
  next
    case R
    from R(2) EOr.prems(2) show ?thesis by (simp add: kor_def)
  next
    case (J X1 A1 U1 X2 A2 U2)
    have h: "\<forall>x \<in> set X1. \<sigma>' x = \<sigma> x" "\<forall>x \<in> set A1 \<union> set U1. \<sigma>' x = None"
      "\<forall>x \<in> set X2. \<sigma>' x = \<sigma> x" "\<forall>x \<in> set A2 \<union> set U2. \<sigma>' x = None"
      using EOr.prems(3,4) J(5-7) by auto
    have s1: "eval e1 \<sigma>' = eval e1 \<sigma>"
    proof (cases "eval e1 \<sigma>")
      case None
      from EOr.IH(1)[OF J(3) None h(1,2)] None show ?thesis by simp
    next
      case (Some v)
      have "\<forall>x \<in> set A1. \<sigma>' x = None" using h(2) by auto
      from evidence_definite[OF J(3) Some h(1) this] Some show ?thesis by simp
    qed
    have s2: "eval e2 \<sigma>' = eval e2 \<sigma>"
    proof (cases "eval e2 \<sigma>")
      case None
      from EOr.IH(2)[OF J(4) None h(3,4)] None show ?thesis by simp
    next
      case (Some v)
      have "\<forall>x \<in> set A2. \<sigma>' x = None" using h(4) by auto
      from evidence_definite[OF J(4) Some h(3) this] Some show ?thesis by simp
    qed
    from EOr.prems(2) s1 s2 show ?thesis by simp
  qed
next
  case (EImp e1 e2)
  from EImp.prems(1) show ?case
  proof (cases rule: evidence_EImp_cases)
    case L
    from L(1) EImp.prems(2) show ?thesis by (simp add: kimp_def)
  next
    case R
    from R(2) EImp.prems(2) show ?thesis by (simp add: kimp_def)
  next
    case (J X1 A1 U1 X2 A2 U2)
    have h: "\<forall>x \<in> set X1. \<sigma>' x = \<sigma> x" "\<forall>x \<in> set A1 \<union> set U1. \<sigma>' x = None"
      "\<forall>x \<in> set X2. \<sigma>' x = \<sigma> x" "\<forall>x \<in> set A2 \<union> set U2. \<sigma>' x = None"
      using EImp.prems(3,4) J(5-7) by auto
    have s1: "eval e1 \<sigma>' = eval e1 \<sigma>"
    proof (cases "eval e1 \<sigma>")
      case None
      from EImp.IH(1)[OF J(3) None h(1,2)] None show ?thesis by simp
    next
      case (Some v)
      have "\<forall>x \<in> set A1. \<sigma>' x = None" using h(2) by auto
      from evidence_definite[OF J(3) Some h(1) this] Some show ?thesis by simp
    qed
    have s2: "eval e2 \<sigma>' = eval e2 \<sigma>"
    proof (cases "eval e2 \<sigma>")
      case None
      from EImp.IH(2)[OF J(4) None h(3,4)] None show ?thesis by simp
    next
      case (Some v)
      have "\<forall>x \<in> set A2. \<sigma>' x = None" using h(4) by auto
      from evidence_definite[OF J(4) Some h(3) this] Some show ?thesis by simp
    qed
    from EImp.prems(2) s1 s2 show ?thesis by simp
  qed
qed (auto split: option.splits)

text \<open>With the read values kept, the read absences kept and values for all awaited names,
  the value is defined, whatever it was.\<close>

lemma evidence_defined:
  "\<lbrakk>evidence c \<sigma> = (X, A, U); \<forall>x \<in> set X. \<sigma>' x = \<sigma> x; \<forall>x \<in> set A. \<sigma>' x = None;
    set U \<subseteq> dom \<sigma>'\<rbrakk> \<Longrightarrow> eval c \<sigma>' \<noteq> None"
proof (induction c arbitrary: X A U)
  case (EEq a1 a2)
  from EEq.prems(1) have j: "ejoin (evidV a1 \<sigma>) (evidV a2 \<sigma>) = (X, A, U)" by simp
  from pair_resolved[OF j EEq.prems(2,3,4)] show ?case by (auto split: option.splits)
next
  case (ELt a1 a2)
  from ELt.prems(1) have j: "ejoin (evidV a1 \<sigma>) (evidV a2 \<sigma>) = (X, A, U)" by simp
  from pair_resolved[OF j ELt.prems(2,3,4)] show ?case by (auto split: option.splits)
next
  case (ELe a1 a2)
  from ELe.prems(1) have j: "ejoin (evidV a1 \<sigma>) (evidV a2 \<sigma>) = (X, A, U)" by simp
  from pair_resolved[OF j ELe.prems(2,3,4)] show ?case by (auto split: option.splits)
next
  case (ENot e)
  from ENot.prems(1) have ev: "evidence e \<sigma> = (X, A, U)" by simp
  from ENot.IH[OF ev ENot.prems(2,3,4)] show ?case by (simp add: knot_None)
next
  case (EAnd e1 e2)
  from EAnd.prems(1) show ?case
  proof (cases rule: evidence_EAnd_cases)
    case L
    from evidence_definite[OF L(2) L(1) EAnd.prems(2,3)] have "eval e1 \<sigma>' = Some False" .
    then show ?thesis by (simp add: kand_def)
  next
    case R
    from evidence_definite[OF R(3) R(2) EAnd.prems(2,3)] have "eval e2 \<sigma>' = Some False" .
    then show ?thesis by (simp add: kand_def)
  next
    case (J X1 A1 U1 X2 A2 U2)
    have h: "\<forall>x \<in> set X1. \<sigma>' x = \<sigma> x" "\<forall>x \<in> set A1. \<sigma>' x = None" "set U1 \<subseteq> dom \<sigma>'"
      "\<forall>x \<in> set X2. \<sigma>' x = \<sigma> x" "\<forall>x \<in> set A2. \<sigma>' x = None" "set U2 \<subseteq> dom \<sigma>'"
      using EAnd.prems(2,3,4) J(5-7) by auto
    from kand_not_None[OF EAnd.IH(1)[OF J(3) h(1-3)] EAnd.IH(2)[OF J(4) h(4-6)]]
    show ?thesis by simp
  qed
next
  case (EOr e1 e2)
  from EOr.prems(1) show ?case
  proof (cases rule: evidence_EOr_cases)
    case L
    from evidence_definite[OF L(2) L(1) EOr.prems(2,3)] have "eval e1 \<sigma>' = Some True" .
    then show ?thesis by (simp add: kor_def)
  next
    case R
    from evidence_definite[OF R(3) R(2) EOr.prems(2,3)] have "eval e2 \<sigma>' = Some True" .
    then show ?thesis by (simp add: kor_def)
  next
    case (J X1 A1 U1 X2 A2 U2)
    have h: "\<forall>x \<in> set X1. \<sigma>' x = \<sigma> x" "\<forall>x \<in> set A1. \<sigma>' x = None" "set U1 \<subseteq> dom \<sigma>'"
      "\<forall>x \<in> set X2. \<sigma>' x = \<sigma> x" "\<forall>x \<in> set A2. \<sigma>' x = None" "set U2 \<subseteq> dom \<sigma>'"
      using EOr.prems(2,3,4) J(5-7) by auto
    from kor_not_None[OF EOr.IH(1)[OF J(3) h(1-3)] EOr.IH(2)[OF J(4) h(4-6)]]
    show ?thesis by simp
  qed
next
  case (EImp e1 e2)
  from EImp.prems(1) show ?case
  proof (cases rule: evidence_EImp_cases)
    case L
    from evidence_definite[OF L(2) L(1) EImp.prems(2,3)] have "eval e1 \<sigma>' = Some False" .
    then show ?thesis by (simp add: kimp_def)
  next
    case R
    from evidence_definite[OF R(3) R(2) EImp.prems(2,3)] have "eval e2 \<sigma>' = Some True" .
    then show ?thesis by (simp add: kimp_def)
  next
    case (J X1 A1 U1 X2 A2 U2)
    have h: "\<forall>x \<in> set X1. \<sigma>' x = \<sigma> x" "\<forall>x \<in> set A1. \<sigma>' x = None" "set U1 \<subseteq> dom \<sigma>'"
      "\<forall>x \<in> set X2. \<sigma>' x = \<sigma> x" "\<forall>x \<in> set A2. \<sigma>' x = None" "set U2 \<subseteq> dom \<sigma>'"
      using EImp.prems(2,3,4) J(5-7) by auto
    from kimp_not_None[OF EImp.IH(1)[OF J(3) h(1-3)] EImp.IH(2)[OF J(4) h(4-6)]]
    show ?thesis by simp
  qed
qed (auto split: option.splits)

lemma evidence_undefined_resolved:
  "\<lbrakk>evidence c \<sigma> = (X, A, U); eval c \<sigma> = None; \<forall>x \<in> set X. \<sigma>' x = \<sigma> x;
    \<forall>x \<in> set A. \<sigma>' x = None; set U \<subseteq> dom \<sigma>'\<rbrakk> \<Longrightarrow> eval c \<sigma>' \<noteq> None"
  by (rule evidence_defined)

lemma evidence_undefined_pf:
  assumes "present_free c" and "evidence c \<sigma> = (X, A, U)" and "eval c \<sigma> = None"
    and "\<sigma> \<sqsubseteq> \<sigma>'" and "set U \<subseteq> dom \<sigma>'"
  shows "eval c \<sigma>' \<noteq> None"
proof -
  from evidence_present_free[OF assms(1,2)] have ha: "\<forall>x \<in> set A. \<sigma>' x = None" by simp
  have dx: "set X \<subseteq> dom \<sigma>" using evidence_shape[OF assms(2)] by blast
  have hx: "\<forall>x \<in> set X. \<sigma>' x = \<sigma> x"
  proof
    fix x assume "x \<in> set X"
    with dx have "x \<in> dom \<sigma>" by blast
    from domD[OF this] obtain v where v: "\<sigma> x = Some v" by blast
    from info_leD[OF assms(4) v] v show "\<sigma>' x = \<sigma> x" by simp
  qed
  from evidence_defined[OF assms(2) hx ha assms(5)] show ?thesis .
qed


section \<open>A supporting set is checked by one evaluation\<close>

lemma supports_sound:
  assumes "present_free c" and "supports X c \<sigma> b" and "\<forall>x \<in> X. \<sigma>' x = \<sigma> x"
  shows "eval c \<sigma>' = Some b"
proof -
  have e: "eval c (\<sigma> |` X) = Some b" using assms(2) by (simp add: supports_def)
  have "\<sigma> |` X \<sqsubseteq> \<sigma>'" unfolding info_le_def
  proof
    fix x assume "x \<in> dom (\<sigma> |` X)"
    then have x: "x \<in> X" by simp
    with assms(3) show "\<sigma>' x = (\<sigma> |` X) x" by simp
  qed
  from T2_monotone[OF assms(1) this e] show ?thesis .
qed

lemma supports_mono:
  assumes "present_free c" and "X \<subseteq> Y" and "supports X c \<sigma> b"
  shows "supports Y c \<sigma> b"
proof -
  have "\<forall>x \<in> X. (\<sigma> |` Y) x = \<sigma> x" using assms(2) by auto
  from supports_sound[OF assms(1,3) this] show ?thesis by (simp add: supports_def)
qed

lemma evidence_supports:
  assumes "present_free c" and "evidence c \<sigma> = (X, A, U)" and "eval c \<sigma> = Some b"
  shows "supports (set X) c \<sigma> b"
proof -
  have "\<forall>x \<in> set X. (\<sigma> |` set X) x = \<sigma> x" by simp
  from evidence_definite_pf[OF assms(1,2,3) this] show ?thesis by (simp add: supports_def)
qed


section \<open>The decisions of the monitor with their evidence\<close>

lemma monitor_evidence_decisions:
  "map (\<lambda>(j, v, w). (j, v \<noteq> Some False)) (monitor_evidence s a c \<pi>) = monitor_decisions s a c \<pi>"
  by (simp add: monitor_evidence_def monitor_decisions_def blocks_def comp_def)

lemma monitor_evidence_append:
  "\<exists>ws. monitor_evidence s a c (\<pi> @ \<rho>) = monitor_evidence s a c \<pi> @ ws"
proof (cases "\<pi> = []")
  case True
  then show ?thesis by (simp add: monitor_evidence_def)
next
  case False
  then have l1: "1 \<le> length \<pi>" by (cases \<pi>) simp_all
  have u: "[1..<length (\<pi> @ \<rho>)] = [1..<length \<pi>] @ [length \<pi>..<length \<pi> + length \<rho>]"
    unfolding length_append by (rule upt_add_eq_append[OF l1])
  have f: "filter (\<lambda>j. does s a (evt ((\<pi> @ \<rho>) ! j))) [1..<length \<pi>]
           = filter (\<lambda>j. does s a (evt (\<pi> ! j))) [1..<length \<pi>]"
    by (rule filter_cong) simp_all
  have m: "map (\<lambda>j. (j, eval c (st (\<pi> @ \<rho>) (j - 1)), evidence c (st (\<pi> @ \<rho>) (j - 1))))
             (filter (\<lambda>j. does s a (evt (\<pi> ! j))) [1..<length \<pi>])
           = map (\<lambda>j. (j, eval c (st \<pi> (j - 1)), evidence c (st \<pi> (j - 1))))
             (filter (\<lambda>j. does s a (evt (\<pi> ! j))) [1..<length \<pi>])"
    by (rule map_cong) (auto simp: less_imp_diff_less)
  show ?thesis
    unfolding monitor_evidence_def u filter_append map_append f m by blast
qed

lemma monitor_evidence_stable:
  "\<lbrakk>(j, Some b, (X, A, U)) \<in> set (monitor_evidence s a c \<pi>); length \<pi>' = length \<pi>;
    evt (\<pi>' ! j) = evt (\<pi> ! j); \<forall>x \<in> set X. st \<pi>' (j - 1) x = st \<pi> (j - 1) x;
    \<forall>x \<in> set A. st \<pi>' (j - 1) x = None\<rbrakk> \<Longrightarrow> (j, b) \<in> set (monitor_decisions s a c \<pi>')"
proof -
  assume m: "(j, Some b, (X, A, U)) \<in> set (monitor_evidence s a c \<pi>)"
    and l: "length \<pi>' = length \<pi>" and ev: "evt (\<pi>' ! j) = evt (\<pi> ! j)"
    and hx: "\<forall>x \<in> set X. st \<pi>' (j - 1) x = st \<pi> (j - 1) x"
    and ha: "\<forall>x \<in> set A. st \<pi>' (j - 1) x = None"
  from m have j: "1 \<le> j" "j < length \<pi>" "does s a (evt (\<pi> ! j))"
    and e: "eval c (st \<pi> (j - 1)) = Some b" "evidence c (st \<pi> (j - 1)) = (X, A, U)"
    by (auto simp: monitor_evidence_def image_iff)
  from evidence_definite[OF e(2) e(1) hx ha] have "eval c (st \<pi>' (j - 1)) = Some b" .
  with j l ev show ?thesis by (simp add: monitor_decisions_iff blocks_def)
qed

end
