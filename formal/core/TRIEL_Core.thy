(*  Title:      TRIEL_Core.thy
    Purpose:    A small core of the TRIEL specification language:
                states as partial maps, the information order, strong-Kleene
                three-valued evaluation of boolean expressions, PRESENT,
                and five theorems (T1-T5) about that semantics.
    Source:     Public description only (github.com/triel-lang/grammar,
                TECHNICAL_REPORT.md section 2.9, FOUNDATIONS.md).
*)

theory TRIEL_Core
  imports Main
begin

section \<open>States and the information order\<close>

text \<open>Names and values are arbitrary types, represented by the type variables
  \<^typ>\<open>'n\<close> and \<^typ>\<open>'v\<close>. A state is a partial map from names to values;
  a name outside the domain is absent (empty or stale).\<close>

type_synonym ('n, 'v) state = "'n \<rightharpoonup> 'v"

definition info_le :: "('n, 'v) state \<Rightarrow> ('n, 'v) state \<Rightarrow> bool" (infix \<open>\<sqsubseteq>\<close> 50)
  where "\<sigma> \<sqsubseteq> \<sigma>' \<longleftrightarrow> (\<forall>x \<in> dom \<sigma>. \<sigma>' x = \<sigma> x)"

text \<open>The information order is exactly HOL's map ordering, hence a partial order.\<close>

lemma info_le_map_le: "\<sigma> \<sqsubseteq> \<sigma>' \<longleftrightarrow> \<sigma> \<subseteq>\<^sub>m \<sigma>'"
  unfolding info_le_def map_le_def by (simp add: eq_commute)

lemma info_leD: "\<sigma> \<sqsubseteq> \<sigma>' \<Longrightarrow> \<sigma> x = Some v \<Longrightarrow> \<sigma>' x = Some v"
  unfolding info_le_def by (metis domI)

lemma info_le_refl: "\<sigma> \<sqsubseteq> \<sigma>"
  by (simp add: info_le_map_le)

lemma info_le_trans: "\<sigma>\<^sub>1 \<sqsubseteq> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>2 \<sqsubseteq> \<sigma>\<^sub>3 \<Longrightarrow> \<sigma>\<^sub>1 \<sqsubseteq> \<sigma>\<^sub>3"
  unfolding info_le_map_le by (rule map_le_trans)

lemma info_le_antisym: "\<sigma> \<sqsubseteq> \<sigma>' \<Longrightarrow> \<sigma>' \<sqsubseteq> \<sigma> \<Longrightarrow> \<sigma> = \<sigma>'"
  unfolding info_le_map_le by (rule map_le_antisym)


section \<open>Syntax\<close>

text \<open>Expressions are two-sorted. Value expressions (value constants and names)
  denote values; they occur only as operands of the equality comparison.
  Boolean expressions are the literals true/false, equality, NOT, AND, OR,
  IMPLIES and PRESENT(name). This is what lets
  \<open>eval :: expr \<Rightarrow> state \<Rightarrow> bool option\<close> be well typed.\<close>

datatype ('n, 'v) vexp =
    VConst 'v       \<comment> \<open>value constant\<close>
  | VName 'n        \<comment> \<open>name\<close>

datatype ('n, 'v) expr =
    ETrue                                         \<comment> \<open>literal true\<close>
  | EFalse                                        \<comment> \<open>literal false\<close>
  | EEq "('n, 'v) vexp" "('n, 'v) vexp"           \<comment> \<open>a = b\<close>
  | ENot "('n, 'v) expr"                          \<comment> \<open>NOT e\<close>
  | EAnd "('n, 'v) expr" "('n, 'v) expr"          \<comment> \<open>e AND e\<close>
  | EOr "('n, 'v) expr" "('n, 'v) expr"           \<comment> \<open>e OR e\<close>
  | EImp "('n, 'v) expr" "('n, 'v) expr"          \<comment> \<open>e IMPLIES e\<close>
  | EPresent 'n                                   \<comment> \<open>PRESENT(x)\<close>


section \<open>Strong Kleene connectives\<close>

text \<open>Truth values are \<^typ>\<open>bool option\<close>; \<^term>\<open>None\<close> is undefined (\<open>\<bottom>\<close>).
  Each definition transcribes the rule stated in TECHNICAL_REPORT.md section 2.9.\<close>

fun knot :: "bool option \<Rightarrow> bool option" where
  "knot (Some b) = Some (\<not> b)"
| "knot None = None"

definition kand :: "bool option \<Rightarrow> bool option \<Rightarrow> bool option" where
  "kand p q =
     (if p = Some False \<or> q = Some False then Some False
      else if p = Some True \<and> q = Some True then Some True
      else None)"

definition kor :: "bool option \<Rightarrow> bool option \<Rightarrow> bool option" where
  "kor p q =
     (if p = Some True \<or> q = Some True then Some True
      else if p = Some False \<and> q = Some False then Some False
      else None)"

definition kimp :: "bool option \<Rightarrow> bool option \<Rightarrow> bool option" where
  "kimp p q =
     (if p = Some False \<or> q = Some True then Some True
      else if p = Some True \<and> q = Some False then Some False
      else None)"

lemma bool_option_cases: "p = None \<or> p = Some True \<or> p = Some False"
  by (cases p) auto

text \<open>On defined arguments the connectives are the classical ones.\<close>

lemma kand_Some [simp]: "kand (Some a) (Some b) = Some (a \<and> b)"
  by (simp add: kand_def)

lemma kor_Some [simp]: "kor (Some a) (Some b) = Some (a \<or> b)"
  by (simp add: kor_def)

lemma kimp_Some [simp]: "kimp (Some a) (Some b) = Some (a \<longrightarrow> b)"
  by (simp add: kimp_def)

text \<open>IMPLIES coincides with the usual encoding \<open>NOT p OR q\<close>.\<close>

lemma kimp_kor_knot: "kimp p q = kor (knot p) q"
  using bool_option_cases[of p] bool_option_cases[of q]
  by (auto simp: kimp_def kor_def)


section \<open>Evaluation\<close>

primrec evalV :: "('n, 'v) vexp \<Rightarrow> ('n, 'v) state \<Rightarrow> 'v option" where
  "evalV (VConst v) \<sigma> = Some v"
| "evalV (VName x) \<sigma> = \<sigma> x"

primrec eval :: "('n, 'v) expr \<Rightarrow> ('n, 'v) state \<Rightarrow> bool option" where
  "eval ETrue \<sigma> = Some True"
| "eval EFalse \<sigma> = Some False"
| "eval (EEq a b) \<sigma> =
     (case evalV a \<sigma> of
        None \<Rightarrow> None
      | Some u \<Rightarrow> (case evalV b \<sigma> of None \<Rightarrow> None | Some w \<Rightarrow> Some (u = w)))"
| "eval (ENot e) \<sigma> = knot (eval e \<sigma>)"
| "eval (EAnd e\<^sub>1 e\<^sub>2) \<sigma> = kand (eval e\<^sub>1 \<sigma>) (eval e\<^sub>2 \<sigma>)"
| "eval (EOr e\<^sub>1 e\<^sub>2) \<sigma> = kor (eval e\<^sub>1 \<sigma>) (eval e\<^sub>2 \<sigma>)"
| "eval (EImp e\<^sub>1 e\<^sub>2) \<sigma> = kimp (eval e\<^sub>1 \<sigma>) (eval e\<^sub>2 \<sigma>)"
| "eval (EPresent x) \<sigma> = Some (x \<in> dom \<sigma>)"

text \<open>PRESENT is always defined.\<close>

lemma eval_present_defined: "eval (EPresent x) \<sigma> \<noteq> None"
  by simp


section \<open>T1: algebraic laws\<close>

lemma kand_commute: "kand p q = kand q p"
  using bool_option_cases[of p] bool_option_cases[of q]
  by (auto simp: kand_def)

lemma kor_commute: "kor p q = kor q p"
  using bool_option_cases[of p] bool_option_cases[of q]
  by (auto simp: kor_def)

lemma kand_assoc: "kand (kand p q) r = kand p (kand q r)"
  using bool_option_cases[of p] bool_option_cases[of q] bool_option_cases[of r]
  by (auto simp: kand_def)

lemma kor_assoc: "kor (kor p q) r = kor p (kor q r)"
  using bool_option_cases[of p] bool_option_cases[of q] bool_option_cases[of r]
  by (auto simp: kor_def)

lemma knot_kand: "knot (kand p q) = kor (knot p) (knot q)"
  using bool_option_cases[of p] bool_option_cases[of q]
  by (auto simp: kand_def kor_def)

lemma knot_kor: "knot (kor p q) = kand (knot p) (knot q)"
  using bool_option_cases[of p] bool_option_cases[of q]
  by (auto simp: kand_def kor_def)

lemma knot_knot: "knot (knot p) = p"
  by (cases p) simp_all

theorem T1_and_commute: "eval (EAnd e\<^sub>1 e\<^sub>2) \<sigma> = eval (EAnd e\<^sub>2 e\<^sub>1) \<sigma>"
  by (simp add: kand_commute)

theorem T1_or_commute: "eval (EOr e\<^sub>1 e\<^sub>2) \<sigma> = eval (EOr e\<^sub>2 e\<^sub>1) \<sigma>"
  by (simp add: kor_commute)

theorem T1_and_assoc: "eval (EAnd (EAnd e\<^sub>1 e\<^sub>2) e\<^sub>3) \<sigma> = eval (EAnd e\<^sub>1 (EAnd e\<^sub>2 e\<^sub>3)) \<sigma>"
  by (simp add: kand_assoc)

theorem T1_or_assoc: "eval (EOr (EOr e\<^sub>1 e\<^sub>2) e\<^sub>3) \<sigma> = eval (EOr e\<^sub>1 (EOr e\<^sub>2 e\<^sub>3)) \<sigma>"
  by (simp add: kor_assoc)

theorem T1_de_morgan_and: "eval (ENot (EAnd e\<^sub>1 e\<^sub>2)) \<sigma> = eval (EOr (ENot e\<^sub>1) (ENot e\<^sub>2)) \<sigma>"
  by (simp add: knot_kand)

theorem T1_de_morgan_or: "eval (ENot (EOr e\<^sub>1 e\<^sub>2)) \<sigma> = eval (EAnd (ENot e\<^sub>1) (ENot e\<^sub>2)) \<sigma>"
  by (simp add: knot_kor)

theorem T1_not_not: "eval (ENot (ENot e)) \<sigma> = eval e \<sigma>"
  by (simp add: knot_knot)


section \<open>T2: monotonicity of PRESENT-free expressions\<close>

primrec present_free :: "('n, 'v) expr \<Rightarrow> bool" where
  "present_free ETrue = True"
| "present_free EFalse = True"
| "present_free (EEq a b) = True"
| "present_free (ENot e) = present_free e"
| "present_free (EAnd e\<^sub>1 e\<^sub>2) = (present_free e\<^sub>1 \<and> present_free e\<^sub>2)"
| "present_free (EOr e\<^sub>1 e\<^sub>2) = (present_free e\<^sub>1 \<and> present_free e\<^sub>2)"
| "present_free (EImp e\<^sub>1 e\<^sub>2) = (present_free e\<^sub>1 \<and> present_free e\<^sub>2)"
| "present_free (EPresent x) = False"

text \<open>Definedness order on partial results: \<open>p \<preceq> q\<close> iff every value \<open>p\<close> has
  is also the value of \<open>q\<close> (\<open>\<bottom>\<close> is below everything).\<close>

definition approx :: "'a option \<Rightarrow> 'a option \<Rightarrow> bool" (infix \<open>\<preceq>\<close> 50)
  where "p \<preceq> q \<longleftrightarrow> (\<forall>b. p = Some b \<longrightarrow> q = Some b)"

lemma approx_iff: "p \<preceq> q \<longleftrightarrow> p = None \<or> p = q"
  by (cases p) (auto simp: approx_def)

lemma approx_refl [simp]: "p \<preceq> p"
  by (simp add: approx_def)

lemma knot_mono: "p \<preceq> p' \<Longrightarrow> knot p \<preceq> knot p'"
  by (auto simp: approx_iff)

lemma kand_mono: "p \<preceq> p' \<Longrightarrow> q \<preceq> q' \<Longrightarrow> kand p q \<preceq> kand p' q'"
  using bool_option_cases[of p] bool_option_cases[of q]
        bool_option_cases[of p'] bool_option_cases[of q']
  by (auto simp: approx_iff kand_def)

lemma kor_mono: "p \<preceq> p' \<Longrightarrow> q \<preceq> q' \<Longrightarrow> kor p q \<preceq> kor p' q'"
  using bool_option_cases[of p] bool_option_cases[of q]
        bool_option_cases[of p'] bool_option_cases[of q']
  by (auto simp: approx_iff kor_def)

lemma kimp_mono: "p \<preceq> p' \<Longrightarrow> q \<preceq> q' \<Longrightarrow> kimp p q \<preceq> kimp p' q'"
  using bool_option_cases[of p] bool_option_cases[of q]
        bool_option_cases[of p'] bool_option_cases[of q']
  by (auto simp: approx_iff kimp_def)

lemma evalV_mono: "\<sigma> \<sqsubseteq> \<sigma>' \<Longrightarrow> evalV a \<sigma> \<preceq> evalV a \<sigma>'"
  by (cases a) (auto simp: approx_def intro: info_leD)

lemma eval_mono: "present_free e \<Longrightarrow> \<sigma> \<sqsubseteq> \<sigma>' \<Longrightarrow> eval e \<sigma> \<preceq> eval e \<sigma>'"
proof (induction e)
  case (EEq a b)
  then have "evalV a \<sigma> \<preceq> evalV a \<sigma>'" "evalV b \<sigma> \<preceq> evalV b \<sigma>'"
    by (simp_all add: evalV_mono)
  then show ?case
    by (auto simp: approx_iff split: option.splits)
qed (simp_all add: knot_mono kand_mono kor_mono kimp_mono)

theorem T2_monotone:
  assumes "present_free e" and "\<sigma> \<sqsubseteq> \<sigma>'" and "eval e \<sigma> = Some b"
  shows "eval e \<sigma>' = Some b"
  using eval_mono[OF assms(1,2)] assms(3) by (simp add: approx_def)


section \<open>T3: PRESENT is not monotone\<close>

lemma present_flips:
  assumes "x \<notin> dom \<sigma>"
  shows "\<sigma> \<sqsubseteq> \<sigma>(x \<mapsto> v)"
    and "eval (EPresent x) \<sigma> = Some False"
    and "eval (EPresent x) (\<sigma>(x \<mapsto> v)) = Some True"
  using assms by (auto simp: info_le_def)

theorem T3_present_not_monotone:
  "\<exists>(\<sigma> :: ('n, 'v) state) \<sigma>' x. \<sigma> \<sqsubseteq> \<sigma>' \<and> eval (EPresent x) \<sigma> \<noteq> eval (EPresent x) \<sigma>'"
proof -
  fix x :: 'n and v :: 'v
  have "(Map.empty :: ('n, 'v) state) \<sqsubseteq> [x \<mapsto> v]"
    by (simp add: info_le_def)
  moreover have "eval (EPresent x) (Map.empty :: ('n, 'v) state) \<noteq> eval (EPresent x) [x \<mapsto> v]"
    by simp
  ultimately show ?thesis
    by blast
qed


section \<open>T4: agreement with two-valued logic\<close>

text \<open>Names occurring in value positions (operands of comparisons). The argument
  of PRESENT is not included: PRESENT never needs the name's value.\<close>

primrec vnames :: "('n, 'v) vexp \<Rightarrow> 'n set" where
  "vnames (VConst v) = {}"
| "vnames (VName x) = {x}"

primrec names :: "('n, 'v) expr \<Rightarrow> 'n set" where
  "names ETrue = {}"
| "names EFalse = {}"
| "names (EEq a b) = vnames a \<union> vnames b"
| "names (ENot e) = names e"
| "names (EAnd e\<^sub>1 e\<^sub>2) = names e\<^sub>1 \<union> names e\<^sub>2"
| "names (EOr e\<^sub>1 e\<^sub>2) = names e\<^sub>1 \<union> names e\<^sub>2"
| "names (EImp e\<^sub>1 e\<^sub>2) = names e\<^sub>1 \<union> names e\<^sub>2"
| "names (EPresent x) = {}"

text \<open>Classical two-valued semantics over a total valuation \<open>\<rho>\<close> and a set \<open>D\<close>
  of present names (PRESENT is a plain two-valued predicate here).\<close>

primrec cevalV :: "('n, 'v) vexp \<Rightarrow> ('n \<Rightarrow> 'v) \<Rightarrow> 'v" where
  "cevalV (VConst v) \<rho> = v"
| "cevalV (VName x) \<rho> = \<rho> x"

primrec ceval :: "('n, 'v) expr \<Rightarrow> 'n set \<Rightarrow> ('n \<Rightarrow> 'v) \<Rightarrow> bool" where
  "ceval ETrue D \<rho> = True"
| "ceval EFalse D \<rho> = False"
| "ceval (EEq a b) D \<rho> = (cevalV a \<rho> = cevalV b \<rho>)"
| "ceval (ENot e) D \<rho> = (\<not> ceval e D \<rho>)"
| "ceval (EAnd e\<^sub>1 e\<^sub>2) D \<rho> = (ceval e\<^sub>1 D \<rho> \<and> ceval e\<^sub>2 D \<rho>)"
| "ceval (EOr e\<^sub>1 e\<^sub>2) D \<rho> = (ceval e\<^sub>1 D \<rho> \<or> ceval e\<^sub>2 D \<rho>)"
| "ceval (EImp e\<^sub>1 e\<^sub>2) D \<rho> = (ceval e\<^sub>1 D \<rho> \<longrightarrow> ceval e\<^sub>2 D \<rho>)"
| "ceval (EPresent x) D \<rho> = (x \<in> D)"

lemma evalV_classical:
  assumes "vnames a \<subseteq> dom \<sigma>" and "\<forall>x \<in> dom \<sigma>. \<sigma> x = Some (\<rho> x)"
  shows "evalV a \<sigma> = Some (cevalV a \<rho>)"
  using assms by (cases a) auto

lemma eval_classical:
  assumes "names e \<subseteq> dom \<sigma>" and "\<forall>x \<in> dom \<sigma>. \<sigma> x = Some (\<rho> x)"
  shows "eval e \<sigma> = Some (ceval e (dom \<sigma>) \<rho>)"
  using assms(1)
proof (induction e)
  case (EEq a b)
  then have "vnames a \<subseteq> dom \<sigma>" "vnames b \<subseteq> dom \<sigma>"
    by simp_all
  then show ?case
    using evalV_classical[OF _ assms(2)] by simp
qed auto

text \<open>T4: if every name of \<open>e\<close> is defined in \<open>\<sigma>\<close>, then \<open>e\<close> is defined in \<open>\<sigma>\<close>, and its
  value is the classical value of \<open>e\<close> under any total valuation \<open>\<rho>\<close> extending \<open>\<sigma>\<close>
  (in particular under \<open>\<lambda>x. the (\<sigma> x)\<close>).\<close>

theorem T4_classical:
  assumes "names e \<subseteq> dom \<sigma>" and "\<forall>x \<in> dom \<sigma>. \<sigma> x = Some (\<rho> x)"
  shows "eval e \<sigma> \<noteq> None" and "eval e \<sigma> = Some (ceval e (dom \<sigma>) \<rho>)"
  using eval_classical[OF assms] by simp_all

corollary T4_classical_the:
  assumes "names e \<subseteq> dom \<sigma>"
  shows "eval e \<sigma> = Some (ceval e (dom \<sigma>) (\<lambda>x. the (\<sigma> x)))"
  by (rule eval_classical[OF assms]) auto

text \<open>If also every PRESENT argument is defined, PRESENT is just \<open>True\<close> and \<open>D\<close>
  can be taken to be the set of all names: a fully classical, total valuation.\<close>

primrec pnames :: "('n, 'v) expr \<Rightarrow> 'n set" where
  "pnames ETrue = {}"
| "pnames EFalse = {}"
| "pnames (EEq a b) = {}"
| "pnames (ENot e) = pnames e"
| "pnames (EAnd e\<^sub>1 e\<^sub>2) = pnames e\<^sub>1 \<union> pnames e\<^sub>2"
| "pnames (EOr e\<^sub>1 e\<^sub>2) = pnames e\<^sub>1 \<union> pnames e\<^sub>2"
| "pnames (EImp e\<^sub>1 e\<^sub>2) = pnames e\<^sub>1 \<union> pnames e\<^sub>2"
| "pnames (EPresent x) = {x}"

lemma ceval_present_UNIV: "pnames e \<subseteq> D \<Longrightarrow> ceval e D \<rho> = ceval e UNIV \<rho>"
  by (induction e) auto

corollary T4_total:
  assumes "names e \<union> pnames e \<subseteq> dom \<sigma>" and "\<forall>x \<in> dom \<sigma>. \<sigma> x = Some (\<rho> x)"
  shows "eval e \<sigma> = Some (ceval e UNIV \<rho>)"
  using assms eval_classical[of e \<sigma> \<rho>] ceval_present_UNIV[of e "dom \<sigma>" \<rho>] by simp


section \<open>T5: meaning of PRESENT\<close>

theorem T5_present: "eval (EPresent x) \<sigma> = Some True \<longleftrightarrow> x \<in> dom \<sigma>"
  by simp

end
