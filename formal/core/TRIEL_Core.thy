(*  Title:      TRIEL_Core.thy
    Purpose:    A small core of the TRIEL specification language:
                states as partial maps, the information order, strong-Kleene
                three-valued evaluation of boolean expressions, PRESENT,
                DEFAULT, the ordering comparisons, and five theorems (T1-T5)
                about that semantics.
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

text \<open>Expressions are two-sorted. Value expressions (value constants, names and
  DEFAULT(x, a)) denote values; they occur only as operands of the comparisons.
  Boolean expressions are the literals true/false, the comparisons \<open>=\<close>, \<open><\<close> and
  \<open>\<le>\<close>, NOT, AND, OR, IMPLIES and PRESENT(name). This is what lets
  \<open>eval :: expr \<Rightarrow> state \<Rightarrow> bool option\<close> be well typed.\<close>

datatype ('n, 'v) vexp =
    VConst 'v                       \<comment> \<open>value constant\<close>
  | VName 'n                        \<comment> \<open>name\<close>
  | VDefault 'n "('n, 'v) vexp"     \<comment> \<open>DEFAULT(x, a)\<close>

text \<open>The ordering comparisons need an order on values. The class \<open>value_order\<close> fixes
  the two relations and assumes nothing about them, so every theorem below holds for
  every choice. TRIEL_Exec instantiates them on its basic values: exact numbers
  (Integer and Decimal, TRIEL_Numbers) are compared as rationals.\<close>

class value_order =
  fixes vless :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and vleq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"

datatype ('n, 'v) expr =
    ETrue                                         \<comment> \<open>literal true\<close>
  | EFalse                                        \<comment> \<open>literal false\<close>
  | EEq "('n, 'v) vexp" "('n, 'v) vexp"           \<comment> \<open>a = b\<close>
  | ELt "('n, 'v) vexp" "('n, 'v) vexp"           \<comment> \<open>a < b\<close>
  | ELe "('n, 'v) vexp" "('n, 'v) vexp"           \<comment> \<open>a <= b\<close>
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

text \<open>DEFAULT(x, a) is the value of \<open>x\<close> when \<open>x\<close> has one, and the value of \<open>a\<close>
  otherwise (TECHNICAL_REPORT.md section 2.9).\<close>

primrec evalV :: "('n, 'v) vexp \<Rightarrow> ('n, 'v) state \<Rightarrow> 'v option" where
  "evalV (VConst v) \<sigma> = Some v"
| "evalV (VName x) \<sigma> = \<sigma> x"
| "evalV (VDefault x a) \<sigma> = (case \<sigma> x of Some v \<Rightarrow> Some v | None \<Rightarrow> evalV a \<sigma>)"

primrec eval :: "('n, 'v :: value_order) expr \<Rightarrow> ('n, 'v) state \<Rightarrow> bool option" where
  "eval ETrue \<sigma> = Some True"
| "eval EFalse \<sigma> = Some False"
| "eval (EEq a b) \<sigma> =
     (case evalV a \<sigma> of
        None \<Rightarrow> None
      | Some u \<Rightarrow> (case evalV b \<sigma> of None \<Rightarrow> None | Some w \<Rightarrow> Some (u = w)))"
| "eval (ELt a b) \<sigma> =
     (case evalV a \<sigma> of
        None \<Rightarrow> None
      | Some u \<Rightarrow> (case evalV b \<sigma> of None \<Rightarrow> None | Some w \<Rightarrow> Some (vless u w)))"
| "eval (ELe a b) \<sigma> =
     (case evalV a \<sigma> of
        None \<Rightarrow> None
      | Some u \<Rightarrow> (case evalV b \<sigma> of None \<Rightarrow> None | Some w \<Rightarrow> Some (vleq u w)))"
| "eval (ENot e) \<sigma> = knot (eval e \<sigma>)"
| "eval (EAnd e\<^sub>1 e\<^sub>2) \<sigma> = kand (eval e\<^sub>1 \<sigma>) (eval e\<^sub>2 \<sigma>)"
| "eval (EOr e\<^sub>1 e\<^sub>2) \<sigma> = kor (eval e\<^sub>1 \<sigma>) (eval e\<^sub>2 \<sigma>)"
| "eval (EImp e\<^sub>1 e\<^sub>2) \<sigma> = kimp (eval e\<^sub>1 \<sigma>) (eval e\<^sub>2 \<sigma>)"
| "eval (EPresent x) \<sigma> = Some (x \<in> dom \<sigma>)"

text \<open>DEFAULT(x, a) is x when PRESENT(x) is true, that is when x has a value (\<open>E\<^sub>x\<close>),
  and a otherwise.\<close>

lemma evalV_default: "evalV (VDefault x a) \<sigma> = (if x \<in> dom \<sigma> then \<sigma> x else evalV a \<sigma>)"
  by (auto split: option.splits)

text \<open>PRESENT is always defined.\<close>

lemma eval_present_defined: "eval (EPresent x) \<sigma> \<noteq> None"
  by simp

text \<open>A comparison with an operand that has no value is undefined, like every other
  condition of the core that reads an absent name.\<close>

theorem cmp_undefined:
  assumes "evalV a \<sigma> = None \<or> evalV b \<sigma> = None"
  shows "eval (EEq a b) \<sigma> = None" and "eval (ELt a b) \<sigma> = None" and "eval (ELe a b) \<sigma> = None"
  using assms by (auto split: option.splits)

corollary cmp_absent_name:
  assumes "x \<notin> dom \<sigma>"
  shows "eval (ELt (VName x) b) \<sigma> = None" and "eval (ELt b (VName x)) \<sigma> = None"
    and "eval (ELe (VName x) b) \<sigma> = None" and "eval (ELe b (VName x)) \<sigma> = None"
  using assms by (auto simp: domIff split: option.splits)


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

text \<open>Section 2.9 excepts PRESENT and DEFAULT from monotonicity. An expression is
  \<open>present_free\<close> if it contains neither: no PRESENT, and no DEFAULT in an operand of a
  comparison.\<close>

primrec default_free :: "('n, 'v) vexp \<Rightarrow> bool" where
  "default_free (VConst v) = True"
| "default_free (VName x) = True"
| "default_free (VDefault x a) = False"

primrec present_free :: "('n, 'v) expr \<Rightarrow> bool" where
  "present_free ETrue = True"
| "present_free EFalse = True"
| "present_free (EEq a b) = (default_free a \<and> default_free b)"
| "present_free (ELt a b) = (default_free a \<and> default_free b)"
| "present_free (ELe a b) = (default_free a \<and> default_free b)"
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

lemma evalV_mono: "default_free a \<Longrightarrow> \<sigma> \<sqsubseteq> \<sigma>' \<Longrightarrow> evalV a \<sigma> \<preceq> evalV a \<sigma>'"
  by (cases a) (auto simp: approx_def intro: info_leD)

lemma eval_mono: "present_free e \<Longrightarrow> \<sigma> \<sqsubseteq> \<sigma>' \<Longrightarrow> eval e \<sigma> \<preceq> eval e \<sigma>'"
proof (induction e)
  case (EEq a b)
  then have "evalV a \<sigma> \<preceq> evalV a \<sigma>'" "evalV b \<sigma> \<preceq> evalV b \<sigma>'"
    by (simp_all add: evalV_mono)
  then show ?case
    by (auto simp: approx_iff split: option.splits)
next
  case (ELt a b)
  then have "evalV a \<sigma> \<preceq> evalV a \<sigma>'" "evalV b \<sigma> \<preceq> evalV b \<sigma>'"
    by (simp_all add: evalV_mono)
  then show ?case
    by (auto simp: approx_iff split: option.splits)
next
  case (ELe a b)
  then have "evalV a \<sigma> \<preceq> evalV a \<sigma>'" "evalV b \<sigma> \<preceq> evalV b \<sigma>'"
    by (simp_all add: evalV_mono)
  then show ?case
    by (auto simp: approx_iff split: option.splits)
qed (simp_all add: knot_mono kand_mono kor_mono kimp_mono)

theorem T2_monotone:
  assumes "present_free e" and "\<sigma> \<sqsubseteq> \<sigma>'" and "eval e \<sigma> = Some b"
  shows "eval e \<sigma>' = Some b"
  using eval_mono[OF assms(1,2)] assms(3) by (simp add: approx_def)

text \<open>A comparison without DEFAULT is PRESENT-free, so it is monotone: a definite answer
  of \<open>a = b\<close>, \<open>a < b\<close> or \<open>a \<le> b\<close> survives every extension of the state.\<close>

corollary cmp_mono:
  assumes "default_free a" and "default_free b" and "\<sigma> \<sqsubseteq> \<sigma>'"
  shows "eval (EEq a b) \<sigma> \<preceq> eval (EEq a b) \<sigma>'"
    and "eval (ELt a b) \<sigma> \<preceq> eval (ELt a b) \<sigma>'"
    and "eval (ELe a b) \<sigma> \<preceq> eval (ELe a b) \<sigma>'"
  by (rule eval_mono[OF _ assms(3)], simp add: assms(1,2))+


section \<open>T3: PRESENT is not monotone\<close>

lemma present_flips:
  assumes "x \<notin> dom \<sigma>"
  shows "\<sigma> \<sqsubseteq> \<sigma>(x \<mapsto> v)"
    and "eval (EPresent x) \<sigma> = Some False"
    and "eval (EPresent x) (\<sigma>(x \<mapsto> v)) = Some True"
  using assms by (auto simp: info_le_def)

theorem T3_present_not_monotone:
  "\<exists>(\<sigma> :: ('n, 'v :: value_order) state) \<sigma>' x. \<sigma> \<sqsubseteq> \<sigma>' \<and> eval (EPresent x) \<sigma> \<noteq> eval (EPresent x) \<sigma>'"
proof -
  fix x :: 'n and v :: 'v
  have "(Map.empty :: ('n, 'v) state) \<sqsubseteq> [x \<mapsto> v]"
    by (simp add: info_le_def)
  moreover have "eval (EPresent x) (Map.empty :: ('n, 'v) state) \<noteq> eval (EPresent x) [x \<mapsto> v]"
    by simp
  ultimately show ?thesis
    by blast
qed


text \<open>DEFAULT is not monotone either: on \<open>\<emptyset> \<sqsubseteq> [x \<mapsto> v]\<close>, DEFAULT(x, w) changes from \<open>w\<close>
  to \<open>v\<close>, and the condition DEFAULT(x, w) = w changes from T to F. Both results are
  definite, so this is not the passage from \<open>\<bottom>\<close> to a value that monotonicity allows.\<close>

theorem T3_default_not_monotone:
  fixes v w :: "'v :: value_order" and x :: 'n
  assumes "v \<noteq> w"
  shows "(Map.empty :: ('n, 'v) state) \<sqsubseteq> [x \<mapsto> v]"
    and "evalV (VDefault x (VConst w)) (Map.empty :: ('n, 'v) state) = Some w"
    and "evalV (VDefault x (VConst w)) [x \<mapsto> v] = Some v"
    and "eval (EEq (VDefault x (VConst w)) (VConst w)) (Map.empty :: ('n, 'v) state) = Some True"
    and "eval (EEq (VDefault x (VConst w)) (VConst w)) [x \<mapsto> v] = Some False"
  using assms by (simp_all add: info_le_def)


section \<open>T4: agreement with two-valued logic\<close>

text \<open>Names occurring in value positions (operands of comparisons). The argument
  of PRESENT is not included: PRESENT never needs the name's value. Nor is the first
  argument of DEFAULT: DEFAULT(x, a) has a value whenever \<open>a\<close> has one.\<close>

primrec vnames :: "('n, 'v) vexp \<Rightarrow> 'n set" where
  "vnames (VConst v) = {}"
| "vnames (VName x) = {x}"
| "vnames (VDefault x a) = vnames a"

primrec names :: "('n, 'v) expr \<Rightarrow> 'n set" where
  "names ETrue = {}"
| "names EFalse = {}"
| "names (EEq a b) = vnames a \<union> vnames b"
| "names (ELt a b) = vnames a \<union> vnames b"
| "names (ELe a b) = vnames a \<union> vnames b"
| "names (ENot e) = names e"
| "names (EAnd e\<^sub>1 e\<^sub>2) = names e\<^sub>1 \<union> names e\<^sub>2"
| "names (EOr e\<^sub>1 e\<^sub>2) = names e\<^sub>1 \<union> names e\<^sub>2"
| "names (EImp e\<^sub>1 e\<^sub>2) = names e\<^sub>1 \<union> names e\<^sub>2"
| "names (EPresent x) = {}"

text \<open>Classical two-valued semantics over a total valuation \<open>\<rho>\<close> and a set \<open>D\<close>
  of present names (PRESENT is a plain two-valued predicate here, and DEFAULT(x, a) is
  \<open>\<rho> x\<close> if \<open>x \<in> D\<close> and the value of \<open>a\<close> otherwise).\<close>

primrec cevalV :: "('n, 'v) vexp \<Rightarrow> 'n set \<Rightarrow> ('n \<Rightarrow> 'v) \<Rightarrow> 'v" where
  "cevalV (VConst v) D \<rho> = v"
| "cevalV (VName x) D \<rho> = \<rho> x"
| "cevalV (VDefault x a) D \<rho> = (if x \<in> D then \<rho> x else cevalV a D \<rho>)"

primrec ceval :: "('n, 'v :: value_order) expr \<Rightarrow> 'n set \<Rightarrow> ('n \<Rightarrow> 'v) \<Rightarrow> bool" where
  "ceval ETrue D \<rho> = True"
| "ceval EFalse D \<rho> = False"
| "ceval (EEq a b) D \<rho> = (cevalV a D \<rho> = cevalV b D \<rho>)"
| "ceval (ELt a b) D \<rho> = vless (cevalV a D \<rho>) (cevalV b D \<rho>)"
| "ceval (ELe a b) D \<rho> = vleq (cevalV a D \<rho>) (cevalV b D \<rho>)"
| "ceval (ENot e) D \<rho> = (\<not> ceval e D \<rho>)"
| "ceval (EAnd e\<^sub>1 e\<^sub>2) D \<rho> = (ceval e\<^sub>1 D \<rho> \<and> ceval e\<^sub>2 D \<rho>)"
| "ceval (EOr e\<^sub>1 e\<^sub>2) D \<rho> = (ceval e\<^sub>1 D \<rho> \<or> ceval e\<^sub>2 D \<rho>)"
| "ceval (EImp e\<^sub>1 e\<^sub>2) D \<rho> = (ceval e\<^sub>1 D \<rho> \<longrightarrow> ceval e\<^sub>2 D \<rho>)"
| "ceval (EPresent x) D \<rho> = (x \<in> D)"

lemma evalV_classical:
  assumes "vnames a \<subseteq> dom \<sigma>" and "\<forall>x \<in> dom \<sigma>. \<sigma> x = Some (\<rho> x)"
  shows "evalV a \<sigma> = Some (cevalV a (dom \<sigma>) \<rho>)"
  using assms by (induction a) (auto split: option.splits)

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
next
  case (ELt a b)
  then have "vnames a \<subseteq> dom \<sigma>" "vnames b \<subseteq> dom \<sigma>"
    by simp_all
  then show ?case
    using evalV_classical[OF _ assms(2)] by simp
next
  case (ELe a b)
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

text \<open>If also every argument of PRESENT and the first argument of every DEFAULT is
  defined, PRESENT is just \<open>True\<close> and \<open>D\<close>
  can be taken to be the set of all names: a fully classical, total valuation.\<close>

primrec vpnames :: "('n, 'v) vexp \<Rightarrow> 'n set" where
  "vpnames (VConst v) = {}"
| "vpnames (VName x) = {}"
| "vpnames (VDefault x a) = insert x (vpnames a)"

primrec pnames :: "('n, 'v) expr \<Rightarrow> 'n set" where
  "pnames ETrue = {}"
| "pnames EFalse = {}"
| "pnames (EEq a b) = vpnames a \<union> vpnames b"
| "pnames (ELt a b) = vpnames a \<union> vpnames b"
| "pnames (ELe a b) = vpnames a \<union> vpnames b"
| "pnames (ENot e) = pnames e"
| "pnames (EAnd e\<^sub>1 e\<^sub>2) = pnames e\<^sub>1 \<union> pnames e\<^sub>2"
| "pnames (EOr e\<^sub>1 e\<^sub>2) = pnames e\<^sub>1 \<union> pnames e\<^sub>2"
| "pnames (EImp e\<^sub>1 e\<^sub>2) = pnames e\<^sub>1 \<union> pnames e\<^sub>2"
| "pnames (EPresent x) = {x}"

text \<open>The names whose presence a DEFAULT tests: the first arguments of DEFAULT.\<close>

primrec dnames :: "('n, 'v) expr \<Rightarrow> 'n set" where
  "dnames ETrue = {}"
| "dnames EFalse = {}"
| "dnames (EEq a b) = vpnames a \<union> vpnames b"
| "dnames (ELt a b) = vpnames a \<union> vpnames b"
| "dnames (ELe a b) = vpnames a \<union> vpnames b"
| "dnames (ENot e) = dnames e"
| "dnames (EAnd e\<^sub>1 e\<^sub>2) = dnames e\<^sub>1 \<union> dnames e\<^sub>2"
| "dnames (EOr e\<^sub>1 e\<^sub>2) = dnames e\<^sub>1 \<union> dnames e\<^sub>2"
| "dnames (EImp e\<^sub>1 e\<^sub>2) = dnames e\<^sub>1 \<union> dnames e\<^sub>2"
| "dnames (EPresent x) = {}"

lemma cevalV_present_UNIV: "vpnames a \<subseteq> D \<Longrightarrow> cevalV a D \<rho> = cevalV a UNIV \<rho>"
  by (induction a) auto

lemma ceval_present_UNIV: "pnames e \<subseteq> D \<Longrightarrow> ceval e D \<rho> = ceval e UNIV \<rho>"
proof (induction e)
  case (EEq a b)
  then show ?case using cevalV_present_UNIV[of a D \<rho>] cevalV_present_UNIV[of b D \<rho>] by simp
next
  case (ELt a b)
  then show ?case using cevalV_present_UNIV[of a D \<rho>] cevalV_present_UNIV[of b D \<rho>] by simp
next
  case (ELe a b)
  then show ?case using cevalV_present_UNIV[of a D \<rho>] cevalV_present_UNIV[of b D \<rho>] by simp
qed auto

corollary T4_total:
  assumes "names e \<union> pnames e \<subseteq> dom \<sigma>" and "\<forall>x \<in> dom \<sigma>. \<sigma> x = Some (\<rho> x)"
  shows "eval e \<sigma> = Some (ceval e UNIV \<rho>)"
  using assms eval_classical[of e \<sigma> \<rho>] ceval_present_UNIV[of e "dom \<sigma>" \<rho>] by simp


section \<open>T5: meaning of PRESENT\<close>

theorem T5_present: "eval (EPresent x) \<sigma> = Some True \<longleftrightarrow> x \<in> dom \<sigma>"
  by simp

end
