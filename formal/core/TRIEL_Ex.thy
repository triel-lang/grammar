(*  Title:      TRIEL_Ex.thy
    Purpose:    The total indicator predicate Ex of the logics of quasiary predicates
                (Nikitchenko, Shkilniak), and the theorem that PRESENT(x) is Ex.
    Source:     O. Shkilniak, S. Shkilniak. Transitional modal logics of quasiary
                predicates with equality and sequent calculi for these logics.
                UkrPROG'2024, CEUR Workshop Proceedings 3806, 2024, section 2
                (reference [5] of FOUNDATIONS.md).
*)

theory TRIEL_Ex
  imports TRIEL_Core
begin

section \<open>Quasiary predicates\<close>

text \<open>A quasiary predicate on nominative data (here: states) is determined by its
  truth domain \<open>T(Q)\<close> and its falsity domain \<open>F(Q)\<close>. A predicate with values in
  \<^typ>\<open>bool option\<close> is single-valued (a P-predicate) by construction: \<open>T(Q) \<inter> F(Q) = \<emptyset>\<close>.
  The extension order \<open>d \<subseteq> d'\<close> on data is the information order \<open>\<sqsubseteq>\<close> of TRIEL_Core.\<close>

type_synonym ('n, 'v) qpred = "('n, 'v) state \<Rightarrow> bool option"

definition truth_dom :: "('n, 'v) qpred \<Rightarrow> ('n, 'v) state set" where
  "truth_dom Q = {d. Q d = Some True}"

definition false_dom :: "('n, 'v) qpred \<Rightarrow> ('n, 'v) state set" where
  "false_dom Q = {d. Q d = Some False}"

lemma single_valued: "truth_dom Q \<inter> false_dom Q = {}"
  by (auto simp: truth_dom_def false_dom_def)

text \<open>Q is total if it is defined on all data, and equitone if
  \<open>Q(d)\<down> and d \<subseteq> d' \<Longrightarrow> Q(d')\<down> = Q(d)\<close>.\<close>

definition total_pred :: "('n, 'v) qpred \<Rightarrow> bool" where
  "total_pred Q \<longleftrightarrow> (\<forall>d. Q d \<noteq> None)"

definition equitone :: "('n, 'v) qpred \<Rightarrow> bool" where
  "equitone Q \<longleftrightarrow> (\<forall>d d'. Q d \<noteq> None \<and> d \<sqsubseteq> d' \<longrightarrow> Q d' = Q d)"


section \<open>The total indicator predicate Ex\<close>

text \<open>The total indicator predicate \<open>E\<^sub>z\<close>: \<open>T(E\<^sub>z) = {d | d(z)\<down>}\<close>, \<open>F(E\<^sub>z) = {d | d(z)\<up>}\<close>.
  The constant is called \<open>Ex_ind\<close>, because \<open>Ex\<close> is the existential quantifier of HOL.\<close>

definition Ex_ind :: "'n \<Rightarrow> ('n, 'v) qpred" where
  "Ex_ind z d = (if z \<in> dom d then Some True else Some False)"

lemma Ex_ind_domains:
  "truth_dom (Ex_ind z) = {d. z \<in> dom d}"
  "false_dom (Ex_ind z) = {d. z \<notin> dom d}"
  by (auto simp: truth_dom_def false_dom_def Ex_ind_def)

text \<open>These two domains determine \<open>Ex_ind z\<close> uniquely, so the definition is exactly the
  one given by the truth and falsity domains.\<close>

lemma Ex_ind_unique:
  assumes "truth_dom Q = {d. z \<in> dom d}" and "false_dom Q = {d. z \<notin> dom d}"
  shows "Q = Ex_ind z"
proof (rule ext)
  fix d
  show "Q d = Ex_ind z d"
  proof (cases "z \<in> dom d")
    case True
    then have "d \<in> truth_dom Q" using assms(1) by simp
    with True show ?thesis by (simp add: truth_dom_def Ex_ind_def)
  next
    case False
    then have "d \<in> false_dom Q" using assms(2) by simp
    with False show ?thesis by (simp add: false_dom_def Ex_ind_def)
  qed
qed

theorem Ex_ind_total: "total_pred (Ex_ind z)"
  by (auto simp: total_pred_def Ex_ind_def)

theorem Ex_ind_not_equitone: "\<not> equitone (Ex_ind z :: ('n, 'v) qpred)"
proof
  assume eq: "equitone (Ex_ind z :: ('n, 'v) qpred)"
  fix v :: 'v
  have le: "(Map.empty :: ('n, 'v) state) \<sqsubseteq> [z \<mapsto> v]"
    by (simp add: info_le_def)
  have "Ex_ind z (Map.empty :: ('n, 'v) state) \<noteq> None"
    by (simp add: Ex_ind_def)
  with eq le have "Ex_ind z [z \<mapsto> v] = Ex_ind z (Map.empty :: ('n, 'v) state)"
    unfolding equitone_def by blast
  then show False by (simp add: Ex_ind_def)
qed

text \<open>In free logic the existence predicate is \<open>E!x \<equiv> \<exists>y. y = x\<close>. Correspondingly,
  \<open>Ex_ind x\<close> is true exactly when the value of \<open>x\<close> is equal to some value.\<close>

theorem Ex_ind_exists:
  "Ex_ind x d = Some True \<longleftrightarrow> (\<exists>v. eval (EEq (VName x) (VConst v)) d = Some True)"
  by (cases "d x") (auto simp: Ex_ind_def)


section \<open>PRESENT is Ex\<close>

theorem present_is_Ex: "eval (EPresent x) = Ex_ind x"
  by (rule ext) (simp add: Ex_ind_def)

corollary present_total_not_equitone:
  "total_pred (eval (EPresent x))" and "\<not> equitone (eval (EPresent x) :: ('n, 'v) qpred)"
  unfolding present_is_Ex by (rule Ex_ind_total, rule Ex_ind_not_equitone)


section \<open>Equitone expressions and the partial indicator\<close>

text \<open>Theorem T2 of TRIEL_Core in the terminology of quasiary predicates: every
  PRESENT-free expression denotes an equitone predicate.\<close>

theorem present_free_equitone:
  assumes "present_free e"
  shows "equitone (eval e)"
  unfolding equitone_def
proof (intro allI impI)
  fix d d' assume "eval e d \<noteq> None \<and> d \<sqsubseteq> d'"
  then obtain b where b: "eval e d = Some b" and le: "d \<sqsubseteq> d'" by auto
  from T2_monotone[OF assms le b] b show "eval e d' = eval e d" by simp
qed

text \<open>The weak equality \<open>=xy\<close>: \<open>T(=xy) = {d | d(x)\<down>, d(y)\<down>, d(x) = d(y)}\<close> and
  \<open>F(=xy) = {d | d(x)\<down>, d(y)\<down>, d(x) \<noteq> d(y)}\<close>. TRIEL's comparison of two names is this
  predicate. Its diagonal \<open>=xx\<close> is the partial indicator predicate: it has the truth
  domain of \<open>Ex\<close>, an empty falsity domain, and it is equitone.\<close>

definition weq :: "'n \<Rightarrow> 'n \<Rightarrow> ('n, 'v) qpred" where
  "weq x y d = (case d x of None \<Rightarrow> None | Some a \<Rightarrow> (case d y of None \<Rightarrow> None | Some b \<Rightarrow> Some (a = b)))"

lemma eval_eq_names: "eval (EEq (VName x) (VName y)) = weq x y"
  by (rule ext) (simp add: weq_def split: option.split)

theorem partial_indicator:
  "truth_dom (weq x x) = truth_dom (Ex_ind x :: ('n, 'v) qpred)"
  "false_dom (weq x x :: ('n, 'v) qpred) = {}"
  "equitone (weq x x :: ('n, 'v) qpred)"
proof -
  show "truth_dom (weq x x) = truth_dom (Ex_ind x :: ('n, 'v) qpred)"
    by (auto simp: truth_dom_def weq_def Ex_ind_def split: option.splits)
  show "false_dom (weq x x :: ('n, 'v) qpred) = {}"
    by (auto simp: false_dom_def weq_def split: option.splits)
  have "equitone (eval (EEq (VName x) (VName x)) :: ('n, 'v) qpred)"
    by (rule present_free_equitone) simp
  then show "equitone (weq x x :: ('n, 'v) qpred)"
    by (simp add: eval_eq_names)
qed

end
