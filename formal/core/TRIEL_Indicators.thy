(*  Title:      TRIEL_Indicators.thy
    Purpose:    R-predicates and P-predicates given by truth and falsity domains; the
                total indicator Ez and the partial indicator (written \<down>z in the text) on
                states and on nominative data; stability of definite verdicts of
                conditions built from equitone atoms by NOT, AND and OR.
    Source:     S. S. Shkilniak. First-order logics with partial predicates for checking
                whether a variable is defined. Problems in Programming, 2024, No. 4,
                23-33 (in Ukrainian). DOI 10.15407/pp2024.04.023
                (reference [8] of FOUNDATIONS.md).
*)

theory TRIEL_Indicators
  imports TRIEL_ND TRIEL_Invariants
begin

section \<open>R-predicates and P-predicates\<close>

text \<open>An R-predicate \<open>Q\<close> on V-A-named sets is given by a pair \<open>(T(Q), F(Q))\<close>: its truth
  domain and its falsity domain. The two sets may overlap. \<open>Q\<close> is a P-predicate if
  \<open>T(Q) \<inter> F(Q) = \<emptyset>\<close>. V-A-named sets are the states of TRIEL_Core, and the extension
  \<open>d \<subseteq> d'\<close> (inclusion of graphs) is the information order \<open>\<sqsubseteq>\<close>. The definitions below take
  the extension order as a parameter \<open>le\<close>, so that they apply to the nominative data of
  TRIEL_ND as well.\<close>

type_synonym 'd rpred = "'d set \<times> 'd set"

definition R_T :: "'d rpred \<Rightarrow> 'd set" where
  "R_T Q = fst Q"

definition R_F :: "'d rpred \<Rightarrow> 'd set" where
  "R_F Q = snd Q"

lemma R_T_pair [simp]: "R_T (A, B) = A" and R_F_pair [simp]: "R_F (A, B) = B"
  by (simp_all add: R_T_def R_F_def)

definition P_pred :: "'d rpred \<Rightarrow> bool" where
  "P_pred Q \<longleftrightarrow> R_T Q \<inter> R_F Q = {}"

text \<open>\<open>Q[d]\<close> is the set of truth values that \<open>Q\<close> takes on \<open>d\<close>.\<close>

definition rval :: "'d rpred \<Rightarrow> 'd \<Rightarrow> bool set" where
  "rval Q d = {b. (b \<and> d \<in> R_T Q) \<or> (\<not> b \<and> d \<in> R_F Q)}"

lemma rval_True: "True \<in> rval Q d \<longleftrightarrow> d \<in> R_T Q"
  and rval_False: "False \<in> rval Q d \<longleftrightarrow> d \<in> R_F Q"
  by (simp_all add: rval_def)

lemma rval_subset:
  "rval Q d\<^sub>1 \<subseteq> rval Q d\<^sub>2 \<longleftrightarrow> (d\<^sub>1 \<in> R_T Q \<longrightarrow> d\<^sub>2 \<in> R_T Q) \<and> (d\<^sub>1 \<in> R_F Q \<longrightarrow> d\<^sub>2 \<in> R_F Q)"
proof
  assume "rval Q d\<^sub>1 \<subseteq> rval Q d\<^sub>2"
  then show "(d\<^sub>1 \<in> R_T Q \<longrightarrow> d\<^sub>2 \<in> R_T Q) \<and> (d\<^sub>1 \<in> R_F Q \<longrightarrow> d\<^sub>2 \<in> R_F Q)"
    using rval_True[of Q] rval_False[of Q] by blast
qed (auto simp: rval_def)

text \<open>A monotone R-predicate: \<open>d\<^sub>1 \<subseteq> d\<^sub>2 \<Longrightarrow> Q[d\<^sub>1] \<subseteq> Q[d\<^sub>2]\<close>. Equivalently, \<open>T(Q)\<close> and \<open>F(Q)\<close>
  are closed upwards.\<close>

definition rmono :: "('d \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> 'd rpred \<Rightarrow> bool" where
  "rmono le Q \<longleftrightarrow> (\<forall>d\<^sub>1 d\<^sub>2. le d\<^sub>1 d\<^sub>2 \<longrightarrow> rval Q d\<^sub>1 \<subseteq> rval Q d\<^sub>2)"

lemma rmono_iff:
  "rmono le Q \<longleftrightarrow>
     (\<forall>d\<^sub>1 d\<^sub>2. le d\<^sub>1 d\<^sub>2 \<longrightarrow> (d\<^sub>1 \<in> R_T Q \<longrightarrow> d\<^sub>2 \<in> R_T Q) \<and> (d\<^sub>1 \<in> R_F Q \<longrightarrow> d\<^sub>2 \<in> R_F Q))"
  by (simp add: rmono_def rval_subset)

text \<open>Total: every datum is in \<open>T(Q)\<close> or in \<open>F(Q)\<close>. Irrefutable: \<open>F(Q) = \<emptyset>\<close>.\<close>

definition total_R :: "'d rpred \<Rightarrow> bool" where
  "total_R Q \<longleftrightarrow> R_T Q \<union> R_F Q = UNIV"

definition irrefutable :: "'d rpred \<Rightarrow> bool" where
  "irrefutable Q \<longleftrightarrow> R_F Q = {}"

subsection \<open>P-predicates as partial predicates\<close>

text \<open>The value \<open>Q(d)\<close> of a P-predicate is T on \<open>T(Q)\<close>, F on \<open>F(Q)\<close>, and undefined
  elsewhere. This is the \<^typ>\<open>bool option\<close> of TRIEL_Core; \<open>of_qpred\<close> goes back.\<close>

definition pval :: "'d rpred \<Rightarrow> 'd \<Rightarrow> bool option" where
  "pval Q d = (if d \<in> R_T Q then Some True else if d \<in> R_F Q then Some False else None)"

definition of_qpred :: "('d \<Rightarrow> bool option) \<Rightarrow> 'd rpred" where
  "of_qpred Q = ({d. Q d = Some True}, {d. Q d = Some False})"

lemma of_qpred_domains: "of_qpred Q = (truth_dom Q, false_dom Q)"
  by (simp add: of_qpred_def truth_dom_def false_dom_def)

lemma of_qpred_P: "P_pred (of_qpred Q)"
  by (auto simp: P_pred_def of_qpred_def)

lemma pval_of_qpred: "pval (of_qpred Q) = Q"
proof (rule ext)
  fix d
  show "pval (of_qpred Q) d = Q d"
    using bool_option_cases[of "Q d"] by (auto simp: pval_def of_qpred_def)
qed

lemma of_qpred_pval: "P_pred Q \<Longrightarrow> of_qpred (pval Q) = Q"
  by (cases Q) (auto simp: of_qpred_def pval_def P_pred_def)

text \<open>Equitone: if \<open>Q(d)\<close> is defined and \<open>d \<subseteq> d'\<close>, then \<open>Q(d') = Q(d)\<close>. \<open>equitone_on\<close>
  is the definition of TRIEL_Ex with the extension order as a parameter.\<close>

definition equitone_on :: "('d \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> ('d \<Rightarrow> bool option) \<Rightarrow> bool" where
  "equitone_on le Q \<longleftrightarrow> (\<forall>d d'. Q d \<noteq> None \<and> le d d' \<longrightarrow> Q d' = Q d)"

lemma equitone_on_states: "equitone_on (\<sqsubseteq>) = equitone"
  by (rule ext) (simp add: equitone_on_def equitone_def)

lemma equitone_on_nd: "equitone_on nd_le = equitone_nd"
  by (rule ext) (simp add: equitone_on_def equitone_nd_def)

lemma equitone_on_approx: "equitone_on le Q \<longleftrightarrow> (\<forall>d d'. le d d' \<longrightarrow> Q d \<preceq> Q d')"
proof
  assume e: "equitone_on le Q"
  show "\<forall>d d'. le d d' \<longrightarrow> Q d \<preceq> Q d'"
  proof (intro allI impI)
    fix d d' assume "le d d'"
    with e have "Q d \<noteq> None \<Longrightarrow> Q d' = Q d" unfolding equitone_on_def by blast
    then show "Q d \<preceq> Q d'" by (cases "Q d") (auto simp: approx_iff)
  qed
next
  assume a: "\<forall>d d'. le d d' \<longrightarrow> Q d \<preceq> Q d'"
  show "equitone_on le Q"
    unfolding equitone_on_def
  proof (intro allI impI)
    fix d d' assume "Q d \<noteq> None \<and> le d d'"
    with a have "Q d \<preceq> Q d'" by blast
    with \<open>Q d \<noteq> None \<and> le d d'\<close> show "Q d' = Q d" by (auto simp: approx_iff)
  qed
qed

definition equitone_R :: "('d \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> 'd rpred \<Rightarrow> bool" where
  "equitone_R le Q \<longleftrightarrow> P_pred Q \<and> equitone_on le (pval Q)"

text \<open>For a P-predicate, monotone and equitone are the same property.\<close>

theorem P_pred_rmono_iff_equitone:
  assumes "P_pred Q"
  shows "rmono le Q \<longleftrightarrow> equitone_on le (pval Q)"
proof
  assume m: "rmono le Q"
  show "equitone_on le (pval Q)"
    unfolding equitone_on_def
  proof (intro allI impI)
    fix d d' assume a: "pval Q d \<noteq> None \<and> le d d'"
    show "pval Q d' = pval Q d"
    proof (cases "d \<in> R_T Q")
      case True
      with a m have "d' \<in> R_T Q" by (auto simp: rmono_iff)
      with True show ?thesis by (simp add: pval_def)
    next
      case False
      with a have F: "d \<in> R_F Q" by (auto simp: pval_def split: if_splits)
      with a m have "d' \<in> R_F Q" by (auto simp: rmono_iff)
      with assms have "d' \<notin> R_T Q" by (auto simp: P_pred_def)
      with False F \<open>d' \<in> R_F Q\<close> show ?thesis by (simp add: pval_def)
    qed
  qed
next
  assume e: "equitone_on le (pval Q)"
  show "rmono le Q"
    unfolding rmono_iff
  proof (intro allI impI conjI)
    fix d\<^sub>1 d\<^sub>2 assume le: "le d\<^sub>1 d\<^sub>2"
    {
      assume "d\<^sub>1 \<in> R_T Q"
      then have "pval Q d\<^sub>1 = Some True" by (simp add: pval_def)
      with e le have "pval Q d\<^sub>2 = Some True" unfolding equitone_on_def by fastforce
      then show "d\<^sub>2 \<in> R_T Q" by (simp add: pval_def split: if_splits)
    }
    {
      assume "d\<^sub>1 \<in> R_F Q"
      with assms have "pval Q d\<^sub>1 = Some False" by (auto simp: pval_def P_pred_def)
      with e le have "pval Q d\<^sub>2 = Some False" unfolding equitone_on_def by fastforce
      then show "d\<^sub>2 \<in> R_F Q" by (simp add: pval_def split: if_splits)
    }
  qed
qed

corollary equitone_R_iff: "equitone_R le Q \<longleftrightarrow> P_pred Q \<and> rmono le Q"
  unfolding equitone_R_def using P_pred_rmono_iff_equitone[of Q le] by blast


section \<open>The indicators Ez and \<open>\<down>z\<close> on V-A-named sets\<close>

text \<open>The total indicator \<open>E\<^sub>z\<close>: \<open>T(E\<^sub>z) = {d | d(z)\<down>}\<close>, \<open>F(E\<^sub>z) = {d | d(z)\<up>}\<close>.
  The partial indicator \<open>\<down>z\<close> (called \<open>DownInd\<close> here): \<open>T(\<down>z) = {d | d(z)\<down>}\<close>,
  \<open>F(\<down>z) = \<emptyset>\<close>.\<close>

definition Ex_R :: "'n \<Rightarrow> ('n, 'v) state rpred" where
  "Ex_R z = ({d. z \<in> dom d}, {d. z \<notin> dom d})"

definition DownInd :: "'n \<Rightarrow> ('n, 'v) state rpred" where
  "DownInd z = ({d. z \<in> dom d}, {})"

text \<open>\<open>E\<^sub>z\<close> is the predicate \<open>Ex_ind\<close> of TRIEL_Ex, and so \<open>PRESENT(z)\<close> (\<open>present_is_Ex\<close>).\<close>

lemma Ex_R_of_qpred: "of_qpred (Ex_ind z) = Ex_R z"
  by (simp add: of_qpred_domains Ex_ind_domains Ex_R_def)

lemma pval_Ex_R: "pval (Ex_R z) = Ex_ind z"
  by (rule ext) (simp add: pval_def Ex_R_def Ex_ind_def)

lemma pval_Ex_R_present: "pval (Ex_R z) = eval (EPresent z)"
  by (simp add: pval_Ex_R present_is_Ex)

text \<open>In logics with weak equality, \<open>\<down>z\<close> is \<open>=zz\<close>. Only the diagonal is used here, as in
  the source: \<open>T(=zz) = {d | d(z)\<down>}\<close> and \<open>F(=zz) = \<emptyset>\<close> (\<open>partial_indicator\<close> of TRIEL_Ex, for
  the comparison \<open>weq\<close> of TRIEL_Ex). No new definition of \<open>=xy\<close> is introduced.\<close>

theorem DownInd_is_eq_zz: "of_qpred (weq z z) = DownInd z"
  unfolding of_qpred_def DownInd_def weq_def by (auto split: option.splits)

lemma pval_DownInd: "pval (DownInd z) = weq z z"
  by (rule ext) (auto simp: pval_def DownInd_def weq_def split: option.split)

text \<open>So in TRIEL expressions \<open>\<down>z\<close> is the comparison \<open>z = z\<close>.\<close>

corollary self_eq_is_DownInd: "eval (EEq (VName z) (VName z)) = pval (DownInd z)"
  by (simp add: eval_eq_names pval_DownInd)

subsection \<open>Theorem 1\<close>

theorem T_DownInd_eq_T_Ex: "R_T (DownInd z) = R_T (Ex_R z)"
  by (simp add: DownInd_def Ex_R_def)

subsection \<open>Theorem 2: \<open>\<down>z\<close> is an equitone, irrefutable P-predicate\<close>

theorem DownInd_P_pred: "P_pred (DownInd z)"
  by (simp add: P_pred_def DownInd_def)

theorem DownInd_irrefutable: "irrefutable (DownInd z)"
  by (simp add: irrefutable_def DownInd_def)

theorem DownInd_mono: "rmono (\<sqsubseteq>) (DownInd z)"
  unfolding rmono_iff DownInd_def by (auto simp: info_le_def) (metis domI)

theorem DownInd_equitone: "equitone (pval (DownInd z :: ('n, 'v) state rpred))"
proof -
  have "rmono (\<sqsubseteq>) (DownInd z :: ('n, 'v) state rpred)" by (rule DownInd_mono)
  then have "equitone_on (\<sqsubseteq>) (pval (DownInd z :: ('n, 'v) state rpred))"
    by (simp add: P_pred_rmono_iff_equitone[OF DownInd_P_pred])
  then show ?thesis by (simp add: equitone_on_states)
qed

corollary DownInd_equitone_R: "equitone_R (\<sqsubseteq>) (DownInd z)"
  by (simp add: equitone_R_iff DownInd_P_pred DownInd_mono)

subsection \<open>Theorem 3: Ez is total and single-valued, and not monotone\<close>

theorem Ex_R_P_pred: "P_pred (Ex_R z)"
  by (auto simp: P_pred_def Ex_R_def)

theorem Ex_R_total: "total_R (Ex_R z)"
  by (auto simp: total_R_def Ex_R_def)

text \<open>The counterexample: \<open>\<emptyset> \<subseteq> [z \<mapsto> v]\<close>, with \<open>E\<^sub>z(\<emptyset>) = F\<close> and \<open>E\<^sub>z([z \<mapsto> v]) = T\<close>.\<close>

theorem Ex_R_counterexample:
  fixes z :: 'n and v :: 'v
  shows "(Map.empty :: ('n, 'v) state) \<sqsubseteq> [z \<mapsto> v]"
    and "pval (Ex_R z) (Map.empty :: ('n, 'v) state) = Some False"
    and "pval (Ex_R z) [z \<mapsto> v] = Some True"
    and "rval (Ex_R z) (Map.empty :: ('n, 'v) state) = {False}"
    and "rval (Ex_R z) [z \<mapsto> v] = {True}"
  by (auto simp: info_le_def pval_def Ex_R_def rval_def)

theorem Ex_R_not_mono: "\<not> rmono (\<sqsubseteq>) (Ex_R z :: ('n, 'v) state rpred)"
proof
  assume m: "rmono (\<sqsubseteq>) (Ex_R z :: ('n, 'v) state rpred)"
  fix v :: 'v
  from m Ex_R_counterexample(1)[of z v] Ex_R_counterexample(4)[of z] Ex_R_counterexample(5)[of z v]
  have "{False} \<subseteq> {True}" unfolding rmono_def by metis
  then show False by simp
qed

corollary Ex_R_not_equitone_R: "\<not> equitone_R (\<sqsubseteq>) (Ex_R z :: ('n, 'v) state rpred)"
  by (simp add: equitone_R_iff Ex_R_not_mono)


section \<open>Partial presence on nominative data (theorem 4)\<close>

text \<open>\<open>PRESENT(p)\<close> is the total indicator \<open>E\<^sub>p\<close> (\<open>present_nd_is_Ex\<close>). Partial presence is the
  indicator \<open>\<down>p\<close> for a complex name: T where \<open>p\<close> leads to a value (an atom or a record),
  undefined elsewhere. It never says ``absent''.\<close>

definition present_partial :: "'n list \<Rightarrow> ('n, 'b) nd \<Rightarrow> bool option" where
  "present_partial p d = (if den_path p d \<noteq> None then Some True else None)"

definition DownInd_nd :: "'n list \<Rightarrow> ('n, 'b) nd rpred" where
  "DownInd_nd p = ({d. den_path p d \<noteq> None}, {})"

lemma pval_DownInd_nd: "pval (DownInd_nd p) = present_partial p"
  by (rule ext) (simp add: pval_def DownInd_nd_def present_partial_def)

theorem present_partial_domains:
  "{d. present_partial p d = Some True} = {d. Ex_nd p d = Some True}"
  "{d. present_partial p d = Some False} = {}"
  by (auto simp: present_partial_def Ex_nd_def)

text \<open>Partial presence is below \<open>PRESENT\<close> in the definedness order: where it is defined,
  it agrees with \<open>PRESENT\<close>.\<close>

theorem present_partial_below_present: "present_partial p d \<preceq> eval_nd (EPresent p) d"
  by (simp add: approx_iff present_partial_def)

theorem present_partial_mono:
  assumes "nd_le d d'"
  shows "present_partial p d \<preceq> present_partial p d'"
  using nd_le_defined[OF assms, of p] by (auto simp: approx_iff present_partial_def)

theorem present_partial_equitone: "equitone_nd (present_partial p)"
  using present_partial_mono by (auto simp: equitone_on_nd[symmetric] equitone_on_approx)

theorem DownInd_nd_equitone_R: "equitone_R nd_le (DownInd_nd p)"
  "irrefutable (DownInd_nd p)"
  unfolding equitone_R_def pval_DownInd_nd
  by (simp_all add: P_pred_def DownInd_nd_def irrefutable_def equitone_on_nd present_partial_equitone)

text \<open>Contrast: \<open>PRESENT(p)\<close> is not equitone (\<open>Ex_nd_not_equitone\<close>). The comparison \<open>p = p\<close>
  is below partial presence: it is undefined when \<open>p\<close> leads to a record, because
  comparisons see only atoms.\<close>

lemma self_eq_below_present_partial: "eval_nd (EEq (VName p) (VName p)) d \<preceq> present_partial p d"
  by (auto simp: approx_iff present_partial_def flat_def split: option.splits nd.splits)


section \<open>Stability of verdicts (theorem 5)\<close>

text \<open>Conditions are built from atoms by NOT, AND and OR, and evaluated with the strong
  Kleene connectives of TRIEL_Core. A verdict is the value of a condition: T, F, or
  undefined (\<^typ>\<open>bool option\<close>). The atoms are interpreted by quasiary predicates \<open>I a\<close>.\<close>

datatype 'a cond = CAtom 'a | CNot "'a cond" | CAnd "'a cond" "'a cond" | COr "'a cond" "'a cond"

primrec cond_atoms :: "'a cond \<Rightarrow> 'a set" where
  "cond_atoms (CAtom a) = {a}"
| "cond_atoms (CNot \<phi>) = cond_atoms \<phi>"
| "cond_atoms (CAnd \<phi> \<psi>) = cond_atoms \<phi> \<union> cond_atoms \<psi>"
| "cond_atoms (COr \<phi> \<psi>) = cond_atoms \<phi> \<union> cond_atoms \<psi>"

primrec cond_eval :: "('a \<Rightarrow> 'd \<Rightarrow> bool option) \<Rightarrow> 'a cond \<Rightarrow> 'd \<Rightarrow> bool option" where
  "cond_eval I (CAtom a) d = I a d"
| "cond_eval I (CNot \<phi>) d = knot (cond_eval I \<phi> d)"
| "cond_eval I (CAnd \<phi> \<psi>) d = kand (cond_eval I \<phi> d) (cond_eval I \<psi> d)"
| "cond_eval I (COr \<phi> \<psi>) d = kor (cond_eval I \<phi> d) (cond_eval I \<psi> d)"

theorem cond_equitone:
  assumes "\<And>a. a \<in> cond_atoms \<phi> \<Longrightarrow> equitone_on le (I a)"
  shows "equitone_on le (cond_eval I \<phi>)"
proof -
  have "le d d' \<Longrightarrow> cond_eval I \<phi> d \<preceq> cond_eval I \<phi> d'" for d d'
    using assms
    by (induction \<phi>) (auto simp: equitone_on_approx intro: knot_mono kand_mono kor_mono)
  then show ?thesis by (simp add: equitone_on_approx)
qed

text \<open>Theorem 5: a definite verdict of a condition built from equitone atoms is kept
  under every extension of the data.\<close>

theorem verdict_stable:
  assumes "\<And>a. a \<in> cond_atoms \<phi> \<Longrightarrow> equitone_on le (I a)"
    and "le d d'" and "cond_eval I \<phi> d = Some b"
  shows "cond_eval I \<phi> d' = Some b"
  using cond_equitone[OF assms(1)] assms(2,3) unfolding equitone_on_def by fastforce

subsection \<open>Atoms over nominative data\<close>

text \<open>Three kinds of atoms over TRIEL data: \<open>PRESENT(p)\<close> (that is \<open>E\<^sub>p\<close>), partial presence
  \<open>\<down>p\<close>, and ``\<open>p\<close> is an atom of primitive type \<open>q\<close>'', which is undefined when \<open>p\<close> leads to
  nothing and false when it leads to a record.\<close>

datatype ('n, 'p) catom = AEx "'n list" | ADown "'n list" | AIs "'n list" 'p

definition is_prim :: "('p \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'n list \<Rightarrow> 'p \<Rightarrow> ('n, 'b) nd \<Rightarrow> bool option" where
  "is_prim I p q d =
     (case den_path p d of None \<Rightarrow> None | Some (Atom b) \<Rightarrow> Some (I q b) | Some (Nom m) \<Rightarrow> Some False)"

primrec catom_eval :: "('p \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('n, 'p) catom \<Rightarrow> ('n, 'b) nd \<Rightarrow> bool option" where
  "catom_eval I (AEx p) = Ex_nd p"
| "catom_eval I (ADown p) = present_partial p"
| "catom_eval I (AIs p q) = is_prim I p q"

primrec Ex_free_atom :: "('n, 'p) catom \<Rightarrow> bool" where
  "Ex_free_atom (AEx p) = False"
| "Ex_free_atom (ADown p) = True"
| "Ex_free_atom (AIs p q) = True"

lemma is_prim_equitone: "equitone_nd (is_prim I p q)"
  unfolding equitone_nd_def
proof (intro allI impI)
  fix d d' assume a: "is_prim I p q d \<noteq> None \<and> nd_le d d'"
  then obtain x where x: "den_path p d = Some x" by (auto simp: is_prim_def split: option.splits)
  show "is_prim I p q d' = is_prim I p q d"
  proof (cases x)
    case (Atom b)
    with x a have "den_path p d' = Some (Atom b)" unfolding nd_le_def by blast
    with x Atom show ?thesis by (simp add: is_prim_def)
  next
    case (Nom m)
    with x a obtain m' where "den_path p d' = Some (Nom m')" unfolding nd_le_def by blast
    with x Nom show ?thesis by (simp add: is_prim_def)
  qed
qed

lemma catom_equitone: "Ex_free_atom a \<Longrightarrow> equitone_nd (catom_eval I a)"
  by (cases a) (simp_all add: present_partial_equitone is_prim_equitone)

text \<open>Theorem 5 for TRIEL data: with atoms \<open>\<down>p\<close> and type checks, and without \<open>E\<^sub>p\<close>, a
  definite verdict survives every extension of the data.\<close>

theorem verdict_stable_nd:
  assumes "\<And>a. a \<in> cond_atoms \<phi> \<Longrightarrow> Ex_free_atom a"
    and "nd_le d d'" and "cond_eval (catom_eval I) \<phi> d = Some b"
  shows "cond_eval (catom_eval I) \<phi> d' = Some b"
  by (rule verdict_stable[where le = nd_le, OF _ assms(2,3)])
     (simp add: equitone_on_nd catom_equitone assms(1))

subsection \<open>With the atom Ex the property fails: the example of \<open>wt_not_mono_optional\<close>\<close>

text \<open>A field \<open>f\<close> of type \<open>Optional<q>\<close> in a record, as a condition. With \<open>E\<^sub>f\<close>:
  ``\<open>f\<close> is absent, or \<open>f\<close> has type \<open>q\<close>''. With \<open>\<down>f\<close>, the same shape.\<close>

definition opt_cond_Ex :: "'n \<Rightarrow> 'p \<Rightarrow> ('n, 'p) catom cond" where
  "opt_cond_Ex f q = COr (CNot (CAtom (AEx [f]))) (CAtom (AIs [f] q))"

definition opt_cond_Down :: "'n \<Rightarrow> 'p \<Rightarrow> ('n, 'p) catom cond" where
  "opt_cond_Down f q = COr (CNot (CAtom (ADown [f]))) (CAtom (AIs [f] q))"

inductive_cases wt_Record_NomE: "wt I (TRecord fs) (Some (Nom m))"

lemma wt_single_record_iff: "wt I (TRecord [(f, t)]) (Some (Nom m)) \<longleftrightarrow> wt I t (fmlookup m f)"
proof
  assume "wt I (TRecord [(f, t)]) (Some (Nom m))"
  then show "wt I t (fmlookup m f)" by (rule wt_Record_NomE) simp
next
  assume "wt I t (fmlookup m f)"
  then show "wt I (TRecord [(f, t)]) (Some (Nom m))" by (intro wt.wt_record) simp
qed

lemma wt_opt_prim_iff: "wt I (TOptional (TPrim q)) v \<longleftrightarrow> v = None \<or> (\<exists>b. v = Some (Atom b) \<and> I q b)"
  by (auto elim!: wt_OptionalE wt_PrimE intro: wt.intros)

text \<open>With \<open>E\<^sub>f\<close> the condition is the typing judgement of TRIEL_ND on records.\<close>

theorem opt_cond_Ex_wt:
  "cond_eval (catom_eval I) (opt_cond_Ex f q) (Nom m) =
     Some (wt I (TRecord [(f, TOptional (TPrim q))]) (Some (Nom m)))"
proof (cases "fmlookup m f")
  case None
  then show ?thesis
    by (simp add: opt_cond_Ex_def Ex_nd_def is_prim_def wt_single_record_iff wt_opt_prim_iff kor_def)
next
  case (Some y)
  then show ?thesis
    by (cases y) (simp_all add: opt_cond_Ex_def Ex_nd_def is_prim_def wt_single_record_iff wt_opt_prim_iff)
qed

text \<open>With \<open>\<down>f\<close> the condition agrees with typing when \<open>f\<close> is present, and is undefined when
  \<open>f\<close> is absent: absence reads as ``not yet known''.\<close>

theorem opt_cond_Down_wt:
  "fmlookup m f \<noteq> None \<Longrightarrow> cond_eval (catom_eval I) (opt_cond_Down f q) (Nom m) =
     Some (wt I (TRecord [(f, TOptional (TPrim q))]) (Some (Nom m)))"
  "fmlookup m f = None \<Longrightarrow> cond_eval (catom_eval I) (opt_cond_Down f q) (Nom m) = None"
proof -
  assume "fmlookup m f \<noteq> None"
  then obtain y where y: "fmlookup m f = Some y" by auto
  then show "cond_eval (catom_eval I) (opt_cond_Down f q) (Nom m) =
     Some (wt I (TRecord [(f, TOptional (TPrim q))]) (Some (Nom m)))"
    by (cases y) (simp_all add: opt_cond_Down_def present_partial_def is_prim_def wt_single_record_iff
        wt_opt_prim_iff)
next
  assume "fmlookup m f = None"
  then show "cond_eval (catom_eval I) (opt_cond_Down f q) (Nom m) = None"
    by (simp add: opt_cond_Down_def present_partial_def is_prim_def kor_def)
qed

text \<open>The data of \<open>wt_not_mono_optional\<close>: the empty record, extended by \<open>[f \<mapsto> b]\<close> where
  \<open>b\<close> is not of type \<open>q\<close>. With \<open>E\<^sub>f\<close> the definite verdict T becomes F; with \<open>\<down>f\<close> the
  verdict is undefined before the extension, so no definite verdict is overturned.\<close>

theorem Ex_breaks_stability:
  fixes f :: 'n and q :: 'p and b :: 'b
  defines "I \<equiv> \<lambda>(q :: 'p) (b :: 'b). False"
  defines "t \<equiv> TRecord [(f, TOptional (TPrim q))] :: ('n, 'p) ty"
  shows "nd_le (Nom fmempty) (naming f (Atom b))"
    and "wt I t (Some (Nom fmempty))" and "\<not> wt I t (Some (naming f (Atom b)))"
    and "cond_eval (catom_eval I) (opt_cond_Ex f q) (Nom fmempty) = Some True"
    and "cond_eval (catom_eval I) (opt_cond_Ex f q) (naming f (Atom b)) = Some False"
    and "cond_eval (catom_eval I) (opt_cond_Down f q) (Nom fmempty) = None"
    and "cond_eval (catom_eval I) (opt_cond_Down f q) (naming f (Atom b)) = Some False"
proof -
  show "nd_le (Nom fmempty) (naming f (Atom b))" by (rule nd_le_empty_naming)
  show w0: "wt I t (Some (Nom fmempty))"
    unfolding t_def by (simp add: wt_single_record_iff wt_opt_prim_iff)
  show w1: "\<not> wt I t (Some (naming f (Atom b)))"
    unfolding t_def I_def by (simp add: naming_def wt_single_record_iff wt_opt_prim_iff)
  show "cond_eval (catom_eval I) (opt_cond_Ex f q) (Nom fmempty) = Some True"
    using w0 opt_cond_Ex_wt[of I f q fmempty] by (simp add: t_def)
  show "cond_eval (catom_eval I) (opt_cond_Ex f q) (naming f (Atom b)) = Some False"
    using w1 opt_cond_Ex_wt[of I f q "fmupd f (Atom b) fmempty"] by (simp add: t_def naming_def)
  show "cond_eval (catom_eval I) (opt_cond_Down f q) (Nom fmempty) = None"
    by (rule opt_cond_Down_wt(2)) simp
  show "cond_eval (catom_eval I) (opt_cond_Down f q) (naming f (Atom b)) = Some False"
    using w1 opt_cond_Down_wt(1)[of "fmupd f (Atom b) fmempty" f I q]
    by (simp add: t_def naming_def)
qed

corollary Ex_cond_not_equitone:
  "\<not> equitone_nd (cond_eval (catom_eval (\<lambda>(q :: 'p) (b :: 'b). False)) (opt_cond_Ex (f :: 'n) (q :: 'p)))"
proof
  fix b :: 'b
  let ?Q = "cond_eval (catom_eval (\<lambda>(q :: 'p) (b :: 'b). False)) (opt_cond_Ex f q)"
  assume "equitone_nd ?Q"
  then have "?Q d \<noteq> None \<and> nd_le d d' \<longrightarrow> ?Q d' = ?Q d" for d d'
    unfolding equitone_nd_def by blast
  from Ex_breaks_stability(4)[of f q] Ex_breaks_stability(5)[of f q b]
    nd_le_empty_naming[of f b] this[of "Nom fmempty" "naming f (Atom b)"]
  show False by auto
qed

corollary Down_cond_equitone: "equitone_nd (cond_eval (catom_eval I) (opt_cond_Down f q))"
  by (subst equitone_on_nd[symmetric], rule cond_equitone)
     (auto simp: opt_cond_Down_def equitone_on_nd present_partial_equitone is_prim_equitone)

subsection \<open>Invariants (LTL3 verdicts)\<close>

text \<open>The three-valued verdicts of invariants (TRIEL_Invariants) rest on the same property:
  \<open>inv_data_mono\<close> holds for every state formula whose predicate is equitone, not only for
  PRESENT-free ones (for those it is \<open>present_free_equitone\<close>).\<close>

theorem inv_data_mono_equitone:
  assumes eq: "equitone (eval (inv_formula \<iota>))"
    and len: "length \<pi>' = length \<pi>"
    and le: "\<And>j. j < length \<pi> \<Longrightarrow> st \<pi> j \<sqsubseteq> st \<pi>' j"
    and v: "inv_eval \<iota> \<pi> = Some b"
  shows "inv_eval \<iota> \<pi>' = Some b"
proof -
  have keep: "eval (inv_formula \<iota>) (st \<pi>' j) = Some c"
    if "j < length \<pi>" "eval (inv_formula \<iota>) (st \<pi> j) = Some c" for j c
    using eq le[OF that(1)] that(2) unfolding equitone_def by fastforce
  show ?thesis
  proof (cases \<iota>)
    case (Always \<phi>)
    let ?P = "\<exists>j < length \<pi>. eval \<phi> (st \<pi> j) = Some False"
    from v Always have "(if ?P then Some False else None) = Some b" by simp
    then have ex: ?P and b: "b = False" by (cases ?P; simp)+
    from ex obtain j where j: "j < length \<pi>" "eval \<phi> (st \<pi> j) = Some False" by blast
    with keep Always have "eval \<phi> (st \<pi>' j) = Some False" by simp
    with j(1) len Always b show ?thesis by auto
  next
    case (Eventually \<phi>)
    let ?P = "\<exists>j < length \<pi>. eval \<phi> (st \<pi> j) = Some True"
    from v Eventually have "(if ?P then Some True else None) = Some b" by simp
    then have ex: ?P and b: "b = True" by (cases ?P; simp)+
    from ex obtain j where j: "j < length \<pi>" "eval \<phi> (st \<pi> j) = Some True" by blast
    with keep Eventually have "eval \<phi> (st \<pi>' j) = Some True" by simp
    with j(1) len Eventually b show ?thesis by auto
  next
    case (Next \<phi>)
    from v Next have "(if 1 < length \<pi> then eval \<phi> (st \<pi> 1) else None) = Some b" by simp
    then have n: "1 < length \<pi>" and e: "eval \<phi> (st \<pi> 1) = Some b"
      by (cases "1 < length \<pi>"; simp)+
    with keep Next have "eval \<phi> (st \<pi>' 1) = Some b" by simp
    with n len Next show ?thesis by simp
  qed
qed


section \<open>Closure of the equitone P-predicates (theorem 6)\<close>

text \<open>The compositions of negation and disjunction on R-predicates:
  \<open>T(\<not>Q) = F(Q)\<close>, \<open>F(\<not>Q) = T(Q)\<close>; \<open>T(Q\<^sub>1 \<or> Q\<^sub>2) = T(Q\<^sub>1) \<union> T(Q\<^sub>2)\<close>, \<open>F(Q\<^sub>1 \<or> Q\<^sub>2) = F(Q\<^sub>1) \<inter> F(Q\<^sub>2)\<close>.
  On P-predicates they are the strong Kleene connectives of TRIEL_Core.\<close>

definition R_not :: "'d rpred \<Rightarrow> 'd rpred" where
  "R_not Q = (R_F Q, R_T Q)"

definition R_or :: "'d rpred \<Rightarrow> 'd rpred \<Rightarrow> 'd rpred" where
  "R_or Q\<^sub>1 Q\<^sub>2 = (R_T Q\<^sub>1 \<union> R_T Q\<^sub>2, R_F Q\<^sub>1 \<inter> R_F Q\<^sub>2)"

lemma pval_R_not: "P_pred Q \<Longrightarrow> pval (R_not Q) = knot \<circ> pval Q"
  by (rule ext) (auto simp: pval_def R_not_def P_pred_def)

lemma pval_R_or: "pval (R_or Q\<^sub>1 Q\<^sub>2) d = kor (pval Q\<^sub>1 d) (pval Q\<^sub>2 d)"
  by (auto simp: pval_def R_or_def kor_def)

theorem equitone_R_not: "equitone_R le Q \<Longrightarrow> equitone_R le (R_not Q)"
  by (auto simp: equitone_R_iff rmono_iff P_pred_def R_not_def)

theorem equitone_R_or: "equitone_R le Q\<^sub>1 \<Longrightarrow> equitone_R le Q\<^sub>2 \<Longrightarrow> equitone_R le (R_or Q\<^sub>1 Q\<^sub>2)"
  by (auto simp: equitone_R_iff rmono_iff P_pred_def R_or_def)

text \<open>\<open>\<down>z\<close> belongs to the class (\<open>DownInd_equitone_R\<close>); \<open>E\<^sub>z\<close> does not (\<open>Ex_R_not_equitone_R\<close>).
  So every predicate built from \<open>\<down>z\<close> and other equitone P-predicates by \<open>\<not>\<close> and \<open>\<or>\<close> is an
  equitone P-predicate.\<close>

inductive_set equitone_closure :: "('n, 'v) state rpred set \<Rightarrow> ('n, 'v) state rpred set"
  for B :: "('n, 'v) state rpred set" where
  base: "Q \<in> B \<Longrightarrow> Q \<in> equitone_closure B"
| down: "DownInd z \<in> equitone_closure B"
| neg: "Q \<in> equitone_closure B \<Longrightarrow> R_not Q \<in> equitone_closure B"
| disj: "Q\<^sub>1 \<in> equitone_closure B \<Longrightarrow> Q\<^sub>2 \<in> equitone_closure B \<Longrightarrow> R_or Q\<^sub>1 Q\<^sub>2 \<in> equitone_closure B"

theorem equitone_closure_equitone:
  assumes "\<And>Q. Q \<in> B \<Longrightarrow> equitone_R (\<sqsubseteq>) Q" and "Q \<in> equitone_closure B"
  shows "equitone_R (\<sqsubseteq>) Q"
  using assms(2)
  by induction (simp_all add: assms(1) DownInd_equitone_R equitone_R_not equitone_R_or)

end
