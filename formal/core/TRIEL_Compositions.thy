(*  Title:      TRIEL_Compositions.thy
    Purpose:    The base compositions of the composition predicate algebras: the existential
                quantifier and renomination (traditional and extended) on R-predicates;
                closure of the P-, RM- and PE-predicates under all base compositions;
                formulas as terms of the algebra, with their interpretation; the
                conditions of TRIEL_Indicators as such terms.
    Sources:    M. Nikitchenko, S. Shkilniak. Algebras and logics of partial quasiary
                predicates. Algebra and Discrete Mathematics, 23(2), 2017, 263-278
                (reference [2] of FOUNDATIONS.md).
                S. S. Shkilniak. First-order logics with partial predicates for checking
                whether a variable is defined. Problems in Programming, 2024, No. 4,
                23-33 (in Ukrainian). DOI 10.15407/pp2024.04.023
                (reference [8] of FOUNDATIONS.md).
*)

theory TRIEL_Compositions
  imports TRIEL_Indicators
begin

section \<open>Operations on V-A-named sets\<close>

text \<open>V-A-named sets are the states of TRIEL_Core. Deleting the components whose names are
  in \<open>Z\<close> ([8], p. 24): \<open>d\<parallel>\<^sub>-\<^sub>Z = {v \<mapsto> a \<in> d | v \<notin> Z}\<close>.\<close>

definition del_names :: "'n set \<Rightarrow> ('n, 'v) state \<Rightarrow> ('n, 'v) state" where
  "del_names Z d = d |` (- Z)"

text \<open>Extended renomination ([8], p. 24). Its parameter is a list of distinct upper names
  \<open>v\<^sub>1, \<dots>, v\<^sub>n, u\<^sub>1, \<dots>, u\<^sub>m\<close> with lower names \<open>x\<^sub>1, \<dots>, x\<^sub>n, \<bottom>, \<dots>, \<bottom>\<close>, where \<open>\<bottom>\<close> means
  ``no value'':
  \<open>r(d) = [v\<^sub>1 \<mapsto> d(x\<^sub>1), \<dots>, v\<^sub>n \<mapsto> d(x\<^sub>n)] \<union> d\<parallel>\<^sub>-\<^sub>Z\<close>, where \<open>Z = {v\<^sub>1, \<dots>, v\<^sub>n, u\<^sub>1, \<dots>, u\<^sub>m}\<close>.
  The order of the pairs does not matter ([8], p. 24), and [2], p. 265, reads the parameter
  as a mapping from the upper names to the lower ones. Here it is a partial map \<open>\<rho>\<close> with
  \<open>dom \<rho> = {v\<^sub>1, \<dots>, v\<^sub>n, u\<^sub>1, \<dots>, u\<^sub>m}\<close>, \<open>\<rho> v\<^sub>i = Some (Some x\<^sub>i)\<close> and \<open>\<rho> u\<^sub>j = Some None\<close>.
  In the sources the parameter is finite; the definitions and theorems below hold for every
  \<open>\<rho>\<close>. The union is \<open>++\<close>; its two operands have disjoint domains.\<close>

definition ren_ext :: "('n \<rightharpoonup> 'n option) \<Rightarrow> ('n, 'v) state \<Rightarrow> ('n, 'v) state" where
  "ren_ext \<rho> d = del_names (dom \<rho>) d ++ (\<lambda>v. case \<rho> v of Some (Some x) \<Rightarrow> d x | _ \<Rightarrow> None)"

lemma ren_ext_apply:
  "ren_ext \<rho> d v = (case \<rho> v of None \<Rightarrow> d v | Some None \<Rightarrow> None | Some (Some x) \<Rightarrow> d x)"
  by (auto simp: ren_ext_def del_names_def map_add_def restrict_map_def split: option.split)

text \<open>Traditional renomination ([2], p. 265):
  \<open>r\<^sup>v\<^sub>x(d) = [v \<mapsto> a | v \<mapsto> a \<in> d, v \<notin> {v\<^sub>1, \<dots>, v\<^sub>n}] \<union> [v\<^sub>i \<mapsto> a\<^sub>i | x\<^sub>i \<mapsto> a\<^sub>i \<in> d]\<close>, with the
  parameter a partial map \<open>\<sigma>\<close>, \<open>\<sigma> v\<^sub>i = Some x\<^sub>i\<close>. It is the extended renomination without
  pairs \<open>u/\<bottom>\<close> ([8], p. 25).\<close>

definition ren :: "('n \<rightharpoonup> 'n) \<Rightarrow> ('n, 'v) state \<Rightarrow> ('n, 'v) state" where
  "ren \<sigma> d = (\<lambda>v. if v \<notin> dom \<sigma> then d v else None) ++ (\<lambda>v. case \<sigma> v of None \<Rightarrow> None | Some x \<Rightarrow> d x)"

definition trad :: "('n \<rightharpoonup> 'n) \<Rightarrow> ('n \<rightharpoonup> 'n option)" where
  "trad \<sigma> v = map_option Some (\<sigma> v)"

lemma ren_is_ren_ext: "ren \<sigma> = ren_ext (trad \<sigma>)"
proof (intro ext)
  fix d v
  show "ren \<sigma> d v = ren_ext (trad \<sigma>) d v"
    by (cases "\<sigma> v") (auto simp: ren_def ren_ext_apply trad_def map_add_def domIff split: option.split)
qed

text \<open>The data of the quantifier: \<open>d\<parallel>\<^sub>-\<^sub>x \<union> x \<mapsto> a\<close> ([8], p. 25), written \<open>d\<nabla>x \<mapsto> a\<close> in [2],
  p. 266.\<close>

lemma del_names_upd: "del_names {x} d ++ [x \<mapsto> a] = d(x \<mapsto> a)"
  by (rule ext) (auto simp: del_names_def map_add_def restrict_map_def)

lemma del_names_upd': "(del_names {x} d)(x \<mapsto> a) = d(x \<mapsto> a)"
  by (rule ext) (auto simp: del_names_def restrict_map_def)

subsection \<open>Pointwise extension orders\<close>

text \<open>\<open>pw_le vle\<close> extends a named set: every name keeps a value, and the value may grow in the
  order \<open>vle\<close>. With \<open>vle\<close> the equality it is the inclusion \<open>d \<subseteq> d'\<close> of [8], that is \<open>\<sqsubseteq>\<close>
  (\<open>pw_le_eq\<close>). The order of nominative data is another instance (\<open>nd_le_pw\<close> below).\<close>

definition pw_le :: "('v \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow> ('n, 'v) state \<Rightarrow> ('n, 'v) state \<Rightarrow> bool" where
  "pw_le vle d d' \<longleftrightarrow> (\<forall>v a. d v = Some a \<longrightarrow> (\<exists>a'. d' v = Some a' \<and> vle a a'))"

lemma pw_le_eq_apply: "pw_le (=) d d' \<longleftrightarrow> d \<sqsubseteq> d'"
proof
  assume "pw_le (=) d d'"
  then show "d \<sqsubseteq> d'"
    unfolding pw_le_def info_le_def by (auto dest!: domD)
next
  assume "d \<sqsubseteq> d'"
  then show "pw_le (=) d d'"
    unfolding pw_le_def by (auto dest: info_leD)
qed

lemma pw_le_eq: "pw_le (=) = (\<sqsubseteq>)"
  by (intro ext) (rule pw_le_eq_apply)

lemma ren_ext_mono_pw: "pw_le vle d d' \<Longrightarrow> pw_le vle (ren_ext \<rho> d) (ren_ext \<rho> d')"
  unfolding pw_le_def ren_ext_apply by (auto split: option.splits)

text \<open>Monotonicity of the renomination operation: \<open>d \<subseteq> d' \<Longrightarrow> r(d) \<subseteq> r(d')\<close>.\<close>

theorem ren_ext_mono: "d \<sqsubseteq> d' \<Longrightarrow> ren_ext \<rho> d \<sqsubseteq> ren_ext \<rho> d'"
  using ren_ext_mono_pw[of "(=)" d d' \<rho>] by (simp add: pw_le_eq)

corollary ren_mono: "d \<sqsubseteq> d' \<Longrightarrow> ren \<sigma> d \<sqsubseteq> ren \<sigma> d'"
  by (simp add: ren_is_ren_ext ren_ext_mono)

lemma upd_mono_pw: "vle a a \<Longrightarrow> pw_le vle d d' \<Longrightarrow> pw_le vle (d(x \<mapsto> a)) (d'(x \<mapsto> a))"
  unfolding pw_le_def by auto


section \<open>The quantifier and renomination on R-predicates\<close>

text \<open>[8], p. 25 (the same in [2], p. 266):
  \<open>T(\<exists>xP) = \<Union>\<^sub>a\<^sub>\<in>\<^sub>A {d | d\<parallel>\<^sub>-\<^sub>x \<union> x \<mapsto> a \<in> T(P)}\<close>,
  \<open>F(\<exists>xP) = \<Inter>\<^sub>a\<^sub>\<in>\<^sub>A {d | d\<parallel>\<^sub>-\<^sub>x \<union> x \<mapsto> a \<in> F(P)}\<close>.\<close>

definition R_ex :: "'n \<Rightarrow> ('n, 'v) state rpred \<Rightarrow> ('n, 'v) state rpred" where
  "R_ex x Q = ((\<Union>a. {d. del_names {x} d ++ [x \<mapsto> a] \<in> R_T Q}),
               (\<Inter>a. {d. del_names {x} d ++ [x \<mapsto> a] \<in> R_F Q}))"

lemma R_ex_domains:
  "R_T (R_ex x Q) = {d. \<exists>a. d(x \<mapsto> a) \<in> R_T Q}"
  "R_F (R_ex x Q) = {d. \<forall>a. d(x \<mapsto> a) \<in> R_F Q}"
  by (auto simp: R_ex_def del_names_upd del_names_upd')

text \<open>Renomination composition ([8], p. 25): \<open>R(Q)[d] = Q[r(d)]\<close>. In terms of the domains
  ([2], p. 266): \<open>T(R(Q)) = {d | r(d) \<in> T(Q)}\<close>, \<open>F(R(Q)) = {d | r(d) \<in> F(Q)}\<close>.\<close>

definition R_ren_ext :: "('n \<rightharpoonup> 'n option) \<Rightarrow> ('n, 'v) state rpred \<Rightarrow> ('n, 'v) state rpred" where
  "R_ren_ext \<rho> Q = ({d. ren_ext \<rho> d \<in> R_T Q}, {d. ren_ext \<rho> d \<in> R_F Q})"

lemma rval_R_ren_ext: "rval (R_ren_ext \<rho> Q) d = rval Q (ren_ext \<rho> d)"
  by (simp add: rval_def R_ren_ext_def)

definition R_ren :: "('n \<rightharpoonup> 'n) \<Rightarrow> ('n, 'v) state rpred \<Rightarrow> ('n, 'v) state rpred" where
  "R_ren \<sigma> Q = ({d. ren \<sigma> d \<in> R_T Q}, {d. ren \<sigma> d \<in> R_F Q})"

lemma R_ren_is_R_ren_ext: "R_ren \<sigma> = R_ren_ext (trad \<sigma>)"
  by (intro ext) (simp add: R_ren_def R_ren_ext_def ren_is_ren_ext)

text \<open>On P-predicates, renomination is precomposition with \<open>r\<close>, and the quantifier is the
  strong Kleene existential quantifier.\<close>

lemma pval_R_ren_ext: "pval (R_ren_ext \<rho> Q) d = pval Q (ren_ext \<rho> d)"
  by (simp add: pval_def R_ren_ext_def)

lemma pval_Some_True: "pval Q d = Some True \<longleftrightarrow> d \<in> R_T Q"
  by (simp add: pval_def)

lemma pval_Some_False: "P_pred Q \<Longrightarrow> pval Q d = Some False \<longleftrightarrow> d \<in> R_F Q"
  by (auto simp: pval_def P_pred_def)

lemma pval_R_ex:
  assumes "P_pred Q"
  shows "pval (R_ex x Q) d =
    (if \<exists>a. pval Q (d(x \<mapsto> a)) = Some True then Some True
     else if \<forall>a. pval Q (d(x \<mapsto> a)) = Some False then Some False else None)"
  using assms by (auto simp: pval_def R_ex_domains P_pred_def)


section \<open>Closure under the base compositions\<close>

text \<open>[8], p. 26: the classes of P-predicates, of monotone (RM) R-predicates and of equitone
  (PE) P-predicates are closed under the base compositions
  \<open>C\<^sub>\<down>\<^sub>\<bottom>\<^sub>Q = {\<not>, \<or>, R\<^sup>v\<^sup>,\<^sup>u\<^sub>x\<^sub>,\<^sub>\<bottom>, \<exists>x, \<down>z}\<close> and \<open>C\<^sub>\<down>\<^sub>Q = {\<not>, \<or>, R\<^sup>v\<^sub>x, \<exists>x, \<down>z}\<close> ([8], p. 25).
  TRIEL_Indicators proves this for \<open>\<not>\<close>, \<open>\<or>\<close> and \<open>\<down>z\<close>; here it is proved for \<open>\<exists>x\<close> and both
  renominations. Monotonicity is proved for every pointwise extension order with a
  reflexive order on values, and \<open>\<sqsubseteq>\<close> is the case of equality.\<close>

subsection \<open>P-predicates\<close>

lemma P_pred_R_not: "P_pred Q \<Longrightarrow> P_pred (R_not Q)"
  by (auto simp: P_pred_def R_not_def)

lemma P_pred_R_or: "P_pred Q\<^sub>1 \<Longrightarrow> P_pred Q\<^sub>2 \<Longrightarrow> P_pred (R_or Q\<^sub>1 Q\<^sub>2)"
  by (auto simp: P_pred_def R_or_def)

theorem P_pred_R_ex: "P_pred Q \<Longrightarrow> P_pred (R_ex x Q)"
  by (auto simp: P_pred_def R_ex_domains)

theorem P_pred_R_ren_ext: "P_pred Q \<Longrightarrow> P_pred (R_ren_ext \<rho> Q)"
  by (auto simp: P_pred_def R_ren_ext_def)

corollary P_pred_R_ren: "P_pred Q \<Longrightarrow> P_pred (R_ren \<sigma> Q)"
  by (simp add: R_ren_is_R_ren_ext P_pred_R_ren_ext)

subsection \<open>Monotone R-predicates\<close>

lemma rmono_R_not: "rmono le Q \<Longrightarrow> rmono le (R_not Q)"
  by (auto simp: rmono_iff R_not_def)

lemma rmono_R_or: "rmono le Q\<^sub>1 \<Longrightarrow> rmono le Q\<^sub>2 \<Longrightarrow> rmono le (R_or Q\<^sub>1 Q\<^sub>2)"
  by (auto simp: rmono_iff R_or_def)

theorem rmono_R_ex:
  assumes refl: "\<And>a. vle a a" and m: "rmono (pw_le vle) Q"
  shows "rmono (pw_le vle) (R_ex x Q)"
proof -
  have le: "pw_le vle (d\<^sub>1(x \<mapsto> a)) (d\<^sub>2(x \<mapsto> a))" if "pw_le vle d\<^sub>1 d\<^sub>2" for d\<^sub>1 d\<^sub>2 a
    using upd_mono_pw[OF refl that] .
  show ?thesis
    using m le unfolding rmono_iff R_ex_domains by blast
qed

theorem rmono_R_ren_ext:
  assumes "rmono (pw_le vle) Q"
  shows "rmono (pw_le vle) (R_ren_ext \<rho> Q)"
proof -
  have le: "pw_le vle (ren_ext \<rho> d\<^sub>1) (ren_ext \<rho> d\<^sub>2)" if "pw_le vle d\<^sub>1 d\<^sub>2" for d\<^sub>1 d\<^sub>2
    using ren_ext_mono_pw[OF that] .
  show ?thesis
    using assms le unfolding rmono_iff R_ren_ext_def R_T_pair R_F_pair by blast
qed

corollary rmono_R_ren: "rmono (pw_le vle) Q \<Longrightarrow> rmono (pw_le vle) (R_ren \<sigma> Q)"
  by (simp add: R_ren_is_R_ren_ext rmono_R_ren_ext)

lemma DownInd_rmono_pw: "rmono (pw_le vle) (DownInd z :: ('n, 'v) state rpred)"
proof -
  have "z \<in> dom d\<^sub>2" if le: "pw_le vle d\<^sub>1 d\<^sub>2" and z: "z \<in> dom d\<^sub>1" for d\<^sub>1 d\<^sub>2 :: "('n, 'v) state"
  proof -
    from z obtain a where "d\<^sub>1 z = Some a" by auto
    with le obtain a' where "d\<^sub>2 z = Some a'" unfolding pw_le_def by blast
    then show ?thesis by auto
  qed
  then show ?thesis by (auto simp: rmono_iff DownInd_def)
qed

subsection \<open>Equitone P-predicates\<close>

theorem equitone_R_ex_pw:
  "(\<And>a. vle a a) \<Longrightarrow> equitone_R (pw_le vle) Q \<Longrightarrow> equitone_R (pw_le vle) (R_ex x Q)"
  by (simp add: equitone_R_iff P_pred_R_ex rmono_R_ex)

theorem equitone_R_ren_ext_pw:
  "equitone_R (pw_le vle) Q \<Longrightarrow> equitone_R (pw_le vle) (R_ren_ext \<rho> Q)"
  by (simp add: equitone_R_iff P_pred_R_ren_ext rmono_R_ren_ext)

text \<open>For the extension \<open>d \<subseteq> d'\<close> of [8]:\<close>

theorem equitone_R_ex: "equitone_R (\<sqsubseteq>) Q \<Longrightarrow> equitone_R (\<sqsubseteq>) (R_ex x Q)"
  using equitone_R_ex_pw[of "(=)" Q x] by (simp add: pw_le_eq)

theorem equitone_R_ren_ext: "equitone_R (\<sqsubseteq>) Q \<Longrightarrow> equitone_R (\<sqsubseteq>) (R_ren_ext \<rho> Q)"
  using equitone_R_ren_ext_pw[of "(=)" Q \<rho>] by (simp add: pw_le_eq)

corollary equitone_R_ren: "equitone_R (\<sqsubseteq>) Q \<Longrightarrow> equitone_R (\<sqsubseteq>) (R_ren \<sigma> Q)"
  by (simp add: R_ren_is_R_ren_ext equitone_R_ren_ext)

subsection \<open>The closure\<close>

text \<open>The predicates built from a set \<open>B\<close> of R-predicates by the compositions of
  \<open>C\<^sub>\<down>\<^sub>\<bottom>\<^sub>Q\<close>. Traditional renomination is a special case (\<open>comp_closure_ren\<close>), so the closure
  under \<open>C\<^sub>\<down>\<^sub>Q\<close> is contained in this set. So is the closure under \<open>\<not>\<close>, \<open>\<or>\<close> and \<open>\<down>z\<close> of
  TRIEL_Indicators (\<open>equitone_closure_sub\<close>).\<close>

inductive_set comp_closure :: "('n, 'v) state rpred set \<Rightarrow> ('n, 'v) state rpred set"
  for B :: "('n, 'v) state rpred set" where
  base: "Q \<in> B \<Longrightarrow> Q \<in> comp_closure B"
| down: "DownInd z \<in> comp_closure B"
| neg: "Q \<in> comp_closure B \<Longrightarrow> R_not Q \<in> comp_closure B"
| disj: "Q\<^sub>1 \<in> comp_closure B \<Longrightarrow> Q\<^sub>2 \<in> comp_closure B \<Longrightarrow> R_or Q\<^sub>1 Q\<^sub>2 \<in> comp_closure B"
| ren_ext: "Q \<in> comp_closure B \<Longrightarrow> R_ren_ext \<rho> Q \<in> comp_closure B"
| ex: "Q \<in> comp_closure B \<Longrightarrow> R_ex x Q \<in> comp_closure B"

lemma comp_closure_ren: "Q \<in> comp_closure B \<Longrightarrow> R_ren \<sigma> Q \<in> comp_closure B"
  by (simp add: R_ren_is_R_ren_ext comp_closure.ren_ext)

lemma equitone_closure_sub: "equitone_closure B \<subseteq> comp_closure B"
proof
  fix Q assume "Q \<in> equitone_closure B"
  then show "Q \<in> comp_closure B"
    by induction (auto intro: comp_closure.intros)
qed

theorem comp_closure_P:
  assumes "\<And>Q. Q \<in> B \<Longrightarrow> P_pred Q" and "Q \<in> comp_closure B"
  shows "P_pred Q"
  using assms(2)
  by induction
     (simp_all add: assms(1) DownInd_P_pred P_pred_R_not P_pred_R_or P_pred_R_ren_ext P_pred_R_ex)

theorem comp_closure_rmono:
  assumes "\<And>a. vle a a" and "\<And>Q. Q \<in> B \<Longrightarrow> rmono (pw_le vle) Q" and "Q \<in> comp_closure B"
  shows "rmono (pw_le vle) Q"
  using assms(3)
proof induction
  case (ex Q x)
  show ?case by (rule rmono_R_ex[where vle = vle, OF assms(1) ex.IH])
qed (simp_all add: assms(2) DownInd_rmono_pw rmono_R_not rmono_R_or rmono_R_ren_ext)

theorem comp_closure_equitone_pw:
  assumes "\<And>a. vle a a" and "\<And>Q. Q \<in> B \<Longrightarrow> equitone_R (pw_le vle) Q" and "Q \<in> comp_closure B"
  shows "equitone_R (pw_le vle) Q"
proof -
  have B: "P_pred Q'" "rmono (pw_le vle) Q'" if "Q' \<in> B" for Q'
    using assms(2)[OF that] by (simp_all add: equitone_R_iff)
  have "P_pred Q"
    by (rule comp_closure_P[OF B(1) assms(3)])
  moreover have "rmono (pw_le vle) Q"
    by (rule comp_closure_rmono[where vle = vle, OF assms(1) B(2) assms(3)])
  ultimately show ?thesis by (simp add: equitone_R_iff)
qed

text \<open>The claim of [8], p. 26, for the equitone P-predicates: built from equitone
  P-predicates by the compositions of \<open>C\<^sub>\<down>\<^sub>\<bottom>\<^sub>Q\<close> (or of \<open>C\<^sub>\<down>\<^sub>Q\<close>), a predicate is an equitone
  P-predicate.\<close>

theorem comp_closure_equitone:
  assumes "\<And>Q. Q \<in> B \<Longrightarrow> equitone_R (\<sqsubseteq>) Q" and "Q \<in> comp_closure B"
  shows "equitone_R (\<sqsubseteq>) Q"
proof -
  have "equitone_R (pw_le (=)) Q"
    by (rule comp_closure_equitone_pw[OF _ _ assms(2)]) (simp_all add: pw_le_eq assms(1))
  then show ?thesis by (simp add: pw_le_eq)
qed

text \<open>The same page states that the classes of total predicates are not closed, because
  \<open>\<down>z\<close> is not total: the empty named set is in neither of its domains.\<close>

theorem DownInd_not_total: "\<not> total_R (DownInd z :: ('n, 'v) state rpred)"
proof
  assume "total_R (DownInd z :: ('n, 'v) state rpred)"
  then have "(Map.empty :: ('n, 'v) state) \<in> R_T (DownInd z) \<union> R_F (DownInd z)"
    unfolding total_R_def by blast
  then show False by (simp add: DownInd_def)
qed


section \<open>The variable unassignment predicate of [2]\<close>

text \<open>[2], p. 266: \<open>T(\<epsilon>z) = {d | z \<notin> asn(d)}\<close>, \<open>F(\<epsilon>z) = {d | z \<in> asn(d)}\<close>, where
  \<open>asn(d)\<close> is the set of names assigned in \<open>d\<close> ([2], p. 265), that is \<open>dom d\<close>. \<open>\<epsilon>z\<close> is a
  0-ary composition of the extended algebra of [2]. \<open>E\<^sub>z\<close> is its negation, so \<open>E\<^sub>z\<close> is a term
  of that algebra. It is not a composition of \<open>C\<^sub>\<down>\<^sub>\<bottom>\<^sub>Q\<close>.\<close>

definition eps_R :: "'n \<Rightarrow> ('n, 'v) state rpred" where
  "eps_R z = ({d. z \<notin> dom d}, {d. z \<in> dom d})"

theorem Ex_R_is_not_eps: "Ex_R z = R_not (eps_R z)"
  by (simp add: Ex_R_def R_not_def eps_R_def)


section \<open>Formulas as terms of the composition algebra\<close>

text \<open>[8], section 2, p. 26: the terms of the composition algebra are the formulas of the
  language. The set \<open>Fr\<close> of formulas is defined inductively:
  Fa) \<open>Ps \<subseteq> Fr\<close>; F\<open>\<down>\<close>) \<open>\<down>z \<in> Fr\<close>; Fp) \<open>\<Phi>, \<Psi> \<in> Fr \<Longrightarrow> \<not>\<Phi> \<in> Fr, \<or>\<Phi>\<Psi> \<in> Fr\<close>;
  FR\<open>\<bottom>\<close>) \<open>\<Phi> \<in> Fr \<Longrightarrow> R\<^sup>v\<^sup>,\<^sup>u\<^sub>x\<^sub>,\<^sub>\<bottom>\<Phi> \<in> Fr\<close>; F\<open>\<exists>\<close>) \<open>\<Phi> \<in> Fr \<Longrightarrow> \<exists>x\<Phi> \<in> Fr\<close>.
  Here the formulas also include \<open>E\<^sub>z\<close> (\<open>FE\<close>), the term \<open>\<not>\<epsilon>z\<close> of [2], so that the atoms
  \<open>E\<^sub>p\<close> of TRIEL conditions can be translated. A formula without \<open>FE\<close> is a formula of [8].\<close>

datatype ('p, 'n) fm =
    FPs 'p
  | FDown 'n
  | FE 'n
  | FNot "('p, 'n) fm"
  | FOr "('p, 'n) fm" "('p, 'n) fm"
  | FRen "'n \<rightharpoonup> 'n option" "('p, 'n) fm"
  | FExists 'n "('p, 'n) fm"

text \<open>The interpretation ([8], p. 26): a map \<open>I : Ps \<rightarrow> PrR\<close> extends to formulas by
  Ip) \<open>I(\<not>\<Phi>) = \<not>(I(\<Phi>))\<close>, \<open>I(\<or>\<Phi>\<Psi>) = \<or>(I(\<Phi>), I(\<Psi>))\<close>; IR\<open>\<bottom>\<close>) \<open>I(R\<Phi>) = R(I(\<Phi>))\<close>;
  I\<open>\<exists>\<close>) \<open>I(\<exists>x\<Phi>) = \<exists>x(I(\<Phi>))\<close>. The symbols \<open>\<down>x\<close> denote the indicators.\<close>

primrec interp :: "('p \<Rightarrow> ('n, 'v) state rpred) \<Rightarrow> ('p, 'n) fm \<Rightarrow> ('n, 'v) state rpred" where
  "interp I (FPs p) = I p"
| "interp I (FDown z) = DownInd z"
| "interp I (FE z) = Ex_R z"
| "interp I (FNot \<Phi>) = R_not (interp I \<Phi>)"
| "interp I (FOr \<Phi> \<Psi>) = R_or (interp I \<Phi>) (interp I \<Psi>)"
| "interp I (FRen \<rho> \<Phi>) = R_ren_ext \<rho> (interp I \<Phi>)"
| "interp I (FExists x \<Phi>) = R_ex x (interp I \<Phi>)"

primrec E_free :: "('p, 'n) fm \<Rightarrow> bool" where
  "E_free (FPs p) = True"
| "E_free (FDown z) = True"
| "E_free (FE z) = False"
| "E_free (FNot \<Phi>) = E_free \<Phi>"
| "E_free (FOr \<Phi> \<Psi>) = (E_free \<Phi> \<and> E_free \<Psi>)"
| "E_free (FRen \<rho> \<Phi>) = E_free \<Phi>"
| "E_free (FExists x \<Phi>) = E_free \<Phi>"

theorem interp_comp_closure: "E_free \<Phi> \<Longrightarrow> interp I \<Phi> \<in> comp_closure (range I)"
  by (induction \<Phi>) (auto intro: comp_closure.intros)

theorem interp_P_pred: "(\<And>p. P_pred (I p)) \<Longrightarrow> P_pred (interp I \<Phi>)"
  by (induction \<Phi>)
     (simp_all add: DownInd_P_pred Ex_R_P_pred P_pred_R_not P_pred_R_or P_pred_R_ren_ext P_pred_R_ex)

theorem interp_equitone_pw:
  assumes "\<And>a. vle a a" and "\<And>p. equitone_R (pw_le vle) (I p)" and "E_free \<Phi>"
  shows "equitone_R (pw_le vle) (interp I \<Phi>)"
  using comp_closure_equitone_pw[where vle = vle, OF assms(1) _ interp_comp_closure[OF assms(3)]] assms(2) by blast

theorem interp_equitone:
  assumes "\<And>p. equitone_R (\<sqsubseteq>) (I p)" and "E_free \<Phi>"
  shows "equitone_R (\<sqsubseteq>) (interp I \<Phi>)"
  using comp_closure_equitone[OF _ interp_comp_closure[OF assms(2)]] assms(1) by blast


section \<open>Conditions of TRIEL as terms\<close>

text \<open>A nominative datum \<open>d\<close> gives a V-A-named set whose names are the complex names and
  whose values are data: \<open>p \<mapsto> d(p)\<close>. On these named sets the order \<open>\<le>\<close> of nominative data
  is the pointwise extension in which an atom stays the same atom and a record stays a
  record (\<open>nd_le_pw\<close>).\<close>

definition nd_named :: "('n, 'b) nd \<Rightarrow> ('n list, ('n, 'b) nd) state" where
  "nd_named d = (\<lambda>p. den_path p d)"

definition nd_vle :: "('n, 'b) nd \<Rightarrow> ('n, 'b) nd \<Rightarrow> bool" where
  "nd_vle a a' \<longleftrightarrow> (\<forall>b. a = Atom b \<longrightarrow> a' = Atom b) \<and> (\<forall>m. a = Nom m \<longrightarrow> (\<exists>m'. a' = Nom m'))"

lemma nd_vle_refl: "nd_vle a a"
  by (cases a) (simp_all add: nd_vle_def)

theorem nd_le_pw: "nd_le d d' \<longleftrightarrow> pw_le nd_vle (nd_named d) (nd_named d')"
proof
  assume le: "nd_le d d'"
  show "pw_le nd_vle (nd_named d) (nd_named d')"
    unfolding pw_le_def nd_named_def
  proof (intro allI impI)
    fix p a assume a: "den_path p d = Some a"
    show "\<exists>a'. den_path p d' = Some a' \<and> nd_vle a a'"
    proof (cases a)
      case (Atom b)
      with a le have "den_path p d' = Some (Atom b)" unfolding nd_le_def by blast
      with Atom show ?thesis by (simp add: nd_vle_def)
    next
      case (Nom m)
      with a le obtain m' where "den_path p d' = Some (Nom m')" unfolding nd_le_def by blast
      with Nom show ?thesis by (simp add: nd_vle_def)
    qed
  qed
next
  assume "pw_le nd_vle (nd_named d) (nd_named d')"
  then show "nd_le d d'"
    unfolding nd_le_def pw_le_def nd_named_def nd_vle_def by fastforce
qed

text \<open>The atom ``\<open>p\<close> is an atom of primitive type \<open>q\<close>'' (\<open>is_prim\<close>) as a base predicate on
  these named sets.\<close>

fun is_R :: "('p \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'n list \<times> 'p \<Rightarrow> ('n list, ('n, 'b) nd) state rpred" where
  "is_R I (p, q) =
     ({\<sigma>. \<exists>b. \<sigma> p = Some (Atom b) \<and> I q b},
      {\<sigma>. (\<exists>b. \<sigma> p = Some (Atom b) \<and> \<not> I q b) \<or> (\<exists>m. \<sigma> p = Some (Nom m))})"

lemma is_R_P_pred: "P_pred (is_R I pq)"
  by (cases pq) (auto simp: P_pred_def)

lemma pw_nd_atom: "pw_le nd_vle \<sigma> \<sigma>' \<Longrightarrow> \<sigma> p = Some (Atom b) \<Longrightarrow> \<sigma>' p = Some (Atom b)"
  unfolding pw_le_def nd_vle_def by fastforce

lemma pw_nd_nom: "pw_le nd_vle \<sigma> \<sigma>' \<Longrightarrow> \<sigma> p = Some (Nom m) \<Longrightarrow> \<exists>m'. \<sigma>' p = Some (Nom m')"
  unfolding pw_le_def nd_vle_def by fastforce

lemma is_R_equitone: "equitone_R (pw_le nd_vle) (is_R I pq)"
proof (cases pq)
  case (Pair p q)
  have "rmono (pw_le nd_vle) (is_R I (p, q))"
    unfolding rmono_iff by (auto dest: pw_nd_atom pw_nd_nom)
  with Pair is_R_P_pred[of I pq] show ?thesis by (simp add: equitone_R_iff)
qed

text \<open>The translation. The atoms \<open>E\<^sub>p\<close>, \<open>\<down>p\<close> and type checks go to \<open>FE\<close>, \<open>FDown\<close> and base
  predicates. NOT and OR go to the compositions \<open>\<not>\<close> and \<open>\<or>\<close>. There is no conjunction among
  the base compositions ([8], p. 25), so AND goes to \<open>\<not>(\<not>\<Phi> \<or> \<not>\<Psi>)\<close>.\<close>

primrec catom_fm :: "('n, 'p) catom \<Rightarrow> ('n list \<times> 'p, 'n list) fm" where
  "catom_fm (AEx p) = FE p"
| "catom_fm (ADown p) = FDown p"
| "catom_fm (AIs p q) = FPs (p, q)"

primrec cond_fm :: "('n, 'p) catom cond \<Rightarrow> ('n list \<times> 'p, 'n list) fm" where
  "cond_fm (CAtom a) = catom_fm a"
| "cond_fm (CNot \<phi>) = FNot (cond_fm \<phi>)"
| "cond_fm (CAnd \<phi> \<psi>) = FNot (FOr (FNot (cond_fm \<phi>)) (FNot (cond_fm \<psi>)))"
| "cond_fm (COr \<phi> \<psi>) = FOr (cond_fm \<phi>) (cond_fm \<psi>)"

lemma pval_catom_fm: "pval (interp (is_R I) (catom_fm a)) (nd_named d) = catom_eval I a d"
proof (cases a)
  case (AEx p)
  then show ?thesis by (simp add: pval_Ex_R Ex_ind_def Ex_nd_def nd_named_def domIff)
next
  case (ADown p)
  then show ?thesis by (simp add: pval_def DownInd_def present_partial_def nd_named_def domIff)
next
  case (AIs p q)
  then show ?thesis
    by (auto simp: pval_def is_prim_def nd_named_def split: option.split nd.split)
qed

lemma interp_is_R_P_pred: "P_pred (interp (is_R I) \<Phi>)"
  by (rule interp_P_pred) (rule is_R_P_pred)

lemma pval_R_not_apply: "P_pred Q \<Longrightarrow> pval (R_not Q) d = knot (pval Q d)"
  by (simp add: pval_R_not)

lemma kand_de_morgan: "kand p q = knot (kor (knot p) (knot q))"
  using bool_option_cases[of p] bool_option_cases[of q] by (auto simp: kand_def kor_def)

text \<open>Every TRIEL condition is a term of the composition algebra: its value is the value of
  the interpretation of its translation.\<close>

theorem cond_fm_correct:
  "pval (interp (is_R I) (cond_fm \<phi>)) (nd_named d) = cond_eval (catom_eval I) \<phi> d"
  by (induction \<phi>)
     (simp_all add: pval_catom_fm pval_R_not_apply pval_R_or interp_is_R_P_pred P_pred_R_not
       P_pred_R_or kand_de_morgan)

lemma catom_fm_E_free: "E_free (catom_fm a) = Ex_free_atom a"
  by (cases a) simp_all

lemma cond_fm_E_free: "(\<And>a. a \<in> cond_atoms \<phi> \<Longrightarrow> Ex_free_atom a) \<Longrightarrow> E_free (cond_fm \<phi>)"
  by (induction \<phi>) (simp_all add: catom_fm_E_free)

text \<open>Stability of verdicts (theorem 5 of TRIEL_Indicators) again, now from the closure of
  the equitone P-predicates under the base compositions.\<close>

theorem cond_equitone_from_closure:
  assumes "\<And>a. a \<in> cond_atoms \<phi> \<Longrightarrow> Ex_free_atom a"
  shows "equitone_nd (cond_eval (catom_eval I) \<phi>)"
proof -
  let ?Q = "interp (is_R I) (cond_fm \<phi>)"
  have "equitone_R (pw_le nd_vle) ?Q"
    by (rule interp_equitone_pw[where vle = nd_vle, OF nd_vle_refl is_R_equitone cond_fm_E_free[OF assms]])
  then have e: "equitone_on (pw_le nd_vle) (pval ?Q)"
    by (simp add: equitone_R_def)
  show ?thesis
    unfolding equitone_nd_def
  proof (intro allI impI)
    fix d d' assume a: "cond_eval (catom_eval I) \<phi> d \<noteq> None \<and> nd_le d d'"
    then have "pval ?Q (nd_named d) \<noteq> None" "pw_le nd_vle (nd_named d) (nd_named d')"
      by (simp_all add: cond_fm_correct nd_le_pw[symmetric])
    with e have "pval ?Q (nd_named d') = pval ?Q (nd_named d)"
      unfolding equitone_on_def by blast
    then show "cond_eval (catom_eval I) \<phi> d' = cond_eval (catom_eval I) \<phi> d"
      by (simp add: cond_fm_correct)
  qed
qed

corollary verdict_stable_from_closure:
  assumes "\<And>a. a \<in> cond_atoms \<phi> \<Longrightarrow> Ex_free_atom a"
    and "nd_le d d'" and "cond_eval (catom_eval I) \<phi> d = Some b"
  shows "cond_eval (catom_eval I) \<phi> d' = Some b"
  using cond_equitone_from_closure[OF assms(1)] assms(2,3) unfolding equitone_nd_def by fastforce

end
