(*  Title:      TRIEL_ND.thy
    Purpose:    TRIEL data (records, optional values, nesting) as multi-level nominative
                data; expressions, PRESENT and Ex over such data with complex names;
                a typing predicate for Record and Optional.
    Source:     The definition of nominative data follows the Mizar formalisation
                I. Ivanov, M. Nikitchenko, A. Kryvolap, A. Kornilowicz. Simple-named
                complex-valued nominative data -- definition and basic operations.
                Formalized Mathematics 25(3), 2017, 205-216 (reference [7] of FOUNDATIONS.md).
*)

theory TRIEL_ND
  imports TRIEL_Ex "HOL-Library.Finite_Map"
begin

section \<open>Nominative data\<close>

text \<open>Simple-named complex-valued nominative data, following the Mizar formalisation
  NOMIN_1 of Ivanov, Nikitchenko, Kryvolap and Kornilowicz: a datum is either a basic
  value (an atom) or a finite partial map from names to data. Every map is finite and
  every datum has finite depth, which corresponds to the rank sequences of NOMIN_1.\<close>

datatype ('n, 'b) nd = Atom 'b | Nom "('n, ('n, 'b) nd) fmap"

subsection \<open>Operations of NOMIN_1\<close>

text \<open>Denaming \<open>v\<Rightarrow>\<close> takes the value named \<open>v\<close>; naming \<open>\<Rightarrow>v\<close> builds the datum
  \<open>[v \<mapsto> d]\<close>; global overlapping \<open>d\<^sub>1 \<nabla> d\<^sub>2\<close> is \<open>d\<^sub>2 \<union> d\<^sub>1|(dom d\<^sub>1 - dom d\<^sub>2)\<close>, so \<open>d\<^sub>2\<close> wins;
  local overlapping replaces the value of one name.\<close>

fun denaming :: "'n \<Rightarrow> ('n, 'b) nd \<Rightarrow> ('n, 'b) nd option" where
  "denaming v (Nom m) = fmlookup m v"
| "denaming v (Atom b) = None"

definition naming :: "'n \<Rightarrow> ('n, 'b) nd \<Rightarrow> ('n, 'b) nd" where
  "naming v d = Nom (fmupd v d fmempty)"

fun global_overlapping :: "('n, 'b) nd \<Rightarrow> ('n, 'b) nd \<Rightarrow> ('n, 'b) nd" where
  "global_overlapping (Nom m\<^sub>1) (Nom m\<^sub>2) = Nom (fmadd m\<^sub>1 m\<^sub>2)"
| "global_overlapping d\<^sub>1 d\<^sub>2 = d\<^sub>2"

definition local_overlapping :: "('n, 'b) nd \<Rightarrow> ('n, 'b) nd \<Rightarrow> 'n \<Rightarrow> ('n, 'b) nd" where
  "local_overlapping d\<^sub>1 d\<^sub>2 v = global_overlapping d\<^sub>1 (naming v d\<^sub>2)"

lemma denaming_naming [simp]: "denaming v (naming v d) = Some d"
  by (simp add: naming_def)

lemma denaming_local_overlapping_same: "denaming v (local_overlapping d\<^sub>1 d\<^sub>2 v) = Some d\<^sub>2"
  by (cases d\<^sub>1) (simp_all add: local_overlapping_def naming_def)

lemma denaming_local_overlapping_other:
  "u \<noteq> v \<Longrightarrow> denaming u (local_overlapping (Nom m) d\<^sub>2 v) = denaming u (Nom m)"
  by (simp add: local_overlapping_def naming_def)

subsection \<open>Complex names\<close>

text \<open>A complex name (a path \<open>x\<^sub>1.x\<^sub>2. \<dots> .x\<^sub>k\<close>, as in TRIEL's \<open>factor_ref\<close>) is a list of
  names; its value is obtained by successive denaming.\<close>

fun den_path :: "'n list \<Rightarrow> ('n, 'b) nd \<Rightarrow> ('n, 'b) nd option" where
  "den_path [] d = Some d"
| "den_path (x # p) d = (case denaming x d of None \<Rightarrow> None | Some d' \<Rightarrow> den_path p d')"

lemma den_path_Nom: "den_path (x # p) (Nom m) = (case fmlookup m x of None \<Rightarrow> None | Some y \<Rightarrow> den_path p y)"
  by simp

lemma den_path_Atom: "den_path (x # p) (Atom b) = None"
  by simp

lemma den_path_child: "fmlookup m x = Some y \<Longrightarrow> den_path (x # p) (Nom m) = den_path p y"
  by simp


section \<open>The information order on nominative data\<close>

text \<open>\<open>d \<le> d'\<close> (\<open>nd_le\<close>): every atom of \<open>d\<close> is an atom of \<open>d'\<close> at the same complex name, and
  every inner node of \<open>d\<close> is an inner node of \<open>d'\<close>. So \<open>d'\<close> may add names at any depth,
  but does not change or remove anything present in \<open>d\<close>.\<close>

definition nd_le :: "('n, 'b) nd \<Rightarrow> ('n, 'b) nd \<Rightarrow> bool" where
  "nd_le d d' \<longleftrightarrow>
     (\<forall>p b. den_path p d = Some (Atom b) \<longrightarrow> den_path p d' = Some (Atom b)) \<and>
     (\<forall>p m. den_path p d = Some (Nom m) \<longrightarrow> (\<exists>m'. den_path p d' = Some (Nom m')))"

lemma nd_le_refl: "nd_le d d"
  by (simp add: nd_le_def)

lemma nd_le_trans: "nd_le d\<^sub>1 d\<^sub>2 \<Longrightarrow> nd_le d\<^sub>2 d\<^sub>3 \<Longrightarrow> nd_le d\<^sub>1 d\<^sub>3"
  unfolding nd_le_def by blast

lemma nd_le_defined: "nd_le d d' \<Longrightarrow> den_path p d \<noteq> None \<Longrightarrow> den_path p d' \<noteq> None"
  unfolding nd_le_def by (metis nd.exhaust option.distinct(1) option.exhaust)

lemma nd_le_Atom: "nd_le (Atom b) d' \<longleftrightarrow> d' = Atom b"
proof
  assume "nd_le (Atom b) d'"
  then have "den_path [] d' = Some (Atom b)"
    unfolding nd_le_def by (metis den_path.simps(1))
  then show "d' = Atom b" by simp
qed (simp add: nd_le_refl)

text \<open>The order seen node by node: an inner node is below another inner node when every
  child is below the child of the same name.\<close>

lemma nd_le_NomD:
  assumes "nd_le (Nom m) d'"
  shows "\<exists>m'. d' = Nom m' \<and>
           (\<forall>x y. fmlookup m x = Some y \<longrightarrow> (\<exists>y'. fmlookup m' x = Some y' \<and> nd_le y y'))"
proof -
  from assms have "\<exists>m'. den_path [] d' = Some (Nom m')"
    unfolding nd_le_def by (metis den_path.simps(1))
  then obtain m' where d': "d' = Nom m'" by auto
  have "\<exists>y'. fmlookup m' x = Some y' \<and> nd_le y y'" if y: "fmlookup m x = Some y" for x y
  proof -
    have "den_path [x] (Nom m) \<noteq> None" using y by simp
    with assms have "den_path [x] (Nom m') \<noteq> None"
      unfolding d' by (rule nd_le_defined)
    then obtain y' where y': "fmlookup m' x = Some y'"
      by (auto split: option.splits)
    have "nd_le y y'"
      unfolding nd_le_def
    proof (intro conjI allI impI)
      fix p b assume "den_path p y = Some (Atom b)"
      then have "den_path (x # p) (Nom m) = Some (Atom b)" using y by simp
      with assms have "den_path (x # p) (Nom m') = Some (Atom b)"
        unfolding d' nd_le_def by blast
      then show "den_path p y' = Some (Atom b)" using y' by simp
    next
      fix p n assume "den_path p y = Some (Nom n)"
      then have "den_path (x # p) (Nom m) = Some (Nom n)" using y by simp
      with assms obtain n' where "den_path (x # p) (Nom m') = Some (Nom n')"
        unfolding d' nd_le_def by blast
      then show "\<exists>n'. den_path p y' = Some (Nom n')" using y' by simp
    qed
    with y' show ?thesis by blast
  qed
  with d' show ?thesis by blast
qed

text \<open>\<open>nd_le\<close> is a partial order.\<close>

lemma nd_le_antisym: "nd_le d d' \<Longrightarrow> nd_le d' d \<Longrightarrow> d = d'"
proof (induction d arbitrary: d')
  case (Atom b)
  then show ?case by (simp add: nd_le_Atom)
next
  case (Nom m)
  from nd_le_NomD[OF Nom.prems(1)] obtain m' where d': "d' = Nom m'"
    and down: "\<And>x y. fmlookup m x = Some y \<Longrightarrow> \<exists>y'. fmlookup m' x = Some y' \<and> nd_le y y'"
    by blast
  from nd_le_NomD[OF Nom.prems(2)[unfolded d']]
  have up': "\<And>x y. fmlookup m' x = Some y \<Longrightarrow> \<exists>y'. fmlookup m x = Some y' \<and> nd_le y y'"
    by auto
  have "fmlookup m x = fmlookup m' x" for x
  proof (cases "fmlookup m x")
    case None
    then show ?thesis using up' by (cases "fmlookup m' x") fastforce+
  next
    case (Some y)
    with down obtain y' where y': "fmlookup m' x = Some y'" "nd_le y y'" by blast
    with up' Some have "nd_le y' y" by fastforce
    moreover have "y \<in> fmran' m" using Some by (rule fmran'I)
    ultimately have "y = y'" using Nom.IH y'(2) by blast
    with Some y' show ?thesis by simp
  qed
  then show ?case unfolding d' by (simp add: fmap_ext)
qed


section \<open>Flattening\<close>

text \<open>The bridge to the expression core: \<open>flat d\<close> is the state over complex names that
  maps every complex name leading to an atom to that atom. Inner nodes are not in its
  domain.\<close>

definition flat :: "('n, 'b) nd \<Rightarrow> ('n list, 'b) state" where
  "flat d p = (case den_path p d of Some (Atom b) \<Rightarrow> Some b | _ \<Rightarrow> None)"

lemma flat_Some: "flat d p = Some b \<longleftrightarrow> den_path p d = Some (Atom b)"
  by (auto simp: flat_def split: option.splits nd.splits)

theorem flat_mono:
  assumes "nd_le d d'"
  shows "flat d \<sqsubseteq> flat d'"
  unfolding info_le_def
proof
  fix p assume "p \<in> dom (flat d)"
  then obtain b where b: "flat d p = Some b" by auto
  then have "den_path p d = Some (Atom b)" by (simp add: flat_Some)
  with assms have "den_path p d' = Some (Atom b)" unfolding nd_le_def by blast
  then have "flat d' p = Some b" by (simp add: flat_Some)
  with b show "flat d' p = flat d p" by simp
qed


section \<open>Expressions over nominative data\<close>

text \<open>Expressions are those of TRIEL_Core with complex names. A complex name denotes a
  basic value only when it leads to an atom; a name that leads to a record, or to nothing,
  is undefined in comparisons (\<open>\<bottom>\<close>). \<open>PRESENT(p)\<close> asks whether \<open>p\<close> leads to anything,
  an atom or a record.\<close>

primrec evalV_nd :: "('n list, 'b) vexp \<Rightarrow> ('n, 'b) nd \<Rightarrow> 'b option" where
  "evalV_nd (VConst v) d = Some v"
| "evalV_nd (VName p) d = flat d p"

primrec eval_nd :: "('n list, 'b) expr \<Rightarrow> ('n, 'b) nd \<Rightarrow> bool option" where
  "eval_nd ETrue d = Some True"
| "eval_nd EFalse d = Some False"
| "eval_nd (EEq a c) d =
     (case evalV_nd a d of
        None \<Rightarrow> None
      | Some u \<Rightarrow> (case evalV_nd c d of None \<Rightarrow> None | Some w \<Rightarrow> Some (u = w)))"
| "eval_nd (ENot e) d = knot (eval_nd e d)"
| "eval_nd (EAnd e\<^sub>1 e\<^sub>2) d = kand (eval_nd e\<^sub>1 d) (eval_nd e\<^sub>2 d)"
| "eval_nd (EOr e\<^sub>1 e\<^sub>2) d = kor (eval_nd e\<^sub>1 d) (eval_nd e\<^sub>2 d)"
| "eval_nd (EImp e\<^sub>1 e\<^sub>2) d = kimp (eval_nd e\<^sub>1 d) (eval_nd e\<^sub>2 d)"
| "eval_nd (EPresent p) d = Some (den_path p d \<noteq> None)"

lemma evalV_nd_flat: "evalV_nd a d = evalV a (flat d)"
  by (cases a) simp_all

text \<open>On PRESENT-free expressions, evaluation over nominative data is evaluation of
  TRIEL_Core over the flattened state. This is how the theorems of TRIEL_Core carry over.\<close>

theorem eval_nd_flat: "present_free e \<Longrightarrow> eval_nd e d = eval e (flat d)"
  by (induction e) (simp_all add: evalV_nd_flat cong: option.case_cong)


section \<open>Ex for complex names\<close>

text \<open>The total indicator predicate for a complex name: true on data where \<open>p\<close> leads to a
  value, false on data where it does not.\<close>

definition Ex_nd :: "'n list \<Rightarrow> ('n, 'b) nd \<Rightarrow> bool option" where
  "Ex_nd p d = (if den_path p d \<noteq> None then Some True else Some False)"

definition equitone_nd :: "(('n, 'b) nd \<Rightarrow> bool option) \<Rightarrow> bool" where
  "equitone_nd Q \<longleftrightarrow> (\<forall>d d'. Q d \<noteq> None \<and> nd_le d d' \<longrightarrow> Q d' = Q d)"

lemma Ex_nd_domains:
  "{d. Ex_nd p d = Some True} = {d. den_path p d \<noteq> None}"
  "{d. Ex_nd p d = Some False} = {d. den_path p d = None}"
  by (auto simp: Ex_nd_def)

theorem present_nd_is_Ex: "eval_nd (EPresent p) = Ex_nd p"
  by (rule ext) (simp add: Ex_nd_def)

theorem Ex_nd_total: "Ex_nd p d \<noteq> None"
  by (auto simp: Ex_nd_def)

lemma nd_le_empty_naming: "nd_le (Nom fmempty) (naming x (Atom b) :: ('n, 'b) nd)"
  unfolding nd_le_def
proof (intro conjI allI impI)
  fix p c assume "den_path p (Nom fmempty :: ('n, 'b) nd) = Some (Atom c)"
  then show "den_path p (naming x (Atom b)) = Some (Atom c)" by (cases p) simp_all
next
  fix p and n :: "('n, ('n, 'b) nd) fmap"
  assume "den_path p (Nom fmempty :: ('n, 'b) nd) = Some (Nom n)"
  then have "p = []" by (cases p) simp_all
  then show "\<exists>n'. den_path p (naming x (Atom b)) = Some (Nom n')" by (simp add: naming_def)
qed

theorem Ex_nd_not_equitone: "\<not> equitone_nd (Ex_nd [x] :: ('n, 'b) nd \<Rightarrow> bool option)"
proof
  assume eq: "equitone_nd (Ex_nd [x] :: ('n, 'b) nd \<Rightarrow> bool option)"
  fix b :: 'b
  have "Ex_nd [x] (naming x (Atom b)) = Ex_nd [x] (Nom fmempty :: ('n, 'b) nd)"
    using eq nd_le_empty_naming[of x b] Ex_nd_total[of "[x]" "Nom fmempty :: ('n, 'b) nd"]
    unfolding equitone_nd_def by blast
  then show False by (simp add: Ex_nd_def naming_def)
qed

text \<open>A complex name that leads to an atom is present; the converse fails for records.\<close>

lemma Ex_ind_flat_imp_Ex_nd: "Ex_ind p (flat d) = Some True \<Longrightarrow> Ex_nd p d = Some True"
  by (auto simp: Ex_ind_def Ex_nd_def flat_def split: option.splits if_splits)


section \<open>The theorems of TRIEL_Core over nominative data\<close>

theorem T1_nd:
  "eval_nd (EAnd e\<^sub>1 e\<^sub>2) d = eval_nd (EAnd e\<^sub>2 e\<^sub>1) d"
  "eval_nd (EOr e\<^sub>1 e\<^sub>2) d = eval_nd (EOr e\<^sub>2 e\<^sub>1) d"
  "eval_nd (EAnd (EAnd e\<^sub>1 e\<^sub>2) e\<^sub>3) d = eval_nd (EAnd e\<^sub>1 (EAnd e\<^sub>2 e\<^sub>3)) d"
  "eval_nd (EOr (EOr e\<^sub>1 e\<^sub>2) e\<^sub>3) d = eval_nd (EOr e\<^sub>1 (EOr e\<^sub>2 e\<^sub>3)) d"
  "eval_nd (ENot (EAnd e\<^sub>1 e\<^sub>2)) d = eval_nd (EOr (ENot e\<^sub>1) (ENot e\<^sub>2)) d"
  "eval_nd (ENot (EOr e\<^sub>1 e\<^sub>2)) d = eval_nd (EAnd (ENot e\<^sub>1) (ENot e\<^sub>2)) d"
  "eval_nd (ENot (ENot e)) d = eval_nd e d"
  subgoal by (simp add: kand_commute)
  subgoal by (simp add: kor_commute)
  subgoal by (simp add: kand_assoc)
  subgoal by (simp add: kor_assoc)
  subgoal by (simp add: knot_kand)
  subgoal by (simp add: knot_kor)
  subgoal by (simp add: knot_knot)
  done

text \<open>Monotonicity (T2, the claim of TECHNICAL_REPORT.md section 2.9) under the deep
  information order, obtained from T2 through \<open>flat\<close>.\<close>

theorem T2_nd_monotone:
  assumes "present_free e" and "nd_le d d'" and "eval_nd e d = Some b"
  shows "eval_nd e d' = Some b"
proof -
  have "eval e (flat d) = Some b" using assms(1,3) by (simp add: eval_nd_flat)
  then have "eval e (flat d') = Some b"
    by (rule T2_monotone[OF assms(1) flat_mono[OF assms(2)]])
  then show ?thesis using assms(1) by (simp add: eval_nd_flat)
qed

corollary present_free_equitone_nd: "present_free e \<Longrightarrow> equitone_nd (eval_nd e)"
  unfolding equitone_nd_def using T2_nd_monotone by fastforce

theorem T3_nd_present_not_monotone:
  "\<exists>(d :: ('n, 'b) nd) d' p. nd_le d d' \<and> eval_nd (EPresent p) d \<noteq> eval_nd (EPresent p) d'"
proof -
  fix x :: 'n and b :: 'b
  have "nd_le (Nom fmempty) (naming x (Atom b) :: ('n, 'b) nd)" by (rule nd_le_empty_naming)
  moreover have "eval_nd (EPresent [x]) (Nom fmempty :: ('n, 'b) nd) \<noteq> eval_nd (EPresent [x]) (naming x (Atom b))"
    by (simp add: naming_def)
  ultimately show ?thesis by blast
qed

text \<open>Agreement with two-valued logic: if every complex name read by a comparison leads to
  an atom, evaluation is defined and classical, with PRESENT read as presence of a node.\<close>

theorem T4_nd:
  assumes "names e \<subseteq> dom (flat d)" and "\<forall>p \<in> dom (flat d). flat d p = Some (\<rho> p)"
  shows "eval_nd e d = Some (ceval e {p. den_path p d \<noteq> None} \<rho>)"
  using assms(1)
proof (induction e)
  case (EEq a c)
  then have "vnames a \<subseteq> dom (flat d)" "vnames c \<subseteq> dom (flat d)" by simp_all
  then show ?case
    using evalV_classical[OF _ assms(2)] by (simp add: evalV_nd_flat)
qed auto

theorem T5_nd_present: "eval_nd (EPresent p) d = Some True \<longleftrightarrow> den_path p d \<noteq> None"
  by simp


section \<open>Why comparisons see only atoms\<close>

text \<open>An inner node is below another inner node when every child is below the child of
  the same name (the converse of \<open>nd_le_NomD\<close>).\<close>

lemma nd_le_NomI:
  assumes "\<And>x y. fmlookup m x = Some y \<Longrightarrow> \<exists>y'. fmlookup m' x = Some y' \<and> nd_le y y'"
  shows "nd_le (Nom m) (Nom m')"
  unfolding nd_le_def
proof (intro conjI allI impI)
  fix p b assume "den_path p (Nom m) = Some (Atom b)"
  then obtain x q y where p: "p = x # q" and y: "fmlookup m x = Some y" and q: "den_path q y = Some (Atom b)"
    by (cases p) (auto split: option.splits)
  from assms[OF y] obtain y' where y': "fmlookup m' x = Some y'" "nd_le y y'" by blast
  with q have "den_path q y' = Some (Atom b)" unfolding nd_le_def by blast
  with p y' show "den_path p (Nom m') = Some (Atom b)" by simp
next
  fix p n assume "den_path p (Nom m) = Some (Nom n)"
  show "\<exists>n'. den_path p (Nom m') = Some (Nom n')"
  proof (cases p)
    case Nil
    then show ?thesis by simp
  next
    case (Cons x q)
    with \<open>den_path p (Nom m) = Some (Nom n)\<close> obtain y where y: "fmlookup m x = Some y"
      and q: "den_path q y = Some (Nom n)"
      by (auto split: option.splits)
    from assms[OF y] obtain y' where y': "fmlookup m' x = Some y'" "nd_le y y'" by blast
    with q obtain n' where "den_path q y' = Some (Nom n')" unfolding nd_le_def by blast
    with Cons y' show ?thesis by simp
  qed
qed

text \<open>Equality of whole data is not monotone under the information order: two equal
  records stop being equal when one of them is extended. This is why a complex name that
  leads to a record is undefined in comparisons, and comparisons see only atoms.\<close>

theorem whole_data_equality_not_monotone:
  assumes "x \<noteq> y"
  shows "\<exists>(d :: ('n, 'b) nd) d'. nd_le d d'
           \<and> den_path [x] d \<noteq> None \<and> den_path [x] d = den_path [y] d
           \<and> den_path [x] d' \<noteq> den_path [y] d'"
proof -
  fix b :: 'b
  let ?e = "Nom fmempty :: ('n, 'b) nd"
  let ?d = "Nom (fmupd x ?e (fmupd y ?e fmempty))"
  let ?d' = "Nom (fmupd x (naming x (Atom b)) (fmupd y ?e fmempty))"
  have "nd_le ?d ?d'"
  proof (rule nd_le_NomI)
    fix z v assume "fmlookup (fmupd x ?e (fmupd y ?e fmempty)) z = Some v"
    then show "\<exists>v'. fmlookup (fmupd x (naming x (Atom b)) (fmupd y ?e fmempty)) z = Some v' \<and> nd_le v v'"
      using nd_le_empty_naming[of x b] nd_le_refl[of ?e] by (auto split: if_splits)
  qed
  moreover have "naming x (Atom b) \<noteq> ?e"
    by (metis denaming.simps(1) denaming_naming fmempty_lookup option.distinct(1))
  ultimately show ?thesis
    using assms by (intro exI[of _ ?d] exI[of _ ?d']) simp
qed


section \<open>Types: Record and Optional\<close>

text \<open>Types of TRIEL data, without List and Map: primitive types (interpreted by a
  predicate \<open>I\<close> on atoms), \<open>Optional<T>\<close>, and \<open>Record {f: T, \<dots>}\<close>. Records are open: a
  datum may have names that the record type does not declare, and only declared fields
  are checked. \<open>Optional<T>\<close> is not a value but permitted absence: the typing judgement
  is on \<open>nd option\<close>, where \<open>None\<close> is an absent name.\<close>

datatype ('n, 'p) ty = TPrim 'p | TOptional "('n, 'p) ty" | TRecord "('n \<times> ('n, 'p) ty) list"

inductive wt :: "('p \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('n, 'p) ty \<Rightarrow> ('n, 'b) nd option \<Rightarrow> bool"
  for I :: "'p \<Rightarrow> 'b \<Rightarrow> bool" where
  wt_prim: "I q b \<Longrightarrow> wt I (TPrim q) (Some (Atom b))"
| wt_none: "wt I (TOptional t) None"
| wt_some: "wt I t (Some d) \<Longrightarrow> wt I (TOptional t) (Some d)"
| wt_record: "(\<And>f t. (f, t) \<in> set fs \<Longrightarrow> wt I t (fmlookup m f)) \<Longrightarrow> wt I (TRecord fs) (Some (Nom m))"

inductive_cases wt_NoneE: "wt I t None"
inductive_cases wt_OptionalE: "wt I (TOptional t) v"
inductive_cases wt_PrimE: "wt I (TPrim q) v"

text \<open>Types without Optional anywhere.\<close>

inductive opt_free :: "('n, 'p) ty \<Rightarrow> bool" where
  "opt_free (TPrim q)"
| "(\<And>f t. (f, t) \<in> set fs \<Longrightarrow> opt_free t) \<Longrightarrow> opt_free (TRecord fs)"

inductive_cases opt_free_OptionalE: "opt_free (TOptional t)"
inductive_cases opt_free_RecordE: "opt_free (TRecord fs)"

lemma wt_opt_free_Some: "wt I t v \<Longrightarrow> opt_free t \<Longrightarrow> v \<noteq> None"
  by (cases v) (auto elim: wt_NoneE opt_free_OptionalE)

text \<open>A required (non-Optional) field of a well-typed record is present.\<close>

lemma wt_required_field_present:
  assumes "wt I (TRecord fs) (Some d)" and "(f, t) \<in> set fs" and "opt_free t"
  shows "eval_nd (EPresent [f]) d = Some True"
proof -
  from assms(1) obtain m where d: "d = Nom m" and "wt I t (fmlookup m f)"
    using assms(2) by (cases rule: wt.cases) auto
  with assms(3) have "fmlookup m f \<noteq> None" by (blast dest: wt_opt_free_Some)
  then show ?thesis unfolding d by (auto split: option.splits)
qed

text \<open>Typing is monotone under the information order for types without Optional: adding
  names at any depth keeps an Optional-free type, since records are open.\<close>

theorem wt_mono:
  assumes "wt I t (Some d)" and "opt_free t" and "nd_le d d'"
  shows "wt I t (Some d')"
proof -
  have "\<And>d d'. opt_free t \<Longrightarrow> v = Some d \<Longrightarrow> nd_le d d' \<Longrightarrow> wt I t (Some d')"
    if "wt I t v" for v
    using that
  proof (induction rule: wt.induct)
    case (wt_prim q b)
    then show ?case by (auto simp: nd_le_Atom intro: wt.wt_prim)
  next
    case (wt_none t)
    then show ?case by simp
  next
    case (wt_some t d)
    then show ?case by (auto elim: opt_free_OptionalE)
  next
    case (wt_record fs m)
    from wt_record.prems(2,3) have le: "nd_le (Nom m) d'" by simp
    from nd_le_NomD[OF le] obtain m' where d': "d' = Nom m'"
      and down: "\<And>x y. fmlookup m x = Some y \<Longrightarrow> \<exists>y'. fmlookup m' x = Some y' \<and> nd_le y y'"
      by blast
    show ?case
      unfolding d'
    proof (rule wt.wt_record)
      fix f t assume ft: "(f, t) \<in> set fs"
      from wt_record.prems(1) ft have of: "opt_free t" by (auto elim: opt_free_RecordE)
      have wt_f: "wt I t (fmlookup m f)"
        using wt_record.hyps ft by blast
      have ih: "\<And>d d'. opt_free t \<Longrightarrow> fmlookup m f = Some d \<Longrightarrow> nd_le d d' \<Longrightarrow> wt I t (Some d')"
        by (rule wt_record.IH[OF ft])
      from wt_opt_free_Some[OF wt_f of] obtain y where y: "fmlookup m f = Some y" by auto
      with down obtain y' where y': "fmlookup m' f = Some y'" "nd_le y y'" by blast
      from ih[OF of y y'(2)] y'(1) show "wt I t (fmlookup m' f)" by simp
    qed
  qed
  with assms show ?thesis by blast
qed

text \<open>With Optional the statement fails: a field that is absent may be filled, by an
  extension, with a value of the wrong type.\<close>

theorem wt_not_mono_optional:
  "\<exists>(I :: 'p \<Rightarrow> 'b \<Rightarrow> bool) (t :: ('n, 'p) ty) (d :: ('n, 'b) nd) d'.
     wt I t (Some d) \<and> nd_le d d' \<and> \<not> wt I t (Some d')"
proof -
  fix f :: 'n and q :: 'p and b :: 'b
  let ?I = "\<lambda>(q :: 'p) (b :: 'b). False"
  let ?t = "TRecord [(f, TOptional (TPrim q))] :: ('n, 'p) ty"
  have "wt ?I ?t (Some (Nom fmempty :: ('n, 'b) nd))"
    by (rule wt.wt_record) (auto intro: wt.wt_none)
  moreover have "nd_le (Nom fmempty) (naming f (Atom b) :: ('n, 'b) nd)" by (rule nd_le_empty_naming)
  moreover have "\<not> wt ?I ?t (Some (naming f (Atom b) :: ('n, 'b) nd))"
  proof
    assume "wt ?I ?t (Some (naming f (Atom b)))"
    then have "wt ?I (TOptional (TPrim q) :: ('n, 'p) ty) (Some (Atom b :: ('n, 'b) nd))"
      by (cases rule: wt.cases) (auto simp: naming_def)
    then show False by (auto elim: wt_OptionalE wt_PrimE)
  qed
  ultimately show ?thesis by blast
qed

end
