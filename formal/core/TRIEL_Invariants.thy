(*  Title:      TRIEL_Invariants.thy
    Purpose:    ALWAYS, EVENTUALLY and NEXT over finite prefixes of implementation
                traces, with three-valued verdicts in the style of LTL3
                (A. Bauer, M. Leucker, C. Schallhart. Runtime verification for LTL and
                TLTL. ACM TOSEM 20(4), 2011), and strong Kleene evaluation of the state
                formulas.
    SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause
*)

theory TRIEL_Invariants
  imports TRIEL_Breach
begin

section \<open>Invariants on finite prefixes\<close>

text \<open>An invariant is \<open>ALWAYS \<phi>\<close>, \<open>EVENTUALLY \<phi>\<close> or \<open>NEXT \<phi>\<close> for a state formula \<open>\<phi>\<close>, read at
  the activation entry of an implementation trace (TECHNICAL_REPORT.md sections 2.4 and
  2.5). On a finite prefix the verdict follows LTL3: it is T or F only if every
  continuation of the prefix would give the same answer, and \<open>\<bottom>\<close> (inconclusive) otherwise.
  \<^item> \<open>ALWAYS \<phi>\<close> is F from the first entry where \<open>\<phi>\<close> is F, and \<open>\<bottom>\<close> otherwise; it is never T.
  \<^item> \<open>EVENTUALLY \<phi>\<close> is T from the first entry where \<open>\<phi>\<close> is T, and \<open>\<bottom>\<close> otherwise; it is never F.
  \<^item> \<open>NEXT \<phi>\<close> is the value of \<open>\<phi>\<close> at entry 1, and \<open>\<bottom>\<close> while the prefix has only entry 0.
  An entry where \<open>\<phi>\<close> is \<open>\<bottom>\<close> because data is missing neither violates ALWAYS nor fulfils
  EVENTUALLY.\<close>

datatype ('n, 'v) inv =
    Always "('n, 'v) expr"
  | Eventually "('n, 'v) expr"
  | Next "('n, 'v) expr"

fun inv_eval :: "('n, 'v :: value_order) inv \<Rightarrow> ('n, 'v, 's, 'a) itrace \<Rightarrow> bool option" where
  "inv_eval (Always \<phi>) \<pi> =
     (if \<exists>j < length \<pi>. eval \<phi> (st \<pi> j) = Some False then Some False else None)"
| "inv_eval (Eventually \<phi>) \<pi> =
     (if \<exists>j < length \<pi>. eval \<phi> (st \<pi> j) = Some True then Some True else None)"
| "inv_eval (Next \<phi>) \<pi> = (if 1 < length \<pi> then eval \<phi> (st \<pi> 1) else None)"


section \<open>Properties of the verdicts\<close>

theorem always_never_true: "inv_eval (Always \<phi>) \<pi> \<noteq> Some True"
  by simp

theorem eventually_never_false: "inv_eval (Eventually \<phi>) \<pi> \<noteq> Some False"
  by simp

text \<open>Finality: a definite verdict does not change when the trace is extended.\<close>

theorem inv_final:
  assumes "inv_eval \<iota> \<pi> = Some b"
  shows "inv_eval \<iota> (\<pi> @ \<rho>) = Some b"
proof (cases \<iota>)
  case (Always \<phi>)
  let ?P = "\<exists>j < length \<pi>. eval \<phi> (st \<pi> j) = Some False"
  from assms Always have "(if ?P then Some False else None) = Some b" by simp
  then have ex: ?P and b: "b = False" by (cases ?P; simp)+
  from ex obtain j where "j < length \<pi>" "eval \<phi> (st \<pi> j) = Some False" by blast
  then have "\<exists>j < length (\<pi> @ \<rho>). eval \<phi> (st (\<pi> @ \<rho>) j) = Some False"
    by (intro exI[of _ j]) simp
  with Always b show ?thesis by simp
next
  case (Eventually \<phi>)
  let ?P = "\<exists>j < length \<pi>. eval \<phi> (st \<pi> j) = Some True"
  from assms Eventually have "(if ?P then Some True else None) = Some b" by simp
  then have ex: ?P and b: "b = True" by (cases ?P; simp)+
  from ex obtain j where "j < length \<pi>" "eval \<phi> (st \<pi> j) = Some True" by blast
  then have "\<exists>j < length (\<pi> @ \<rho>). eval \<phi> (st (\<pi> @ \<rho>) j) = Some True"
    by (intro exI[of _ j]) simp
  with Eventually b show ?thesis by simp
next
  case (Next \<phi>)
  from assms Next have "(if 1 < length \<pi> then eval \<phi> (st \<pi> 1) else None) = Some b" by simp
  then have "1 < length \<pi>" "eval \<phi> (st \<pi> 1) = Some b" by (cases "1 < length \<pi>"; simp)+
  with Next show ?thesis by simp
qed

text \<open>Consistency with strong Kleene logic: \<open>\<bottom>\<close> caused by missing data never yields a
  definite verdict on its own.\<close>

theorem always_undefined_data:
  "(\<And>j. j < length \<pi> \<Longrightarrow> eval \<phi> (st \<pi> j) \<noteq> Some False) \<Longrightarrow> inv_eval (Always \<phi>) \<pi> = None"
  by auto

theorem eventually_undefined_data:
  "(\<And>j. j < length \<pi> \<Longrightarrow> eval \<phi> (st \<pi> j) \<noteq> Some True) \<Longrightarrow> inv_eval (Eventually \<phi>) \<pi> = None"
  by auto

text \<open>Consistency with the information order: for a PRESENT-free state formula, a
  definite verdict on a trace stays the same on any trace with the same entries whose
  states carry more data (T2 at each entry).\<close>

primrec inv_formula :: "('n, 'v) inv \<Rightarrow> ('n, 'v) expr" where
  "inv_formula (Always \<phi>) = \<phi>"
| "inv_formula (Eventually \<phi>) = \<phi>"
| "inv_formula (Next \<phi>) = \<phi>"

theorem inv_data_mono:
  assumes pf: "present_free (inv_formula \<iota>)"
    and len: "length \<pi>' = length \<pi>"
    and le: "\<And>j. j < length \<pi> \<Longrightarrow> st \<pi> j \<sqsubseteq> st \<pi>' j"
    and v: "inv_eval \<iota> \<pi> = Some b"
  shows "inv_eval \<iota> \<pi>' = Some b"
proof (cases \<iota>)
  case (Always \<phi>)
  let ?P = "\<exists>j < length \<pi>. eval \<phi> (st \<pi> j) = Some False"
  from v Always have "(if ?P then Some False else None) = Some b" by simp
  then have ex: ?P and b: "b = False" by (cases ?P; simp)+
  from ex obtain j where j: "j < length \<pi>" "eval \<phi> (st \<pi> j) = Some False" by blast
  from pf Always have "present_free \<phi>" by simp
  from T2_monotone[OF this le[OF j(1)] j(2)] have "eval \<phi> (st \<pi>' j) = Some False" .
  with j(1) len have "\<exists>j < length \<pi>'. eval \<phi> (st \<pi>' j) = Some False" by auto
  with Always b show ?thesis by simp
next
  case (Eventually \<phi>)
  let ?P = "\<exists>j < length \<pi>. eval \<phi> (st \<pi> j) = Some True"
  from v Eventually have "(if ?P then Some True else None) = Some b" by simp
  then have ex: ?P and b: "b = True" by (cases ?P; simp)+
  from ex obtain j where j: "j < length \<pi>" "eval \<phi> (st \<pi> j) = Some True" by blast
  from pf Eventually have "present_free \<phi>" by simp
  from T2_monotone[OF this le[OF j(1)] j(2)] have "eval \<phi> (st \<pi>' j) = Some True" .
  with j(1) len have "\<exists>j < length \<pi>'. eval \<phi> (st \<pi>' j) = Some True" by auto
  with Eventually b show ?thesis by simp
next
  case (Next \<phi>)
  from v Next have "(if 1 < length \<pi> then eval \<phi> (st \<pi> 1) else None) = Some b" by simp
  then have n: "1 < length \<pi>" and e: "eval \<phi> (st \<pi> 1) = Some b"
    by (cases "1 < length \<pi>"; simp)+
  from pf Next have "present_free \<phi>" by simp
  from T2_monotone[OF this le[OF n] e] n len Next show ?thesis by simp
qed



section \<open>EVENTUALLY with a deadline\<close>

text \<open>\<open>EVENTUALLY \<phi> WITHIN d\<close> (TECHNICAL_REPORT.md section 2.6). The deadline \<open>d\<close> is
  resolved once, at activation, like the deadline of an obligation, to a time \<open>D\<close>. The
  window is the set of entries with a time not after \<open>D\<close>. On a finite prefix:
  \<^item> the verdict is T as soon as \<open>\<phi>\<close> is T at an entry of the window;
  \<^item> it is F once the trace has an entry strictly after \<open>D\<close> and \<open>\<phi>\<close> is F at every entry
    of the window;
  \<^item> it is \<open>\<bottom>\<close> otherwise.
  After \<open>D\<close> the verdict is the strong Kleene disjunction of \<open>\<phi>\<close> over the window, so an
  entry where \<open>\<phi>\<close> is \<open>\<bottom>\<close> because data is missing prevents F.\<close>

definition ew_eval :: "('n, 'v :: value_order) expr \<Rightarrow> int \<Rightarrow> ('n, 'v, 's, 'a) itrace \<Rightarrow> bool option" where
  "ew_eval \<phi> D \<pi> =
     (if \<exists>j < length \<pi>. time \<pi> j \<le> D \<and> eval \<phi> (st \<pi> j) = Some True then Some True
      else if passed D \<pi> \<and> (\<forall>j < length \<pi>. time \<pi> j \<le> D \<longrightarrow> eval \<phi> (st \<pi> j) = Some False)
      then Some False
      else None)"

text \<open>An entry in the window where \<open>\<phi>\<close> is T makes the verdict T; this includes an entry
  exactly at the deadline.\<close>

theorem ew_true:
  assumes "j < length \<pi>" "time \<pi> j \<le> D" "eval \<phi> (st \<pi> j) = Some True"
  shows "ew_eval \<phi> D \<pi> = Some True"
  using assms unfolding ew_eval_def by auto

theorem ew_at_deadline:
  assumes "j < length \<pi>" "time \<pi> j = D" "eval \<phi> (st \<pi> j) = Some True"
  shows "ew_eval \<phi> D \<pi> = Some True"
  using assms by (intro ew_true) auto

text \<open>Past the deadline, with \<open>\<phi>\<close> false at every entry of the window, the verdict is F.\<close>

theorem ew_missed:
  assumes "passed D \<pi>" "\<And>j. j < length \<pi> \<Longrightarrow> time \<pi> j \<le> D \<Longrightarrow> eval \<phi> (st \<pi> j) = Some False"
  shows "ew_eval \<phi> D \<pi> = Some False"
proof -
  have "\<not> (\<exists>j < length \<pi>. time \<pi> j \<le> D \<and> eval \<phi> (st \<pi> j) = Some True)"
    using assms(2) by fastforce
  with assms show ?thesis unfolding ew_eval_def by auto
qed

text \<open>Before the deadline has passed the verdict is never F.\<close>

theorem ew_not_false_before:
  "\<not> passed D \<pi> \<Longrightarrow> ew_eval \<phi> D \<pi> \<noteq> Some False"
  unfolding ew_eval_def by auto

text \<open>An entry of the window where \<open>\<phi>\<close> is \<open>\<bottom>\<close> prevents F.\<close>

theorem ew_undefined_data:
  assumes "j < length \<pi>" "time \<pi> j \<le> D" "eval \<phi> (st \<pi> j) = None"
  shows "ew_eval \<phi> D \<pi> \<noteq> Some False"
proof -
  have "\<not> (\<forall>j < length \<pi>. time \<pi> j \<le> D \<longrightarrow> eval \<phi> (st \<pi> j) = Some False)"
    using assms by auto
  then show ?thesis unfolding ew_eval_def by simp
qed

text \<open>After the deadline the verdict is the strong Kleene disjunction of \<open>\<phi>\<close> over the
  window: T if some entry is T, F if every entry is F, and \<open>\<bottom>\<close> otherwise.\<close>

theorem ew_after_deadline:
  assumes "passed D \<pi>"
  shows "ew_eval \<phi> D \<pi> =
           (if \<exists>j < length \<pi>. time \<pi> j \<le> D \<and> eval \<phi> (st \<pi> j) = Some True then Some True
            else if \<forall>j < length \<pi>. time \<pi> j \<le> D \<longrightarrow> eval \<phi> (st \<pi> j) = Some False then Some False
            else None)"
  unfolding ew_eval_def by (intro if_cong refl) (simp_all add: assms)

text \<open>A true \<open>EVENTUALLY \<phi> WITHIN d\<close> makes \<open>EVENTUALLY \<phi>\<close> true.\<close>

theorem ew_eventually:
  assumes "ew_eval \<phi> D \<pi> = Some True"
  shows "inv_eval (Eventually \<phi>) \<pi> = Some True"
proof -
  have "\<exists>j < length \<pi>. time \<pi> j \<le> D \<and> eval \<phi> (st \<pi> j) = Some True"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    with assms show False unfolding ew_eval_def by (simp split: if_splits)
  qed
  then show ?thesis by auto
qed

text \<open>Finality: with non-decreasing timestamps a definite verdict does not change when the
  trace is extended. A T stays T because its entry stays. An F stays F because every new
  entry is at or after the entry that passed the deadline, so it is outside the window.\<close>

theorem ew_final:
  assumes tr: "is_trace (\<pi> @ \<rho>)" and v: "ew_eval \<phi> D \<pi> = Some b"
  shows "ew_eval \<phi> D (\<pi> @ \<rho>) = Some b"
proof (cases "\<exists>j < length \<pi>. time \<pi> j \<le> D \<and> eval \<phi> (st \<pi> j) = Some True")
  case True
  then obtain j where j: "j < length \<pi>" "time \<pi> j \<le> D" "eval \<phi> (st \<pi> j) = Some True" by blast
  from True v have b: "b = True" unfolding ew_eval_def by simp
  have "ew_eval \<phi> D (\<pi> @ \<rho>) = Some True"
    by (rule ew_true[of j]) (use j in simp_all)
  with b show ?thesis by simp
next
  case False
  let ?F = "passed D \<pi> \<and> (\<forall>j < length \<pi>. time \<pi> j \<le> D \<longrightarrow> eval \<phi> (st \<pi> j) = Some False)"
  from v False have "(if ?F then Some False else None) = Some b" unfolding ew_eval_def by simp
  then have F: ?F and b: "b = False" by (cases ?F; simp)+
  from F have p: "passed D \<pi>"
    and allF: "\<forall>j < length \<pi>. time \<pi> j \<le> D \<longrightarrow> eval \<phi> (st \<pi> j) = Some False"
    by blast+
  from p obtain i where i: "i < length \<pi>" "D < time \<pi> i" unfolding passed_def by blast
  have "eval \<phi> (st (\<pi> @ \<rho>) j) = Some False"
    if j: "j < length (\<pi> @ \<rho>)" "time (\<pi> @ \<rho>) j \<le> D" for j
  proof (cases "j < length \<pi>")
    case True
    with j allF show ?thesis by simp
  next
    case False
    then have "i \<le> j" using i(1) by simp
    from time_mono[OF tr this j(1)] i have "D < time (\<pi> @ \<rho>) j" by simp
    with j(2) show ?thesis by simp
  qed
  moreover have "passed D (\<pi> @ \<rho>)" using passed_append[OF p] .
  ultimately have "ew_eval \<phi> D (\<pi> @ \<rho>) = Some False" by (intro ew_missed) auto
  with b show ?thesis by simp
qed

text \<open>Consistency with the information order: for \<open>\<phi>\<close> without PRESENT and DEFAULT, a
  definite verdict stays the same on a trace with the same times whose states carry more
  data (T2 at each entry).\<close>

theorem ew_data_mono:
  assumes pf: "present_free \<phi>"
    and len: "length \<pi>' = length \<pi>"
    and tm: "\<And>j. j < length \<pi> \<Longrightarrow> time \<pi>' j = time \<pi> j"
    and le: "\<And>j. j < length \<pi> \<Longrightarrow> st \<pi> j \<sqsubseteq> st \<pi>' j"
    and v: "ew_eval \<phi> D \<pi> = Some b"
  shows "ew_eval \<phi> D \<pi>' = Some b"
proof (cases "\<exists>j < length \<pi>. time \<pi> j \<le> D \<and> eval \<phi> (st \<pi> j) = Some True")
  case True
  then obtain j where j: "j < length \<pi>" "time \<pi> j \<le> D" "eval \<phi> (st \<pi> j) = Some True" by blast
  from True v have b: "b = True" unfolding ew_eval_def by simp
  from T2_monotone[OF pf le[OF j(1)] j(3)] have "eval \<phi> (st \<pi>' j) = Some True" .
  with j len tm have "ew_eval \<phi> D \<pi>' = Some True" by (intro ew_true[of j]) auto
  with b show ?thesis by simp
next
  case False
  let ?F = "passed D \<pi> \<and> (\<forall>j < length \<pi>. time \<pi> j \<le> D \<longrightarrow> eval \<phi> (st \<pi> j) = Some False)"
  from v False have "(if ?F then Some False else None) = Some b" unfolding ew_eval_def by simp
  then have F: ?F and b: "b = False" by (cases ?F; simp)+
  from F have p: "passed D \<pi>"
    and allF: "\<forall>j < length \<pi>. time \<pi> j \<le> D \<longrightarrow> eval \<phi> (st \<pi> j) = Some False"
    by blast+
  from p obtain i where i: "i < length \<pi>" "D < time \<pi> i" unfolding passed_def by blast
  with len tm have p': "passed D \<pi>'" unfolding passed_def by (intro exI[of _ i]) auto
  have "eval \<phi> (st \<pi>' j) = Some False" if "j < length \<pi>'" "time \<pi>' j \<le> D" for j
  proof -
    from that len tm have j: "j < length \<pi>" "time \<pi> j \<le> D" by auto
    with allF have "eval \<phi> (st \<pi> j) = Some False" by simp
    from T2_monotone[OF pf le[OF j(1)] this] show ?thesis .
  qed
  with p' have "ew_eval \<phi> D \<pi>' = Some False" by (intro ew_missed) auto
  with b show ?thesis by simp
qed


section \<open>Invariants with deadlines\<close>

text \<open>The invariants of a specification: an invariant of the section above, or
  \<open>EVENTUALLY \<phi> WITHIN d\<close> with its deadline not yet resolved. The deadline is resolved at
  the activation entry, entry 0, like the deadlines of the TERMS block; a duration counts
  from the activation time.\<close>

datatype ('n, 'v) sinv = SInv "('n, 'v) inv" | SEventuallyWithin "('n, 'v) expr" "'n deadline"

fun sinv_eval :: "('v \<Rightarrow> int option) \<Rightarrow> ('n, 'v :: value_order) sinv \<Rightarrow> ('n, 'v, 's, 'a) itrace \<Rightarrow> bool option" where
  "sinv_eval T (SInv \<iota>) \<pi> = inv_eval \<iota> \<pi>"
| "sinv_eval T (SEventuallyWithin \<phi> d) \<pi> =
     (case resolve T (time \<pi> 0) (st \<pi> 0) d of None \<Rightarrow> None | Some D \<Rightarrow> ew_eval \<phi> D \<pi>)"

fun sinv_deadlines :: "('n, 'v) sinv \<Rightarrow> 'n deadline list" where
  "sinv_deadlines (SInv \<iota>) = []"
| "sinv_deadlines (SEventuallyWithin \<phi> d) = [d]"

text \<open>The invariants are activated only if every deadline in them resolves.\<close>

definition inv_activates :: "('v \<Rightarrow> int option) \<Rightarrow> int \<Rightarrow> ('n, 'v) state \<Rightarrow> ('n, 'v) sinv list \<Rightarrow> bool" where
  "inv_activates T \<tau>\<^sub>0 \<sigma>\<^sub>0 invs \<longleftrightarrow> (\<forall>\<iota> \<in> set invs. \<forall>d \<in> set (sinv_deadlines \<iota>). resolve T \<tau>\<^sub>0 \<sigma>\<^sub>0 d \<noteq> None)"

theorem activation_rejected_inv:
  assumes "SEventuallyWithin \<phi> (DFactor x k) \<in> set invs" and "\<sigma>\<^sub>0 x = None"
  shows "\<not> inv_activates T \<tau>\<^sub>0 \<sigma>\<^sub>0 invs"
  using assms unfolding inv_activates_def by force

text \<open>After activation, every deadline of an invariant resolves, so the verdict of
  \<open>EVENTUALLY \<phi> WITHIN d\<close> is that of its window.\<close>

theorem inv_activates_resolves:
  assumes "inv_activates T (time \<pi> 0) (st \<pi> 0) invs" and "SEventuallyWithin \<phi> d \<in> set invs"
  shows "\<exists>D. resolve T (time \<pi> 0) (st \<pi> 0) d = Some D \<and> sinv_eval T (SEventuallyWithin \<phi> d) \<pi> = ew_eval \<phi> D \<pi>"
  using assms unfolding inv_activates_def by fastforce

lemma resolve_mono:
  assumes "\<sigma> \<sqsubseteq> \<sigma>'" "resolve T \<tau> \<sigma> d = Some D"
  shows "resolve T \<tau> \<sigma>' d = Some D"
  using assms by (cases d) (auto dest: info_leD split: option.splits)

text \<open>Every invariant keeps a definite verdict when the trace is extended (with
  non-decreasing timestamps) and, without PRESENT and DEFAULT, when the states carry more
  data.\<close>

theorem sinv_final:
  assumes tr: "is_trace (\<pi> @ \<rho>)" and ne: "\<pi> \<noteq> []" and v: "sinv_eval T \<iota> \<pi> = Some b"
  shows "sinv_eval T \<iota> (\<pi> @ \<rho>) = Some b"
proof (cases \<iota>)
  case (SInv \<kappa>)
  with v inv_final show ?thesis by simp
next
  case (SEventuallyWithin \<phi> d)
  from ne have 0: "time (\<pi> @ \<rho>) 0 = time \<pi> 0" "st (\<pi> @ \<rho>) 0 = st \<pi> 0" by simp_all
  from v SEventuallyWithin obtain D where
    D: "resolve T (time \<pi> 0) (st \<pi> 0) d = Some D" and e: "ew_eval \<phi> D \<pi> = Some b"
    by (auto split: option.splits)
  from ew_final[OF tr e] D 0 SEventuallyWithin show ?thesis by simp
qed

primrec sinv_formula :: "('n, 'v) sinv \<Rightarrow> ('n, 'v) expr" where
  "sinv_formula (SInv \<iota>) = inv_formula \<iota>"
| "sinv_formula (SEventuallyWithin \<phi> d) = \<phi>"

theorem sinv_data_mono:
  assumes pf: "present_free (sinv_formula \<iota>)"
    and len: "length \<pi>' = length \<pi>" and ne: "\<pi> \<noteq> []"
    and tm: "\<And>j. j < length \<pi> \<Longrightarrow> time \<pi>' j = time \<pi> j"
    and le: "\<And>j. j < length \<pi> \<Longrightarrow> st \<pi> j \<sqsubseteq> st \<pi>' j"
    and v: "sinv_eval T \<iota> \<pi> = Some b"
  shows "sinv_eval T \<iota> \<pi>' = Some b"
proof (cases \<iota>)
  case (SInv \<kappa>)
  with pf len le v inv_data_mono[of \<kappa> \<pi>' \<pi> b] show ?thesis by simp
next
  case (SEventuallyWithin \<phi> d)
  from ne have 0: "0 < length \<pi>" by simp
  from v SEventuallyWithin obtain D where
    D: "resolve T (time \<pi> 0) (st \<pi> 0) d = Some D" and e: "ew_eval \<phi> D \<pi> = Some b"
    by (auto split: option.splits)
  from resolve_mono[OF le[OF 0] D] tm[OF 0] have D': "resolve T (time \<pi>' 0) (st \<pi>' 0) d = Some D"
    by simp
  from pf SEventuallyWithin have "present_free \<phi>" by simp
  from ew_data_mono[OF this len tm le e] D' SEventuallyWithin show ?thesis by simp
qed

text \<open>The same, with the hypothesis packed as \<open>data_le\<close> (TRIEL_Trace): the same entries, times
  and events, and more data at each entry. This is the form the evaluator uses.\<close>

corollary inv_data_mono_le:
  assumes "present_free (inv_formula \<iota>)" and le: "data_le \<pi> \<pi>'" and "inv_eval \<iota> \<pi> = Some b"
  shows "inv_eval \<iota> \<pi>' = Some b"
  using assms(1) data_le_length[OF le] data_le_st[OF le] assms(3) by (rule inv_data_mono)

corollary sinv_data_mono_le:
  assumes "present_free (sinv_formula \<iota>)" and "\<pi> \<noteq> []" and le: "data_le \<pi> \<pi>'"
    and "sinv_eval T \<iota> \<pi> = Some b"
  shows "sinv_eval T \<iota> \<pi>' = Some b"
  using assms(1) data_le_length[OF le] assms(2) data_le_time[OF le] data_le_st[OF le] assms(4)
  by (rule sinv_data_mono)

end
