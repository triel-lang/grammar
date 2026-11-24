(*  Title:      TRIEL_MFOTL_Future.thy
    Purpose:    The bridge from the TRIEL core to MFOTL, part 2: the verdict of an
                obligation with a deadline as the three-valued reading, over all MFOTL
                traces that encode the prefix, of a formula of bounded future at entry 0.
    SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause
*)

theory TRIEL_MFOTL_Future
  imports TRIEL_MFOTL_Norm
begin

section \<open>Encodings with a chosen entry after the prefix\<close>

text \<open>An encoding whose entry after the prefix has a given database and the last
  timestamp of the prefix, and whose later entries are empty.\<close>

lemma enc_pre_ext:
  fixes \<pi> :: "('n, 'v :: value_order, 's, 'a) itrace"
    and X :: "(string \<times> ('n, 'v, 's, 'a) mval list) set"
  assumes "is_trace \<pi>" and "finite C" and "\<forall>j < length \<pi>. finite (dom (st \<pi> j))" and "finite X"
  shows "\<exists>\<sigma>. enc_pre C \<pi> \<sigma> \<and> \<Gamma> \<sigma> (length \<pi>) = X
           \<and> \<tau> \<sigma> (length \<pi>) = nat (time \<pi> (length \<pi> - 1) - time \<pi> 0)
           \<and> (\<forall>i > length \<pi>. \<Gamma> \<sigma> i = {})"
proof -
  define n where "n = length \<pi>"
  define t where "t i = nat (time \<pi> i - time \<pi> 0)" for i
  define f :: "nat \<Rightarrow> (string \<times> ('n, 'v, 's, 'a) mval list) set \<times> nat" where
    "f i = (if i < n then (enc_db C \<pi> i, t i) else (if i = n then X else {}, t (n - 1) + (i - n)))" for i
  have t_mono: "t i \<le> t k" if "i \<le> k" and "k < n" for i k
    using time_mono[OF assms(1) that(1)] that(2) by (simp add: t_def n_def nat_mono)
  have mono: "snd (f i) \<le> snd (f k)" if "i \<le> k" for i k
  proof (cases "k < n")
    case True
    then show ?thesis using that t_mono by (simp add: f_def)
  next
    case False
    show ?thesis
    proof (cases "i < n")
      case True
      then have "i \<le> n - 1" and "n - 1 < n"
        by simp_all
      then have "t i \<le> t (n - 1)"
        by (rule t_mono)
      with False True show ?thesis
        by (simp add: f_def)
    next
      case False
      with \<open>\<not> k < n\<close> that show ?thesis
        by (simp add: f_def)
    qed
  qed
  have grows: "x < snd (f (Suc x + n))" for x
    by (simp add: f_def)
  have fin: "finite (fst (f i))" for i
    using enc_db_finite[of \<pi> i C] assms(2,3,4) by (simp add: f_def n_def)
  let ?s = "smap f nats"
  have snth: "?s !! i = f i" for i
    by simp
  have s: "?s \<in> {s. ssorted (smap snd s) \<and> sincreasing (smap snd s) \<and> sfinite (smap fst s)}"
    using mono grows fin
    by (auto simp: snth ssorted_iff_mono sincreasing_def sfinite_def)
  define \<sigma> :: "(string, ('n, 'v, 's, 'a) mval) Formula.trace" where "\<sigma> = Abs_trace ?s"
  have rep: "Rep_trace \<sigma> = ?s"
    unfolding \<sigma>_def using s by (rule Abs_trace_inverse)
  have G: "\<Gamma> \<sigma> i = fst (f i)" and T: "\<tau> \<sigma> i = snd (f i)" for i
    by (simp_all add: \<Gamma>.rep_eq \<tau>.rep_eq rep snth)
  have "enc_pre C \<pi> \<sigma>"
    by (simp add: enc_pre_def G T f_def t_def n_def)
  moreover have "\<Gamma> \<sigma> (length \<pi>) = X"
    by (simp add: G f_def n_def)
  moreover have "\<tau> \<sigma> (length \<pi>) = nat (time \<pi> (length \<pi> - 1) - time \<pi> 0)"
    by (simp add: T f_def n_def t_def)
  moreover have "\<forall>i > length \<pi>. \<Gamma> \<sigma> i = {}"
    by (simp add: G f_def n_def)
  ultimately show ?thesis by blast
qed


section \<open>An obligation with a deadline as a formula of bounded future\<close>

text \<open>\<open>s MUST a BY d\<close> read at entry 0: within \<open>n\<close> time units the action is taken.\<close>

definition ObFut :: "nat \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> (string, ('n, 'v, 's, 'a) mval) Formula.formula" where
  "ObFut n s a = formula.Eventually (Interval.interval 0 (enat n)) (Act s a)"

lemma sat_ObFut:
  "Formula.sat \<sigma> v 0 (ObFut n s a) \<longleftrightarrow> (\<exists>i. \<tau> \<sigma> i - \<tau> \<sigma> 0 \<le> n \<and> Formula.sat \<sigma> v i (Act s a))"
proof -
  have "enat 0 \<le> enat n" by simp
  then show ?thesis
    using left_interval[of 0 "enat n"] right_interval[of 0 "enat n"] by (auto simp: ObFut_def)
qed

text \<open>The window without \<open>FROM\<close> is fulfilled exactly when the formula holds at entry 0 of
  every trace that encodes the prefix, and breached exactly when it fails on every such
  trace. The premises of finiteness make such traces exist.\<close>

theorem bridge_window_future:
  fixes \<pi> :: "('n, 'v :: value_order, 's, 'a) itrace"
  assumes tr: "is_trace \<pi>" and fC: "finite C" and fd: "\<forall>j < length \<pi>. finite (dom (st \<pi> j))"
    and d0: "time \<pi> 0 \<le> d"
  shows "window s a None d \<pi> = Fulfilled \<longleftrightarrow>
      (\<forall>\<sigma>. enc_pre C \<pi> \<sigma> \<longrightarrow> Formula.sat \<sigma> v 0 (ObFut (nat (d - time \<pi> 0)) s a))" (is "?F \<longleftrightarrow> ?AllSat")
    and "window s a None d \<pi> = Breached d \<longleftrightarrow>
      (\<forall>\<sigma>. enc_pre C \<pi> \<sigma> \<longrightarrow> \<not> Formula.sat \<sigma> v 0 (ObFut (nat (d - time \<pi> 0)) s a))" (is "?B \<longleftrightarrow> ?AllVio")
proof -
  let ?n = "nat (d - time \<pi> 0)"
  let ?act = "(''act'', [MS s, MA a]) :: string \<times> ('n, 'v, 's, 'a) mval list"
  have len: "0 < length \<pi>" using tr by (simp add: is_trace_def)
  have A: "acted s a None d \<pi> \<longleftrightarrow> (\<exists>i < length \<pi>. 1 \<le> i \<and> does s a (evt (\<pi> ! i)) \<and> time \<pi> i \<le> d)"
    by (auto simp: acted_def)
  have key: "Formula.sat \<sigma> v i (Act s a) \<and> \<tau> \<sigma> i - \<tau> \<sigma> 0 \<le> ?n
      \<longleftrightarrow> 1 \<le> i \<and> does s a (evt (\<pi> ! i)) \<and> time \<pi> i \<le> d"
    if e: "enc_pre C \<pi> \<sigma>" and i: "i < length \<pi>" for \<sigma> i
    using sat_Act[OF e i, of v s a] enc_tau[OF tr e i] enc_tau0[OF tr e] d0 by auto
  have sat_if_acted: "Formula.sat \<sigma> v 0 (ObFut ?n s a)" if "acted s a None d \<pi>" and e: "enc_pre C \<pi> \<sigma>" for \<sigma>
  proof -
    from that(1) obtain i where i: "i < length \<pi>" "1 \<le> i" "does s a (evt (\<pi> ! i))" "time \<pi> i \<le> d"
      unfolding A by blast
    then have "Formula.sat \<sigma> v i (Act s a) \<and> \<tau> \<sigma> i - \<tau> \<sigma> 0 \<le> ?n"
      using key[OF e i(1)] by simp
    then show ?thesis unfolding sat_ObFut by blast
  qed
  have acted_if_sat: "acted s a None d \<pi>"
    if e: "enc_pre C \<pi> \<sigma>" and sat: "Formula.sat \<sigma> v 0 (ObFut ?n s a)"
      and tail: "\<And>i. length \<pi> \<le> i \<Longrightarrow> \<not> (Formula.sat \<sigma> v i (Act s a) \<and> \<tau> \<sigma> i - \<tau> \<sigma> 0 \<le> ?n)" for \<sigma>
  proof -
    from sat obtain i where i: "\<tau> \<sigma> i - \<tau> \<sigma> 0 \<le> ?n" "Formula.sat \<sigma> v i (Act s a)"
      unfolding sat_ObFut by blast
    with tail[of i] have il: "i < length \<pi>" by (meson not_le)
    with key[OF e il] i show ?thesis unfolding A by blast
  qed
  obtain \<sigma>\<^sub>0 :: "(string, ('n, 'v, 's, 'a) mval) Formula.trace" where
    e0: "enc_pre C \<pi> \<sigma>\<^sub>0" and g0: "\<Gamma> \<sigma>\<^sub>0 (length \<pi>) = {}" and tl0: "\<forall>i > length \<pi>. \<Gamma> \<sigma>\<^sub>0 i = {}"
    using enc_pre_ext[OF tr fC fd, of "{}"] by auto
  have empty0: "\<not> Formula.sat \<sigma>\<^sub>0 v i (Act s a)" if "length \<pi> \<le> i" for i
    using that g0 tl0 by (cases "i = length \<pi>") (auto simp: Act_def)
  show "?F \<longleftrightarrow> ?AllSat"
  proof
    assume ?F
    then have "acted s a None d \<pi>" by (auto simp: window_def split: if_splits)
    then show ?AllSat using sat_if_acted by blast
  next
    assume ?AllSat
    then have "Formula.sat \<sigma>\<^sub>0 v 0 (ObFut ?n s a)" using e0 by blast
    then have "acted s a None d \<pi>" using acted_if_sat[OF e0] empty0 by blast
    then show ?F by (simp add: window_def)
  qed
  show "?B \<longleftrightarrow> ?AllVio"
  proof
    assume ?B
    then have na: "\<not> acted s a None d \<pi>" and p: "passed d \<pi>"
      by (auto simp: window_def split: if_splits)
    from p obtain k where k: "k < length \<pi>" "d < time \<pi> k" unfolding passed_def by blast
    show ?AllVio
    proof (intro allI impI notI)
      fix \<sigma> assume e: "enc_pre C \<pi> \<sigma>" and sat: "Formula.sat \<sigma> v 0 (ObFut ?n s a)"
      have "\<not> (Formula.sat \<sigma> v i (Act s a) \<and> \<tau> \<sigma> i - \<tau> \<sigma> 0 \<le> ?n)" if "length \<pi> \<le> i" for i
      proof -
        have "k \<le> i" using k(1) that by simp
        then have "\<tau> \<sigma> k \<le> \<tau> \<sigma> i" by simp
        moreover have "?n < \<tau> \<sigma> k" using enc_tau[OF tr e k(1)] k(2) d0 by simp
        ultimately show ?thesis using enc_tau0[OF tr e] by simp
      qed
      from acted_if_sat[OF e sat this] na show False by simp
    qed
  next
    assume av: ?AllVio
    have na: "\<not> acted s a None d \<pi>" using av sat_if_acted[OF _ e0] e0 by blast
    have p: "passed d \<pi>"
    proof (rule ccontr)
      assume np: "\<not> passed d \<pi>"
      have "length \<pi> - 1 < length \<pi>" using len by simp
      with np have last: "time \<pi> (length \<pi> - 1) \<le> d" unfolding passed_def by (meson not_less)
      obtain \<sigma>\<^sub>1 :: "(string, ('n, 'v, 's, 'a) mval) Formula.trace" where
        e1: "enc_pre C \<pi> \<sigma>\<^sub>1" and g1: "\<Gamma> \<sigma>\<^sub>1 (length \<pi>) = {?act}"
        and t1: "\<tau> \<sigma>\<^sub>1 (length \<pi>) = nat (time \<pi> (length \<pi> - 1) - time \<pi> 0)"
        using enc_pre_ext[OF tr fC fd, of "{?act}"] by auto
      have "Formula.sat \<sigma>\<^sub>1 v (length \<pi>) (Act s a)" using g1 by (simp add: Act_def eval_trms_def)
      moreover have "\<tau> \<sigma>\<^sub>1 (length \<pi>) - \<tau> \<sigma>\<^sub>1 0 \<le> ?n" using t1 last enc_tau0[OF tr e1] by simp
      ultimately have "Formula.sat \<sigma>\<^sub>1 v 0 (ObFut ?n s a)" unfolding sat_ObFut by blast
      with av e1 show False by blast
    qed
    from na p show ?B by (simp add: window_def)
  qed
qed

end
