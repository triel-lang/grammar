(*  Title:      TRIEL_MFOTL_Norm.thy
    Purpose:    The bridge from the TRIEL core to MFOTL, part 2: the verdicts of norms as
                past-time formulas of MFOTL, read at the last entry of a prefix of an
                implementation trace. An obligation with a window and one without a
                deadline, a prohibition and the time of its breach, the decision of the
                fail-closed monitor at an entry, a permission, a fresh factor, fallbacks
                (ELSE) and the handlers of a breach (CURE_BY, ESCALATE_TO, TERMINATE).
    SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause
*)

theory TRIEL_MFOTL_Norm
  imports TRIEL_MFOTL_Cond TRIEL_MFOTL_Time
begin

section \<open>Actions\<close>

text \<open>The fact \<open>act(s, a)\<close>. The encoding writes it for the action \<open>a\<close> of \<open>s\<close> at every
  entry but entry 0, whose event is not an action.\<close>

definition Act :: "'s \<Rightarrow> 'a \<Rightarrow> (string, ('n, 'v, 's, 'a) mval) Formula.formula" where
  "Act s a = formula.Pred ''act'' [trm.Const (MS s), trm.Const (MA a)]"

lemma sat_Act:
  assumes "enc_pre C \<pi> \<sigma>" and "j < length \<pi>"
  shows "Formula.sat \<sigma> v j (Act s a) \<longleftrightarrow> 1 \<le> j \<and> does s a (evt (\<pi> ! j))"
  using assms
  by (auto simp: Act_def enc_pre_def enc_db_def eval_trms_def does_def split: event.splits)


section \<open>Obligations with a window\<close>

text \<open>\<open>Acted\<close>: at some entry up to this one the action was taken at a time of the window
  \<open>(lo, d]\<close>. \<open>ObBre\<close>: no such entry, and this entry is strictly after \<open>d\<close>.\<close>

definition Acted :: "int \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> int option \<Rightarrow> int \<Rightarrow> (string, ('n, 'v, 's, 'a) mval) Formula.formula" where
  "Acted \<tau>\<^sub>0 s a lo d = formula.Once Interval.all (formula.And (Act s a) (InWin \<tau>\<^sub>0 lo d))"

lemma sat_Acted:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>" and "j < length \<pi>"
  shows "Formula.sat \<sigma> v j (Acted (time \<pi> 0) s a lo d) \<longleftrightarrow> acted s a lo d (pre \<pi> j)"
proof -
  have "Formula.sat \<sigma> v i (formula.And (Act s a) (InWin (time \<pi> 0) lo d)) \<longleftrightarrow>
        1 \<le> i \<and> does s a (evt (\<pi> ! i)) \<and> after lo (time \<pi> i) \<and> time \<pi> i \<le> d" if "i \<le> j" for i
  proof -
    have i: "i < length \<pi>" using that assms(3) by simp
    show ?thesis using sat_Act[OF assms(2) i, of v s a] sat_InWin[OF assms(1,2) i, of v lo d] by simp
  qed
  then show ?thesis unfolding acted_pre[OF assms(3)] by (auto simp: Acted_def)
qed

definition ObBre :: "int \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> int option \<Rightarrow> int \<Rightarrow> (string, ('n, 'v, 's, 'a) mval) Formula.formula" where
  "ObBre \<tau>\<^sub>0 s a lo d = formula.And (formula.Neg (Acted \<tau>\<^sub>0 s a lo d)) (Passed \<tau>\<^sub>0 d)"

text \<open>The verdict of the window on the prefix up to entry \<open>j\<close>, read from the two formulas
  at entry \<open>j\<close>.\<close>

lemma window_pre_sat:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>" and "j < length \<pi>"
  shows "window s a lo d (pre \<pi> j) =
    (if Formula.sat \<sigma> v j (Acted (time \<pi> 0) s a lo d) then Fulfilled
     else if Formula.sat \<sigma> v j (Passed (time \<pi> 0) d) then Breached d else Pending)"
  by (simp add: window_def passed_pre[OF assms(1,3)] sat_Acted[OF assms] sat_Passed[OF assms])

theorem bridge_window_fulfilled:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>" and "j < length \<pi>"
  shows "window s a lo d (pre \<pi> j) = Fulfilled \<longleftrightarrow> Formula.sat \<sigma> v j (Acted (time \<pi> 0) s a lo d)"
  by (simp add: window_pre_sat[OF assms, where v = v])

theorem bridge_window_breached:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>" and "j < length \<pi>"
  shows "window s a lo d (pre \<pi> j) = Breached t \<longleftrightarrow>
    t = d \<and> Formula.sat \<sigma> v j (ObBre (time \<pi> 0) s a lo d)"
  by (auto simp: window_pre_sat[OF assms, where v = v] ObBre_def)

theorem bridge_window_pending:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>" and "j < length \<pi>"
  shows "window s a lo d (pre \<pi> j) = Pending \<longleftrightarrow>
    \<not> Formula.sat \<sigma> v j (Acted (time \<pi> 0) s a lo d) \<and> \<not> Formula.sat \<sigma> v j (ObBre (time \<pi> 0) s a lo d)"
  by (auto simp: window_pre_sat[OF assms, where v = v] ObBre_def)

text \<open>The same at the last entry of the whole trace.\<close>

corollary bridge_window_last:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>"
  shows "window s a lo d \<pi> = Fulfilled \<longleftrightarrow> Formula.sat \<sigma> v (length \<pi> - 1) (Acted (time \<pi> 0) s a lo d)"
    and "window s a lo d \<pi> = Breached d \<longleftrightarrow> Formula.sat \<sigma> v (length \<pi> - 1) (ObBre (time \<pi> 0) s a lo d)"
proof -
  have j: "length \<pi> - 1 < length \<pi>" using assms(1) by (simp add: is_trace_def)
  show "window s a lo d \<pi> = Fulfilled \<longleftrightarrow> Formula.sat \<sigma> v (length \<pi> - 1) (Acted (time \<pi> 0) s a lo d)"
    using bridge_window_fulfilled[OF assms j, of s a lo d v] by (simp add: pre_last)
  show "window s a lo d \<pi> = Breached d \<longleftrightarrow> Formula.sat \<sigma> v (length \<pi> - 1) (ObBre (time \<pi> 0) s a lo d)"
    using bridge_window_breached[OF assms j, of s a lo d d v] by (simp add: pre_last)
qed

text \<open>An obligation without a deadline is fulfilled by an action after \<open>lo\<close> and is never
  breached.\<close>

definition ActedN :: "int \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> int option \<Rightarrow> (string, ('n, 'v, 's, 'a) mval) Formula.formula" where
  "ActedN \<tau>\<^sub>0 s a lo = formula.Once Interval.all (formula.And (Act s a) (AfterLo \<tau>\<^sub>0 lo))"

theorem bridge_ob_no_deadline:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>" and "j < length \<pi>"
  shows "ob_verdict s a lo None (pre \<pi> j) =
    (if Formula.sat \<sigma> v j (ActedN (time \<pi> 0) s a lo) then Fulfilled else Pending)"
proof -
  have "Formula.sat \<sigma> v i (formula.And (Act s a) (AfterLo (time \<pi> 0) lo)) \<longleftrightarrow>
        1 \<le> i \<and> does s a (evt (\<pi> ! i)) \<and> after lo (time \<pi> i)" if "i \<le> j" for i
  proof -
    have i: "i < length \<pi>" using that assms(3) by simp
    show ?thesis using sat_Act[OF assms(2) i, of v s a] sat_AfterLo[OF assms(1,2) i, of v lo] by simp
  qed
  then have "Formula.sat \<sigma> v j (ActedN (time \<pi> 0) s a lo) \<longleftrightarrow>
      (\<exists>i. 1 \<le> i \<and> i \<le> j \<and> does s a (evt (\<pi> ! i)) \<and> after lo (time \<pi> i))"
    by (auto simp: ActedN_def)
  also have "\<dots> \<longleftrightarrow> (\<exists>i. 1 \<le> i \<and> i < length (pre \<pi> j) \<and> does s a (evt (pre \<pi> j ! i)) \<and> after lo (time (pre \<pi> j) i))"
    unfolding length_pre[OF assms(3)] by (auto simp: time_pre nth_pre less_Suc_eq_le)
  finally show ?thesis by (simp add: ob_verdict_def)
qed


section \<open>Prohibitions\<close>

text \<open>\<open>Forb\<close>: this entry is the action, and the condition was true at the entry before
  it. \<open>PrBre\<close>: some entry up to this one is a forbidden action.\<close>

definition Forb :: "'s \<Rightarrow> 'a \<Rightarrow> ('n, 'v) expr \<Rightarrow> (string, ('n, 'v, 's, 'a) mval) Formula.formula" where
  "Forb s a c = formula.And (Act s a) (formula.Prev Interval.all (Pc c))"

lemma sat_Forb:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>" and "j < length \<pi>" and "econsts c \<subseteq> C"
  shows "Formula.sat \<sigma> v j (Forb s a c) \<longleftrightarrow> forbidden s a c \<pi> j"
proof (cases j)
  case 0
  then show ?thesis by (simp add: Forb_def forbidden_def)
next
  case (Suc k)
  then have k: "k < length \<pi>" using assms(3) by simp
  show ?thesis
    using sat_Act[OF assms(2,3), of v s a] bridge_true[OF assms(1,2) k assms(4), of v] Suc assms(3)
    by (auto simp: Forb_def forbidden_def)
qed

definition PrBre :: "'s \<Rightarrow> 'a \<Rightarrow> ('n, 'v) expr \<Rightarrow> (string, ('n, 'v, 's, 'a) mval) Formula.formula" where
  "PrBre s a c = formula.Once Interval.all (Forb s a c)"

lemma sat_PrBre:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>" and "j < length \<pi>" and "econsts c \<subseteq> C"
  shows "Formula.sat \<sigma> v j (PrBre s a c) \<longleftrightarrow> (\<exists>i \<le> j. forbidden s a c \<pi> i)"
proof -
  have "Formula.sat \<sigma> v i (Forb s a c) \<longleftrightarrow> forbidden s a c \<pi> i" if "i \<le> j" for i
    using sat_Forb[OF assms(1,2) _ assms(4), of i v s a] that assms(3) by simp
  then show ?thesis by (auto simp: PrBre_def)
qed

theorem bridge_pr_breached:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>" and "j < length \<pi>" and "econsts c \<subseteq> C"
  shows "(\<exists>t. pr_verdict s a c (pre \<pi> j) = Breached t) \<longleftrightarrow> Formula.sat \<sigma> v j (PrBre s a c)"
  unfolding sat_PrBre[OF assms] by (auto simp: pr_verdict_def forbidden_pre[OF assms(3)])

theorem bridge_pr_pending:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>" and "j < length \<pi>" and "econsts c \<subseteq> C"
  shows "pr_verdict s a c (pre \<pi> j) = Pending \<longleftrightarrow> \<not> Formula.sat \<sigma> v j (PrBre s a c)"
  unfolding sat_PrBre[OF assms] by (auto simp: pr_verdict_def forbidden_pre[OF assms(3)])

text \<open>The time of the breach: the entry of the first forbidden action.\<close>

definition PrFirst :: "'s \<Rightarrow> 'a \<Rightarrow> ('n, 'v) expr \<Rightarrow> (string, ('n, 'v, 's, 'a) mval) Formula.formula" where
  "PrFirst s a c = formula.And (Forb s a c) (formula.Neg (formula.Prev Interval.all (PrBre s a c)))"

lemma sat_PrFirst:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>" and "k < length \<pi>" and "econsts c \<subseteq> C"
  shows "Formula.sat \<sigma> v k (PrFirst s a c) \<longleftrightarrow> forbidden s a c \<pi> k \<and> (\<forall>i < k. \<not> forbidden s a c \<pi> i)"
proof (cases k)
  case 0
  then show ?thesis using sat_Forb[OF assms, of v s a] by (simp add: PrFirst_def)
next
  case (Suc m)
  then have m: "m < length \<pi>" using assms(3) by simp
  show ?thesis
    using sat_Forb[OF assms, of v s a] sat_PrBre[OF assms(1,2) m assms(4), of v s a] Suc
    by (auto simp: PrFirst_def less_Suc_eq_le)
qed

theorem bridge_pr_time:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>" and "j < length \<pi>" and "econsts c \<subseteq> C"
  shows "pr_verdict s a c (pre \<pi> j) = Breached t \<longleftrightarrow>
    (\<exists>k \<le> j. Formula.sat \<sigma> v k (PrFirst s a c) \<and> time \<pi> k = t)"
proof -
  let ?P = "\<lambda>i. forbidden s a c (pre \<pi> j) i"
  have P: "?P i \<longleftrightarrow> i \<le> j \<and> forbidden s a c \<pi> i" for i
    by (rule forbidden_pre[OF assms(3)])
  have F: "Formula.sat \<sigma> v k (PrFirst s a c) \<longleftrightarrow> forbidden s a c \<pi> k \<and> (\<forall>i < k. \<not> forbidden s a c \<pi> i)"
    if "k \<le> j" for k
    using sat_PrFirst[OF assms(1,2) _ assms(4), of k v s a] that assms(3) by simp
  show ?thesis
  proof
    assume b: "pr_verdict s a c (pre \<pi> j) = Breached t"
    then have ex: "\<exists>i. ?P i" by (auto simp: pr_verdict_def split: if_splits)
    define k where "k = (LEAST i. ?P i)"
    have Pk: "?P k" unfolding k_def using ex by (rule LeastI_ex)
    have before: "\<not> ?P i" if "i < k" for i
      using that not_less_Least[of i ?P] unfolding k_def by blast
    have kj: "k \<le> j" using Pk P by simp
    have t: "t = time \<pi> k" using b ex kj by (simp add: pr_verdict_def k_def[symmetric] time_pre)
    have "forbidden s a c \<pi> k \<and> (\<forall>i < k. \<not> forbidden s a c \<pi> i)"
      using Pk before kj P by auto
    with F[OF kj] kj t show "\<exists>k \<le> j. Formula.sat \<sigma> v k (PrFirst s a c) \<and> time \<pi> k = t" by blast
  next
    assume "\<exists>k \<le> j. Formula.sat \<sigma> v k (PrFirst s a c) \<and> time \<pi> k = t"
    then obtain k where kj: "k \<le> j" and fk: "forbidden s a c \<pi> k"
      and before: "\<forall>i < k. \<not> forbidden s a c \<pi> i" and t: "time \<pi> k = t"
      using F by blast
    have Pk: "?P k" using P kj fk by simp
    have least: "(LEAST i. ?P i) = k"
    proof (rule Least_equality)
      show "?P k" by (rule Pk)
    next
      fix y assume "?P y"
      then have "forbidden s a c \<pi> y" using P by simp
      with before show "k \<le> y" by (meson not_le)
    qed
    have "\<exists>i. ?P i" using Pk by blast
    then show "pr_verdict s a c (pre \<pi> j) = Breached t"
      using least t kj by (simp add: pr_verdict_def time_pre)
  qed
qed

text \<open>The decision of the fail-closed monitor at an entry: it blocks the action unless
  the condition was known to be false at the entry before it.\<close>

definition Blk :: "'s \<Rightarrow> 'a \<Rightarrow> ('n, 'v) expr \<Rightarrow> (string, ('n, 'v, 's, 'a) mval) Formula.formula" where
  "Blk s a c = formula.And (Act s a) (formula.Prev Interval.all (formula.Neg (Nc c)))"

theorem bridge_blocked_action:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>" and "j < length \<pi>" and "econsts c \<subseteq> C"
  shows "blocked_action s a c \<pi> j \<longleftrightarrow> Formula.sat \<sigma> v j (Blk s a c)"
proof (cases j)
  case 0
  then show ?thesis by (simp add: Blk_def blocked_action_def)
next
  case (Suc k)
  then have k: "k < length \<pi>" using assms(3) by simp
  show ?thesis
    using sat_Act[OF assms(2,3), of v s a] bridge_false[OF assms(1,2) k assms(4), of v] Suc assms(3)
    by (auto simp: Blk_def blocked_action_def blocks_def)
qed

text \<open>A permission is exercised by the same entries that breach the prohibition with its
  condition.\<close>

theorem bridge_may:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>" and "j < length \<pi>" and "econsts c \<subseteq> C"
  shows "may_verdict s a c (pre \<pi> j) = Fulfilled \<longleftrightarrow> Formula.sat \<sigma> v j (PrBre s a c)"
proof -
  have "may_verdict s a c (pre \<pi> j) = Fulfilled \<longleftrightarrow> (\<exists>i. forbidden s a c (pre \<pi> j) i)"
    by (auto simp: may_verdict_def forbidden_def)
  then show ?thesis unfolding sat_PrBre[OF assms] by (auto simp: forbidden_pre[OF assms(3)])
qed


section \<open>MAX_AGE: a fresh factor\<close>

definition Fresh :: "int \<Rightarrow> 'n \<Rightarrow> (string, ('n, 'v, 's, 'a) mval) Formula.formula" where
  "Fresh m x = formula.Once (Interval.interval 0 (enat (nat m))) (formula.Pred ''arr'' [trm.Const (MN x)])"

theorem bridge_fresh:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>" and "j < length \<pi>" and "0 \<le> m"
  shows "fresh m x \<pi> j \<longleftrightarrow> Formula.sat \<sigma> v j (Fresh m x)"
proof -
  have arr: "(''arr'', [MN x]) \<in> \<Gamma> \<sigma> i \<longleftrightarrow> evt (\<pi> ! i) = Arrival x" if "i \<le> j" for i
    using that assms(2,3) by (auto simp: enc_pre_def enc_db_def split: event.splits)
  have tm: "\<tau> \<sigma> j - \<tau> \<sigma> i \<le> nat m \<longleftrightarrow> time \<pi> j - time \<pi> i \<le> m" if "i \<le> j" for i
  proof -
    have i: "i < length \<pi>" using that assms(3) by simp
    show ?thesis
      using enc_tau[OF assms(1,2,3)] enc_tau[OF assms(1,2) i] time_mono[OF assms(1) that assms(3)] assms(4)
      by auto
  qed
  have "enat 0 \<le> enat (nat m)" by simp
  then show ?thesis
    using left_interval[of 0 "enat (nat m)"] right_interval[of 0 "enat (nat m)"] arr tm
    by (auto simp: fresh_def Fresh_def eval_trms_def)
qed


section \<open>Fallbacks: ELSE\<close>

text \<open>\<open>ElseIn\<close>: the fallback is in force, since the trace passed \<open>d\<close> without the action.
  The window of the fallback is \<open>(d, d']\<close>, or the times after \<open>d\<close> when it has no
  deadline.\<close>

definition ElseIn :: "int \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> int \<Rightarrow> (string, ('n, 'v, 's, 'a) mval) Formula.formula" where
  "ElseIn \<tau>\<^sub>0 s a d = formula.And (formula.Neg (Acted \<tau>\<^sub>0 s a None d)) (Passed \<tau>\<^sub>0 d)"

lemma else_pre_sat:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>" and "j < length \<pi>"
  shows "else_verdict s a d s' a' (Some d') (pre \<pi> j) =
    (if Formula.sat \<sigma> v j (Acted (time \<pi> 0) s a None d) then EFulfilled
     else if Formula.sat \<sigma> v j (Passed (time \<pi> 0) d)
       then EElse d (if Formula.sat \<sigma> v j (Acted (time \<pi> 0) s' a' (Some d) d') then Fulfilled
                     else if Formula.sat \<sigma> v j (Passed (time \<pi> 0) d') then Breached d' else Pending)
     else EPending)"
  by (simp add: else_verdict_def ob_verdict_def window_pre_sat[OF assms, where v = v]
      passed_pre[OF assms(1,3)] sat_Acted[OF assms] sat_Passed[OF assms])

theorem bridge_else:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>" and "j < length \<pi>"
  shows "else_verdict s a d s' a' (Some d') (pre \<pi> j) = EFulfilled \<longleftrightarrow>
      Formula.sat \<sigma> v j (Acted (time \<pi> 0) s a None d)"
    and "else_verdict s a d s' a' (Some d') (pre \<pi> j) = EElse d Fulfilled \<longleftrightarrow>
      Formula.sat \<sigma> v j (formula.And (ElseIn (time \<pi> 0) s a d) (Acted (time \<pi> 0) s' a' (Some d) d'))"
    and "else_verdict s a d s' a' (Some d') (pre \<pi> j) = EElse d (Breached d') \<longleftrightarrow>
      Formula.sat \<sigma> v j (formula.And (ElseIn (time \<pi> 0) s a d) (ObBre (time \<pi> 0) s' a' (Some d) d'))"
    and "else_verdict s a d s' a' (Some d') (pre \<pi> j) = EPending \<longleftrightarrow>
      \<not> Formula.sat \<sigma> v j (Acted (time \<pi> 0) s a None d) \<and> \<not> Formula.sat \<sigma> v j (Passed (time \<pi> 0) d)"
  by (auto simp: else_pre_sat[OF assms, where v = v] ElseIn_def ObBre_def)

text \<open>The fallback is in force and still open: neither of its two formulas holds.\<close>

theorem bridge_else_alt_pending:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>" and "j < length \<pi>"
  shows "else_verdict s a d s' a' (Some d') (pre \<pi> j) = EElse d Pending \<longleftrightarrow>
      Formula.sat \<sigma> v j (ElseIn (time \<pi> 0) s a d)
      \<and> \<not> Formula.sat \<sigma> v j (Acted (time \<pi> 0) s' a' (Some d) d')
      \<and> \<not> Formula.sat \<sigma> v j (ObBre (time \<pi> 0) s' a' (Some d) d')"
  by (auto simp: else_pre_sat[OF assms, where v = v] ElseIn_def ObBre_def)

text \<open>A fallback without a deadline is fulfilled by an action after \<open>d\<close> and is never
  breached.\<close>

lemma else_none_pre_sat:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>" and "j < length \<pi>"
  shows "else_verdict s a d s' a' None (pre \<pi> j) =
    (if Formula.sat \<sigma> v j (Acted (time \<pi> 0) s a None d) then EFulfilled
     else if Formula.sat \<sigma> v j (Passed (time \<pi> 0) d)
       then EElse d (if Formula.sat \<sigma> v j (ActedN (time \<pi> 0) s' a' (Some d)) then Fulfilled else Pending)
     else EPending)"
  by (simp add: else_verdict_def bridge_ob_no_deadline[OF assms, where v = v]
      passed_pre[OF assms(1,3)] sat_Acted[OF assms] sat_Passed[OF assms])

theorem bridge_else_no_deadline:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>" and "j < length \<pi>"
  shows "else_verdict s a d s' a' None (pre \<pi> j) = EFulfilled \<longleftrightarrow>
      Formula.sat \<sigma> v j (Acted (time \<pi> 0) s a None d)"
    and "else_verdict s a d s' a' None (pre \<pi> j) = EElse d Fulfilled \<longleftrightarrow>
      Formula.sat \<sigma> v j (formula.And (ElseIn (time \<pi> 0) s a d) (ActedN (time \<pi> 0) s' a' (Some d)))"
    and "else_verdict s a d s' a' None (pre \<pi> j) = EElse d Pending \<longleftrightarrow>
      Formula.sat \<sigma> v j (ElseIn (time \<pi> 0) s a d) \<and> \<not> Formula.sat \<sigma> v j (ActedN (time \<pi> 0) s' a' (Some d))"
    and "else_verdict s a d s' a' None (pre \<pi> j) = EPending \<longleftrightarrow>
      \<not> Formula.sat \<sigma> v j (Acted (time \<pi> 0) s a None d) \<and> \<not> Formula.sat \<sigma> v j (Passed (time \<pi> 0) d)"
  by (auto simp: else_none_pre_sat[OF assms, where v = v] ElseIn_def)


section \<open>Handlers of a breach\<close>

text \<open>The status of an obligation with a handler. While the obligation is not breached the
  handler does not matter: the status is that of the window.\<close>

theorem bridge_handle_open:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>" and "j < length \<pi>"
  shows "handle_breach b lo s a d acts (pre \<pi> j) = SFulfilled \<longleftrightarrow>
      Formula.sat \<sigma> v j (Acted (time \<pi> 0) s a lo d)"
    and "handle_breach b lo s a d acts (pre \<pi> j) = SPending \<longleftrightarrow>
      \<not> Formula.sat \<sigma> v j (Acted (time \<pi> 0) s a lo d) \<and> \<not> Formula.sat \<sigma> v j (ObBre (time \<pi> 0) s a lo d)"
  by (auto simp: handle_breach_def window_pre_sat[OF assms, where v = v] ObBre_def)

text \<open>TERMINATE, and a handler without a continuation: the obligation stays breached.\<close>

theorem bridge_terminate:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>" and "j < length \<pi>"
    and "cont_of acts = Some Terminate"
  shows "handle_breach b lo s a d acts (pre \<pi> j) = SBreached d Terminated \<longleftrightarrow>
      Formula.sat \<sigma> v j (ObBre (time \<pi> 0) s a lo d)"
  using assms(4) by (auto simp: handle_breach_def window_pre_sat[OF assms(1-3), where v = v] ObBre_def)

theorem bridge_no_continuation:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>" and "j < length \<pi>"
    and "cont_of acts = None"
  shows "handle_breach b lo s a d acts (pre \<pi> j) = SBreached d NoContinuation \<longleftrightarrow>
      Formula.sat \<sigma> v j (ObBre (time \<pi> 0) s a lo d)"
  using assms(4) by (auto simp: handle_breach_def window_pre_sat[OF assms(1-3), where v = v] ObBre_def)

text \<open>\<open>CURE_BY k\<close>: a second window \<open>(d, d + k]\<close> for the same action.\<close>

theorem bridge_cure:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>" and "j < length \<pi>"
    and "cont_of acts = Some (CureBy k)"
  shows "handle_breach b lo s a d acts (pre \<pi> j) = SBreached d (Cure Fulfilled) \<longleftrightarrow>
      Formula.sat \<sigma> v j (formula.And (ObBre (time \<pi> 0) s a lo d) (Acted (time \<pi> 0) s a (Some d) (d + k)))"
    and "handle_breach b lo s a d acts (pre \<pi> j) = SBreached d (Cure (Breached (d + k))) \<longleftrightarrow>
      Formula.sat \<sigma> v j (formula.And (ObBre (time \<pi> 0) s a lo d) (ObBre (time \<pi> 0) s a (Some d) (d + k)))"
    and "handle_breach b lo s a d acts (pre \<pi> j) = SFulfilled \<longleftrightarrow>
      Formula.sat \<sigma> v j (Acted (time \<pi> 0) s a lo d)"
  using assms(4) by (auto simp: handle_breach_def window_pre_sat[OF assms(1-3), where v = v] ObBre_def)

theorem bridge_cure_pending:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>" and "j < length \<pi>"
    and "cont_of acts = Some (CureBy k)"
  shows "handle_breach b lo s a d acts (pre \<pi> j) = SBreached d (Cure Pending) \<longleftrightarrow>
      Formula.sat \<sigma> v j (ObBre (time \<pi> 0) s a lo d)
      \<and> \<not> Formula.sat \<sigma> v j (Acted (time \<pi> 0) s a (Some d) (d + k))
      \<and> \<not> Formula.sat \<sigma> v j (ObBre (time \<pi> 0) s a (Some d) (d + k))"
  using assms(4) by (auto simp: handle_breach_def window_pre_sat[OF assms(1-3), where v = v] ObBre_def)

text \<open>\<open>ESCALATE_TO s'\<close>: a window of the same length for \<open>s'\<close>, counted from \<open>d\<close>; \<open>b\<close> is
  the start of the obligation.\<close>

theorem bridge_escalate:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>" and "j < length \<pi>"
    and "cont_of acts = Some (EscalateTo s')"
  shows "handle_breach b lo s a d acts (pre \<pi> j) = SBreached d (Escalated s' Fulfilled) \<longleftrightarrow>
      Formula.sat \<sigma> v j (formula.And (ObBre (time \<pi> 0) s a lo d)
        (Acted (time \<pi> 0) s' a (Some d) (d + (d - b))))"
    and "handle_breach b lo s a d acts (pre \<pi> j) = SBreached d (Escalated s' (Breached (d + (d - b)))) \<longleftrightarrow>
      Formula.sat \<sigma> v j (formula.And (ObBre (time \<pi> 0) s a lo d)
        (ObBre (time \<pi> 0) s' a (Some d) (d + (d - b))))"
  using assms(4) by (auto simp: handle_breach_def window_pre_sat[OF assms(1-3), where v = v] ObBre_def)

theorem bridge_escalate_pending:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>" and "j < length \<pi>"
    and "cont_of acts = Some (EscalateTo s')"
  shows "handle_breach b lo s a d acts (pre \<pi> j) = SBreached d (Escalated s' Pending) \<longleftrightarrow>
      Formula.sat \<sigma> v j (ObBre (time \<pi> 0) s a lo d)
      \<and> \<not> Formula.sat \<sigma> v j (Acted (time \<pi> 0) s' a (Some d) (d + (d - b)))
      \<and> \<not> Formula.sat \<sigma> v j (ObBre (time \<pi> 0) s' a (Some d) (d + (d - b)))"
  using assms(4) by (auto simp: handle_breach_def window_pre_sat[OF assms(1-3), where v = v] ObBre_def)

end
