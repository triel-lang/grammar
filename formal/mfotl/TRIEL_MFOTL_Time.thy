(*  Title:      TRIEL_MFOTL_Time.thy
    Purpose:    The bridge from the TRIEL core to MFOTL, part 2: the time of an entry as
                the distance from the activation entry, the formulas that read it
                (First, At, InWin, AfterLo, Passed), and the verdict predicates of the
                core on a prefix of an implementation trace.
    SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause
*)

theory TRIEL_MFOTL_Time
  imports TRIEL_MFOTL_Enc
begin

section \<open>Intervals\<close>

text \<open>The bounds of the two intervals the formulas use. The intervals of MFOTL are closed
  on both sides.\<close>

lemma left_all [simp]: "Interval.left Interval.all = 0"
  by transfer simp

lemma right_all [simp]: "Interval.right Interval.all = \<infinity>"
  by transfer simp

lemma left_interval [simp]: "enat l \<le> r \<Longrightarrow> Interval.left (Interval.interval l r) = l"
  by (simp add: Interval.interval_def left.rep_eq Abs_\<I>_inverse)

lemma right_interval [simp]: "enat l \<le> r \<Longrightarrow> Interval.right (Interval.interval l r) = r"
  by (simp add: Interval.interval_def right.rep_eq Abs_\<I>_inverse)


section \<open>Time since activation\<close>

text \<open>The timestamp of entry \<open>j\<close> of an encoding is the time of the entry counted from
  entry 0, the activation entry; the timestamp of entry 0 is 0.\<close>

lemma enc_tau0:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>"
  shows "\<tau> \<sigma> 0 = 0"
  using assms by (simp add: enc_pre_def is_trace_def)

lemma enc_tau:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>" and "j < length \<pi>"
  shows "\<tau> \<sigma> j = nat (time \<pi> j - time \<pi> 0)" and "time \<pi> 0 \<le> time \<pi> j"
  using assms time_mono[OF assms(1), of 0 j] by (simp_all add: enc_pre_def)

text \<open>\<open>First\<close> holds exactly at entry 0, and \<open>At I\<close> holds at an entry when its time
  since entry 0 is in \<open>I\<close>.\<close>

definition First :: "(string, ('n, 'v, 's, 'a) mval) Formula.formula" where
  "First = formula.Neg (formula.Prev Interval.all formula.TT)"

lemma sat_First: "Formula.sat \<sigma> v j First \<longleftrightarrow> j = 0"
  by (cases j) (simp_all add: First_def)

definition At :: "\<I> \<Rightarrow> (string, ('n, 'v, 's, 'a) mval) Formula.formula" where
  "At I = formula.Once I First"

lemma sat_At: "Formula.sat \<sigma> v j (At I) \<longleftrightarrow> mem (\<tau> \<sigma> j - \<tau> \<sigma> 0) I"
  by (auto simp: At_def sat_First)

text \<open>The lower bound of a window \<open>(lo, d]\<close> as a distance from the activation time
  \<open>\<tau>\<^sub>0\<close>: times are integers, so "strictly after \<open>l\<close>" is "from \<open>l + 1\<close> on".\<close>

definition rel_lo :: "int \<Rightarrow> int option \<Rightarrow> nat" where
  "rel_lo \<tau>\<^sub>0 lo = (case lo of None \<Rightarrow> 0 | Some l \<Rightarrow> nat (l + 1 - \<tau>\<^sub>0))"

lemma after_rel: "\<tau>\<^sub>0 \<le> t \<Longrightarrow> after lo t \<longleftrightarrow> rel_lo \<tau>\<^sub>0 lo \<le> nat (t - \<tau>\<^sub>0)"
  by (cases lo) (auto simp: rel_lo_def)

text \<open>The times of the window \<open>(lo, d]\<close>, the times after \<open>lo\<close>, and the times strictly
  after \<open>d\<close>. A deadline before the activation and an empty window are cases of the
  definitions: an interval of MFOTL needs its left bound below its right bound.\<close>

definition InWin :: "int \<Rightarrow> int option \<Rightarrow> int \<Rightarrow> (string, ('n, 'v, 's, 'a) mval) Formula.formula" where
  "InWin \<tau>\<^sub>0 lo d = (if d < \<tau>\<^sub>0 \<or> nat (d - \<tau>\<^sub>0) < rel_lo \<tau>\<^sub>0 lo then formula.FF
     else At (Interval.interval (rel_lo \<tau>\<^sub>0 lo) (enat (nat (d - \<tau>\<^sub>0)))))"

lemma sat_InWin:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>" and "j < length \<pi>"
  shows "Formula.sat \<sigma> v j (InWin (time \<pi> 0) lo d) \<longleftrightarrow> after lo (time \<pi> j) \<and> time \<pi> j \<le> d"
proof -
  note t = enc_tau[OF assms] and t0 = enc_tau0[OF assms(1,2)]
  note ar = after_rel[OF t(2), of lo]
  show ?thesis
  proof (cases "d < time \<pi> 0 \<or> nat (d - time \<pi> 0) < rel_lo (time \<pi> 0) lo")
    case True
    then show ?thesis using t(2) ar by (auto simp: InWin_def)
  next
    case False
    then have "enat (rel_lo (time \<pi> 0) lo) \<le> enat (nat (d - time \<pi> 0))" by simp
    then show ?thesis using False t t0 ar by (auto simp: InWin_def sat_At)
  qed
qed

definition AfterLo :: "int \<Rightarrow> int option \<Rightarrow> (string, ('n, 'v, 's, 'a) mval) Formula.formula" where
  "AfterLo \<tau>\<^sub>0 lo = At (Interval.interval (rel_lo \<tau>\<^sub>0 lo) \<infinity>)"

lemma sat_AfterLo:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>" and "j < length \<pi>"
  shows "Formula.sat \<sigma> v j (AfterLo (time \<pi> 0) lo) \<longleftrightarrow> after lo (time \<pi> j)"
  using enc_tau[OF assms] enc_tau0[OF assms(1,2)] after_rel[of "time \<pi> 0" "time \<pi> j" lo]
  by (simp add: AfterLo_def sat_At)

definition Passed :: "int \<Rightarrow> int \<Rightarrow> (string, ('n, 'v, 's, 'a) mval) Formula.formula" where
  "Passed \<tau>\<^sub>0 d = (if d < \<tau>\<^sub>0 then formula.TT else At (Interval.interval (Suc (nat (d - \<tau>\<^sub>0))) \<infinity>))"

lemma sat_Passed:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>" and "j < length \<pi>"
  shows "Formula.sat \<sigma> v j (Passed (time \<pi> 0) d) \<longleftrightarrow> d < time \<pi> j"
  using enc_tau[OF assms] enc_tau0[OF assms(1,2)]
  by (auto simp: Passed_def sat_At)

text \<open>For \<open>WITHIN k\<close> without \<open>FROM\<close> the deadline is \<open>\<tau>\<^sub>0 + k\<close>, and the formulas do not
  depend on the activation time.\<close>

lemma InWin_within:
  "0 \<le> k \<Longrightarrow> (InWin \<tau>\<^sub>0 None (\<tau>\<^sub>0 + k) :: (string, ('n, 'v, 's, 'a) mval) Formula.formula)
     = At (Interval.interval 0 (enat (nat k)))"
  by (simp add: InWin_def rel_lo_def)

lemma Passed_within:
  "0 \<le> k \<Longrightarrow> (Passed \<tau>\<^sub>0 (\<tau>\<^sub>0 + k) :: (string, ('n, 'v, 's, 'a) mval) Formula.formula)
     = At (Interval.interval (Suc (nat k)) \<infinity>)"
  by (simp add: Passed_def)


section \<open>Prefixes of an implementation trace\<close>

text \<open>The verdicts of the core are functions of a finite trace. Read on the prefix
  \<open>pre \<pi> j\<close>, their predicates are statements about the entries \<open>0..j\<close> of \<open>\<pi>\<close>.\<close>

lemma pre_last: "pre \<pi> (length \<pi> - Suc 0) = \<pi>"
  by (simp add: pre_def)

lemma time_pre: "i \<le> j \<Longrightarrow> time (pre \<pi> j) i = time \<pi> i"
  by (simp add: time_def nth_pre)

lemma acted_pre:
  assumes "j < length \<pi>"
  shows "acted s a lo d (pre \<pi> j) \<longleftrightarrow>
    (\<exists>i. 1 \<le> i \<and> i \<le> j \<and> does s a (evt (\<pi> ! i)) \<and> after lo (time \<pi> i) \<and> time \<pi> i \<le> d)"
  unfolding acted_def length_pre[OF assms]
  by (auto simp: time_pre nth_pre less_Suc_eq_le)

lemma passed_pre:
  assumes "is_trace \<pi>" and "j < length \<pi>"
  shows "passed d (pre \<pi> j) \<longleftrightarrow> d < time \<pi> j"
proof
  assume "passed d (pre \<pi> j)"
  then obtain i where i: "i \<le> j" "d < time \<pi> i"
    unfolding passed_def length_pre[OF assms(2)] by (auto simp: time_pre less_Suc_eq_le)
  from time_mono[OF assms(1) i(1) assms(2)] i(2) show "d < time \<pi> j" by simp
next
  assume "d < time \<pi> j"
  then show "passed d (pre \<pi> j)"
    unfolding passed_def length_pre[OF assms(2)] by (auto simp: time_pre intro!: exI[of _ j])
qed

lemma forbidden_pre:
  assumes "j < length \<pi>"
  shows "forbidden s a c (pre \<pi> j) i \<longleftrightarrow> i \<le> j \<and> forbidden s a c \<pi> i"
proof -
  have eq: "pre \<pi> j @ drop (Suc j) \<pi> = \<pi>" by (simp add: pre_def)
  have lp: "length (pre \<pi> j) = Suc j" using assms by (rule length_pre)
  have "forbidden s a c (pre \<pi> j) i \<longleftrightarrow> forbidden s a c \<pi> i" if "i \<le> j"
    using forbidden_append[of i "pre \<pi> j" s a c "drop (Suc j) \<pi>"] that lp by (simp only: eq)
  moreover have "i \<le> j" if "forbidden s a c (pre \<pi> j) i"
    using forbidden_less[OF that] lp by simp
  ultimately show ?thesis by blast
qed

end
