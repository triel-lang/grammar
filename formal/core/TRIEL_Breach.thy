(*  Title:      TRIEL_Breach.thy
    Purpose:    Deadlines and breach (TECHNICAL_REPORT.md section 2.6) as a layer of
                verdicts over implementation traces: BY and WITHIN, prohibitions and
                permissions, the fail-closed monitor of a prohibition as a function on
                traces (enforce: sound, transparent on defined data, idempotent),
                binding of ON_BREACH, breach actions and their continuations, and
                MAX_AGE with ON_STALE BLOCK. The trace semantics of TRIEL_Trace and
                TRIEL_Terms is unchanged.
    SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause
*)

theory TRIEL_Breach
  imports TRIEL_Trace
begin

section \<open>Implementation traces\<close>

text \<open>Section 2.6 distinguishes the specification trace of section 2.5 from the
  implementation trace, the events a running system produces, each with a timestamp.
  Implementation traces reuse the traces of TRIEL_Trace with integer timestamps. Entry 0
  is the activation entry: its timestamp is the activation time \<open>\<tau>\<^sub>0\<close> and its state the
  activation state. Actions are the events of the later entries. An event is matched by
  subject and action only (\<open>does\<close> of TRIEL_Trace, as in the trace semantics): the polarity
  belongs to the norm, not to the event.\<close>

type_synonym ('n, 'v, 's, 'a) itrace = "('n, 'v, int, 's, 'a) trace"

definition time :: "('n, 'v, 's, 'a) itrace \<Rightarrow> nat \<Rightarrow> int" where
  "time \<pi> j = tstamp (\<pi> ! j)"

lemma time_mono: "is_trace \<pi> \<Longrightarrow> i \<le> j \<Longrightarrow> j < length \<pi> \<Longrightarrow> time \<pi> i \<le> time \<pi> j"
  unfolding is_trace_def time_def using sorted_nth_mono[of "map tstamp \<pi>" i j] by simp

lemma time_append [simp]: "j < length \<pi> \<Longrightarrow> time (\<pi> @ \<rho>) j = time \<pi> j"
  by (simp add: time_def nth_append)

lemma itrace_nth_append [simp]: "j < length \<pi> \<Longrightarrow> (\<pi> @ \<rho>) ! j = \<pi> ! j"
  by (simp add: nth_append)

lemma st_append [simp]: "j < length \<pi> \<Longrightarrow> st (\<pi> @ \<rho>) j = st \<pi> j"
  by (simp add: st_def nth_append)


section \<open>Deadlines and activation\<close>

text \<open>A deadline is an absolute time, a duration, or the value of a factor plus an
  offset. It is resolved once, at activation: a duration counts from the activation time
  \<open>\<tau>\<^sub>0\<close>, and a factor is read in the activation state (the function \<open>T\<close> turns a value into
  a time). If a factor is absent or its value is not a time, the deadline is undefined and
  the activation is rejected. A term-level \<open>WITHIN d\<close> on an obligation is the same as
  \<open>BY d\<close> with a duration.\<close>

datatype 'n deadline =
    DAt int            \<comment> \<open>an absolute time\<close>
  | DAfter int         \<comment> \<open>a duration, counted from the activation time\<close>
  | DFactor 'n int     \<comment> \<open>the value of a factor at activation, plus an offset\<close>

fun resolve :: "('v \<Rightarrow> int option) \<Rightarrow> int \<Rightarrow> ('n, 'v) state \<Rightarrow> 'n deadline \<Rightarrow> int option" where
  "resolve T \<tau>\<^sub>0 \<sigma>\<^sub>0 (DAt t) = Some t"
| "resolve T \<tau>\<^sub>0 \<sigma>\<^sub>0 (DAfter k) = Some (\<tau>\<^sub>0 + k)"
| "resolve T \<tau>\<^sub>0 \<sigma>\<^sub>0 (DFactor x k) =
     (case \<sigma>\<^sub>0 x of None \<Rightarrow> None | Some v \<Rightarrow> map_option (\<lambda>t. t + k) (T v))"


section \<open>Verdicts of obligations\<close>

datatype verdict = Fulfilled | Breached int | Pending

fun after :: "int option \<Rightarrow> int \<Rightarrow> bool" where
  "after None \<tau> = True"
| "after (Some l) \<tau> = (l < \<tau>)"

text \<open>\<open>acted s a lo d \<pi>\<close>: subject \<open>s\<close> performed action \<open>a\<close> in the window \<open>(lo, d]\<close>.
  \<open>passed d \<pi>\<close>: the trace has an entry strictly after \<open>d\<close>.\<close>

definition acted :: "'s \<Rightarrow> 'a \<Rightarrow> int option \<Rightarrow> int \<Rightarrow> ('n, 'v, 's, 'a) itrace \<Rightarrow> bool" where
  "acted s a lo d \<pi> \<longleftrightarrow>
     (\<exists>j. 1 \<le> j \<and> j < length \<pi> \<and> does s a (evt (\<pi> ! j)) \<and> after lo (time \<pi> j) \<and> time \<pi> j \<le> d)"

definition passed :: "int \<Rightarrow> ('n, 'v, 's, 'a) itrace \<Rightarrow> bool" where
  "passed d \<pi> \<longleftrightarrow> (\<exists>j < length \<pi>. d < time \<pi> j)"

text \<open>The verdict of an obligation with window \<open>(lo, d]\<close>: fulfilled by an action in the
  window; breached at \<open>d\<close> once the trace has gone strictly past \<open>d\<close> without one; pending
  otherwise. An action exactly at \<open>d\<close> fulfils.\<close>

definition window :: "'s \<Rightarrow> 'a \<Rightarrow> int option \<Rightarrow> int \<Rightarrow> ('n, 'v, 's, 'a) itrace \<Rightarrow> verdict" where
  "window s a lo d \<pi> =
     (if acted s a lo d \<pi> then Fulfilled else if passed d \<pi> then Breached d else Pending)"

text \<open>\<open>s MUST a BY d\<close> (or \<open>WITHIN d\<close>) has the window \<open>(lo, d]\<close>, with \<open>lo = None\<close>, that
  is \<open>(-\<infinity>, d]\<close>, unless the obligation has \<open>FROM\<close> (see below). Without a deadline an
  obligation is never breached.\<close>

definition ob_verdict :: "'s \<Rightarrow> 'a \<Rightarrow> int option \<Rightarrow> int option \<Rightarrow> ('n, 'v, 's, 'a) itrace \<Rightarrow> verdict" where
  "ob_verdict s a lo D \<pi> =
     (case D of
        Some d \<Rightarrow> window s a lo d \<pi>
      | None \<Rightarrow> (if \<exists>j. 1 \<le> j \<and> j < length \<pi> \<and> does s a (evt (\<pi> ! j)) \<and> after lo (time \<pi> j)
                 then Fulfilled else Pending))"

theorem deadline_missed_breach:
  "\<not> acted s a lo d \<pi> \<Longrightarrow> passed d \<pi> \<Longrightarrow> ob_verdict s a lo (Some d) \<pi> = Breached d"
  by (simp add: ob_verdict_def window_def)

corollary within_missed_breach:
  assumes "resolve T \<tau>\<^sub>0 \<sigma>\<^sub>0 (DAfter k) = Some d"
    and "\<not> acted s a None d \<pi>" and "passed d \<pi>"
  shows "ob_verdict s a None (Some d) \<pi> = Breached (\<tau>\<^sub>0 + k)"
  using assms by (simp add: ob_verdict_def window_def)

theorem fulfilled_at_deadline:
  assumes "1 \<le> j" and "j < length \<pi>" and "does s a (evt (\<pi> ! j))" and "time \<pi> j = d"
  shows "ob_verdict s a None (Some d) \<pi> = Fulfilled"
  using assms unfolding ob_verdict_def window_def acted_def by auto

text \<open>A pending verdict means that the window is still open: no entry is past \<open>d\<close>.\<close>

theorem pending_open: "window s a lo d \<pi> = Pending \<Longrightarrow> \<forall>j < length \<pi>. time \<pi> j \<le> d"
  unfolding window_def passed_def by (auto split: if_splits)

lemma window_breached_at: "window s a lo d \<pi> = Breached \<tau> \<Longrightarrow> \<tau> = d"
  unfolding window_def by (auto split: if_splits)

lemma acted_append:
  assumes "acted s a lo d \<pi>"
  shows "acted s a lo d (\<pi> @ \<rho>)"
proof -
  from assms obtain j where "1 \<le> j" "j < length \<pi>" "does s a (evt (\<pi> ! j))"
    "after lo (time \<pi> j)" "time \<pi> j \<le> d"
    unfolding acted_def by blast
  then show ?thesis unfolding acted_def by (intro exI[of _ j]) simp
qed

lemma passed_append:
  assumes "passed d \<pi>"
  shows "passed d (\<pi> @ \<rho>)"
proof -
  from assms obtain j where "j < length \<pi>" "d < time \<pi> j" unfolding passed_def by blast
  then show ?thesis unfolding passed_def by (intro exI[of _ j]) simp
qed

text \<open>Verdicts are final: once a verdict is reached, later events do not change it. For a
  breach this needs non-decreasing timestamps: an action that comes after an entry past the
  deadline is itself past the deadline.\<close>

theorem window_final:
  assumes tr: "is_trace (\<pi> @ \<rho>)" and dec: "window s a lo d \<pi> \<noteq> Pending"
  shows "window s a lo d (\<pi> @ \<rho>) = window s a lo d \<pi>"
proof (cases "acted s a lo d \<pi>")
  case True
  then show ?thesis by (simp add: window_def acted_append)
next
  case False
  with dec have p: "passed d \<pi>" by (auto simp: window_def split: if_splits)
  then obtain i where i: "i < length \<pi>" "d < time \<pi> i" unfolding passed_def by blast
  have "\<not> acted s a lo d (\<pi> @ \<rho>)"
  proof
    assume "acted s a lo d (\<pi> @ \<rho>)"
    then obtain j where j: "1 \<le> j" "j < length (\<pi> @ \<rho>)" "does s a (evt ((\<pi> @ \<rho>) ! j))"
      "after lo (time (\<pi> @ \<rho>) j)" "time (\<pi> @ \<rho>) j \<le> d"
      unfolding acted_def by blast
    show False
    proof (cases "j < length \<pi>")
      case True
      with j False show False unfolding acted_def by auto
    next
      case False
      then have ij: "i \<le> j" using i(1) by simp
      have "time (\<pi> @ \<rho>) i \<le> time (\<pi> @ \<rho>) j" by (rule time_mono[OF tr ij j(2)])
      moreover have "time (\<pi> @ \<rho>) i = time \<pi> i" using i(1) by simp
      ultimately show False using i(2) j(5) by linarith
    qed
  qed
  with False p show ?thesis by (simp add: window_def passed_append)
qed

corollary ob_verdict_final:
  "is_trace (\<pi> @ \<rho>) \<Longrightarrow> ob_verdict s a lo (Some d) \<pi> \<noteq> Pending \<Longrightarrow>
     ob_verdict s a lo (Some d) (\<pi> @ \<rho>) = ob_verdict s a lo (Some d) \<pi>"
  unfolding ob_verdict_def by (simp add: window_final)


section \<open>The start of an obligation: FROM\<close>

text \<open>\<open>s MUST a BY d FROM f\<close> has the window \<open>[f, d]\<close>: an action before \<open>f\<close> does not fulfil
  it. \<open>f\<close> is resolved at activation like a deadline (a DATETIME, or a factor read in the
  activation state), and a duration in \<open>BY\<close> counts from \<open>f\<close>. Without \<open>FROM\<close> the start
  is the activation time \<open>\<tau>\<^sub>0\<close> and the window is \<open>(-\<infinity>, d]\<close>, as above. Times are
  integers, so the closed window \<open>[f, d]\<close> is the window \<open>(f - 1, d]\<close>.\<close>

definition start_of :: "('v \<Rightarrow> int option) \<Rightarrow> int \<Rightarrow> ('n, 'v) state \<Rightarrow> 'n deadline option \<Rightarrow> int option" where
  "start_of T \<tau>\<^sub>0 \<sigma>\<^sub>0 F = (case F of None \<Rightarrow> Some \<tau>\<^sub>0 | Some f \<Rightarrow> resolve T \<tau>\<^sub>0 \<sigma>\<^sub>0 f)"

definition lo_of :: "'n deadline option \<Rightarrow> int \<Rightarrow> int option" where
  "lo_of F b = (case F of None \<Rightarrow> None | Some f \<Rightarrow> Some (b - 1))"

definition deadline_of :: "('v \<Rightarrow> int option) \<Rightarrow> int \<Rightarrow> ('n, 'v) state \<Rightarrow> 'n deadline option
    \<Rightarrow> 'n deadline option \<Rightarrow> int option" where
  "deadline_of T \<tau>\<^sub>0 \<sigma>\<^sub>0 F D =
     (case start_of T \<tau>\<^sub>0 \<sigma>\<^sub>0 F of None \<Rightarrow> None | Some b \<Rightarrow> Option.bind D (resolve T b \<sigma>\<^sub>0))"

lemma int_minus_one_less: "(b :: int) - 1 < t \<longleftrightarrow> b \<le> t"
  by presburger

lemma after_from: "after (Some (b - 1)) t \<longleftrightarrow> b \<le> t"
  by (simp add: int_minus_one_less)

theorem from_window:
  "acted s a (Some (b - 1)) d \<pi> \<longleftrightarrow>
     (\<exists>j. 1 \<le> j \<and> j < length \<pi> \<and> does s a (evt (\<pi> ! j)) \<and> b \<le> time \<pi> j \<and> time \<pi> j \<le> d)"
  unfolding acted_def by (auto simp: int_minus_one_less)

text \<open>Without \<open>FROM\<close>, start, window and deadline are those of an obligation without it.\<close>

theorem no_from:
  "start_of T \<tau>\<^sub>0 \<sigma>\<^sub>0 None = Some \<tau>\<^sub>0" and "lo_of None b = None"
  and "deadline_of T \<tau>\<^sub>0 \<sigma>\<^sub>0 None D = Option.bind D (resolve T \<tau>\<^sub>0 \<sigma>\<^sub>0)"
  by (simp_all add: start_of_def lo_of_def deadline_of_def)

theorem from_duration:
  "start_of T \<tau>\<^sub>0 \<sigma>\<^sub>0 F = Some b \<Longrightarrow> deadline_of T \<tau>\<^sub>0 \<sigma>\<^sub>0 F (Some (DAfter k)) = Some (b + k)"
  by (simp add: deadline_of_def)

theorem from_at: "start_of T \<tau>\<^sub>0 \<sigma>\<^sub>0 (Some (DAt t)) = Some t"
  by (simp add: start_of_def)

theorem from_absent_factor: "\<sigma>\<^sub>0 x = None \<Longrightarrow> start_of T \<tau>\<^sub>0 \<sigma>\<^sub>0 (Some (DFactor x k)) = None"
  by (simp add: start_of_def)

text \<open>An action before the start does not fulfil the obligation; one exactly at the start
  does.\<close>

theorem before_from_no_fulfil:
  assumes "\<And>j. 1 \<le> j \<Longrightarrow> j < length \<pi> \<Longrightarrow> does s a (evt (\<pi> ! j)) \<Longrightarrow> time \<pi> j < b"
    and "passed d \<pi>"
  shows "ob_verdict s a (Some (b - 1)) (Some d) \<pi> = Breached d"
proof -
  have "\<not> acted s a (Some (b - 1)) d \<pi>"
    unfolding from_window using assms(1) by force
  from this assms(2) show ?thesis by (rule deadline_missed_breach)
qed

theorem fulfilled_at_from:
  assumes "1 \<le> j" and "j < length \<pi>" and "does s a (evt (\<pi> ! j))" and "time \<pi> j = b"
    and "b \<le> d"
  shows "ob_verdict s a (Some (b - 1)) (Some d) \<pi> = Fulfilled"
  using assms unfolding ob_verdict_def window_def acted_def by (auto simp: int_minus_one_less)

theorem from_no_deadline:
  "ob_verdict s a (Some (b - 1)) None \<pi> =
     (if \<exists>j. 1 \<le> j \<and> j < length \<pi> \<and> does s a (evt (\<pi> ! j)) \<and> b \<le> time \<pi> j then Fulfilled else Pending)"
  by (simp add: ob_verdict_def int_minus_one_less)

text \<open>A window that starts after its deadline cannot be met: the obligation is breached
  at the deadline once the trace passes it.\<close>

theorem empty_window_breached:
  "d < b \<Longrightarrow> passed d \<pi> \<Longrightarrow> ob_verdict s a (Some (b - 1)) (Some d) \<pi> = Breached d"
  by (rule deadline_missed_breach) (auto simp: acted_def)


section \<open>Prohibitions and permissions\<close>

text \<open>\<open>s MUST_NOT a WHEN c\<close> is breached at the first action \<open>a\<close> of \<open>s\<close> before which \<open>c\<close> is
  true (\<open>forbidden\<close> of TRIEL_Trace); \<open>c\<close> is evaluated in the state before the action. An
  undefined \<open>c\<close> is not a breach.\<close>

definition pr_verdict :: "'s \<Rightarrow> 'a \<Rightarrow> ('n, 'v :: value_order) expr \<Rightarrow> ('n, 'v, 's, 'a) itrace \<Rightarrow> verdict" where
  "pr_verdict s a c \<pi> =
     (if \<exists>j. forbidden s a c \<pi> j then Breached (time \<pi> (LEAST j. forbidden s a c \<pi> j)) else Pending)"

theorem pr_verdict_final:
  assumes "pr_verdict s a c \<pi> \<noteq> Pending"
  shows "pr_verdict s a c (\<pi> @ \<rho>) = pr_verdict s a c \<pi>"
proof -
  from assms obtain j where j: "forbidden s a c \<pi> j" by (auto simp: pr_verdict_def split: if_splits)
  define k where "k = (LEAST j. forbidden s a c \<pi> j)"
  have fk: "forbidden s a c \<pi> k" unfolding k_def using j by (rule LeastI)
  have kl: "k < length \<pi>" using fk by (rule forbidden_less)
  have least: "(LEAST j. forbidden s a c (\<pi> @ \<rho>) j) = k"
  proof (rule Least_equality)
    show "forbidden s a c (\<pi> @ \<rho>) k" using fk kl by (simp add: forbidden_append)
  next
    fix y assume y: "forbidden s a c (\<pi> @ \<rho>) y"
    show "k \<le> y"
    proof (rule ccontr)
      assume "\<not> k \<le> y"
      then have "y < k" by simp
      with kl y have "forbidden s a c \<pi> y" by (simp add: forbidden_append)
      then have "k \<le> y" unfolding k_def by (rule Least_le)
      with \<open>y < k\<close> show False by simp
    qed
  qed
  have ex: "\<exists>j. forbidden s a c (\<pi> @ \<rho>) j"
    by (intro exI[of _ k]) (simp add: forbidden_append[OF kl] fk)
  have "pr_verdict s a c (\<pi> @ \<rho>) = Breached (time (\<pi> @ \<rho>) k)"
    using ex least by (simp add: pr_verdict_def)
  also have "\<dots> = Breached (time \<pi> k)" using kl by simp
  also have "\<dots> = pr_verdict s a c \<pi>" using j by (auto simp: pr_verdict_def k_def)
  finally show ?thesis .
qed

text \<open>The verdict and the trace semantics of a prohibition agree. A violated trace of
  \<open>s MUST_NOT a WHEN c\<close> (TRIEL_Trace, \<open>mustnot_d\<close>) is breached at its last entry, and every
  breached trace has the prefix up to the breach as a violated trace. So the prohibition
  watches the same entries in both layers: every entry after the one where it is reached.\<close>

theorem mustnot_violated_breach:
  assumes "(\<pi>, Violated) \<in> mustnot_d s a c"
  shows "pr_verdict s a c \<pi> = Breached (time \<pi> (length \<pi> - 1))"
proof -
  from assms have f: "forbidden s a c \<pi> (length \<pi> - 1)"
    and nf: "\<forall>j < length \<pi> - 1. \<not> forbidden s a c \<pi> j"
    unfolding mustnot_d_def by auto
  have "(LEAST j. forbidden s a c \<pi> j) = length \<pi> - 1"
    by (rule Least_equality) (use f nf in \<open>auto simp: not_le[symmetric]\<close>)
  with f show ?thesis by (auto simp: pr_verdict_def)
qed

theorem breach_mustnot_violated:
  assumes tr: "is_trace \<pi>" and b: "pr_verdict s a c \<pi> = Breached \<tau>"
  shows "\<exists>k < length \<pi>. (pre \<pi> k, Violated) \<in> mustnot_d s a c \<and> time \<pi> k = \<tau>"
proof -
  from b obtain j where j: "forbidden s a c \<pi> j" by (auto simp: pr_verdict_def split: if_splits)
  define k where "k = (LEAST j. forbidden s a c \<pi> j)"
  have fk: "forbidden s a c \<pi> k" unfolding k_def using j by (rule LeastI)
  have kl: "k < length \<pi>" using fk by (rule forbidden_less)
  have before: "\<not> forbidden s a c \<pi> i" if "i < k" for i
    using that not_less_Least[of i "forbidden s a c \<pi>"] unfolding k_def by blast
  have ex: "\<exists>j. forbidden s a c \<pi> j" using j by blast
  have tau: "time \<pi> k = \<tau>" using b ex by (simp add: pr_verdict_def k_def)
  have eq: "pre \<pi> k @ drop (Suc k) \<pi> = \<pi>" by (simp add: pre_def)
  have lp: "length (pre \<pi> k) = Suc k" using kl by (rule length_pre)
  have fp: "forbidden s a c (pre \<pi> k) i \<longleftrightarrow> forbidden s a c \<pi> i" if "i < Suc k" for i
    using forbidden_append[of i "pre \<pi> k" s a c "drop (Suc k) \<pi>"] that lp by (simp only: eq)
  have "is_trace (pre \<pi> k)" using tr by (rule is_trace_pre)
  moreover have "forbidden s a c (pre \<pi> k) (length (pre \<pi> k) - 1)" using fp[of k] fk lp by simp
  moreover have "\<forall>i < length (pre \<pi> k) - 1. \<not> forbidden s a c (pre \<pi> k) i"
    using fp before lp by simp
  ultimately have "(pre \<pi> k, Violated) \<in> mustnot_d s a c" unfolding mustnot_d_def by blast
  with kl tau show ?thesis by blast
qed

text \<open>Enforcement and verdict are separate roles. A monitor enforces a prohibition
  fail-closed: it blocks the action unless \<open>c\<close> is known to be false, so it blocks on an
  undefined \<open>c\<close>. The verdict records a breach only when \<open>c\<close> is true.\<close>

definition blocks :: "('n, 'v :: value_order) expr \<Rightarrow> ('n, 'v) state \<Rightarrow> bool" where
  "blocks c \<sigma> \<longleftrightarrow> eval c \<sigma> \<noteq> Some False"

theorem breach_blocked:
  assumes "pr_verdict s a c \<pi> = Breached \<tau>"
  shows "\<exists>j. 1 \<le> j \<and> j < length \<pi> \<and> does s a (evt (\<pi> ! j)) \<and> blocks c (st \<pi> (j - 1))"
proof -
  from assms obtain j where "forbidden s a c \<pi> j" by (auto simp: pr_verdict_def split: if_splits)
  then show ?thesis unfolding forbidden_def blocks_def by auto
qed

theorem enforced_no_breach:
  assumes "\<And>j. 1 \<le> j \<Longrightarrow> j < length \<pi> \<Longrightarrow> does s a (evt (\<pi> ! j)) \<Longrightarrow> \<not> blocks c (st \<pi> (j - 1))"
  shows "pr_verdict s a c \<pi> = Pending"
proof -
  have "\<not> forbidden s a c \<pi> j" for j
    using assms[of j] unfolding forbidden_def blocks_def by auto
  then show ?thesis by (simp add: pr_verdict_def)
qed

theorem undefined_guard_blocks_not_breach:
  assumes "eval c (st \<pi> (j - 1)) = None"
  shows "blocks c (st \<pi> (j - 1))" and "\<not> forbidden s a c \<pi> j"
  using assms by (simp_all add: blocks_def forbidden_def)


subsection \<open>The monitor as a function on traces\<close>

text \<open>The monitor of \<open>s MUST_NOT a WHEN c\<close> as a function on implementation traces, a
  suppression automaton in the sense of Ligatti, Bauer and Walker: \<open>enforce s a c \<pi>\<close> keeps
  every entry of \<open>\<pi>\<close>, except that an action \<open>a\<close> of \<open>s\<close> taken in a blocking state is replaced
  by a clock tick with the same time and the same state. The entry \<open>j\<close> is a blocked action
  when it is a later entry with the action \<open>a\<close> of \<open>s\<close> and \<open>c\<close> is not known to be false in the
  state of the entry before it. States and times are never changed, so the monitor decides
  the same on \<open>\<pi>\<close> and on its own output.\<close>

definition blocked_action :: "'s \<Rightarrow> 'a \<Rightarrow> ('n, 'v :: value_order) expr \<Rightarrow> ('n, 'v, 's, 'a) itrace \<Rightarrow> nat \<Rightarrow> bool" where
  "blocked_action s a c \<pi> j \<longleftrightarrow>
     1 \<le> j \<and> j < length \<pi> \<and> does s a (evt (\<pi> ! j)) \<and> blocks c (st \<pi> (j - 1))"

definition enforce :: "'s \<Rightarrow> 'a \<Rightarrow> ('n, 'v :: value_order) expr \<Rightarrow> ('n, 'v, 's, 'a) itrace \<Rightarrow> ('n, 'v, 's, 'a) itrace" where
  "enforce s a c \<pi> =
     map (\<lambda>j. if blocked_action s a c \<pi> j then (st \<pi> j, time \<pi> j, Tick) else \<pi> ! j) [0..<length \<pi>]"

lemma enforce_length [simp]: "length (enforce s a c \<pi>) = length \<pi>"
  by (simp add: enforce_def)

lemma enforce_nth:
  "j < length \<pi> \<Longrightarrow>
     enforce s a c \<pi> ! j = (if blocked_action s a c \<pi> j then (st \<pi> j, time \<pi> j, Tick) else \<pi> ! j)"
  by (simp add: enforce_def)

lemma enforce_st [simp]: "j < length \<pi> \<Longrightarrow> st (enforce s a c \<pi>) j = st \<pi> j"
  by (simp add: st_def enforce_nth)

lemma enforce_time [simp]: "j < length \<pi> \<Longrightarrow> time (enforce s a c \<pi>) j = time \<pi> j"
  by (simp add: time_def enforce_nth)

lemma enforce_evt:
  "j < length \<pi> \<Longrightarrow> evt (enforce s a c \<pi> ! j) = (if blocked_action s a c \<pi> j then Tick else evt (\<pi> ! j))"
  by (simp add: enforce_nth)

text \<open>The output of the monitor has no blocked action left: a blocked action became a tick,
  and an action that was let through was taken in the same state, which does not block.\<close>

lemma blocked_action_enforce: "\<not> blocked_action s a c (enforce s a c \<pi>) j"
proof
  assume b: "blocked_action s a c (enforce s a c \<pi>) j"
  then have j: "1 \<le> j" "j < length \<pi>" and d: "does s a (evt (enforce s a c \<pi> ! j))"
    and bl: "blocks c (st (enforce s a c \<pi>) (j - 1))"
    unfolding blocked_action_def by simp_all
  have "j - 1 < length \<pi>" using j by simp
  with bl have bl': "blocks c (st \<pi> (j - 1))" by simp
  show False
  proof (cases "blocked_action s a c \<pi> j")
    case True
    with d j show False by (simp add: enforce_evt does_def)
  next
    case False
    with d j have "does s a (evt (\<pi> ! j))" by (simp add: enforce_evt)
    with j bl' False show False by (simp add: blocked_action_def)
  qed
qed

text \<open>Soundness: the output of the monitor is never breached.\<close>

theorem enforce_sound: "pr_verdict s a c (enforce s a c \<pi>) = Pending"
proof (rule enforced_no_breach)
  fix j assume j: "1 \<le> j" "j < length (enforce s a c \<pi>)" "does s a (evt (enforce s a c \<pi> ! j))"
  show "\<not> blocks c (st (enforce s a c \<pi>) (j - 1))"
  proof
    assume "blocks c (st (enforce s a c \<pi>) (j - 1))"
    with j have "blocked_action s a c (enforce s a c \<pi>) j" unfolding blocked_action_def by simp
    with blocked_action_enforce[of s a c \<pi> j] show False by contradiction
  qed
qed

text \<open>The output of the monitor is a trace: times and states are kept, so the timestamps are
  the same, in the same order.\<close>

lemma enforce_tstamps: "map tstamp (enforce s a c \<pi>) = map tstamp \<pi>"
  by (rule nth_equalityI) (simp_all add: enforce_nth time_def)

theorem enforce_preserves_time_order:
  "sorted (map tstamp (enforce s a c \<pi>)) \<longleftrightarrow> sorted (map tstamp \<pi>)"
  by (simp add: enforce_tstamps)

theorem enforce_is_trace:
  assumes tr: "is_trace \<pi>"
  shows "is_trace (enforce s a c \<pi>)"
proof -
  have ne: "enforce s a c \<pi> \<noteq> []" using tr unfolding enforce_def is_trace_def by simp
  from tr ne show ?thesis by (simp add: is_trace_def enforce_tstamps)
qed

text \<open>The monitor is idempotent, and it changes exactly the blocked actions.\<close>

theorem enforce_idempotent: "enforce s a c (enforce s a c \<pi>) = enforce s a c \<pi>"
proof (rule nth_equalityI)
  show "length (enforce s a c (enforce s a c \<pi>)) = length (enforce s a c \<pi>)" by simp
next
  fix j assume "j < length (enforce s a c (enforce s a c \<pi>))"
  then have j: "j < length \<pi>" by simp
  have "\<not> blocked_action s a c (enforce s a c \<pi>) j" by (rule blocked_action_enforce)
  with j show "enforce s a c (enforce s a c \<pi>) ! j = enforce s a c \<pi> ! j"
    by (simp add: enforce_nth)
qed

theorem enforce_blocks_exactly:
  assumes j: "j < length \<pi>"
  shows "enforce s a c \<pi> ! j \<noteq> \<pi> ! j \<longleftrightarrow> blocked_action s a c \<pi> j"
proof (cases "blocked_action s a c \<pi> j")
  case True
  then have "evt (enforce s a c \<pi> ! j) = Tick" using j by (simp add: enforce_evt)
  moreover have "evt (\<pi> ! j) \<noteq> Tick" using True unfolding blocked_action_def does_def by auto
  ultimately have "enforce s a c \<pi> ! j \<noteq> \<pi> ! j" by force
  with True show ?thesis by simp
next
  case False
  with j show ?thesis by (simp add: enforce_nth)
qed

text \<open>The monitor leaves a trace unchanged exactly when the trace has no blocked action.\<close>

theorem enforce_id_iff: "enforce s a c \<pi> = \<pi> \<longleftrightarrow> (\<forall>j. \<not> blocked_action s a c \<pi> j)"
proof
  assume e: "enforce s a c \<pi> = \<pi>"
  show "\<forall>j. \<not> blocked_action s a c \<pi> j"
  proof
    fix j
    show "\<not> blocked_action s a c \<pi> j"
    proof
      assume b: "blocked_action s a c \<pi> j"
      then have j: "j < length \<pi>" by (simp add: blocked_action_def)
      have "enforce s a c \<pi> ! j \<noteq> \<pi> ! j" using enforce_blocks_exactly[OF j] b by simp
      with e show False by simp
    qed
  qed
next
  assume nb: "\<forall>j. \<not> blocked_action s a c \<pi> j"
  show "enforce s a c \<pi> = \<pi>"
  proof (rule nth_equalityI)
    show "length (enforce s a c \<pi>) = length \<pi>" by simp
  next
    fix j assume "j < length (enforce s a c \<pi>)"
    then have "j < length \<pi>" by simp
    with nb show "enforce s a c \<pi> ! j = \<pi> ! j" by (simp add: enforce_nth)
  qed
qed

text \<open>Transparency. A trace the monitor leaves unchanged is not breached. Conversely, when
  \<open>c\<close> is defined at every entry, a trace that is not breached is left unchanged: on defined
  data the monitor changes a trace exactly when the prohibition is breached. Undefined data
  is where the two sides come apart: an action taken while \<open>c\<close> is undefined is blocked
  although it is not a breach (\<open>undefined_guard_blocks_not_breach\<close>), so there the monitor
  changes a trace whose verdict is pending.\<close>

theorem enforce_unchanged_no_breach:
  assumes "enforce s a c \<pi> = \<pi>"
  shows "pr_verdict s a c \<pi> = Pending"
  using enforce_sound[of s a c \<pi>] by (simp add: assms)

theorem enforce_transparent:
  assumes def: "\<And>j. j < length \<pi> \<Longrightarrow> eval c (st \<pi> j) \<noteq> None"
  shows "enforce s a c \<pi> = \<pi> \<longleftrightarrow> pr_verdict s a c \<pi> = Pending"
proof
  assume "enforce s a c \<pi> = \<pi>"
  then show "pr_verdict s a c \<pi> = Pending" by (rule enforce_unchanged_no_breach)
next
  assume p: "pr_verdict s a c \<pi> = Pending"
  have "\<not> blocked_action s a c \<pi> j" for j
  proof
    assume b: "blocked_action s a c \<pi> j"
    then have j: "1 \<le> j" "j < length \<pi>" and d: "does s a (evt (\<pi> ! j))"
      and bl: "blocks c (st \<pi> (j - 1))"
      unfolding blocked_action_def by simp_all
    have "eval c (st \<pi> (j - 1)) \<noteq> None" using def[of "j - 1"] j by simp
    with bl have "eval c (st \<pi> (j - 1)) = Some True"
      unfolding blocks_def by (cases "eval c (st \<pi> (j - 1))") auto
    with j d have "forbidden s a c \<pi> j" by (simp add: forbidden_def)
    then have "pr_verdict s a c \<pi> \<noteq> Pending" by (auto simp: pr_verdict_def)
    with p show False by simp
  qed
  then show "enforce s a c \<pi> = \<pi>" by (simp add: enforce_id_iff)
qed

theorem enforce_undefined_blocks:
  assumes j: "1 \<le> j" "j < length \<pi>" and d: "does s a (evt (\<pi> ! j))"
    and u: "eval c (st \<pi> (j - 1)) = None"
  shows "evt (enforce s a c \<pi> ! j) = Tick" and "enforce s a c \<pi> \<noteq> \<pi>" and "\<not> forbidden s a c \<pi> j"
proof -
  have b: "blocked_action s a c \<pi> j"
    using j d u unfolding blocked_action_def blocks_def by simp
  then show "evt (enforce s a c \<pi> ! j) = Tick" using j by (simp add: enforce_evt)
  have "enforce s a c \<pi> ! j \<noteq> \<pi> ! j" using enforce_blocks_exactly[OF j(2)] b by simp
  then show "enforce s a c \<pi> \<noteq> \<pi>" by auto
  show "\<not> forbidden s a c \<pi> j" using u by (simp add: forbidden_def)
qed

text \<open>Minimality on defined data. Consider any other way to edit the trace that keeps its
  states and times (an edit may replace or suppress events). If the edited trace is not
  breached, then every action \<open>a\<close> of \<open>s\<close> that it keeps was taken in a state that does not block,
  so the monitor keeps it too: no breach-free edit keeps an action that the monitor blocks.
  This needs \<open>c\<close> defined along the trace; on undefined data the fail-closed monitor blocks
  more than the verdict requires, by design.\<close>

theorem enforce_minimal:
  assumes def: "\<And>j. j < length \<pi> \<Longrightarrow> eval c (st \<pi> j) \<noteq> None"
    and len: "length \<pi>' = length \<pi>" and sts: "\<And>j. j < length \<pi> \<Longrightarrow> st \<pi>' j = st \<pi> j"
    and ok: "pr_verdict s a c \<pi>' = Pending"
    and j: "1 \<le> j" "j < length \<pi>" and d: "does s a (evt (\<pi>' ! j))"
  shows "\<not> blocked_action s a c \<pi> j" and "enforce s a c \<pi> ! j = \<pi> ! j"
proof -
  show nb: "\<not> blocked_action s a c \<pi> j"
  proof
    assume "blocked_action s a c \<pi> j"
    then have bl: "blocks c (st \<pi> (j - 1))" by (simp add: blocked_action_def)
    have "eval c (st \<pi> (j - 1)) \<noteq> None" using def[of "j - 1"] j by simp
    with bl have "eval c (st \<pi> (j - 1)) = Some True"
      unfolding blocks_def by (cases "eval c (st \<pi> (j - 1))") auto
    then have "eval c (st \<pi>' (j - 1)) = Some True" using sts[of "j - 1"] j by simp
    with j d len have "forbidden s a c \<pi>' j" by (simp add: forbidden_def)
    then have "pr_verdict s a c \<pi>' \<noteq> Pending" by (auto simp: pr_verdict_def)
    with ok show False by simp
  qed
  then show "enforce s a c \<pi> ! j = \<pi> ! j" using enforce_blocks_exactly[OF j(2), of s a c] by simp
qed

text \<open>Blocking is antitone: what the monitor allows in a state it allows in every state with
  more data, because a false condition stays false (T2).\<close>

theorem blocks_data_mono:
  assumes "present_free c" and "\<sigma> \<sqsubseteq> \<sigma>'" and "blocks c \<sigma>'"
  shows "blocks c \<sigma>"
proof (rule ccontr)
  assume "\<not> blocks c \<sigma>"
  then have "eval c \<sigma> = Some False" by (simp add: blocks_def)
  from T2_monotone[OF assms(1,2) this] have "eval c \<sigma>' = Some False" .
  with assms(3) show False by (simp add: blocks_def)
qed

text \<open>So, for a condition without PRESENT, the monitor blocks fewer actions on a trace whose
  entries carry more data and the same times and events: an action blocked on the trace
  with more data is blocked on the trace with less.\<close>

theorem blocked_action_data_mono:
  assumes pf: "present_free c" and len: "length \<pi>' = length \<pi>"
    and ev: "\<And>i. i < length \<pi> \<Longrightarrow> evt (\<pi>' ! i) = evt (\<pi> ! i)"
    and le: "\<And>i. i < length \<pi> \<Longrightarrow> st \<pi> i \<sqsubseteq> st \<pi>' i"
    and b: "blocked_action s a c \<pi>' j"
  shows "blocked_action s a c \<pi> j"
proof -
  from b len have j: "1 \<le> j" "j < length \<pi>" and d: "does s a (evt (\<pi>' ! j))"
    and bl: "blocks c (st \<pi>' (j - 1))"
    unfolding blocked_action_def by simp_all
  have "j - 1 < length \<pi>" using j by simp
  from blocks_data_mono[OF pf le[OF this] bl] have "blocks c (st \<pi> (j - 1))" .
  with j d ev[OF j(2)] show ?thesis by (simp add: blocked_action_def)
qed

text \<open>The decisions of the monitor on a trace, as the evaluator reports them: for every
  action \<open>a\<close> of \<open>s\<close> in the trace, its entry and whether the monitor blocks it. The blocked
  entries are exactly the entries \<open>enforce\<close> changes.\<close>

definition monitor_decisions :: "'s \<Rightarrow> 'a \<Rightarrow> ('n, 'v :: value_order) expr \<Rightarrow> ('n, 'v, 's, 'a) itrace
    \<Rightarrow> (nat \<times> bool) list" where
  "monitor_decisions s a c \<pi> =
     map (\<lambda>j. (j, blocks c (st \<pi> (j - 1)))) (filter (\<lambda>j. does s a (evt (\<pi> ! j))) [1..<length \<pi>])"

lemma monitor_decisions_iff:
  "(j, b) \<in> set (monitor_decisions s a c \<pi>) \<longleftrightarrow>
     1 \<le> j \<and> j < length \<pi> \<and> does s a (evt (\<pi> ! j)) \<and> b = blocks c (st \<pi> (j - 1))"
  by (auto simp: monitor_decisions_def image_iff)

theorem monitor_decisions_block:
  "(j, True) \<in> set (monitor_decisions s a c \<pi>) \<longleftrightarrow> blocked_action s a c \<pi> j"
  by (auto simp: monitor_decisions_iff blocked_action_def)

theorem monitor_decisions_allow:
  "(j, False) \<in> set (monitor_decisions s a c \<pi>) \<longleftrightarrow>
     1 \<le> j \<and> j < length \<pi> \<and> does s a (evt (\<pi> ! j)) \<and> \<not> blocked_action s a c \<pi> j"
  by (auto simp: monitor_decisions_iff blocked_action_def)

theorem monitor_decisions_enforce:
  assumes "j < length \<pi>"
  shows "(j, True) \<in> set (monitor_decisions s a c \<pi>) \<longleftrightarrow> enforce s a c \<pi> ! j \<noteq> \<pi> ! j"
  by (simp add: monitor_decisions_block enforce_blocks_exactly[OF assms])

text \<open>A decision is final: the decisions on a longer trace begin with those on the shorter
  one, since the decision at an entry reads the state of the entry before it.\<close>

lemma monitor_decisions_append:
  "\<exists>ds. monitor_decisions s a c (\<pi> @ \<rho>) = monitor_decisions s a c \<pi> @ ds"
proof (cases "\<pi> = []")
  case True
  then show ?thesis by (simp add: monitor_decisions_def)
next
  case False
  then have l1: "1 \<le> length \<pi>" by (cases \<pi>) simp_all
  have u: "[1..<length (\<pi> @ \<rho>)] = [1..<length \<pi>] @ [length \<pi>..<length \<pi> + length \<rho>]"
    unfolding length_append by (rule upt_add_eq_append[OF l1])
  have f: "filter (\<lambda>j. does s a (evt ((\<pi> @ \<rho>) ! j))) [1..<length \<pi>]
           = filter (\<lambda>j. does s a (evt (\<pi> ! j))) [1..<length \<pi>]"
    by (rule filter_cong) simp_all
  have m: "map (\<lambda>j. (j, blocks c (st (\<pi> @ \<rho>) (j - 1)))) (filter (\<lambda>j. does s a (evt (\<pi> ! j))) [1..<length \<pi>])
           = map (\<lambda>j. (j, blocks c (st \<pi> (j - 1)))) (filter (\<lambda>j. does s a (evt (\<pi> ! j))) [1..<length \<pi>])"
    by (rule map_cong) (auto simp: less_imp_diff_less)
  show ?thesis
    unfolding monitor_decisions_def u filter_append map_append f m by blast
qed

text \<open>\<open>s MAY a WHEN c\<close> is fulfilled when exercised in a state where \<open>c\<close> holds, and is
  never breached.\<close>

definition may_verdict :: "'s \<Rightarrow> 'a \<Rightarrow> ('n, 'v :: value_order) expr \<Rightarrow> ('n, 'v, 's, 'a) itrace \<Rightarrow> verdict" where
  "may_verdict s a c \<pi> =
     (if \<exists>j. 1 \<le> j \<and> j < length \<pi> \<and> does s a (evt (\<pi> ! j)) \<and> eval c (st \<pi> (j - 1)) = Some True
      then Fulfilled else Pending)"

theorem may_never_breached: "may_verdict s a c \<pi> \<noteq> Breached \<tau>"
  by (simp add: may_verdict_def)


section \<open>Breach actions\<close>

text \<open>Informational actions (NOTIFY, PENALTY) fire at the moment of breach and do not
  affect the continuation. Continuation-determining actions (TERMINATE, CURE_BY,
  ESCALATE_TO) are mutually exclusive: a handler may contain at most one of them.\<close>

datatype ('s, 'p) baction =
    Notify 's
  | Penalty 'p          \<comment> \<open>the amount expression, kept abstract\<close>
  | Terminate
  | CureBy int          \<comment> \<open>a duration, counted from the moment of breach\<close>
  | EscalateTo 's

fun is_cont :: "('s, 'p) baction \<Rightarrow> bool" where
  "is_cont Terminate = True"
| "is_cont (CureBy k) = True"
| "is_cont (EscalateTo s) = True"
| "is_cont (Notify s) = False"
| "is_cont (Penalty p) = False"

definition wf_actions :: "('s, 'p) baction list \<Rightarrow> bool" where
  "wf_actions acts \<longleftrightarrow> acts \<noteq> [] \<and> length (filter is_cont acts) \<le> 1"

definition cont_of :: "('s, 'p) baction list \<Rightarrow> ('s, 'p) baction option" where
  "cont_of acts = (case filter is_cont acts of [] \<Rightarrow> None | c # cs \<Rightarrow> Some c)"

lemma length_le_1_same: "length xs \<le> 1 \<Longrightarrow> x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> x = y"
  by (cases xs) auto

theorem cont_unique:
  assumes "wf_actions acts" and "c \<in> set acts" "is_cont c" and "c' \<in> set acts" "is_cont c'"
  shows "c = c'"
  using assms length_le_1_same[of "filter is_cont acts" c c'] by (auto simp: wf_actions_def)

theorem cont_of_some: "cont_of acts = Some c \<Longrightarrow> c \<in> set acts \<and> is_cont c"
proof -
  assume "cont_of acts = Some c"
  then obtain cs where "filter is_cont acts = c # cs"
    by (auto simp: cont_of_def split: list.splits)
  then have "c \<in> set (filter is_cont acts)" by simp
  then show ?thesis by simp
qed

theorem two_continuations_rejected:
  "is_cont c \<Longrightarrow> is_cont c' \<Longrightarrow> \<not> wf_actions (xs @ c # ys @ c' # zs)"
  by (simp add: wf_actions_def)

text \<open>The list given in section 2.6 as an example of a semantic error.\<close>

corollary section_2_6_example_rejected: "\<not> wf_actions [Penalty x, Notify y, Terminate, CureBy k]"
  by (simp add: wf_actions_def)


section \<open>Handling a breach\<close>

text \<open>The status of an obligation with deadline \<open>d\<close> and handler actions \<open>acts\<close>.
  \<^item> No continuation-determining action, or TERMINATE: the obligation stays breached and is
    closed (TERMINATE closes the obligation, not the whole specification).
  \<^item> \<open>CURE_BY k\<close>: a new window \<open>(\<tau>\<^sub>b, \<tau>\<^sub>b + k]\<close> from the moment of breach \<open>\<tau>\<^sub>b\<close>, in which the
    original obligation can still be met. If it is not, the second breach is final: no
    handler applies to it.
  \<^item> \<open>ESCALATE_TO s'\<close>: the original obligation stays breached, and \<open>s'\<close> gets a new obligation
    for the same action with the same length of window, counted from the moment of
    transfer.
  \<open>\<tau>\<^sub>0\<close> is the start of the obligation and \<open>lo\<close> the lower bound of its window: the
  activation time and \<open>None\<close>, or the start \<open>f\<close> and \<open>f - 1\<close> for an obligation with
  \<open>FROM f\<close>.\<close>

datatype 's continuation = NoContinuation | Terminated | Cure verdict | Escalated 's verdict

datatype 's status = SFulfilled | SPending | SBreached int "'s continuation"

fun continue_after :: "int \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> int \<Rightarrow> int \<Rightarrow> ('s, 'p) baction option
    \<Rightarrow> ('n, 'v, 's, 'a) itrace \<Rightarrow> 's continuation" where
  "continue_after \<tau>\<^sub>0 s a d \<tau>\<^sub>b (Some Terminate) \<pi> = Terminated"
| "continue_after \<tau>\<^sub>0 s a d \<tau>\<^sub>b (Some (CureBy k)) \<pi> = Cure (window s a (Some \<tau>\<^sub>b) (\<tau>\<^sub>b + k) \<pi>)"
| "continue_after \<tau>\<^sub>0 s a d \<tau>\<^sub>b (Some (EscalateTo s')) \<pi> =
     Escalated s' (window s' a (Some \<tau>\<^sub>b) (\<tau>\<^sub>b + (d - \<tau>\<^sub>0)) \<pi>)"
| "continue_after \<tau>\<^sub>0 s a d \<tau>\<^sub>b _ \<pi> = NoContinuation"

definition handle_breach :: "int \<Rightarrow> int option \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> int \<Rightarrow> ('s, 'p) baction list
    \<Rightarrow> ('n, 'v, 's, 'a) itrace \<Rightarrow> 's status" where
  "handle_breach \<tau>\<^sub>0 lo s a d acts \<pi> =
     (case window s a lo d \<pi> of
        Fulfilled \<Rightarrow> SFulfilled
      | Pending \<Rightarrow> SPending
      | Breached \<tau>\<^sub>b \<Rightarrow> SBreached \<tau>\<^sub>b (continue_after \<tau>\<^sub>0 s a d \<tau>\<^sub>b (cont_of acts) \<pi>))"

lemma cont_of_filter: "cont_of (filter is_cont acts) = cont_of acts"
  by (simp add: cont_of_def)

theorem informational_irrelevant:
  "handle_breach \<tau>\<^sub>0 lo s a d acts \<pi> = handle_breach \<tau>\<^sub>0 lo s a d (filter is_cont acts) \<pi>"
  by (simp add: handle_breach_def cont_of_filter split: verdict.split)

theorem cure_restores:
  assumes "window s a lo d \<pi> = Breached d" and "cont_of acts = Some (CureBy k)"
    and "acted s a (Some d) (d + k) \<pi>"
  shows "handle_breach \<tau>\<^sub>0 lo s a d acts \<pi> = SBreached d (Cure Fulfilled)"
  using assms by (simp add: handle_breach_def window_def)

theorem cure_failed:
  assumes "window s a lo d \<pi> = Breached d" and "cont_of acts = Some (CureBy k)"
    and "\<not> acted s a (Some d) (d + k) \<pi>" and "passed (d + k) \<pi>"
  shows "handle_breach \<tau>\<^sub>0 lo s a d acts \<pi> = SBreached d (Cure (Breached (d + k)))"
  using assms by (simp add: handle_breach_def window_def)

theorem escalation_keeps_breach:
  assumes "window s a lo d \<pi> = Breached d" and "cont_of acts = Some (EscalateTo s')"
  shows "handle_breach \<tau>\<^sub>0 lo s a d acts \<pi> =
           SBreached d (Escalated s' (window s' a (Some d) (d + (d - \<tau>\<^sub>0)) \<pi>))"
  using assms by (simp add: handle_breach_def)

text \<open>The status is final once the obligation and the window of its continuation are
  decided.\<close>

theorem handle_breach_final:
  assumes tr: "is_trace (\<pi> @ \<rho>)"
    and base: "window s a lo d \<pi> \<noteq> Pending"
    and cure: "\<And>k. cont_of acts = Some (CureBy k) \<Longrightarrow> window s a (Some d) (d + k) \<pi> \<noteq> Pending"
    and esc: "\<And>s'. cont_of acts = Some (EscalateTo s') \<Longrightarrow>
                window s' a (Some d) (d + (d - \<tau>\<^sub>0)) \<pi> \<noteq> Pending"
  shows "handle_breach \<tau>\<^sub>0 lo s a d acts (\<pi> @ \<rho>) = handle_breach \<tau>\<^sub>0 lo s a d acts \<pi>"
proof -
  have w: "window s a lo d (\<pi> @ \<rho>) = window s a lo d \<pi>"
    using tr base by (rule window_final)
  show ?thesis
  proof (cases "window s a lo d \<pi>")
    case (Breached \<tau>\<^sub>b)
    then have tb: "\<tau>\<^sub>b = d" by (rule window_breached_at)
    have "continue_after \<tau>\<^sub>0 s a d d (cont_of acts) (\<pi> @ \<rho>) = continue_after \<tau>\<^sub>0 s a d d (cont_of acts) \<pi>"
    proof (cases "cont_of acts")
      case (Some c)
      then show ?thesis
      proof (cases c)
        case (CureBy k)
        with Some cure[of k] tr show ?thesis by (simp add: window_final)
      next
        case (EscalateTo s')
        with Some esc[of s'] tr show ?thesis by (simp add: window_final)
      qed simp_all
    qed simp
    with Breached w tb show ?thesis by (simp add: handle_breach_def)
  qed (use base in \<open>simp_all add: handle_breach_def w\<close>)
qed


section \<open>Terms of a TERMS block and the binding of ON_BREACH\<close>

text \<open>The surface terms of a TERMS block. A breach handler \<open>s ON_BREACH acts\<close> is allowed
  only at the top level of the block, and it is bound to the nearest preceding obligation
  or prohibition of the same subject at the top level. \<open>SMust s a D F\<close> is an obligation
  with the deadline \<open>D\<close> and the start \<open>F\<close> given by FROM. \<open>SIf c t u\<close> is a conditional
  term (IF/ELIF/ELSE and WHEN; a missing ELSE is \<open>SSkip\<close>), and \<open>SRef k\<close> is a reference
  \<open>REF name\<close> to the named term declared as the element \<open>k\<close> of the block, counted from 0.
  \<open>SMustElse s a d s' a' D'\<close> is \<open>s MUST a WITHIN d ELSE s' MUST a' BY D'\<close>, an obligation
  with a fallback (see the section on fallbacks below).\<close>

datatype ('n, 'v, 's, 'a, 'p) sterm =
    SMust 's 'a "'n deadline option" "'n deadline option"
  | SMustNot 's 'a "('n, 'v) expr"
  | SMay 's 'a "('n, 'v) expr"
  | SThen "('n, 'v, 's, 'a, 'p) sterm" "('n, 'v, 's, 'a, 'p) sterm"
  | SOr "('n, 'v, 's, 'a, 'p) sterm" "('n, 'v, 's, 'a, 'p) sterm"
  | SAnd "('n, 'v, 's, 'a, 'p) sterm" "('n, 'v, 's, 'a, 'p) sterm"
  | SUnless "('n, 'v, 's, 'a, 'p) sterm" "('n, 'v) expr" "('n, 'v, 's, 'a, 'p) sterm"
  | SOnBreach 's "('s, 'p) baction list"
  | SIf "('n, 'v) expr" "('n, 'v, 's, 'a, 'p) sterm" "('n, 'v, 's, 'a, 'p) sterm"
  | SSkip
  | SRef nat
  | SMustElse 's 'a "'n deadline" 's 'a "'n deadline option"

fun has_handler :: "('n, 'v, 's, 'a, 'p) sterm \<Rightarrow> bool" where
  "has_handler (SOnBreach s acts) = True"
| "has_handler (SThen t u) = (has_handler t \<or> has_handler u)"
| "has_handler (SOr t u) = (has_handler t \<or> has_handler u)"
| "has_handler (SAnd t u) = (has_handler t \<or> has_handler u)"
| "has_handler (SUnless t c u) = (has_handler t \<or> has_handler u)"
| "has_handler (SIf c t u) = (has_handler t \<or> has_handler u)"
| "has_handler _ = False"

fun binds :: "'s \<Rightarrow> ('n, 'v, 's, 'a, 'p) sterm \<Rightarrow> bool" where
  "binds s (SMust s' a d f) = (s' = s)"
| "binds s (SMustElse s' a d s'' a' d') = (s' = s)"
| "binds s (SMustNot s' a c) = (s' = s)"
| "binds s _ = False"

definition bound_to :: "('n, 'v, 's, 'a, 'p) sterm list \<Rightarrow> nat \<Rightarrow> 's \<Rightarrow> nat option" where
  "bound_to blk i s =
     (if \<exists>j < i. binds s (blk ! j) then Some (GREATEST j. j < i \<and> binds s (blk ! j)) else None)"

theorem bound_to_nearest:
  assumes "bound_to blk i s = Some j"
  shows "j < i" and "binds s (blk ! j)" and "\<And>k. j < k \<Longrightarrow> k < i \<Longrightarrow> \<not> binds s (blk ! k)"
proof -
  from assms obtain j\<^sub>0 where j0: "j\<^sub>0 < i" "binds s (blk ! j\<^sub>0)"
    and j: "j = (GREATEST j. j < i \<and> binds s (blk ! j))"
    unfolding bound_to_def by (auto split: if_splits)
  have bnd: "\<And>y. y < i \<and> binds s (blk ! y) \<Longrightarrow> y \<le> i" by simp
  have "j < i \<and> binds s (blk ! j)"
    unfolding j
    by (rule GreatestI_nat[where P = "\<lambda>j. j < i \<and> binds s (blk ! j)" and k = j\<^sub>0 and b = i])
       (use j0 in auto)
  then show "j < i" and "binds s (blk ! j)" by auto
  fix k assume k: "j < k" "k < i"
  show "\<not> binds s (blk ! k)"
  proof
    assume bk: "binds s (blk ! k)"
    have "k \<le> j"
      unfolding j
      by (rule Greatest_le_nat[where P = "\<lambda>j. j < i \<and> binds s (blk ! j)" and k = k and b = i])
         (use k(2) bk in auto)
    with k(1) show False by simp
  qed
qed

theorem bound_to_None: "bound_to blk i s = None \<longleftrightarrow> (\<forall>j < i. \<not> binds s (blk ! j))"
  by (auto simp: bound_to_def)

text \<open>A well-formed block: handlers only at the top level, each handler well formed and
  bound, and at most one handler per obligation or prohibition.\<close>

definition wf_block :: "('n, 'v, 's, 'a, 'p) sterm list \<Rightarrow> bool" where
  "wf_block blk \<longleftrightarrow>
     (\<forall>i < length blk. case blk ! i of
        SOnBreach s acts \<Rightarrow> wf_actions acts \<and> bound_to blk i s \<noteq> None
      | _ \<Rightarrow> \<not> has_handler (blk ! i))
     \<and> (\<forall>i k s s' acts acts'. i < length blk \<longrightarrow> k < length blk \<longrightarrow>
          blk ! i = SOnBreach s acts \<longrightarrow> blk ! k = SOnBreach s' acts' \<longrightarrow>
          bound_to blk i s = bound_to blk k s' \<longrightarrow> i = k)"

theorem nested_handler_rejected:
  assumes "i < length blk" and "has_handler (blk ! i)" and "\<And>s acts. blk ! i \<noteq> SOnBreach s acts"
  shows "\<not> wf_block blk"
proof
  assume "wf_block blk"
  with assms(1) have "case blk ! i of SOnBreach s acts \<Rightarrow> wf_actions acts \<and> bound_to blk i s \<noteq> None
      | _ \<Rightarrow> \<not> has_handler (blk ! i)"
    unfolding wf_block_def by blast
  with assms(2,3) show False by (cases "blk ! i") auto
qed

theorem wf_handler_bound:
  assumes "wf_block blk" and "i < length blk" and "blk ! i = SOnBreach s acts"
  shows "wf_actions acts" and "\<exists>j. bound_to blk i s = Some j \<and> j < i \<and> binds s (blk ! j)"
proof -
  from assms(1,2) have "case blk ! i of SOnBreach s acts \<Rightarrow> wf_actions acts \<and> bound_to blk i s \<noteq> None
      | _ \<Rightarrow> \<not> has_handler (blk ! i)"
    unfolding wf_block_def by blast
  with assms(3) have *: "wf_actions acts \<and> bound_to blk i s \<noteq> None" by simp
  then show "wf_actions acts" by simp
  from * obtain j where "bound_to blk i s = Some j" by auto
  with bound_to_nearest[OF this] show "\<exists>j. bound_to blk i s = Some j \<and> j < i \<and> binds s (blk ! j)"
    by blast
qed

theorem wf_one_handler:
  assumes "wf_block blk" and "i < length blk" and "k < length blk"
    and "blk ! i = SOnBreach s acts" and "blk ! k = SOnBreach s' acts'"
    and "bound_to blk i s = Some j" and "bound_to blk k s' = Some j"
  shows "i = k"
proof -
  from assms(1) have "\<forall>i k s s' acts acts'. i < length blk \<longrightarrow> k < length blk \<longrightarrow>
      blk ! i = SOnBreach s acts \<longrightarrow> blk ! k = SOnBreach s' acts' \<longrightarrow>
      bound_to blk i s = bound_to blk k s' \<longrightarrow> i = k"
    unfolding wf_block_def by blast
  then have "bound_to blk i s = bound_to blk k s' \<Longrightarrow> i = k" using assms(2-5) by blast
  with assms(6,7) show ?thesis by simp
qed


section \<open>Activation\<close>

fun deadlines :: "('n, 'v, 's, 'a, 'p) sterm \<Rightarrow> 'n deadline list" where
  "deadlines (SMust s a D F) = (case D of Some d \<Rightarrow> [d] | None \<Rightarrow> []) @ (case F of Some f \<Rightarrow> [f] | None \<Rightarrow> [])"
| "deadlines (SThen t u) = deadlines t @ deadlines u"
| "deadlines (SOr t u) = deadlines t @ deadlines u"
| "deadlines (SAnd t u) = deadlines t @ deadlines u"
| "deadlines (SUnless t c u) = deadlines t @ deadlines u"
| "deadlines (SIf c t u) = deadlines t @ deadlines u"
| "deadlines (SMustElse s a d s' a' D') = d # (case D' of Some d' \<Rightarrow> [d'] | None \<Rightarrow> [])"
| "deadlines _ = []"

text \<open>A block is activated at time \<open>\<tau>\<^sub>0\<close> in state \<open>\<sigma>\<^sub>0\<close> only if every deadline and every
  start (FROM) in it resolves. Whether a deadline resolves does not depend on the time a
  duration counts from.\<close>

definition activates :: "('v \<Rightarrow> int option) \<Rightarrow> int \<Rightarrow> ('n, 'v) state
    \<Rightarrow> ('n, 'v, 's, 'a, 'p) sterm list \<Rightarrow> bool" where
  "activates T \<tau>\<^sub>0 \<sigma>\<^sub>0 blk \<longleftrightarrow> (\<forall>t \<in> set blk. \<forall>d \<in> set (deadlines t). resolve T \<tau>\<^sub>0 \<sigma>\<^sub>0 d \<noteq> None)"

theorem activation_rejected:
  assumes "SMust s a (Some (DFactor x k)) F \<in> set blk" and "\<sigma>\<^sub>0 x = None"
  shows "\<not> activates T \<tau>\<^sub>0 \<sigma>\<^sub>0 blk"
  using assms unfolding activates_def by force

theorem activation_rejected_from:
  assumes "SMust s a D (Some (DFactor x k)) \<in> set blk" and "\<sigma>\<^sub>0 x = None"
  shows "\<not> activates T \<tau>\<^sub>0 \<sigma>\<^sub>0 blk"
  using assms unfolding activates_def by (cases D) force+

lemma resolve_base: "resolve T b \<sigma>\<^sub>0 d = None \<longleftrightarrow> resolve T b' \<sigma>\<^sub>0 d = None"
  by (cases d) (auto split: option.splits)

lemma deadlines_SMust: "set (deadlines (SMust s a D F)) = set_option D \<union> set_option F"
  by (cases D; cases F) auto

text \<open>After activation, the start and the deadline of every top-level obligation resolve.\<close>

theorem activates_resolves:
  assumes "activates T \<tau>\<^sub>0 \<sigma>\<^sub>0 blk" and "SMust s a D F \<in> set blk"
  shows "\<exists>b. start_of T \<tau>\<^sub>0 \<sigma>\<^sub>0 F = Some b \<and> (D \<noteq> None \<longrightarrow> deadline_of T \<tau>\<^sub>0 \<sigma>\<^sub>0 F D \<noteq> None)"
proof -
  note all = bspec[OF assms(1)[unfolded activates_def] assms(2), unfolded deadlines_SMust]
  obtain b where b: "start_of T \<tau>\<^sub>0 \<sigma>\<^sub>0 F = Some b"
  proof (cases F)
    case None
    then show ?thesis using that by (simp add: start_of_def)
  next
    case (Some f)
    with all have "resolve T \<tau>\<^sub>0 \<sigma>\<^sub>0 f \<noteq> None" by simp
    then obtain b where "resolve T \<tau>\<^sub>0 \<sigma>\<^sub>0 f = Some b" by blast
    with Some show ?thesis using that by (simp add: start_of_def)
  qed
  moreover have "D \<noteq> None \<longrightarrow> deadline_of T \<tau>\<^sub>0 \<sigma>\<^sub>0 F D \<noteq> None"
  proof
    assume "D \<noteq> None"
    then obtain d where d: "D = Some d" by auto
    with all have "resolve T \<tau>\<^sub>0 \<sigma>\<^sub>0 d \<noteq> None" by simp
    then have "resolve T b \<sigma>\<^sub>0 d \<noteq> None" using resolve_base[of T b \<sigma>\<^sub>0 d \<tau>\<^sub>0] by simp
    with b d show "deadline_of T \<tau>\<^sub>0 \<sigma>\<^sub>0 F D \<noteq> None" by (simp add: deadline_of_def)
  qed
  ultimately show ?thesis by blast
qed


section \<open>Fallbacks: WITHIN ... ELSE\<close>

text \<open>\<open>s MUST a WITHIN d ELSE s' MUST a' BY d'\<close> at the top level of a TERMS block. An action
  of \<open>s\<close> in \<open>(-\<infinity>, d]\<close> fulfils it. If the trace passes \<open>d\<close> without one, it is not
  breached: the fallback \<open>s' MUST a'\<close> is in force from \<open>d\<close>, with the window \<open>(d, d']\<close>, and
  only the fallback can be breached. A duration in \<open>d'\<close> counts from \<open>d\<close>; a DATETIME or a
  factor is resolved at activation, like every deadline.\<close>

datatype else_status = EFulfilled | EPending | EElse int verdict

definition else_deadline :: "('v \<Rightarrow> int option) \<Rightarrow> ('n, 'v) state \<Rightarrow> int \<Rightarrow> 'n deadline option \<Rightarrow> int option" where
  "else_deadline T \<sigma>\<^sub>0 d D' = Option.bind D' (resolve T d \<sigma>\<^sub>0)"

definition else_verdict :: "'s \<Rightarrow> 'a \<Rightarrow> int \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> int option \<Rightarrow> ('n, 'v, 's, 'a) itrace \<Rightarrow> else_status" where
  "else_verdict s a d s' a' D' \<pi> =
     (if acted s a None d \<pi> then EFulfilled
      else if passed d \<pi> then EElse d (ob_verdict s' a' (Some d) D' \<pi>)
      else EPending)"

theorem else_fulfilled: "acted s a None d \<pi> \<Longrightarrow> else_verdict s a d s' a' D' \<pi> = EFulfilled"
  by (simp add: else_verdict_def)

theorem else_pending: "\<not> acted s a None d \<pi> \<Longrightarrow> \<not> passed d \<pi> \<Longrightarrow> else_verdict s a d s' a' D' \<pi> = EPending"
  by (simp add: else_verdict_def)

text \<open>A missed deadline puts the fallback in force at \<open>d\<close>, instead of a breach.\<close>

theorem else_taken:
  "\<not> acted s a None d \<pi> \<Longrightarrow> passed d \<pi> \<Longrightarrow>
     else_verdict s a d s' a' D' \<pi> = EElse d (ob_verdict s' a' (Some d) D' \<pi>)"
  by (simp add: else_verdict_def)

theorem else_no_breach:
  "window s a None d \<pi> = Breached d \<Longrightarrow> else_verdict s a d s' a' D' \<pi> = EElse d (ob_verdict s' a' (Some d) D' \<pi>)"
  unfolding window_def else_verdict_def by (auto split: if_splits)

text \<open>An action at or before \<open>d\<close> does not fulfil the fallback: only an action of \<open>s'\<close>
  strictly after \<open>d\<close> does.\<close>

theorem else_alt_after:
  assumes "else_verdict s a d s' a' D' \<pi> = EElse d Fulfilled"
  shows "\<exists>j. 1 \<le> j \<and> j < length \<pi> \<and> does s' a' (evt (\<pi> ! j)) \<and> d < time \<pi> j"
proof -
  from assms have "ob_verdict s' a' (Some d) D' \<pi> = Fulfilled"
    unfolding else_verdict_def by (auto split: if_splits)
  then show ?thesis
    unfolding ob_verdict_def window_def acted_def by (auto split: option.splits if_splits)
qed

text \<open>The fallback with deadline \<open>d'\<close>, missed, is a breach at \<open>d'\<close>.\<close>

theorem else_alt_breached:
  assumes "\<not> acted s a None d \<pi>" "passed d \<pi>" "\<not> acted s' a' (Some d) d' \<pi>" "passed d' \<pi>"
  shows "else_verdict s a d s' a' (Some d') \<pi> = EElse d (Breached d')"
  using assms by (simp add: else_verdict_def ob_verdict_def window_def)

text \<open>A duration in the deadline of the fallback counts from \<open>d\<close>.\<close>

theorem else_alt_duration: "else_deadline T \<sigma>\<^sub>0 d (Some (DAfter k)) = Some (d + k)"
  by (simp add: else_deadline_def)

lemma ob_verdict_None_final:
  assumes "ob_verdict s a lo None \<pi> \<noteq> Pending"
  shows "ob_verdict s a lo None (\<pi> @ \<rho>) = ob_verdict s a lo None \<pi>"
proof -
  from assms have "\<exists>j. 1 \<le> j \<and> j < length \<pi> \<and> does s a (evt (\<pi> ! j)) \<and> after lo (time \<pi> j)"
    unfolding ob_verdict_def by (auto split: if_splits)
  then have "\<exists>j. 1 \<le> j \<and> j < length (\<pi> @ \<rho>) \<and> does s a (evt ((\<pi> @ \<rho>) ! j)) \<and> after lo (time (\<pi> @ \<rho>) j)"
    by (metis length_append itrace_nth_append time_append trans_less_add1)
  with assms show ?thesis unfolding ob_verdict_def by (auto split: if_splits)
qed

text \<open>Finality: once the fallback is in force and its verdict is reached, or the obligation
  is fulfilled, later entries change nothing (non-decreasing timestamps).\<close>

theorem else_final:
  assumes tr: "is_trace (\<pi> @ \<rho>)"
    and dec: "else_verdict s a d s' a' D' \<pi> \<noteq> EPending"
    and alt: "\<And>v. else_verdict s a d s' a' D' \<pi> = EElse d v \<Longrightarrow> v \<noteq> Pending"
  shows "else_verdict s a d s' a' D' (\<pi> @ \<rho>) = else_verdict s a d s' a' D' \<pi>"
proof (cases "acted s a None d \<pi>")
  case True
  then show ?thesis by (simp add: else_verdict_def acted_append)
next
  case False
  with dec have p: "passed d \<pi>" by (auto simp: else_verdict_def split: if_splits)
  with False have w: "window s a None d \<pi> = Breached d" by (simp add: window_def)
  have "window s a None d (\<pi> @ \<rho>) = Breached d"
    using window_final[OF tr] w by simp
  then have na: "\<not> acted s a None d (\<pi> @ \<rho>)" and p': "passed d (\<pi> @ \<rho>)"
    by (auto simp: window_def split: if_splits)
  have v: "ob_verdict s' a' (Some d) D' \<pi> \<noteq> Pending"
    using alt[of "ob_verdict s' a' (Some d) D' \<pi>"] False p by (simp add: else_verdict_def)
  have "ob_verdict s' a' (Some d) D' (\<pi> @ \<rho>) = ob_verdict s' a' (Some d) D' \<pi>"
  proof (cases D')
    case None
    from v None have "ob_verdict s' a' (Some d) None \<pi> \<noteq> Pending" by simp
    from ob_verdict_None_final[OF this] None show ?thesis by simp
  next
    case (Some d')
    from v Some have "ob_verdict s' a' (Some d) (Some d') \<pi> \<noteq> Pending" by simp
    from ob_verdict_final[OF tr this] Some show ?thesis by simp
  qed
  with False p na p' show ?thesis by (simp add: else_verdict_def)
qed

text \<open>Both deadlines are resolved at activation.\<close>

theorem activation_rejected_else:
  assumes "SMustElse s a d s' a' (Some (DFactor x k)) \<in> set blk \<or> SMustElse s a (DFactor x k) s' a' D' \<in> set blk"
    and "\<sigma>\<^sub>0 x = None"
  shows "\<not> activates T \<tau>\<^sub>0 \<sigma>\<^sub>0 blk"
  using assms unfolding activates_def by (cases D') force+

theorem activates_resolves_else:
  assumes "activates T \<tau>\<^sub>0 \<sigma>\<^sub>0 blk" and "SMustElse s a d s' a' D' \<in> set blk"
  shows "\<exists>e. resolve T \<tau>\<^sub>0 \<sigma>\<^sub>0 d = Some e \<and> (D' \<noteq> None \<longrightarrow> else_deadline T \<sigma>\<^sub>0 e D' \<noteq> None)"
proof -
  note all = bspec[OF assms(1)[unfolded activates_def] assms(2)]
  from all obtain e where e: "resolve T \<tau>\<^sub>0 \<sigma>\<^sub>0 d = Some e" by auto
  moreover have "D' \<noteq> None \<longrightarrow> else_deadline T \<sigma>\<^sub>0 e D' \<noteq> None"
  proof
    assume "D' \<noteq> None"
    then obtain d' where d': "D' = Some d'" by auto
    with all have "resolve T \<tau>\<^sub>0 \<sigma>\<^sub>0 d' \<noteq> None" by simp
    then have "resolve T e \<sigma>\<^sub>0 d' \<noteq> None" using resolve_base[of T e \<sigma>\<^sub>0 d' \<tau>\<^sub>0] by simp
    with d' show "else_deadline T \<sigma>\<^sub>0 e D' \<noteq> None" by (simp add: else_deadline_def)
  qed
  ultimately show ?thesis by blast
qed

text \<open>A fallback must end strictly after the first deadline (decision 27 of CORE.md): if its
  deadline resolves at or before the first one, the window \<open>(d, d']\<close> is empty and the
  fallback could never be fulfilled. Such a block is rejected at activation.\<close>

definition else_order_ok :: "('v \<Rightarrow> int option) \<Rightarrow> int \<Rightarrow> ('n, 'v) state
    \<Rightarrow> ('n, 'v, 's, 'a, 'p) sterm list \<Rightarrow> bool" where
  "else_order_ok T \<tau>\<^sub>0 \<sigma>\<^sub>0 blk \<longleftrightarrow>
     (\<forall>t \<in> set blk. case t of
        SMustElse s a d s' a' D' \<Rightarrow>
          (case resolve T \<tau>\<^sub>0 \<sigma>\<^sub>0 d of
             None \<Rightarrow> True
           | Some e \<Rightarrow> (case else_deadline T \<sigma>\<^sub>0 e D' of None \<Rightarrow> True | Some e' \<Rightarrow> e < e'))
      | _ \<Rightarrow> True)"

theorem else_order_rejected:
  assumes "SMustElse s a d s' a' D' \<in> set blk" and "resolve T \<tau>\<^sub>0 \<sigma>\<^sub>0 d = Some e"
    and "else_deadline T \<sigma>\<^sub>0 e D' = Some e'" and "e' \<le> e"
  shows "\<not> else_order_ok T \<tau>\<^sub>0 \<sigma>\<^sub>0 blk"
  using assms unfolding else_order_ok_def by force

theorem else_order_window:
  assumes "else_order_ok T \<tau>\<^sub>0 \<sigma>\<^sub>0 blk" and "SMustElse s a d s' a' D' \<in> set blk"
    and "resolve T \<tau>\<^sub>0 \<sigma>\<^sub>0 d = Some e" and "else_deadline T \<sigma>\<^sub>0 e D' = Some e'"
  shows "e < e'"
  using assms unfolding else_order_ok_def by force

text \<open>A fallback with a positive duration always ends after the first deadline, since the
  duration counts from it.\<close>

lemma else_order_duration:
  "0 < k \<Longrightarrow> else_deadline T \<sigma>\<^sub>0 e (Some (DAfter k)) = Some e' \<Longrightarrow> e < e'"
  by (auto simp: else_deadline_def)

text \<open>A handler bound to an obligation with a fallback would never fire: a fallback is what
  happens instead of a breach. Such a handler is rejected.\<close>

fun is_else :: "('n, 'v, 's, 'a, 'p) sterm \<Rightarrow> bool" where
  "is_else (SMustElse s a d s' a' D') = True"
| "is_else _ = False"

definition else_handlers_ok :: "('n, 'v, 's, 'a, 'p) sterm list \<Rightarrow> bool" where
  "else_handlers_ok blk \<longleftrightarrow>
     (\<forall>k < length blk. case blk ! k of
        SOnBreach s acts \<Rightarrow> (case bound_to blk k s of Some j \<Rightarrow> \<not> is_else (blk ! j) | None \<Rightarrow> True)
      | _ \<Rightarrow> True)"

theorem else_handler_rejected:
  "\<not> else_handlers_ok [SMustElse s a d s' a' D', SOnBreach s acts]"
proof -
  let ?b = "[SMustElse s a d s' a' D', SOnBreach s acts]"
  have g: "(GREATEST j::nat. j < Suc 0 \<and> binds s (?b ! j)) = 0"
    by (rule Greatest_equality) auto
  have b: "bound_to ?b (Suc 0) s = Some 0"
    unfolding bound_to_def g by auto
  show ?thesis
  proof
    assume "else_handlers_ok ?b"
    from this[unfolded else_handlers_ok_def, rule_format, of "Suc 0"] show False by (simp add: b)
  qed
qed


section \<open>MAX_AGE and ON_STALE BLOCK\<close>

text \<open>A factor \<open>x\<close> with \<open>MAX_AGE m\<close> is fresh at entry \<open>j\<close> if its value arrived at most \<open>m\<close>
  time units earlier. Under \<open>ON_STALE BLOCK\<close> a stale factor is treated as absent. \<open>M x\<close> is
  the maximum age of \<open>x\<close> if \<open>x\<close> is under BLOCK, and \<open>None\<close> otherwise (no MAX_AGE, or
  USE_LAST, which keeps the value).\<close>

definition fresh :: "int \<Rightarrow> 'n \<Rightarrow> ('n, 'v, 's, 'a) itrace \<Rightarrow> nat \<Rightarrow> bool" where
  "fresh m x \<pi> j \<longleftrightarrow> (\<exists>i \<le> j. evt (\<pi> ! i) = Arrival x \<and> time \<pi> j - time \<pi> i \<le> m)"

definition blocked :: "('n \<Rightarrow> int option) \<Rightarrow> ('n, 'v, 's, 'a) itrace \<Rightarrow> nat \<Rightarrow> ('n, 'v) state" where
  "blocked M \<pi> j x = (case M x of None \<Rightarrow> st \<pi> j x | Some m \<Rightarrow> if fresh m x \<pi> j then st \<pi> j x else None)"

theorem fresh_at_max_age:
  "i \<le> j \<Longrightarrow> evt (\<pi> ! i) = Arrival x \<Longrightarrow> time \<pi> j - time \<pi> i = m \<Longrightarrow> fresh m x \<pi> j"
  unfolding fresh_def by auto

lemma blocked_le: "blocked M \<pi> j \<sqsubseteq> st \<pi> j"
  unfolding info_le_def blocked_def by (auto split: option.splits if_splits)

theorem stale_absent:
  "M x = Some m \<Longrightarrow> \<not> fresh m x \<pi> j \<Longrightarrow> eval (EPresent x) (blocked M \<pi> j) = Some False"
  by (simp add: blocked_def domIff)

text \<open>The safety claim of section 2.9: a result computed with stale factors treated as
  absent is not overturned by whatever values those factors have when refreshed.\<close>

theorem stale_safe:
  assumes "present_free e" and "eval e (blocked M \<pi> j) = Some b"
    and "\<And>x. M x = None \<or> (\<exists>m. M x = Some m \<and> fresh m x \<pi> j) \<Longrightarrow> \<sigma>' x = st \<pi> j x"
  shows "eval e \<sigma>' = Some b"
proof -
  have "blocked M \<pi> j \<sqsubseteq> \<sigma>'"
    unfolding info_le_def
  proof
    fix x assume "x \<in> dom (blocked M \<pi> j)"
    then have "M x = None \<or> (\<exists>m. M x = Some m \<and> fresh m x \<pi> j)" and "blocked M \<pi> j x = st \<pi> j x"
      by (auto simp: blocked_def split: option.splits if_splits)
    with assms(3) show "\<sigma>' x = blocked M \<pi> j x" by simp
  qed
  from T2_monotone[OF assms(1) this assms(2)] show ?thesis .
qed

end
