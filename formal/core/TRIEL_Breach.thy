(*  Title:      TRIEL_Breach.thy
    Purpose:    Deadlines and breach (TECHNICAL_REPORT.md section 2.6) as a layer of
                verdicts over implementation traces: BY and WITHIN, prohibitions and
                permissions, binding of ON_BREACH, breach actions and their continuations,
                and MAX_AGE with ON_STALE BLOCK. The trace semantics of TRIEL_Trace and
                TRIEL_Terms is unchanged.
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
  subject and action only: the polarity belongs to the norm, not to the event.\<close>

type_synonym ('n, 'v, 's, 'a) itrace = "('n, 'v, int, 's, 'a) trace"

definition does :: "'s \<Rightarrow> 'a \<Rightarrow> ('n, 's, 'a) event \<Rightarrow> bool" where
  "does s a e \<longleftrightarrow> (\<exists>p. e = Deontic s a p)"

definition time :: "('n, 'v, 's, 'a) itrace \<Rightarrow> nat \<Rightarrow> int" where
  "time \<pi> j = tstamp (\<pi> ! j)"

lemma time_mono: "is_trace \<pi> \<Longrightarrow> i \<le> j \<Longrightarrow> j < length \<pi> \<Longrightarrow> time \<pi> i \<le> time \<pi> j"
  unfolding is_trace_def time_def using sorted_nth_mono[of "map tstamp \<pi>" i j] by simp

lemma time_append [simp]: "j < length \<pi> \<Longrightarrow> time (\<pi> @ \<rho>) j = time \<pi> j"
  by (simp add: time_def nth_append)

lemma nth_append_left [simp]: "j < length \<pi> \<Longrightarrow> (\<pi> @ \<rho>) ! j = \<pi> ! j"
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

text \<open>\<open>s MUST a BY d\<close> (or \<open>WITHIN d\<close>) has the window \<open>(-\<infinity>, d]\<close>. Without a deadline an
  obligation is never breached.\<close>

definition ob_verdict :: "'s \<Rightarrow> 'a \<Rightarrow> int option \<Rightarrow> ('n, 'v, 's, 'a) itrace \<Rightarrow> verdict" where
  "ob_verdict s a D \<pi> =
     (case D of
        Some d \<Rightarrow> window s a None d \<pi>
      | None \<Rightarrow> (if \<exists>j. 1 \<le> j \<and> j < length \<pi> \<and> does s a (evt (\<pi> ! j)) then Fulfilled else Pending))"

theorem deadline_missed_breach:
  "\<not> acted s a None d \<pi> \<Longrightarrow> passed d \<pi> \<Longrightarrow> ob_verdict s a (Some d) \<pi> = Breached d"
  by (simp add: ob_verdict_def window_def)

corollary within_missed_breach:
  assumes "resolve T \<tau>\<^sub>0 \<sigma>\<^sub>0 (DAfter k) = Some d"
    and "\<not> acted s a None d \<pi>" and "passed d \<pi>"
  shows "ob_verdict s a (Some d) \<pi> = Breached (\<tau>\<^sub>0 + k)"
  using assms by (simp add: ob_verdict_def window_def)

theorem fulfilled_at_deadline:
  assumes "1 \<le> j" and "j < length \<pi>" and "does s a (evt (\<pi> ! j))" and "time \<pi> j = d"
  shows "ob_verdict s a (Some d) \<pi> = Fulfilled"
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
  "is_trace (\<pi> @ \<rho>) \<Longrightarrow> ob_verdict s a (Some d) \<pi> \<noteq> Pending \<Longrightarrow>
     ob_verdict s a (Some d) (\<pi> @ \<rho>) = ob_verdict s a (Some d) \<pi>"
  unfolding ob_verdict_def by (simp add: window_final)


section \<open>Prohibitions and permissions\<close>

text \<open>\<open>s MUST_NOT a WHEN c\<close> is breached at the first action \<open>a\<close> of \<open>s\<close> before which \<open>c\<close> is
  true; \<open>c\<close> is evaluated in the state before the action. An undefined \<open>c\<close> is not a
  breach.\<close>

definition forbidden :: "'s \<Rightarrow> 'a \<Rightarrow> ('n, 'v) expr \<Rightarrow> ('n, 'v, 's, 'a) itrace \<Rightarrow> nat \<Rightarrow> bool" where
  "forbidden s a c \<pi> j \<longleftrightarrow>
     1 \<le> j \<and> j < length \<pi> \<and> does s a (evt (\<pi> ! j)) \<and> eval c (st \<pi> (j - 1)) = Some True"

definition pr_verdict :: "'s \<Rightarrow> 'a \<Rightarrow> ('n, 'v) expr \<Rightarrow> ('n, 'v, 's, 'a) itrace \<Rightarrow> verdict" where
  "pr_verdict s a c \<pi> =
     (if \<exists>j. forbidden s a c \<pi> j then Breached (time \<pi> (LEAST j. forbidden s a c \<pi> j)) else Pending)"

lemma forbidden_append:
  "j < length \<pi> \<Longrightarrow> forbidden s a c (\<pi> @ \<rho>) j \<longleftrightarrow> forbidden s a c \<pi> j"
  unfolding forbidden_def by auto

lemma forbidden_less: "forbidden s a c \<pi> j \<Longrightarrow> j < length \<pi>"
  by (simp add: forbidden_def)

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

text \<open>Enforcement and verdict are separate roles. A monitor enforces a prohibition
  fail-closed: it blocks the action unless \<open>c\<close> is known to be false, so it blocks on an
  undefined \<open>c\<close>. The verdict records a breach only when \<open>c\<close> is true.\<close>

definition blocks :: "('n, 'v) expr \<Rightarrow> ('n, 'v) state \<Rightarrow> bool" where
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

text \<open>\<open>s MAY a WHEN c\<close> is fulfilled when exercised in a state where \<open>c\<close> holds, and is
  never breached.\<close>

definition may_verdict :: "'s \<Rightarrow> 'a \<Rightarrow> ('n, 'v) expr \<Rightarrow> ('n, 'v, 's, 'a) itrace \<Rightarrow> verdict" where
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
    transfer.\<close>

datatype 's continuation = NoContinuation | Terminated | Cure verdict | Escalated 's verdict

datatype 's status = SFulfilled | SPending | SBreached int "'s continuation"

fun continue_after :: "int \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> int \<Rightarrow> int \<Rightarrow> ('s, 'p) baction option
    \<Rightarrow> ('n, 'v, 's, 'a) itrace \<Rightarrow> 's continuation" where
  "continue_after \<tau>\<^sub>0 s a d \<tau>\<^sub>b (Some Terminate) \<pi> = Terminated"
| "continue_after \<tau>\<^sub>0 s a d \<tau>\<^sub>b (Some (CureBy k)) \<pi> = Cure (window s a (Some \<tau>\<^sub>b) (\<tau>\<^sub>b + k) \<pi>)"
| "continue_after \<tau>\<^sub>0 s a d \<tau>\<^sub>b (Some (EscalateTo s')) \<pi> =
     Escalated s' (window s' a (Some \<tau>\<^sub>b) (\<tau>\<^sub>b + (d - \<tau>\<^sub>0)) \<pi>)"
| "continue_after \<tau>\<^sub>0 s a d \<tau>\<^sub>b _ \<pi> = NoContinuation"

definition handle_breach :: "int \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> int \<Rightarrow> ('s, 'p) baction list
    \<Rightarrow> ('n, 'v, 's, 'a) itrace \<Rightarrow> 's status" where
  "handle_breach \<tau>\<^sub>0 s a d acts \<pi> =
     (case window s a None d \<pi> of
        Fulfilled \<Rightarrow> SFulfilled
      | Pending \<Rightarrow> SPending
      | Breached \<tau>\<^sub>b \<Rightarrow> SBreached \<tau>\<^sub>b (continue_after \<tau>\<^sub>0 s a d \<tau>\<^sub>b (cont_of acts) \<pi>))"

lemma cont_of_filter: "cont_of (filter is_cont acts) = cont_of acts"
  by (simp add: cont_of_def)

theorem informational_irrelevant:
  "handle_breach \<tau>\<^sub>0 s a d acts \<pi> = handle_breach \<tau>\<^sub>0 s a d (filter is_cont acts) \<pi>"
  by (simp add: handle_breach_def cont_of_filter split: verdict.split)

theorem cure_restores:
  assumes "window s a None d \<pi> = Breached d" and "cont_of acts = Some (CureBy k)"
    and "acted s a (Some d) (d + k) \<pi>"
  shows "handle_breach \<tau>\<^sub>0 s a d acts \<pi> = SBreached d (Cure Fulfilled)"
  using assms by (simp add: handle_breach_def window_def)

theorem cure_failed:
  assumes "window s a None d \<pi> = Breached d" and "cont_of acts = Some (CureBy k)"
    and "\<not> acted s a (Some d) (d + k) \<pi>" and "passed (d + k) \<pi>"
  shows "handle_breach \<tau>\<^sub>0 s a d acts \<pi> = SBreached d (Cure (Breached (d + k)))"
  using assms by (simp add: handle_breach_def window_def)

theorem escalation_keeps_breach:
  assumes "window s a None d \<pi> = Breached d" and "cont_of acts = Some (EscalateTo s')"
  shows "handle_breach \<tau>\<^sub>0 s a d acts \<pi> =
           SBreached d (Escalated s' (window s' a (Some d) (d + (d - \<tau>\<^sub>0)) \<pi>))"
  using assms by (simp add: handle_breach_def)

text \<open>The status is final once the obligation and the window of its continuation are
  decided.\<close>

theorem handle_breach_final:
  assumes tr: "is_trace (\<pi> @ \<rho>)"
    and base: "window s a None d \<pi> \<noteq> Pending"
    and cure: "\<And>k. cont_of acts = Some (CureBy k) \<Longrightarrow> window s a (Some d) (d + k) \<pi> \<noteq> Pending"
    and esc: "\<And>s'. cont_of acts = Some (EscalateTo s') \<Longrightarrow>
                window s' a (Some d) (d + (d - \<tau>\<^sub>0)) \<pi> \<noteq> Pending"
  shows "handle_breach \<tau>\<^sub>0 s a d acts (\<pi> @ \<rho>) = handle_breach \<tau>\<^sub>0 s a d acts \<pi>"
proof -
  have w: "window s a None d (\<pi> @ \<rho>) = window s a None d \<pi>"
    using tr base by (rule window_final)
  show ?thesis
  proof (cases "window s a None d \<pi>")
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
  or prohibition of the same subject at the top level.\<close>

datatype ('n, 'v, 's, 'a, 'p) sterm =
    SMust 's 'a "'n deadline option"
  | SMustNot 's 'a "('n, 'v) expr"
  | SMay 's 'a "('n, 'v) expr"
  | SThen "('n, 'v, 's, 'a, 'p) sterm" "('n, 'v, 's, 'a, 'p) sterm"
  | SOr "('n, 'v, 's, 'a, 'p) sterm" "('n, 'v, 's, 'a, 'p) sterm"
  | SAnd "('n, 'v, 's, 'a, 'p) sterm" "('n, 'v, 's, 'a, 'p) sterm"
  | SUnless "('n, 'v, 's, 'a, 'p) sterm" "('n, 'v) expr" "('n, 'v, 's, 'a, 'p) sterm"
  | SOnBreach 's "('s, 'p) baction list"

fun has_handler :: "('n, 'v, 's, 'a, 'p) sterm \<Rightarrow> bool" where
  "has_handler (SOnBreach s acts) = True"
| "has_handler (SThen t u) = (has_handler t \<or> has_handler u)"
| "has_handler (SOr t u) = (has_handler t \<or> has_handler u)"
| "has_handler (SAnd t u) = (has_handler t \<or> has_handler u)"
| "has_handler (SUnless t c u) = (has_handler t \<or> has_handler u)"
| "has_handler _ = False"

fun binds :: "'s \<Rightarrow> ('n, 'v, 's, 'a, 'p) sterm \<Rightarrow> bool" where
  "binds s (SMust s' a d) = (s' = s)"
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
  "deadlines (SMust s a (Some d)) = [d]"
| "deadlines (SThen t u) = deadlines t @ deadlines u"
| "deadlines (SOr t u) = deadlines t @ deadlines u"
| "deadlines (SAnd t u) = deadlines t @ deadlines u"
| "deadlines (SUnless t c u) = deadlines t @ deadlines u"
| "deadlines _ = []"

text \<open>A block is activated at time \<open>\<tau>\<^sub>0\<close> in state \<open>\<sigma>\<^sub>0\<close> only if every deadline in it resolves.\<close>

definition activates :: "('v \<Rightarrow> int option) \<Rightarrow> int \<Rightarrow> ('n, 'v) state
    \<Rightarrow> ('n, 'v, 's, 'a, 'p) sterm list \<Rightarrow> bool" where
  "activates T \<tau>\<^sub>0 \<sigma>\<^sub>0 blk \<longleftrightarrow> (\<forall>t \<in> set blk. \<forall>d \<in> set (deadlines t). resolve T \<tau>\<^sub>0 \<sigma>\<^sub>0 d \<noteq> None)"

theorem activation_rejected:
  assumes "SMust s a (Some (DFactor x k)) \<in> set blk" and "\<sigma>\<^sub>0 x = None"
  shows "\<not> activates T \<tau>\<^sub>0 \<sigma>\<^sub>0 blk"
  using assms unfolding activates_def by force


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
