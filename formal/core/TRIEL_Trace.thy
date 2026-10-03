(*  Title:      TRIEL_Trace.thy
    Purpose:    Trace semantics of TRIEL terms (TECHNICAL_REPORT.md section 2.5):
                traces, fusion, outcomes, the denotations of MUST, MAY, MUST_NOT,
                THEN, AND, OR and UNLESS, and the algebraic laws of UNLESS.
    Source:     Public description only (github.com/triel-lang/grammar,
                TECHNICAL_REPORT.md section 2.5). Guards are expressions of
                TRIEL_Core, evaluated by its strong Kleene semantics.
*)

theory TRIEL_Trace
  imports TRIEL_Core
begin

section \<open>Traces\<close>

text \<open>An entry \<open>(\<sigma>, \<tau>, e)\<close> consists of a state (as in TRIEL_Core: a partial map from
  names to values, values being of an arbitrary type, which may itself contain maps),
  a timestamp, and the event that produced the state.\<close>

datatype polarity = Must | May | MustNot

datatype ('n, 's, 'a) event =
    Deontic 's 'a polarity    \<comment> \<open>deontic event (subject, action, polarity)\<close>
  | Arrival 'n                \<comment> \<open>arrival of data from a factor's SOURCE\<close>
  | Tick                      \<comment> \<open>clock tick\<close>

type_synonym ('n, 'v, 't, 's, 'a) entry = "('n, 'v) state \<times> 't \<times> ('n, 's, 'a) event"
type_synonym ('n, 'v, 't, 's, 'a) trace = "('n, 'v, 't, 's, 'a) entry list"

fun sta :: "('n, 'v, 't, 's, 'a) entry \<Rightarrow> ('n, 'v) state" where
  "sta (\<sigma>, \<tau>, e) = \<sigma>"

fun tstamp :: "('n, 'v, 't, 's, 'a) entry \<Rightarrow> 't" where
  "tstamp (\<sigma>, \<tau>, e) = \<tau>"

fun evt :: "('n, 'v, 't, 's, 'a) entry \<Rightarrow> ('n, 's, 'a) event" where
  "evt (\<sigma>, \<tau>, e) = e"

text \<open>A trace is a finite, non-empty sequence of entries whose timestamps are
  non-decreasing. Traces are lists; \<open>is_trace\<close> is the invariant.\<close>

definition is_trace :: "('n, 'v, 't :: linorder, 's, 'a) trace \<Rightarrow> bool" where
  "is_trace \<pi> \<longleftrightarrow> \<pi> \<noteq> [] \<and> sorted (map tstamp \<pi>)"

text \<open>The state of entry \<open>j\<close>.\<close>

definition st :: "('n, 'v, 't, 's, 'a) trace \<Rightarrow> nat \<Rightarrow> ('n, 'v) state" where
  "st \<pi> j = sta (\<pi> ! j)"

text \<open>Fusion \<open>\<pi>\<^sub>1 \<frown> \<pi>\<^sub>2\<close> is defined when the last entry of \<open>\<pi>\<^sub>1\<close> is the first entry of
  \<open>\<pi>\<^sub>2\<close>; the fused trace is \<open>\<pi>\<^sub>1\<close> followed by \<open>\<pi>\<^sub>2\<close> without its first entry, so
  the shared entry occurs once.\<close>

definition fusable :: "('n, 'v, 't, 's, 'a) trace \<Rightarrow> ('n, 'v, 't, 's, 'a) trace \<Rightarrow> bool" where
  "fusable p q \<longleftrightarrow> p \<noteq> [] \<and> q \<noteq> [] \<and> last p = hd q"

definition fuse :: "('n, 'v, 't, 's, 'a) trace \<Rightarrow> ('n, 'v, 't, 's, 'a) trace \<Rightarrow> ('n, 'v, 't, 's, 'a) trace" where
  "fuse p q = p @ tl q"

text \<open>\<open>\<pi>[0..k]\<close>: the prefix of \<open>\<pi>\<close> ending at entry \<open>k\<close>.\<close>

definition pre :: "('n, 'v, 't, 's, 'a) trace \<Rightarrow> nat \<Rightarrow> ('n, 'v, 't, 's, 'a) trace" where
  "pre \<pi> k = take (Suc k) \<pi>"


section \<open>Outcomes and denotations\<close>

datatype outcome = Done | Interrupted | Violated

type_synonym ('n, 'v, 't, 's, 'a) den = "(('n, 'v, 't, 's, 'a) trace \<times> outcome) set"

text \<open>\<open>o\<^sub>1 \<squnion> o\<^sub>2\<close> is the maximum in the order \<open>Done < Interrupted < Violated\<close>.\<close>

fun rank :: "outcome \<Rightarrow> nat" where
  "rank Done = 0"
| "rank Interrupted = 1"
| "rank Violated = 2"

definition ojoin :: "outcome \<Rightarrow> outcome \<Rightarrow> outcome" where
  "ojoin o\<^sub>1 o\<^sub>2 = (if rank o\<^sub>1 \<le> rank o\<^sub>2 then o\<^sub>2 else o\<^sub>1)"

fun kappa :: "outcome \<Rightarrow> outcome" where
  "kappa Done = Interrupted"
| "kappa Interrupted = Interrupted"
| "kappa Violated = Violated"

subsection \<open>Deontic primitives\<close>

text \<open>\<open>\<pi>\<close> ends with \<open>(subject, action, polarity)\<close> when that is the event of its last entry.
  For MAY, \<open>eval(c, \<sigma>\<^sub>n\<^sub>-\<^sub>1)\<close> with \<open>n = |\<pi>| - 1\<close> refers to the entry before the last
  one, so the action trace has at least two entries.\<close>

definition must_d :: "'s \<Rightarrow> 'a \<Rightarrow> ('n, 'v, 't :: linorder, 's, 'a) den" where
  "must_d s a = {(\<pi>, Done) | \<pi>. is_trace \<pi> \<and> evt (last \<pi>) = Deontic s a Must}"

definition may_d :: "'s \<Rightarrow> 'a \<Rightarrow> ('n, 'v) expr \<Rightarrow> ('n, 'v, 't :: linorder, 's, 'a) den" where
  "may_d s a c =
     {(\<pi>, Done) | \<pi>. is_trace \<pi> \<and> evt (last \<pi>) = Deontic s a May
                     \<and> 1 \<le> length \<pi> - 1 \<and> eval c (st \<pi> (length \<pi> - 2)) = Some True}
     \<union> {([x], Done) | x. True}"

definition mustnot_d :: "'s \<Rightarrow> 'a \<Rightarrow> ('n, 'v) expr \<Rightarrow> ('n, 'v, 't, 's, 'a) den" where
  "mustnot_d s a c = {([x], Done) | x. True}"

subsection \<open>Composite terms\<close>

definition then_d :: "('n, 'v, 't, 's, 'a) den \<Rightarrow> ('n, 'v, 't, 's, 'a) den \<Rightarrow> ('n, 'v, 't, 's, 'a) den" where
  "then_d T\<^sub>1 T\<^sub>2 =
     {(fuse \<pi>\<^sub>1 \<pi>\<^sub>2, o\<^sub>2) | \<pi>\<^sub>1 \<pi>\<^sub>2 o\<^sub>2. (\<pi>\<^sub>1, Done) \<in> T\<^sub>1 \<and> (\<pi>\<^sub>2, o\<^sub>2) \<in> T\<^sub>2 \<and> fusable \<pi>\<^sub>1 \<pi>\<^sub>2}
     \<union> {(\<pi>\<^sub>1, o\<^sub>1). (\<pi>\<^sub>1, o\<^sub>1) \<in> T\<^sub>1 \<and> o\<^sub>1 \<noteq> Done}"

definition or_d :: "('n, 'v, 't, 's, 'a) den \<Rightarrow> ('n, 'v, 't, 's, 'a) den \<Rightarrow> ('n, 'v, 't, 's, 'a) den" where
  "or_d T\<^sub>1 T\<^sub>2 = T\<^sub>1 \<union> T\<^sub>2"

definition unless_d ::
  "('n, 'v, 't, 's, 'a) den \<Rightarrow> ('n, 'v) expr \<Rightarrow> ('n, 'v, 't, 's, 'a) den \<Rightarrow> ('n, 'v, 't, 's, 'a) den" where
  "unless_d T c E =
     {(\<pi>, r). (\<pi>, r) \<in> T \<and> (\<forall>j < length \<pi> - 1. eval c (st \<pi> j) \<noteq> Some True)}
     \<union> {(fuse (pre \<pi> k) \<pi>', kappa r') | \<pi> r k \<pi>' r'.
          (\<pi>, r) \<in> T
          \<and> (\<exists>j < length \<pi> - 1. eval c (st \<pi> j) = Some True)
          \<and> k = (LEAST j. j < length \<pi> - 1 \<and> eval c (st \<pi> j) = Some True)
          \<and> (\<pi>', r') \<in> E \<and> fusable (pre \<pi> k) \<pi>'}"

text \<open>AND interleaves the traces of its operands. Section 2.5 does not define
  \<open>interleave\<close>; it is a parameter, constrained only by the assumption that two total
  denotations have, from every common first entry, traces with at least one
  interleaving starting at that entry. \<open>total\<close> is defined below.\<close>

definition total :: "('n, 'v, 't, 's, 'a) den \<Rightarrow> bool" where
  "total T \<longleftrightarrow> (\<forall>x. \<exists>\<pi> r. (\<pi>, r) \<in> T \<and> \<pi> \<noteq> [] \<and> hd \<pi> = x)"

locale interleaving =
  fixes interleave ::
    "('n, 'v, 't, 's, 'a) trace \<Rightarrow> ('n, 'v, 't, 's, 'a) trace \<Rightarrow> ('n, 'v, 't, 's, 'a) trace set"
  assumes interleave_from_start:
    "total T\<^sub>1 \<Longrightarrow> total T\<^sub>2 \<Longrightarrow>
       \<exists>\<pi>\<^sub>1 o\<^sub>1 \<pi>\<^sub>2 o\<^sub>2 \<pi>. (\<pi>\<^sub>1, o\<^sub>1) \<in> T\<^sub>1 \<and> (\<pi>\<^sub>2, o\<^sub>2) \<in> T\<^sub>2 \<and> \<pi>\<^sub>1 \<noteq> [] \<and> \<pi>\<^sub>2 \<noteq> []
         \<and> hd \<pi>\<^sub>1 = x \<and> hd \<pi>\<^sub>2 = x \<and> \<pi> \<in> interleave \<pi>\<^sub>1 \<pi>\<^sub>2 \<and> \<pi> \<noteq> [] \<and> hd \<pi> = x"
begin

definition and_d :: "('n, 'v, 't, 's, 'a) den \<Rightarrow> ('n, 'v, 't, 's, 'a) den \<Rightarrow> ('n, 'v, 't, 's, 'a) den" where
  "and_d T\<^sub>1 T\<^sub>2 =
     {(\<pi>, ojoin o\<^sub>1 o\<^sub>2) | \<pi> \<pi>\<^sub>1 o\<^sub>1 \<pi>\<^sub>2 o\<^sub>2.
        \<pi> \<in> interleave \<pi>\<^sub>1 \<pi>\<^sub>2 \<and> (\<pi>\<^sub>1, o\<^sub>1) \<in> T\<^sub>1 \<and> (\<pi>\<^sub>2, o\<^sub>2) \<in> T\<^sub>2}"

end


section \<open>Outcome operations\<close>

lemma ojoin_commute: "ojoin x y = ojoin y x"
  by (cases x; cases y) (simp_all add: ojoin_def)

lemma ojoin_assoc: "ojoin (ojoin x y) z = ojoin x (ojoin y z)"
  by (cases x; cases y; cases z) (simp_all add: ojoin_def)

lemma ojoin_idem: "ojoin x x = x"
  by (simp add: ojoin_def)

text \<open>The maximum satisfies every equation that section 2.5 states for \<open>\<squnion>\<close>.\<close>

lemma ojoin_stated_cases:
  "ojoin Done Done = Done"
  "ojoin x Violated = Violated"
  "x \<noteq> Violated \<Longrightarrow> ojoin x Interrupted = Interrupted"
  by (cases x; simp add: ojoin_def)+

lemma kappa_not_Done [simp]: "kappa x \<noteq> Done" "Done \<noteq> kappa x"
  by (cases x; simp)+


section \<open>Guard firing\<close>

text \<open>The guard \<open>c\<close> fires at entry \<open>j\<close> of \<open>\<pi>\<close> when \<open>j\<close> is a watched entry (every entry
  except the last) and \<open>eval(c, \<sigma>\<^sub>j)\<close> is true; an undefined guard does not fire.
  \<open>first_fire\<close> is the least such \<open>j\<close>.\<close>

definition fires :: "('n, 'v) expr \<Rightarrow> ('n, 'v, 't, 's, 'a) trace \<Rightarrow> nat \<Rightarrow> bool" where
  "fires c \<pi> j \<longleftrightarrow> j < length \<pi> - 1 \<and> eval c (st \<pi> j) = Some True"

definition first_fire :: "('n, 'v) expr \<Rightarrow> ('n, 'v, 't, 's, 'a) trace \<Rightarrow> nat" where
  "first_fire c \<pi> = (LEAST j. fires c \<pi> j)"

lemma unless_d_iff:
  "(\<pi>, r) \<in> unless_d T c E \<longleftrightarrow>
     ((\<pi>, r) \<in> T \<and> (\<forall>j. \<not> fires c \<pi> j))
     \<or> (\<exists>\<pi>\<^sub>0 r\<^sub>0 \<pi>' r'. (\<pi>\<^sub>0, r\<^sub>0) \<in> T \<and> (\<exists>j. fires c \<pi>\<^sub>0 j) \<and> (\<pi>', r') \<in> E
          \<and> fusable (pre \<pi>\<^sub>0 (first_fire c \<pi>\<^sub>0)) \<pi>'
          \<and> \<pi> = fuse (pre \<pi>\<^sub>0 (first_fire c \<pi>\<^sub>0)) \<pi>' \<and> r = kappa r')"
  (is "?L \<longleftrightarrow> ?A \<or> ?B")
proof
  assume ?L
  then consider
      (keep) "(\<pi>, r) \<in> T" "\<forall>j < length \<pi> - 1. eval c (st \<pi> j) \<noteq> Some True"
    | (int) \<pi>\<^sub>0 r\<^sub>0 k \<pi>' r' where "(\<pi>, r) = (fuse (pre \<pi>\<^sub>0 k) \<pi>', kappa r')" "(\<pi>\<^sub>0, r\<^sub>0) \<in> T"
        "\<exists>j < length \<pi>\<^sub>0 - 1. eval c (st \<pi>\<^sub>0 j) = Some True"
        "k = (LEAST j. j < length \<pi>\<^sub>0 - 1 \<and> eval c (st \<pi>\<^sub>0 j) = Some True)"
        "(\<pi>', r') \<in> E" "fusable (pre \<pi>\<^sub>0 k) \<pi>'"
    unfolding unless_d_def by blast
  then show "?A \<or> ?B"
  proof cases
    case keep
    then have ?A by (simp add: fires_def)
    then show ?thesis ..
  next
    case int
    have k: "k = first_fire c \<pi>\<^sub>0"
      using int(4) by (simp add: first_fire_def fires_def)
    have eq: "\<pi> = fuse (pre \<pi>\<^sub>0 k) \<pi>'" "r = kappa r'"
      using int(1) by simp_all
    have fi: "\<exists>j. fires c \<pi>\<^sub>0 j"
      using int(3) by (auto simp: fires_def)
    have ?B
      using int(2) fi int(5) int(6) eq unfolding k by blast
    then show ?thesis ..
  qed
next
  assume "?A \<or> ?B"
  then show ?L
  proof
    assume ?A
    then show ?L by (simp add: unless_d_def fires_def)
  next
    assume ?B
    then obtain \<pi>\<^sub>0 r\<^sub>0 \<pi>' r' where
      b: "(\<pi>\<^sub>0, r\<^sub>0) \<in> T" "\<exists>j. fires c \<pi>\<^sub>0 j" "(\<pi>', r') \<in> E"
         "fusable (pre \<pi>\<^sub>0 (first_fire c \<pi>\<^sub>0)) \<pi>'"
         "\<pi> = fuse (pre \<pi>\<^sub>0 (first_fire c \<pi>\<^sub>0)) \<pi>'" "r = kappa r'"
      by blast
    have ex: "\<exists>j < length \<pi>\<^sub>0 - 1. eval c (st \<pi>\<^sub>0 j) = Some True"
      using b(2) by (auto simp: fires_def)
    have k: "first_fire c \<pi>\<^sub>0 = (LEAST j. j < length \<pi>\<^sub>0 - 1 \<and> eval c (st \<pi>\<^sub>0 j) = Some True)"
      by (simp add: first_fire_def fires_def)
    have "(fuse (pre \<pi>\<^sub>0 (first_fire c \<pi>\<^sub>0)) \<pi>', kappa r')
          \<in> {(fuse (pre \<pi> k) \<pi>', kappa r') | \<pi> r k \<pi>' r'.
               (\<pi>, r) \<in> T
               \<and> (\<exists>j < length \<pi> - 1. eval c (st \<pi> j) = Some True)
               \<and> k = (LEAST j. j < length \<pi> - 1 \<and> eval c (st \<pi> j) = Some True)
               \<and> (\<pi>', r') \<in> E \<and> fusable (pre \<pi> k) \<pi>'}"
      using b(1) ex k b(3) b(4) by blast
    then show ?L
      unfolding unless_d_def using b(5) b(6) by blast
  qed
qed

lemma then_d_iff:
  "(\<pi>, r) \<in> then_d T\<^sub>1 T\<^sub>2 \<longleftrightarrow>
     (\<exists>\<pi>\<^sub>1 \<pi>\<^sub>2. (\<pi>\<^sub>1, Done) \<in> T\<^sub>1 \<and> (\<pi>\<^sub>2, r) \<in> T\<^sub>2 \<and> fusable \<pi>\<^sub>1 \<pi>\<^sub>2 \<and> \<pi> = fuse \<pi>\<^sub>1 \<pi>\<^sub>2)
     \<or> ((\<pi>, r) \<in> T\<^sub>1 \<and> r \<noteq> Done)"
  unfolding then_d_def by auto

lemma no_fires_EFalse: "\<not> fires EFalse \<pi> j"
  by (simp add: fires_def)

lemma fires_less: "fires c \<pi> j \<Longrightarrow> j < length \<pi> - 1"
  by (simp add: fires_def)

lemma first_fire_fires: "fires c \<pi> j \<Longrightarrow> fires c \<pi> (first_fire c \<pi>)"
  unfolding first_fire_def by (rule LeastI)

lemma first_fire_le: "fires c \<pi> j \<Longrightarrow> first_fire c \<pi> \<le> j"
  unfolding first_fire_def by (rule Least_le)

lemma not_fires_before: "j < first_fire c \<pi> \<Longrightarrow> \<not> fires c \<pi> j"
  unfolding first_fire_def by (rule not_less_Least)

lemma first_fire_eqI:
  assumes "fires c \<pi> k" and "\<And>j. j < k \<Longrightarrow> \<not> fires c \<pi> j"
  shows "first_fire c \<pi> = k"
  unfolding first_fire_def
proof (rule Least_equality)
  show "fires c \<pi> k" by (fact assms(1))
next
  fix y assume "fires c \<pi> y"
  then show "k \<le> y" using assms(2) not_le by blast
qed


section \<open>Prefixes and fusion\<close>

lemma fuse_nonempty: "p \<noteq> [] \<Longrightarrow> fuse p q \<noteq> []"
  by (simp add: fuse_def)

lemma hd_fuse: "p \<noteq> [] \<Longrightarrow> hd (fuse p q) = hd p"
  by (simp add: fuse_def)

lemma length_fuse: "q \<noteq> [] \<Longrightarrow> length (fuse p q) = length p + length q - 1"
  by (cases q) (simp_all add: fuse_def)

lemma last_fuse: "fusable p q \<Longrightarrow> last (fuse p q) = last q"
  by (cases q) (auto simp: fuse_def fusable_def)

lemma nth_fuse_left: "j < length p \<Longrightarrow> fuse p q ! j = p ! j"
  by (simp add: fuse_def nth_append)

lemma nth_fuse_right:
  assumes "fusable p q" and "i < length q"
  shows "fuse p q ! (length p - 1 + i) = q ! i"
proof (cases i)
  case 0
  from assms(1) have "p \<noteq> []" "q \<noteq> []" "last p = hd q"
    by (simp_all add: fusable_def)
  then show ?thesis
    using 0 by (simp add: fuse_def nth_append last_conv_nth hd_conv_nth)
next
  case (Suc i')
  from assms(1) obtain y ys where q: "q = y # ys" by (cases q) (auto simp: fusable_def)
  from assms(1) have "p \<noteq> []" by (simp add: fusable_def)
  then have idx: "length p - 1 + i = length p + i'" using Suc by simp
  have "fuse p q ! (length p + i') = ys ! i'"
    by (simp add: fuse_def nth_append q)
  also have "\<dots> = q ! i" using Suc by (simp add: q)
  finally show ?thesis using idx by simp
qed

lemma fuse_assoc: "q \<noteq> [] \<Longrightarrow> fuse (fuse p q) r = fuse p (fuse q r)"
  by (cases q) (simp_all add: fuse_def)

lemma fusable_fuse_left: "fusable p q \<Longrightarrow> fusable (fuse p q) r \<longleftrightarrow> fusable q r"
  using last_fuse[of p q] by (auto simp: fusable_def fuse_def)

lemma fusable_fuse_right: "q \<noteq> [] \<Longrightarrow> fusable p (fuse q r) \<longleftrightarrow> fusable p q"
  by (auto simp: fusable_def fuse_def)

lemma pre_nonempty: "\<pi> \<noteq> [] \<Longrightarrow> pre \<pi> k \<noteq> []"
  by (cases \<pi>) (simp_all add: pre_def)

lemma hd_pre: "\<pi> \<noteq> [] \<Longrightarrow> hd (pre \<pi> k) = hd \<pi>"
  by (cases \<pi>) (simp_all add: pre_def)

lemma length_pre: "k < length \<pi> \<Longrightarrow> length (pre \<pi> k) = Suc k"
  by (simp add: pre_def)

lemma last_pre: "k < length \<pi> \<Longrightarrow> last (pre \<pi> k) = \<pi> ! k"
  by (simp add: pre_def take_Suc_conv_app_nth)

lemma nth_pre: "j \<le> k \<Longrightarrow> pre \<pi> k ! j = \<pi> ! j"
  by (simp add: pre_def)

lemma pre_pre: "pre (pre \<pi> k) k = pre \<pi> k"
  by (simp add: pre_def)

lemma fusable_pre:
  assumes "k < length \<pi>"
  shows "fusable (pre \<pi> k) \<pi>' \<longleftrightarrow> \<pi>' \<noteq> [] \<and> \<pi> ! k = hd \<pi>'"
proof -
  from assms have "\<pi> \<noteq> []" by auto
  then have "pre \<pi> k \<noteq> []" by (rule pre_nonempty)
  with last_pre[OF assms] show ?thesis by (simp add: fusable_def)
qed

text \<open>A prefix of a fused trace that ends inside the left operand is a prefix of the
  left operand; one that ends inside the right operand is the left operand fused with
  a prefix of the right operand.\<close>

lemma pre_fuse_left: "k < length p \<Longrightarrow> pre (fuse p q) k = pre p k"
  by (simp add: pre_def fuse_def)

lemma pre_fuse_right:
  "fusable p q \<Longrightarrow> i < length q \<Longrightarrow> pre (fuse p q) (length p - 1 + i) = fuse p (pre q i)"
  by (cases p) (simp_all add: pre_def fuse_def fusable_def take_tl)


section \<open>Firing on prefixes and fused traces\<close>

lemma fires_pre: "j < k \<Longrightarrow> k < length \<pi> \<Longrightarrow> fires c (pre \<pi> k) j \<longleftrightarrow> fires c \<pi> j"
  by (auto simp: fires_def st_def length_pre nth_pre)

text \<open>Entries of the left operand other than its last one are watched exactly as in
  the left operand; from the junction on, the entries are those of the right operand.
  The junction entry is watched as the first entry of the right operand.\<close>

lemma fires_fuse_left:
  assumes "fusable p q" and "j < length p - 1"
  shows "fires c (fuse p q) j \<longleftrightarrow> fires c p j"
proof -
  from assms(1) obtain y ys where q: "q = y # ys" by (cases q) (auto simp: fusable_def)
  with assms(2) have "j < length (fuse p q) - 1" by (simp add: fuse_def)
  moreover have "st (fuse p q) j = st p j"
    using assms(2) by (simp add: st_def nth_fuse_left)
  ultimately show ?thesis using assms(2) by (simp add: fires_def)
qed

lemma fires_fuse_right:
  assumes "fusable p q"
  shows "fires c (fuse p q) (length p - 1 + i) \<longleftrightarrow> fires c q i"
proof -
  from assms have ne: "p \<noteq> []" "q \<noteq> []" by (simp_all add: fusable_def)
  then have pos: "0 < length p" "0 < length q" by simp_all
  obtain x xs y ys where "p = x # xs" "q = y # ys"
    using ne by (cases p; cases q) auto
  then have len: "length (fuse p q) - 1 = (length p - 1) + (length q - 1)"
    by (simp add: fuse_def)
  show ?thesis
  proof (cases "i < length q")
    case True
    then have "st (fuse p q) (length p - 1 + i) = st q i"
      using nth_fuse_right[OF assms True] by (simp add: st_def)
    with len show ?thesis by (simp add: fires_def)
  next
    case False
    with len show ?thesis by (auto simp: fires_def)
  qed
qed

lemma fires_fuse_cases:
  assumes "fusable p q" and "fires c (fuse p q) j"
  shows "(j < length p - 1 \<and> fires c p j) \<or> (length p - 1 \<le> j \<and> fires c q (j - (length p - 1)))"
proof (cases "j < length p - 1")
  case True
  with assms fires_fuse_left show ?thesis by blast
next
  case False
  then have "j = length p - 1 + (j - (length p - 1))" by simp
  with assms False fires_fuse_right[OF assms(1), of c "j - (length p - 1)"] show ?thesis
    by auto
qed

lemma fires_fuse_ex:
  assumes "fusable p q"
  shows "(\<exists>j. fires c (fuse p q) j) \<longleftrightarrow> (\<exists>j. fires c p j) \<or> (\<exists>i. fires c q i)"
proof
  assume "\<exists>j. fires c (fuse p q) j"
  then obtain j where "fires c (fuse p q) j" ..
  from fires_fuse_cases[OF assms this] show "(\<exists>j. fires c p j) \<or> (\<exists>i. fires c q i)"
    by blast
next
  assume "(\<exists>j. fires c p j) \<or> (\<exists>i. fires c q i)"
  then show "\<exists>j. fires c (fuse p q) j"
  proof
    assume "\<exists>j. fires c p j"
    then obtain j where j: "fires c p j" ..
    then have "j < length p - 1" by (rule fires_less)
    with j assms have "fires c (fuse p q) j" by (simp add: fires_fuse_left)
    then show ?thesis ..
  next
    assume "\<exists>i. fires c q i"
    then obtain i where i: "fires c q i" ..
    have "fires c (fuse p q) (length p - 1 + i)"
      using fires_fuse_right[OF assms, of c i] i by blast
    then show ?thesis ..
  qed
qed

lemma first_fire_fuse_left:
  assumes "fusable p q" and "fires c p j"
  shows "first_fire c (fuse p q) = first_fire c p"
proof (rule first_fire_eqI)
  have k: "fires c p (first_fire c p)" using assms(2) by (rule first_fire_fires)
  then have "first_fire c p < length p - 1" by (rule fires_less)
  with k assms(1) show "fires c (fuse p q) (first_fire c p)"
    by (simp add: fires_fuse_left)
next
  fix i assume i: "i < first_fire c p"
  have "first_fire c p < length p - 1"
    using first_fire_fires[OF assms(2)] by (rule fires_less)
  with i have "i < length p - 1" by simp
  moreover have "\<not> fires c p i" using i by (rule not_fires_before)
  ultimately show "\<not> fires c (fuse p q) i"
    using assms(1) by (simp add: fires_fuse_left)
qed

lemma first_fire_fuse_right:
  assumes "fusable p q" and "\<forall>j. \<not> fires c p j" and "fires c q i"
  shows "first_fire c (fuse p q) = length p - 1 + first_fire c q"
proof (rule first_fire_eqI)
  show "fires c (fuse p q) (length p - 1 + first_fire c q)"
    using fires_fuse_right[OF assms(1), of c "first_fire c q"] first_fire_fires[OF assms(3)]
    by blast
next
  fix j assume j: "j < length p - 1 + first_fire c q"
  show "\<not> fires c (fuse p q) j"
  proof
    assume "fires c (fuse p q) j"
    with assms(1) have "(j < length p - 1 \<and> fires c p j) \<or>
        (length p - 1 \<le> j \<and> fires c q (j - (length p - 1)))"
      by (rule fires_fuse_cases)
    then show False
    proof
      assume "j < length p - 1 \<and> fires c p j"
      with assms(2) show False by blast
    next
      assume a: "length p - 1 \<le> j \<and> fires c q (j - (length p - 1))"
      with j have "j - (length p - 1) < first_fire c q" by arith
      then have "\<not> fires c q (j - (length p - 1))" by (rule not_fires_before)
      with a show False by blast
    qed
  qed
qed


section \<open>Laws of UNLESS\<close>

(* §2.5, law 1 *)
theorem unless_false: "unless_d T EFalse E = T"
proof (rule subset_antisym; rule subrelI)
  fix \<pi> r assume "(\<pi>, r) \<in> unless_d T EFalse E"
  then show "(\<pi>, r) \<in> T" unfolding unless_d_iff using no_fires_EFalse by blast
next
  fix \<pi> r assume "(\<pi>, r) \<in> T"
  then show "(\<pi>, r) \<in> unless_d T EFalse E" unfolding unless_d_iff using no_fires_EFalse by blast
qed

(* §2.5, law 2 *)
theorem unless_or: "unless_d (or_d T\<^sub>1 T\<^sub>2) c E = or_d (unless_d T\<^sub>1 c E) (unless_d T\<^sub>2 c E)"
proof (rule subset_antisym; rule subrelI)
  fix \<pi> r assume "(\<pi>, r) \<in> unless_d (or_d T\<^sub>1 T\<^sub>2) c E"
  then show "(\<pi>, r) \<in> or_d (unless_d T\<^sub>1 c E) (unless_d T\<^sub>2 c E)"
    unfolding or_d_def unless_d_iff Un_iff by blast
next
  fix \<pi> r assume "(\<pi>, r) \<in> or_d (unless_d T\<^sub>1 c E) (unless_d T\<^sub>2 c E)"
  then show "(\<pi>, r) \<in> unless_d (or_d T\<^sub>1 T\<^sub>2) c E"
    unfolding or_d_def unless_d_iff Un_iff by blast
qed

text \<open>An interrupted trace \<open>\<pi>[0..k] \<frown> \<pi>'\<close> is watched again at entries \<open>0 \<dots> k-1\<close> (where
  the guard did not fire) and at \<open>k\<close> (where it did) exactly when the handler trace
  \<open>\<pi>'\<close> has more than one entry.\<close>

lemma refire:
  assumes f: "fires c \<pi> j" and fus: "fusable (pre \<pi> (first_fire c \<pi>)) \<pi>'"
  shows "(\<exists>i. fires c (fuse (pre \<pi> (first_fire c \<pi>)) \<pi>') i) \<longleftrightarrow> 2 \<le> length \<pi>'"
    and "2 \<le> length \<pi>' \<Longrightarrow> first_fire c (fuse (pre \<pi> (first_fire c \<pi>)) \<pi>') = first_fire c \<pi>"
    and "pre (fuse (pre \<pi> (first_fire c \<pi>)) \<pi>') (first_fire c \<pi>) = pre \<pi> (first_fire c \<pi>)"
proof -
  define k where "k = first_fire c \<pi>"
  have fk: "fires c \<pi> k" unfolding k_def using f by (rule first_fire_fires)
  then have kl: "k < length \<pi> - 1" by (rule fires_less)
  then have lp: "length (pre \<pi> k) - 1 = k" by (simp add: length_pre)
  from fus have fus': "fusable (pre \<pi> k) \<pi>'" by (simp add: k_def)
  have before: "\<not> fires c (fuse (pre \<pi> k) \<pi>') i" if "i < k" for i
  proof -
    have "\<not> fires c \<pi> i" using that unfolding k_def by (rule not_fires_before)
    with that kl have "\<not> fires c (pre \<pi> k) i" by (simp add: fires_pre)
    with that lp fus' show ?thesis by (simp add: fires_fuse_left)
  qed
  have at_k: "fires c (fuse (pre \<pi> k) \<pi>') k \<longleftrightarrow> 2 \<le> length \<pi>'"
  proof -
    have "fires c (fuse (pre \<pi> k) \<pi>') k \<longleftrightarrow> fires c \<pi>' 0"
      using fires_fuse_right[OF fus', of c 0] lp by simp
    moreover have "st \<pi>' 0 = st \<pi> k"
      using fus' kl by (simp add: fusable_pre st_def hd_conv_nth)
    ultimately show ?thesis
      using fk by (auto simp: fires_def)
  qed
  have after: "2 \<le> length \<pi>'" if "fires c (fuse (pre \<pi> k) \<pi>') i" for i
  proof (cases "i < k")
    case True
    with before that show ?thesis by blast
  next
    case False
    with fires_fuse_cases[OF fus' that] lp have "fires c \<pi>' (i - k)" by auto
    then show ?thesis by (auto simp: fires_def)
  qed
  show "(\<exists>i. fires c (fuse (pre \<pi> (first_fire c \<pi>)) \<pi>') i) \<longleftrightarrow> 2 \<le> length \<pi>'"
    using at_k after unfolding k_def by blast
  show "first_fire c (fuse (pre \<pi> (first_fire c \<pi>)) \<pi>') = first_fire c \<pi>"
    if "2 \<le> length \<pi>'"
    using at_k that before unfolding k_def by (blast intro: first_fire_eqI)
  show "pre (fuse (pre \<pi> (first_fire c \<pi>)) \<pi>') (first_fire c \<pi>) = pre \<pi> (first_fire c \<pi>)"
    using kl unfolding k_def by (simp add: pre_fuse_left length_pre pre_pre)
qed

(* §2.5, law 4 *)
theorem unless_idem: "unless_d (unless_d T c E) c E = unless_d T c E"
proof (rule subset_antisym; rule subrelI)
  fix \<pi> r assume "(\<pi>, r) \<in> unless_d (unless_d T c E) c E"
  then consider
      (keep) "(\<pi>, r) \<in> unless_d T c E"
    | (int) \<pi>\<^sub>0 r\<^sub>0 \<pi>' r' where "(\<pi>\<^sub>0, r\<^sub>0) \<in> unless_d T c E" "\<exists>j. fires c \<pi>\<^sub>0 j" "(\<pi>', r') \<in> E"
        "fusable (pre \<pi>\<^sub>0 (first_fire c \<pi>\<^sub>0)) \<pi>'"
        "\<pi> = fuse (pre \<pi>\<^sub>0 (first_fire c \<pi>\<^sub>0)) \<pi>'" "r = kappa r'"
    unfolding unless_d_iff[where T = "unless_d T c E"] by blast
  then show "(\<pi>, r) \<in> unless_d T c E"
  proof cases
    case keep
    then show ?thesis .
  next
    case int
    text \<open>\<open>\<pi>\<^sub>0\<close> fires, so it is itself an interrupted trace of the inner UNLESS.\<close>
    from int(1) have "((\<pi>\<^sub>0, r\<^sub>0) \<in> T \<and> (\<forall>j. \<not> fires c \<pi>\<^sub>0 j))
        \<or> (\<exists>\<pi>\<^sub>1 r\<^sub>1 \<pi>\<^sub>1' r\<^sub>1'. (\<pi>\<^sub>1, r\<^sub>1) \<in> T \<and> (\<exists>j. fires c \<pi>\<^sub>1 j) \<and> (\<pi>\<^sub>1', r\<^sub>1') \<in> E
            \<and> fusable (pre \<pi>\<^sub>1 (first_fire c \<pi>\<^sub>1)) \<pi>\<^sub>1'
            \<and> \<pi>\<^sub>0 = fuse (pre \<pi>\<^sub>1 (first_fire c \<pi>\<^sub>1)) \<pi>\<^sub>1' \<and> r\<^sub>0 = kappa r\<^sub>1')"
      by (simp only: unless_d_iff)
    with int(2) obtain \<pi>\<^sub>1 r\<^sub>1 \<pi>\<^sub>1' r\<^sub>1' where
      in1: "(\<pi>\<^sub>1, r\<^sub>1) \<in> T" and f1: "\<exists>j. fires c \<pi>\<^sub>1 j"
      and fus1: "fusable (pre \<pi>\<^sub>1 (first_fire c \<pi>\<^sub>1)) \<pi>\<^sub>1'"
      and eq1: "\<pi>\<^sub>0 = fuse (pre \<pi>\<^sub>1 (first_fire c \<pi>\<^sub>1)) \<pi>\<^sub>1'"
      by blast
    from f1 obtain j where j: "fires c \<pi>\<^sub>1 j" ..
    have "2 \<le> length \<pi>\<^sub>1'"
      using refire(1)[OF j fus1] int(2) unfolding eq1 by blast
    then have ff: "first_fire c \<pi>\<^sub>0 = first_fire c \<pi>\<^sub>1"
      using refire(2)[OF j fus1] unfolding eq1 by blast
    have pp: "pre \<pi>\<^sub>0 (first_fire c \<pi>\<^sub>1) = pre \<pi>\<^sub>1 (first_fire c \<pi>\<^sub>1)"
      using refire(3)[OF j fus1] unfolding eq1 .
    have fusA: "fusable (pre \<pi>\<^sub>1 (first_fire c \<pi>\<^sub>1)) \<pi>'"
      using int(4) unfolding ff pp .
    have eqA: "\<pi> = fuse (pre \<pi>\<^sub>1 (first_fire c \<pi>\<^sub>1)) \<pi>'"
      using int(5) unfolding ff pp .
    show ?thesis
      unfolding unless_d_iff using in1 f1 int(3) fusA eqA int(6) by blast
  qed
next
  fix \<pi> r assume mem: "(\<pi>, r) \<in> unless_d T c E"
  then consider
      (keep) "(\<pi>, r) \<in> T" "\<forall>j. \<not> fires c \<pi> j"
    | (int) \<pi>\<^sub>1 r\<^sub>1 \<pi>' r' where "(\<pi>\<^sub>1, r\<^sub>1) \<in> T" "\<exists>j. fires c \<pi>\<^sub>1 j" "(\<pi>', r') \<in> E"
        "fusable (pre \<pi>\<^sub>1 (first_fire c \<pi>\<^sub>1)) \<pi>'"
        "\<pi> = fuse (pre \<pi>\<^sub>1 (first_fire c \<pi>\<^sub>1)) \<pi>'" "r = kappa r'"
    unfolding unless_d_iff by blast
  then show "(\<pi>, r) \<in> unless_d (unless_d T c E) c E"
  proof cases
    case keep
    with mem show ?thesis
      unfolding unless_d_iff[where T = "unless_d T c E"] by blast
  next
    case int
    from int(2) obtain j where j: "fires c \<pi>\<^sub>1 j" ..
    show ?thesis
    proof (cases "2 \<le> length \<pi>'")
      case False
      then have "\<not> (\<exists>i. fires c \<pi> i)"
        using refire(1)[OF j int(4)] unfolding int(5) by blast
      with mem show ?thesis
        unfolding unless_d_iff[where T = "unless_d T c E"] by blast
    next
      case True
      have fi: "\<exists>i. fires c \<pi> i"
        using refire(1)[OF j int(4)] True unfolding int(5) by blast
      have ff: "first_fire c \<pi> = first_fire c \<pi>\<^sub>1"
        using refire(2)[OF j int(4) True] unfolding int(5) .
      have pp: "pre \<pi> (first_fire c \<pi>\<^sub>1) = pre \<pi>\<^sub>1 (first_fire c \<pi>\<^sub>1)"
        using refire(3)[OF j int(4)] unfolding int(5) .
      have fusA: "fusable (pre \<pi> (first_fire c \<pi>)) \<pi>'"
        using int(4) unfolding ff pp .
      have eqA: "\<pi> = fuse (pre \<pi> (first_fire c \<pi>)) \<pi>'"
        using int(5) unfolding ff pp .
      show ?thesis
        unfolding unless_d_iff[where T = "unless_d T c E"]
        using mem fi int(3) fusA eqA int(6) by blast
    qed
  qed
qed


section \<open>Totality\<close>

text \<open>A denotation is total when every entry is the first entry of one of its traces:
  the term can start from any entry.\<close>

lemma totalI: "(\<And>x. \<exists>\<pi> r. (\<pi>, r) \<in> T \<and> \<pi> \<noteq> [] \<and> hd \<pi> = x) \<Longrightarrow> total T"
  by (simp add: total_def)

lemma totalE:
  assumes "total T"
  obtains \<pi> r where "(\<pi>, r) \<in> T" "\<pi> \<noteq> []" "hd \<pi> = x"
  using assms unfolding total_def by blast

lemma total_must: "total (must_d s a :: ('n, 'v, 't :: linorder, 's, 'a) den)"
proof (rule totalI)
  fix x :: "('n, 'v, 't, 's, 'a) entry"
  obtain \<sigma> \<tau> e where x: "x = (\<sigma>, \<tau>, e)" by (cases x) blast
  let ?\<pi> = "[x, (\<sigma>, \<tau>, Deontic s a Must)]"
  have "is_trace ?\<pi>" by (simp add: is_trace_def x)
  then have "(?\<pi>, Done) \<in> must_d s a" by (simp add: must_d_def)
  then show "\<exists>\<pi> r. (\<pi>, r) \<in> must_d s a \<and> \<pi> \<noteq> [] \<and> hd \<pi> = x" by fastforce
qed

lemma total_may: "total (may_d s a c)"
proof (rule totalI)
  fix x
  have "([x], Done) \<in> may_d s a c" unfolding may_d_def by blast
  then show "\<exists>\<pi> r. (\<pi>, r) \<in> may_d s a c \<and> \<pi> \<noteq> [] \<and> hd \<pi> = x" by fastforce
qed

lemma total_mustnot: "total (mustnot_d s a c)"
proof (rule totalI)
  fix x
  have "([x], Done) \<in> mustnot_d s a c" unfolding mustnot_d_def by blast
  then show "\<exists>\<pi> r. (\<pi>, r) \<in> mustnot_d s a c \<and> \<pi> \<noteq> [] \<and> hd \<pi> = x" by fastforce
qed

lemma total_then:
  assumes "total T\<^sub>1" and "total T\<^sub>2"
  shows "total (then_d T\<^sub>1 T\<^sub>2)"
proof (rule totalI)
  fix x
  from assms(1) obtain \<pi>\<^sub>1 r\<^sub>1 where m1: "(\<pi>\<^sub>1, r\<^sub>1) \<in> T\<^sub>1" "\<pi>\<^sub>1 \<noteq> []" "hd \<pi>\<^sub>1 = x"
    by (rule totalE)
  show "\<exists>\<pi> r. (\<pi>, r) \<in> then_d T\<^sub>1 T\<^sub>2 \<and> \<pi> \<noteq> [] \<and> hd \<pi> = x"
  proof (cases "r\<^sub>1 = Done")
    case False
    with m1 have "(\<pi>\<^sub>1, r\<^sub>1) \<in> then_d T\<^sub>1 T\<^sub>2" by (simp add: then_d_iff)
    with m1 show ?thesis by blast
  next
    case True
    from assms(2) obtain \<pi>\<^sub>2 r\<^sub>2 where m2: "(\<pi>\<^sub>2, r\<^sub>2) \<in> T\<^sub>2" "\<pi>\<^sub>2 \<noteq> []" "hd \<pi>\<^sub>2 = last \<pi>\<^sub>1"
      by (rule totalE)
    with m1 have fus: "fusable \<pi>\<^sub>1 \<pi>\<^sub>2" by (simp add: fusable_def)
    have "(fuse \<pi>\<^sub>1 \<pi>\<^sub>2, r\<^sub>2) \<in> then_d T\<^sub>1 T\<^sub>2"
      unfolding then_d_iff using m1(1) True m2(1) fus by blast
    moreover have "fuse \<pi>\<^sub>1 \<pi>\<^sub>2 \<noteq> []" "hd (fuse \<pi>\<^sub>1 \<pi>\<^sub>2) = x"
      using m1 by (simp_all add: fuse_nonempty hd_fuse)
    ultimately show ?thesis by blast
  qed
qed

lemma total_or:
  assumes "total T\<^sub>1" and "total T\<^sub>2"
  shows "total (or_d T\<^sub>1 T\<^sub>2)"
proof (rule totalI)
  fix x
  from assms(1) obtain \<pi> r where "(\<pi>, r) \<in> T\<^sub>1" "\<pi> \<noteq> []" "hd \<pi> = x" by (rule totalE)
  then show "\<exists>\<pi> r. (\<pi>, r) \<in> or_d T\<^sub>1 T\<^sub>2 \<and> \<pi> \<noteq> [] \<and> hd \<pi> = x"
    unfolding or_d_def by blast
qed

lemma total_unless:
  assumes "total T" and "total E"
  shows "total (unless_d T c E)"
proof (rule totalI)
  fix x
  from assms(1) obtain \<pi> r where m: "(\<pi>, r) \<in> T" "\<pi> \<noteq> []" "hd \<pi> = x" by (rule totalE)
  show "\<exists>\<pi> r. (\<pi>, r) \<in> unless_d T c E \<and> \<pi> \<noteq> [] \<and> hd \<pi> = x"
  proof (cases "\<exists>j. fires c \<pi> j")
    case False
    then have "(\<pi>, r) \<in> unless_d T c E"
      unfolding unless_d_iff using m(1) by blast
    with m show ?thesis by blast
  next
    case True
    then obtain j where j: "fires c \<pi> j" ..
    define k where "k = first_fire c \<pi>"
    have kl: "k < length \<pi>"
      using fires_less[OF first_fire_fires[OF j]] unfolding k_def by simp
    from assms(2) obtain \<pi>' r' where e: "(\<pi>', r') \<in> E" "\<pi>' \<noteq> []" "hd \<pi>' = \<pi> ! k"
      by (rule totalE)
    have fus: "fusable (pre \<pi> (first_fire c \<pi>)) \<pi>'"
      using kl e unfolding k_def by (simp add: fusable_pre)
    have "(fuse (pre \<pi> (first_fire c \<pi>)) \<pi>', kappa r') \<in> unless_d T c E"
      unfolding unless_d_iff using m(1) True e(1) fus by blast
    moreover have "fuse (pre \<pi> (first_fire c \<pi>)) \<pi>' \<noteq> []"
      using m(2) by (simp add: fuse_nonempty pre_nonempty)
    moreover have "hd (fuse (pre \<pi> (first_fire c \<pi>)) \<pi>') = x"
      using m(2,3) by (simp add: hd_fuse pre_nonempty hd_pre)
    ultimately show ?thesis by blast
  qed
qed

context interleaving
begin

lemma total_and:
  assumes "total T\<^sub>1" and "total T\<^sub>2"
  shows "total (and_d T\<^sub>1 T\<^sub>2)"
proof (rule totalI)
  fix x
  from interleave_from_start[OF assms, of x] obtain \<pi>\<^sub>1 o\<^sub>1 \<pi>\<^sub>2 o\<^sub>2 \<pi> where
    m: "(\<pi>\<^sub>1, o\<^sub>1) \<in> T\<^sub>1" "(\<pi>\<^sub>2, o\<^sub>2) \<in> T\<^sub>2" "\<pi> \<in> interleave \<pi>\<^sub>1 \<pi>\<^sub>2" "\<pi> \<noteq> []" "hd \<pi> = x"
    by blast
  then have "(\<pi>, ojoin o\<^sub>1 o\<^sub>2) \<in> and_d T\<^sub>1 T\<^sub>2"
    unfolding and_d_def by blast
  with m(4,5) show "\<exists>\<pi> r. (\<pi>, r) \<in> and_d T\<^sub>1 T\<^sub>2 \<and> \<pi> \<noteq> [] \<and> hd \<pi> = x" by blast
qed

end

text \<open>The assumption on \<open>interleave\<close> is satisfiable (so the locale is not vacuous):
  for instance by the function that returns its first argument. This is only a
  consistency witness, not a proposed meaning of AND.\<close>

lemma interleaving_satisfiable:
  "interleaving ((\<lambda>\<pi>\<^sub>1 \<pi>\<^sub>2. {\<pi>\<^sub>1}) ::
     ('n, 'v, 't, 's, 'a) trace \<Rightarrow> ('n, 'v, 't, 's, 'a) trace \<Rightarrow> ('n, 'v, 't, 's, 'a) trace set)"
proof
  fix T\<^sub>1 T\<^sub>2 :: "('n, 'v, 't, 's, 'a) den" and x :: "('n, 'v, 't, 's, 'a) entry"
  assume "total T\<^sub>1" "total T\<^sub>2"
  then obtain \<pi>\<^sub>1 o\<^sub>1 \<pi>\<^sub>2 o\<^sub>2 where
    "(\<pi>\<^sub>1, o\<^sub>1) \<in> T\<^sub>1" "\<pi>\<^sub>1 \<noteq> []" "hd \<pi>\<^sub>1 = x" "(\<pi>\<^sub>2, o\<^sub>2) \<in> T\<^sub>2" "\<pi>\<^sub>2 \<noteq> []" "hd \<pi>\<^sub>2 = x"
    by (meson totalE)
  then show "\<exists>\<pi>\<^sub>1 o\<^sub>1 \<pi>\<^sub>2 o\<^sub>2 \<pi>. (\<pi>\<^sub>1, o\<^sub>1) \<in> T\<^sub>1 \<and> (\<pi>\<^sub>2, o\<^sub>2) \<in> T\<^sub>2 \<and> \<pi>\<^sub>1 \<noteq> [] \<and> \<pi>\<^sub>2 \<noteq> []
      \<and> hd \<pi>\<^sub>1 = x \<and> hd \<pi>\<^sub>2 = x \<and> \<pi> \<in> {\<pi>\<^sub>1} \<and> \<pi> \<noteq> [] \<and> hd \<pi> = x"
    by blast
qed


section \<open>Distributivity of UNLESS over THEN\<close>

text \<open>The fused trace \<open>\<pi>\<^sub>1 \<frown> \<pi>\<^sub>2\<close> is watched at entries \<open>0 \<dots> m-1\<close> as \<open>\<pi>\<^sub>1\<close> and from
  \<open>m\<close> on as \<open>\<pi>\<^sub>2\<close>, where \<open>m = |\<pi>\<^sub>1| - 1\<close> is the junction (lemmas \<open>fires_fuse_left\<close>,
  \<open>fires_fuse_right\<close>). If the guard first holds inside \<open>t\<^sub>1\<close>, both sides interrupt at
  the same entry with the same prefix (\<open>first_fire_fuse_left\<close>, \<open>pre_fuse_left\<close>). If it
  first holds at the junction or later, \<open>t\<^sub>1\<close> has completed and the second UNLESS
  interrupts \<open>t\<^sub>2\<close> at the corresponding entry (\<open>first_fire_fuse_right\<close>,
  \<open>pre_fuse_right\<close>, \<open>fuse_assoc\<close>). An interrupted \<open>t\<^sub>1\<close> never ends Done, so THEN passes it
  through unchanged.

  Section 2.5 states the law without side conditions. It needs one: on the left, the
  interrupted traces of \<open>t\<^sub>1\<close> come from \<open>t\<^sub>1 THEN t\<^sub>2\<close>, which contains a Done trace of \<open>t\<^sub>1\<close>
  only if some trace of \<open>t\<^sub>2\<close> can follow it. Totality of \<open>t\<^sub>2\<close> guarantees that; without it
  the law fails (\<open>unless_then_counterexample\<close> below).\<close>

(* §2.5, law 3 *)
theorem unless_then:
  assumes tot: "total T\<^sub>2"
  shows "unless_d (then_d T\<^sub>1 T\<^sub>2) c E = then_d (unless_d T\<^sub>1 c E) (unless_d T\<^sub>2 c E)"
proof (rule subset_antisym; rule subrelI)
  fix \<pi> r assume "(\<pi>, r) \<in> unless_d (then_d T\<^sub>1 T\<^sub>2) c E"
  then consider
      (keep) "(\<pi>, r) \<in> then_d T\<^sub>1 T\<^sub>2" "\<forall>j. \<not> fires c \<pi> j"
    | (int) \<pi>\<^sub>0 r\<^sub>0 \<pi>' r' where "(\<pi>\<^sub>0, r\<^sub>0) \<in> then_d T\<^sub>1 T\<^sub>2" "\<exists>j. fires c \<pi>\<^sub>0 j" "(\<pi>', r') \<in> E"
        "fusable (pre \<pi>\<^sub>0 (first_fire c \<pi>\<^sub>0)) \<pi>'"
        "\<pi> = fuse (pre \<pi>\<^sub>0 (first_fire c \<pi>\<^sub>0)) \<pi>'" "r = kappa r'"
    unfolding unless_d_iff[where T = "then_d T\<^sub>1 T\<^sub>2"] by blast
  then show "(\<pi>, r) \<in> then_d (unless_d T\<^sub>1 c E) (unless_d T\<^sub>2 c E)"
  proof cases
    case keep
    from keep(1) consider
        (seq) \<pi>\<^sub>1 \<pi>\<^sub>2 where "(\<pi>\<^sub>1, Done) \<in> T\<^sub>1" "(\<pi>\<^sub>2, r) \<in> T\<^sub>2" "fusable \<pi>\<^sub>1 \<pi>\<^sub>2" "\<pi> = fuse \<pi>\<^sub>1 \<pi>\<^sub>2"
      | (left) "(\<pi>, r) \<in> T\<^sub>1" "r \<noteq> Done"
      unfolding then_d_iff by blast
    then show ?thesis
    proof cases
      case seq
      have "\<not> (\<exists>j. fires c (fuse \<pi>\<^sub>1 \<pi>\<^sub>2) j)" using keep(2) unfolding seq(4) by blast
      then have nf: "\<not> (\<exists>j. fires c \<pi>\<^sub>1 j)" "\<not> (\<exists>i. fires c \<pi>\<^sub>2 i)"
        unfolding fires_fuse_ex[OF seq(3)] by blast+
      have u1: "(\<pi>\<^sub>1, Done) \<in> unless_d T\<^sub>1 c E"
        unfolding unless_d_iff using seq(1) nf(1) by blast
      have u2: "(\<pi>\<^sub>2, r) \<in> unless_d T\<^sub>2 c E"
        unfolding unless_d_iff using seq(2) nf(2) by blast
      show ?thesis
        unfolding then_d_iff using u1 u2 seq(3,4) by blast
    next
      case left
      have "(\<pi>, r) \<in> unless_d T\<^sub>1 c E"
        unfolding unless_d_iff using left(1) keep(2) by blast
      with left(2) show ?thesis by (simp add: then_d_iff)
    qed
  next
    case int
    from int(1) consider
        (seq) \<pi>\<^sub>1 \<pi>\<^sub>2 where "(\<pi>\<^sub>1, Done) \<in> T\<^sub>1" "(\<pi>\<^sub>2, r\<^sub>0) \<in> T\<^sub>2" "fusable \<pi>\<^sub>1 \<pi>\<^sub>2" "\<pi>\<^sub>0 = fuse \<pi>\<^sub>1 \<pi>\<^sub>2"
      | (left) "(\<pi>\<^sub>0, r\<^sub>0) \<in> T\<^sub>1" "r\<^sub>0 \<noteq> Done"
      unfolding then_d_iff by blast
    then show ?thesis
    proof cases
      case left
      text \<open>\<open>t\<^sub>1\<close> did not complete normally: this is an interruption of the first UNLESS.\<close>
      have "(\<pi>, r) \<in> unless_d T\<^sub>1 c E"
        unfolding unless_d_iff using left(1) int(2-6) by blast
      with int(6) show ?thesis by (simp add: then_d_iff)
    next
      case seq
      note fus12 = seq(3)
      show ?thesis
      proof (cases "\<exists>j. fires c \<pi>\<^sub>1 j")
        case True
        text \<open>The guard first holds inside \<open>t\<^sub>1\<close>, before its completing entry.\<close>
        then obtain j where j: "fires c \<pi>\<^sub>1 j" ..
        have ff: "first_fire c \<pi>\<^sub>0 = first_fire c \<pi>\<^sub>1"
          unfolding seq(4) by (rule first_fire_fuse_left[OF fus12 j])
        have kl: "first_fire c \<pi>\<^sub>1 < length \<pi>\<^sub>1"
          using fires_less[OF first_fire_fires[OF j]] by simp
        have pp: "pre \<pi>\<^sub>0 (first_fire c \<pi>\<^sub>1) = pre \<pi>\<^sub>1 (first_fire c \<pi>\<^sub>1)"
          unfolding seq(4) by (rule pre_fuse_left[OF kl])
        have fusA: "fusable (pre \<pi>\<^sub>1 (first_fire c \<pi>\<^sub>1)) \<pi>'"
          using int(4) unfolding ff pp .
        have eqA: "\<pi> = fuse (pre \<pi>\<^sub>1 (first_fire c \<pi>\<^sub>1)) \<pi>'"
          using int(5) unfolding ff pp .
        have "(\<pi>, r) \<in> unless_d T\<^sub>1 c E"
          unfolding unless_d_iff using seq(1) True int(3) fusA eqA int(6) by blast
        with int(6) show ?thesis by (simp add: then_d_iff)
      next
        case False
        text \<open>\<open>t\<^sub>1\<close> completes uninterrupted; the guard first holds at the junction or
          later, inside \<open>t\<^sub>2\<close>.\<close>
        have "\<exists>j. fires c (fuse \<pi>\<^sub>1 \<pi>\<^sub>2) j" using int(2) unfolding seq(4) .
        with False obtain i where i: "fires c \<pi>\<^sub>2 i"
          unfolding fires_fuse_ex[OF fus12] by blast
        have nf1: "\<forall>j. \<not> fires c \<pi>\<^sub>1 j" using False by blast
        have ff: "first_fire c (fuse \<pi>\<^sub>1 \<pi>\<^sub>2) = length \<pi>\<^sub>1 - 1 + first_fire c \<pi>\<^sub>2"
          by (rule first_fire_fuse_right[OF fus12 nf1 i])
        have il: "first_fire c \<pi>\<^sub>2 < length \<pi>\<^sub>2"
          using fires_less[OF first_fire_fires[OF i]] by simp
        have pp: "pre (fuse \<pi>\<^sub>1 \<pi>\<^sub>2) (first_fire c (fuse \<pi>\<^sub>1 \<pi>\<^sub>2))
            = fuse \<pi>\<^sub>1 (pre \<pi>\<^sub>2 (first_fire c \<pi>\<^sub>2))"
          unfolding ff by (rule pre_fuse_right[OF fus12 il])
        have ne: "pre \<pi>\<^sub>2 (first_fire c \<pi>\<^sub>2) \<noteq> []"
          using il by (intro pre_nonempty) auto
        have fus1p: "fusable \<pi>\<^sub>1 (pre \<pi>\<^sub>2 (first_fire c \<pi>\<^sub>2))"
          using fus12 il by (auto simp: fusable_def hd_pre pre_nonempty)
        have fus0: "fusable (fuse \<pi>\<^sub>1 (pre \<pi>\<^sub>2 (first_fire c \<pi>\<^sub>2))) \<pi>'"
          using int(4) unfolding seq(4) pp .
        have fus2: "fusable (pre \<pi>\<^sub>2 (first_fire c \<pi>\<^sub>2)) \<pi>'"
          using fus0 unfolding fusable_fuse_left[OF fus1p] .
        have u2: "(fuse (pre \<pi>\<^sub>2 (first_fire c \<pi>\<^sub>2)) \<pi>', kappa r') \<in> unless_d T\<^sub>2 c E"
          unfolding unless_d_iff using seq(2) i int(3) fus2 by blast
        have u1: "(\<pi>\<^sub>1, Done) \<in> unless_d T\<^sub>1 c E"
          unfolding unless_d_iff using seq(1) nf1 by blast
        have fusX: "fusable \<pi>\<^sub>1 (fuse (pre \<pi>\<^sub>2 (first_fire c \<pi>\<^sub>2)) \<pi>')"
          using fus1p unfolding fusable_fuse_right[OF ne] .
        have eq0: "\<pi> = fuse (fuse \<pi>\<^sub>1 (pre \<pi>\<^sub>2 (first_fire c \<pi>\<^sub>2))) \<pi>'"
          using int(5) unfolding seq(4) pp .
        have eq: "\<pi> = fuse \<pi>\<^sub>1 (fuse (pre \<pi>\<^sub>2 (first_fire c \<pi>\<^sub>2)) \<pi>')"
          using eq0 unfolding fuse_assoc[OF ne] .
        have u2': "(fuse (pre \<pi>\<^sub>2 (first_fire c \<pi>\<^sub>2)) \<pi>', r) \<in> unless_d T\<^sub>2 c E"
          using u2 int(6) by simp
        show ?thesis
          unfolding then_d_iff using u1 u2' fusX eq by blast
      qed
    qed
  qed
next
  fix \<pi> r assume "(\<pi>, r) \<in> then_d (unless_d T\<^sub>1 c E) (unless_d T\<^sub>2 c E)"
  then consider
      (seq) \<pi>\<^sub>1 \<pi>\<^sub>2' where "(\<pi>\<^sub>1, Done) \<in> unless_d T\<^sub>1 c E" "(\<pi>\<^sub>2', r) \<in> unless_d T\<^sub>2 c E"
        "fusable \<pi>\<^sub>1 \<pi>\<^sub>2'" "\<pi> = fuse \<pi>\<^sub>1 \<pi>\<^sub>2'"
    | (left) "(\<pi>, r) \<in> unless_d T\<^sub>1 c E" "r \<noteq> Done"
    unfolding then_d_iff by blast
  then show "(\<pi>, r) \<in> unless_d (then_d T\<^sub>1 T\<^sub>2) c E"
  proof cases
    case seq
    text \<open>A Done trace of the first UNLESS is an uninterrupted trace of \<open>t\<^sub>1\<close>.\<close>
    from seq(1) have t1: "(\<pi>\<^sub>1, Done) \<in> T\<^sub>1" and nf1: "\<forall>j. \<not> fires c \<pi>\<^sub>1 j"
      unfolding unless_d_iff by auto
    from seq(2) consider
        (keep2) "(\<pi>\<^sub>2', r) \<in> T\<^sub>2" "\<forall>j. \<not> fires c \<pi>\<^sub>2' j"
      | (int2) \<pi>\<^sub>2 r\<^sub>2 \<pi>' r' where "(\<pi>\<^sub>2, r\<^sub>2) \<in> T\<^sub>2" "\<exists>j. fires c \<pi>\<^sub>2 j" "(\<pi>', r') \<in> E"
          "fusable (pre \<pi>\<^sub>2 (first_fire c \<pi>\<^sub>2)) \<pi>'"
          "\<pi>\<^sub>2' = fuse (pre \<pi>\<^sub>2 (first_fire c \<pi>\<^sub>2)) \<pi>'" "r = kappa r'"
      unfolding unless_d_iff by blast
    then show ?thesis
    proof cases
      case keep2
      have th: "(\<pi>, r) \<in> then_d T\<^sub>1 T\<^sub>2"
        unfolding then_d_iff using t1 keep2(1) seq(3,4) by blast
      have "\<not> (\<exists>j. fires c (fuse \<pi>\<^sub>1 \<pi>\<^sub>2') j)"
        unfolding fires_fuse_ex[OF seq(3)] using nf1 keep2(2) by blast
      then have "\<forall>j. \<not> fires c \<pi> j" unfolding seq(4) by blast
      with th show ?thesis
        unfolding unless_d_iff[where T = "then_d T\<^sub>1 T\<^sub>2"] by blast
    next
      case int2
      from int2(2) obtain i where i: "fires c \<pi>\<^sub>2 i" ..
      have il: "first_fire c \<pi>\<^sub>2 < length \<pi>\<^sub>2"
        using fires_less[OF first_fire_fires[OF i]] by simp
      have ne: "pre \<pi>\<^sub>2 (first_fire c \<pi>\<^sub>2) \<noteq> []"
        using il by (intro pre_nonempty) auto
      have fus1p: "fusable \<pi>\<^sub>1 (pre \<pi>\<^sub>2 (first_fire c \<pi>\<^sub>2))"
        using seq(3) unfolding int2(5) fusable_fuse_right[OF ne] .
      have ne2: "\<pi>\<^sub>2 \<noteq> []" using il by auto
      have fus12: "fusable \<pi>\<^sub>1 \<pi>\<^sub>2"
        using fus1p ne2 by (auto simp: fusable_def hd_pre)
      have th: "(fuse \<pi>\<^sub>1 \<pi>\<^sub>2, r\<^sub>2) \<in> then_d T\<^sub>1 T\<^sub>2"
        unfolding then_d_iff using t1 int2(1) fus12 by blast
      have fi: "\<exists>j. fires c (fuse \<pi>\<^sub>1 \<pi>\<^sub>2) j"
        unfolding fires_fuse_ex[OF fus12] using i by blast
      have ff: "first_fire c (fuse \<pi>\<^sub>1 \<pi>\<^sub>2) = length \<pi>\<^sub>1 - 1 + first_fire c \<pi>\<^sub>2"
        by (rule first_fire_fuse_right[OF fus12 nf1 i])
      have pp: "pre (fuse \<pi>\<^sub>1 \<pi>\<^sub>2) (first_fire c (fuse \<pi>\<^sub>1 \<pi>\<^sub>2))
          = fuse \<pi>\<^sub>1 (pre \<pi>\<^sub>2 (first_fire c \<pi>\<^sub>2))"
        unfolding ff by (rule pre_fuse_right[OF fus12 il])
      have fusA: "fusable (pre (fuse \<pi>\<^sub>1 \<pi>\<^sub>2) (first_fire c (fuse \<pi>\<^sub>1 \<pi>\<^sub>2))) \<pi>'"
        unfolding pp fusable_fuse_left[OF fus1p] by (rule int2(4))
      have eqA: "\<pi> = fuse (pre (fuse \<pi>\<^sub>1 \<pi>\<^sub>2) (first_fire c (fuse \<pi>\<^sub>1 \<pi>\<^sub>2))) \<pi>'"
        unfolding pp fuse_assoc[OF ne] using seq(4) int2(5) by simp
      show ?thesis
        unfolding unless_d_iff[where T = "then_d T\<^sub>1 T\<^sub>2"]
        using th fi int2(3) fusA eqA int2(6) by blast
    qed
  next
    case left
    from left(1) consider
        (keep1) "(\<pi>, r) \<in> T\<^sub>1" "\<forall>j. \<not> fires c \<pi> j"
      | (int1) \<pi>\<^sub>1 r\<^sub>1 \<pi>' r' where "(\<pi>\<^sub>1, r\<^sub>1) \<in> T\<^sub>1" "\<exists>j. fires c \<pi>\<^sub>1 j" "(\<pi>', r') \<in> E"
          "fusable (pre \<pi>\<^sub>1 (first_fire c \<pi>\<^sub>1)) \<pi>'"
          "\<pi> = fuse (pre \<pi>\<^sub>1 (first_fire c \<pi>\<^sub>1)) \<pi>'" "r = kappa r'"
      unfolding unless_d_iff by blast
    then show ?thesis
    proof cases
      case keep1
      have "(\<pi>, r) \<in> then_d T\<^sub>1 T\<^sub>2"
        unfolding then_d_iff using keep1(1) left(2) by blast
      with keep1(2) show ?thesis
        unfolding unless_d_iff[where T = "then_d T\<^sub>1 T\<^sub>2"] by blast
    next
      case int1
      from int1(2) obtain j where j: "fires c \<pi>\<^sub>1 j" ..
      have kl: "first_fire c \<pi>\<^sub>1 < length \<pi>\<^sub>1"
        using fires_less[OF first_fire_fires[OF j]] by simp
      show ?thesis
      proof (cases "r\<^sub>1 = Done")
        case False
        then have "(\<pi>\<^sub>1, r\<^sub>1) \<in> then_d T\<^sub>1 T\<^sub>2"
          unfolding then_d_iff using int1(1) by blast
        then show ?thesis
          unfolding unless_d_iff[where T = "then_d T\<^sub>1 T\<^sub>2"] using int1(2-6) by blast
      next
        case True
        text \<open>Here totality of \<open>t\<^sub>2\<close> is used: some trace of \<open>t\<^sub>2\<close> starts where \<open>\<pi>\<^sub>1\<close> ends,
          so \<open>\<pi>\<^sub>1\<close> extends to a trace of \<open>t\<^sub>1 THEN t\<^sub>2\<close> with the same interruption.\<close>
        have ne1: "\<pi>\<^sub>1 \<noteq> []" using kl by auto
        from tot obtain \<pi>\<^sub>2 r\<^sub>2 where m2: "(\<pi>\<^sub>2, r\<^sub>2) \<in> T\<^sub>2" "\<pi>\<^sub>2 \<noteq> []" "hd \<pi>\<^sub>2 = last \<pi>\<^sub>1"
          by (rule totalE)
        have fus12: "fusable \<pi>\<^sub>1 \<pi>\<^sub>2" using ne1 m2 by (simp add: fusable_def)
        have th: "(fuse \<pi>\<^sub>1 \<pi>\<^sub>2, r\<^sub>2) \<in> then_d T\<^sub>1 T\<^sub>2"
          unfolding then_d_iff using int1(1) True m2(1) fus12 by blast
        have fi: "\<exists>j. fires c (fuse \<pi>\<^sub>1 \<pi>\<^sub>2) j"
          unfolding fires_fuse_ex[OF fus12] using j by blast
        have ff: "first_fire c (fuse \<pi>\<^sub>1 \<pi>\<^sub>2) = first_fire c \<pi>\<^sub>1"
          by (rule first_fire_fuse_left[OF fus12 j])
        have pp: "pre (fuse \<pi>\<^sub>1 \<pi>\<^sub>2) (first_fire c \<pi>\<^sub>1) = pre \<pi>\<^sub>1 (first_fire c \<pi>\<^sub>1)"
          by (rule pre_fuse_left[OF kl])
        have fusA: "fusable (pre (fuse \<pi>\<^sub>1 \<pi>\<^sub>2) (first_fire c (fuse \<pi>\<^sub>1 \<pi>\<^sub>2))) \<pi>'"
          unfolding ff pp by (rule int1(4))
        have eqA: "\<pi> = fuse (pre (fuse \<pi>\<^sub>1 \<pi>\<^sub>2) (first_fire c (fuse \<pi>\<^sub>1 \<pi>\<^sub>2))) \<pi>'"
          unfolding ff pp by (rule int1(5))
        show ?thesis
          unfolding unless_d_iff[where T = "then_d T\<^sub>1 T\<^sub>2"]
          using th fi int1(3) fusA eqA int1(6) by blast
      qed
    qed
  qed
qed

text \<open>Without totality of \<open>t\<^sub>2\<close> the law fails. Take \<open>\<lbrakk>t\<^sub>1\<rbrakk> = {(\<langle>x, x\<rangle>, Done)}\<close>,
  \<open>\<lbrakk>t\<^sub>2\<rbrakk> = \<emptyset>\<close> (not total), \<open>\<lbrakk>e\<rbrakk> = {(\<langle>x\<rangle>, Done)}\<close> and the guard \<open>true\<close>: the left side
  is empty, while the right side contains \<open>(\<langle>x\<rangle>, Interrupted)\<close>.\<close>

theorem unless_then_counterexample:
  fixes x :: "('n, 'v, 't, 's, 'a) entry"
  defines "T\<^sub>1 \<equiv> {([x, x], Done)}" and "E \<equiv> {([x], Done)}"
  shows "\<not> total ({} :: ('n, 'v, 't, 's, 'a) den)"
    and "unless_d (then_d T\<^sub>1 {}) ETrue E = {}"
    and "([x], Interrupted) \<in> then_d (unless_d T\<^sub>1 ETrue E) (unless_d {} ETrue E)"
proof -
  show "\<not> total ({} :: ('n, 'v, 't, 's, 'a) den)"
    by (simp add: total_def)
  have "then_d T\<^sub>1 {} = {}"
    by (auto simp: then_d_def T\<^sub>1_def)
  then show "unless_d (then_d T\<^sub>1 {}) ETrue E = {}"
    by (simp add: unless_d_def)
  have f0: "fires ETrue [x, x] 0" by (simp add: fires_def)
  have ff: "first_fire ETrue [x, x] = 0"
    by (rule first_fire_eqI[OF f0]) simp
  have pre0: "pre [x, x] 0 = [x]" by (simp add: pre_def)
  have "([x], Interrupted) \<in> unless_d T\<^sub>1 ETrue E"
  proof -
    have "([x, x], Done) \<in> T\<^sub>1" "([x], Done) \<in> E" by (simp_all add: T\<^sub>1_def E_def)
    moreover have "fusable (pre [x, x] (first_fire ETrue [x, x])) [x]"
      by (simp add: ff pre0 fusable_def)
    moreover have "[x] = fuse (pre [x, x] (first_fire ETrue [x, x])) [x]"
      by (simp add: ff pre0 fuse_def)
    moreover have "Interrupted = kappa Done" by simp
    ultimately show ?thesis
      unfolding unless_d_iff using f0 by blast
  qed
  then show "([x], Interrupted) \<in> then_d (unless_d T\<^sub>1 ETrue E) (unless_d {} ETrue E)"
    by (simp add: then_d_iff)
qed

corollary unless_then_not_unconditional:
  "\<exists>(T\<^sub>1 :: ('n, 'v, 't, 's, 'a) den) T\<^sub>2 c E.
     unless_d (then_d T\<^sub>1 T\<^sub>2) c E \<noteq> then_d (unless_d T\<^sub>1 c E) (unless_d T\<^sub>2 c E)"
proof -
  fix x :: "('n, 'v, 't, 's, 'a) entry"
  from unless_then_counterexample(2,3)[of x] show ?thesis by blast
qed


section \<open>A non-law\<close>

text \<open>\<open>(t UNLESS c DO e) UNLESS d DO e\<close> differs from \<open>t UNLESS (c OR d) DO e\<close>: the outer
  guard \<open>d\<close> is still watched while the inner handler \<open>e\<close> runs, and can interrupt it.
  Example: \<open>a\<close> and \<open>b\<close> are entries whose states differ only in whether name \<open>n\<close> is
  present; \<open>\<lbrakk>t\<rbrakk> = {(\<langle>a, a\<rangle>, Done)}\<close>, \<open>\<lbrakk>e\<rbrakk> = {(\<langle>a, b, b\<rangle>, Done), (\<langle>b\<rangle>, Done)}\<close>, \<open>c = true\<close>,
  \<open>d = PRESENT(n)\<close>. The handler trace \<open>\<langle>a, b, b\<rangle>\<close> is cut by \<open>d\<close> at \<open>b\<close> on the left only.\<close>

(* §2.5, non-law *)
theorem unless_nested_ne_or:
  fixes n :: 'n and v :: 'v and t :: 't and ev :: "('n, 's, 'a) event"
  defines "a \<equiv> (Map.empty :: ('n, 'v) state, t, ev)" and "b \<equiv> ([n \<mapsto> v], t, ev)"
  defines "T \<equiv> {([a, a], Done)}" and "E \<equiv> {([a, b, b], Done), ([b], Done)}"
  shows "unless_d (unless_d T ETrue E) (EPresent n) E \<noteq> unless_d T (EOr ETrue (EPresent n)) E"
proof
  assume eq: "unless_d (unless_d T ETrue E) (EPresent n) E = unless_d T (EOr ETrue (EPresent n)) E"
  have ab: "a \<noteq> b"
  proof
    assume "a = b"
    then have "(Map.empty :: ('n, 'v) state) n = [n \<mapsto> v] n" by (simp add: a_def b_def)
    then show False by simp
  qed
  text \<open>Inner UNLESS: \<open>true\<close> fires at entry 0 of \<open>\<langle>a, a\<rangle>\<close>; the handler starts at \<open>a\<close>.\<close>
  have f0: "fires ETrue [a, a] 0" by (simp add: fires_def)
  have ff0: "first_fire ETrue [a, a] = 0" by (rule first_fire_eqI[OF f0]) simp
  have pre0: "pre [a, a] 0 = [a]" by (simp add: pre_def)
  have inner: "([a, b, b], Interrupted) \<in> unless_d T ETrue E"
  proof -
    have "([a, a], Done) \<in> T" "([a, b, b], Done) \<in> E" by (simp_all add: T_def E_def)
    moreover have "fusable (pre [a, a] (first_fire ETrue [a, a])) [a, b, b]"
      by (simp add: ff0 pre0 fusable_def)
    moreover have "[a, b, b] = fuse (pre [a, a] (first_fire ETrue [a, a])) [a, b, b]"
      by (simp add: ff0 pre0 fuse_def)
    moreover have "Interrupted = kappa Done" by simp
    ultimately show ?thesis unfolding unless_d_iff using f0 by blast
  qed
  text \<open>Outer UNLESS: \<open>PRESENT(n)\<close> is false at \<open>a\<close> and true at \<open>b\<close>, so it fires at entry 1.\<close>
  have g1: "fires (EPresent n) [a, b, b] 1" by (simp add: fires_def st_def b_def)
  have g0: "\<not> fires (EPresent n) [a, b, b] 0" by (simp add: fires_def st_def a_def)
  have ff1: "first_fire (EPresent n) [a, b, b] = 1"
    by (rule first_fire_eqI[OF g1]) (use g0 in \<open>auto simp: less_Suc_eq\<close>)
  have pre1: "pre [a, b, b] 1 = [a, b]" by (simp add: pre_def)
  have lhs: "([a, b], Interrupted) \<in> unless_d (unless_d T ETrue E) (EPresent n) E"
  proof -
    have "([b], Done) \<in> E" by (simp add: E_def)
    moreover have "fusable (pre [a, b, b] (first_fire (EPresent n) [a, b, b])) [b]"
      by (simp add: ff1 pre_def fusable_def)
    moreover have "[a, b] = fuse (pre [a, b, b] (first_fire (EPresent n) [a, b, b])) [b]"
      by (simp add: ff1 pre_def fuse_def)
    moreover have "Interrupted = kappa Done" by simp
    ultimately show ?thesis
      unfolding unless_d_iff[where T = "unless_d T ETrue E"] using inner g1 by blast
  qed
  text \<open>With the combined guard, \<open>t\<close> is interrupted at entry 0 and the only handler
    trace starting at \<open>a\<close> is \<open>\<langle>a, b, b\<rangle>\<close>, so \<open>(\<langle>a, b\<rangle>, Interrupted)\<close> is not on the right.\<close>
  have h0: "fires (EOr ETrue (EPresent n)) [a, a] 0" by (simp add: fires_def kor_def)
  have hff: "first_fire (EOr ETrue (EPresent n)) [a, a] = 0"
    by (rule first_fire_eqI[OF h0]) simp
  have rhs: "([a, b], Interrupted) \<notin> unless_d T (EOr ETrue (EPresent n)) E"
  proof
    assume "([a, b], Interrupted) \<in> unless_d T (EOr ETrue (EPresent n)) E"
    then consider
        (keep) "([a, b], Interrupted) \<in> T"
      | (int) \<pi>\<^sub>0 r\<^sub>0 \<pi>' r' where "(\<pi>\<^sub>0, r\<^sub>0) \<in> T" "(\<pi>', r') \<in> E"
          "fusable (pre \<pi>\<^sub>0 (first_fire (EOr ETrue (EPresent n)) \<pi>\<^sub>0)) \<pi>'"
          "[a, b] = fuse (pre \<pi>\<^sub>0 (first_fire (EOr ETrue (EPresent n)) \<pi>\<^sub>0)) \<pi>'"
      unfolding unless_d_iff by blast
    then show False
    proof cases
      case keep
      then show False by (simp add: T_def)
    next
      case int
      from int(1) have p0: "\<pi>\<^sub>0 = [a, a]" by (simp add: T_def)
      have fus: "fusable [a] \<pi>'" using int(3) by (simp add: p0 hff pre0)
      have eqf: "[a, b] = fuse [a] \<pi>'" using int(4) by (simp add: p0 hff pre0)
      from int(2) have "\<pi>' = [a, b, b] \<or> \<pi>' = [b]" by (auto simp: E_def)
      then show False
      proof
        assume "\<pi>' = [a, b, b]"
        with eqf show False by (simp add: fuse_def)
      next
        assume "\<pi>' = [b]"
        with fus ab show False by (simp add: fusable_def)
      qed
    qed
  qed
  from lhs rhs eq show False by simp
qed


section \<open>Traces stay well formed\<close>

text \<open>The operations preserve the trace invariant (non-empty, non-decreasing timestamps).\<close>

definition wf_den :: "('n, 'v, 't :: linorder, 's, 'a) den \<Rightarrow> bool" where
  "wf_den T \<longleftrightarrow> (\<forall>(\<pi>, r) \<in> T. is_trace \<pi>)"

lemma wf_denI: "(\<And>\<pi> r. (\<pi>, r) \<in> T \<Longrightarrow> is_trace \<pi>) \<Longrightarrow> wf_den T"
  by (auto simp: wf_den_def)

lemma wf_denD: "wf_den T \<Longrightarrow> (\<pi>, r) \<in> T \<Longrightarrow> is_trace \<pi>"
  by (auto simp: wf_den_def)

lemma sorted_le_last: "sorted xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> y \<le> last xs"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons z zs)
  show ?case
  proof (cases "zs = []")
    case True
    with Cons.prems show ?thesis by simp
  next
    case False
    have "z \<le> last zs" using Cons.prems(1) False by (simp add: last_in_set)
    with Cons False show ?thesis by auto
  qed
qed

lemma is_trace_fuse:
  assumes "is_trace p" and "is_trace q" and "fusable p q"
  shows "is_trace (fuse p q)"
proof -
  have sp: "sorted (map tstamp p)" and sq: "sorted (map tstamp q)"
    using assms(1,2) by (simp_all add: is_trace_def)
  from assms(3) obtain y ys where q: "q = y # ys" by (cases q) (auto simp: fusable_def)
  from assms(3) have pne: "p \<noteq> []" and lp: "last p = y" by (simp_all add: fusable_def q)
  have left: "tstamp z \<le> tstamp y" if "z \<in> set p" for z
  proof -
    have "tstamp z \<le> last (map tstamp p)"
      using sorted_le_last[OF sp] that by simp
    then show ?thesis using pne lp by (simp add: last_map)
  qed
  have right: "tstamp y \<le> tstamp w" if "w \<in> set ys" for w
    using sq that by (simp add: q)
  have sys: "sorted (map tstamp ys)" using sq by (simp add: q)
  have "\<forall>z \<in> set p. \<forall>w \<in> set ys. tstamp z \<le> tstamp w"
    using left right order_trans by blast
  with sp sys have "sorted (map tstamp p @ map tstamp ys)"
    by (simp add: sorted_append)
  then show ?thesis
    using pne by (simp add: is_trace_def fuse_def q)
qed

lemma sorted_take_prefix: "sorted xs \<Longrightarrow> sorted (take n xs)"
proof -
  assume "sorted xs"
  then have "sorted (take n xs @ drop n xs)" by simp
  then show ?thesis unfolding sorted_append by blast
qed

lemma is_trace_pre: "is_trace \<pi> \<Longrightarrow> is_trace (pre \<pi> k)"
  using sorted_take_prefix[of "map tstamp \<pi>" "Suc k"]
  by (simp add: is_trace_def pre_def take_map)

lemma wf_must: "wf_den (must_d s a)"
  by (auto simp: wf_den_def must_d_def)

lemma wf_may: "wf_den (may_d s a c)"
  by (auto simp: wf_den_def may_d_def is_trace_def)

lemma wf_mustnot: "wf_den (mustnot_d s a c)"
  by (auto simp: wf_den_def mustnot_d_def is_trace_def)

lemma wf_or: "wf_den T\<^sub>1 \<Longrightarrow> wf_den T\<^sub>2 \<Longrightarrow> wf_den (or_d T\<^sub>1 T\<^sub>2)"
  by (auto simp: wf_den_def or_d_def)

lemma wf_then:
  assumes "wf_den T\<^sub>1" and "wf_den T\<^sub>2"
  shows "wf_den (then_d T\<^sub>1 T\<^sub>2)"
proof (rule wf_denI)
  fix \<pi> r assume "(\<pi>, r) \<in> then_d T\<^sub>1 T\<^sub>2"
  then consider
      (seq) \<pi>\<^sub>1 \<pi>\<^sub>2 where "(\<pi>\<^sub>1, Done) \<in> T\<^sub>1" "(\<pi>\<^sub>2, r) \<in> T\<^sub>2" "fusable \<pi>\<^sub>1 \<pi>\<^sub>2" "\<pi> = fuse \<pi>\<^sub>1 \<pi>\<^sub>2"
    | (left) "(\<pi>, r) \<in> T\<^sub>1"
    unfolding then_d_iff by blast
  then show "is_trace \<pi>"
  proof cases
    case seq
    show ?thesis
      unfolding seq(4)
      by (rule is_trace_fuse[OF wf_denD[OF assms(1) seq(1)] wf_denD[OF assms(2) seq(2)] seq(3)])
  next
    case left
    show ?thesis by (rule wf_denD[OF assms(1) left])
  qed
qed

lemma wf_unless:
  assumes "wf_den T" and "wf_den E"
  shows "wf_den (unless_d T c E)"
proof (rule wf_denI)
  fix \<pi> r assume "(\<pi>, r) \<in> unless_d T c E"
  then consider
      (keep) "(\<pi>, r) \<in> T"
    | (int) \<pi>\<^sub>0 r\<^sub>0 \<pi>' r' where "(\<pi>\<^sub>0, r\<^sub>0) \<in> T" "(\<pi>', r') \<in> E"
        "fusable (pre \<pi>\<^sub>0 (first_fire c \<pi>\<^sub>0)) \<pi>'" "\<pi> = fuse (pre \<pi>\<^sub>0 (first_fire c \<pi>\<^sub>0)) \<pi>'"
    unfolding unless_d_iff by blast
  then show "is_trace \<pi>"
  proof cases
    case keep
    show ?thesis by (rule wf_denD[OF assms(1) keep])
  next
    case int
    have "is_trace (pre \<pi>\<^sub>0 (first_fire c \<pi>\<^sub>0))"
      by (rule is_trace_pre[OF wf_denD[OF assms(1) int(1)]])
    then show ?thesis
      unfolding int(4) by (rule is_trace_fuse[OF _ wf_denD[OF assms(2) int(2)] int(3)])
  qed
qed

end
