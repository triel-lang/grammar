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

end
