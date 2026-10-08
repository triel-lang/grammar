(*  Title:      TRIEL_Terms.thy
    Purpose:    The term language of TECHNICAL_REPORT.md section 2.5 as an inductive
                type, its denotation in the trace semantics of TRIEL_Trace, totality of
                every term, and the laws of UNLESS for terms (law 3 without side condition).
*)

theory TRIEL_Terms
  imports TRIEL_Trace
begin

section \<open>Terms\<close>

datatype ('n, 'v, 's, 'a) tm =
    TMust 's 'a                                         \<comment> \<open>subject MUST action\<close>
  | TMay 's 'a "('n, 'v) expr"                         \<comment> \<open>subject MAY action WHEN c\<close>
  | TMustNot 's 'a "('n, 'v) expr"                     \<comment> \<open>subject MUST_NOT action WHEN c\<close>
  | TThen "('n, 'v, 's, 'a) tm" "('n, 'v, 's, 'a) tm"     \<comment> \<open>t1 THEN t2\<close>
  | TOr "('n, 'v, 's, 'a) tm" "('n, 'v, 's, 'a) tm"       \<comment> \<open>t1 OR t2\<close>
  | TUnless "('n, 'v, 's, 'a) tm" "('n, 'v) expr" "('n, 'v, 's, 'a) tm"  \<comment> \<open>t1 UNLESS c DO t2\<close>
  | TAnd "('n, 'v, 's, 'a) tm" "('n, 'v, 's, 'a) tm"      \<comment> \<open>t1 AND t2\<close>


section \<open>Denotation\<close>

text \<open>The denotation needs \<open>interleave\<close> for AND, so it is defined in an extension of
  the locale \<open>interleaving\<close> with timestamps in a linear order.\<close>

locale term_semantics = interleaving interleave
  for interleave ::
    "('n, 'v, 't :: linorder, 's, 'a) trace \<Rightarrow> ('n, 'v, 't, 's, 'a) trace
       \<Rightarrow> ('n, 'v, 't, 's, 'a) trace set"
begin

primrec den :: "('n, 'v, 's, 'a) tm \<Rightarrow> ('n, 'v, 't, 's, 'a) den" where
  "den (TMust s a) = must_d s a"
| "den (TMay s a c) = may_d s a c"
| "den (TMustNot s a c) = mustnot_d s a c"
| "den (TThen t\<^sub>1 t\<^sub>2) = then_d (den t\<^sub>1) (den t\<^sub>2)"
| "den (TOr t\<^sub>1 t\<^sub>2) = or_d (den t\<^sub>1) (den t\<^sub>2)"
| "den (TUnless t\<^sub>1 c t\<^sub>2) = unless_d (den t\<^sub>1) c (den t\<^sub>2)"
| "den (TAnd t\<^sub>1 t\<^sub>2) = and_d (den t\<^sub>1) (den t\<^sub>2)"


section \<open>Totality\<close>

text \<open>Every term can start from any entry.\<close>

theorem den_total: "total (den t)"
proof (induction t)
  case (TMust s a)
  show ?case by (simp add: total_must)
next
  case (TMay s a c)
  show ?case by (simp add: total_may)
next
  case (TMustNot s a c)
  show ?case by (simp add: total_mustnot)
next
  case (TThen t\<^sub>1 t\<^sub>2)
  then show ?case by (simp add: total_then)
next
  case (TOr t\<^sub>1 t\<^sub>2)
  then show ?case by (simp add: total_or)
next
  case (TUnless t\<^sub>1 c t\<^sub>2)
  then show ?case by (simp add: total_unless)
next
  case (TAnd t\<^sub>1 t\<^sub>2)
  then show ?case by (simp add: total_and)
qed


section \<open>Laws of UNLESS for terms\<close>

(* §2.5, law 1 *)
theorem term_unless_false: "den (TUnless t EFalse e) = den t"
  by (simp add: unless_false)

(* §2.5, law 2 *)
theorem term_unless_or:
  "den (TUnless (TOr t\<^sub>1 t\<^sub>2) c e) = den (TOr (TUnless t\<^sub>1 c e) (TUnless t\<^sub>2 c e))"
  by (simp add: unless_or)

text \<open>Law 3 holds for every term, with no side condition: the totality it needs is
  a property of all terms (\<open>den_total\<close>).\<close>

(* §2.5, law 3 *)
theorem term_unless_then:
  "den (TUnless (TThen t\<^sub>1 t\<^sub>2) c e) = den (TThen (TUnless t\<^sub>1 c e) (TUnless t\<^sub>2 c e))"
  using unless_then[OF den_total[of t\<^sub>2]] by simp

(* §2.5, law 4 *)
theorem term_unless_idem: "den (TUnless (TUnless t c e) c e) = den (TUnless t c e)"
  by (simp add: unless_idem)

end

text \<open>\<open>term_semantics\<close> adds no assumptions to \<open>interleaving\<close>, so it has models
  whenever \<open>interleaving\<close> does (\<open>interleaving_satisfiable\<close>).\<close>

end
