(*  Title:      TRIEL_Invariants.thy
    Purpose:    ALWAYS, EVENTUALLY and NEXT over finite prefixes of implementation
                traces, with three-valued verdicts in the style of LTL3
                (A. Bauer, M. Leucker, C. Schallhart. Runtime verification for LTL and
                TLTL. ACM TOSEM 20(4), 2011), and strong Kleene evaluation of the state
                formulas.
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

fun inv_eval :: "('n, 'v) inv \<Rightarrow> ('n, 'v, 's, 'a) itrace \<Rightarrow> bool option" where
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

end
