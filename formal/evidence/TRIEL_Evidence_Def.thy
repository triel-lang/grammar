(*  Title:      TRIEL_Evidence_Def.thy
    Purpose:    The evidence of the value of a condition in one state: the names whose values
                were read, the names whose absence was read (PRESENT, the first argument of
                DEFAULT), and, for an undefined value, the absent names that the evaluation
                waits for. Built by the same recursion as eval; eval, the verdicts and the
                reported actions of the core (ob_report, pr_report) do not change.
    SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause
*)

theory TRIEL_Evidence_Def
  imports TRIEL_Core.TRIEL_Completions
begin

text \<open>Evidence is a triple of lists of names \<open>(X, A, U)\<close>: \<open>X\<close> the names whose values were
  read, \<open>A\<close> the names whose absence was read, \<open>U\<close> the absent names an undefined value
  waits for.\<close>

type_synonym 'n evid = "'n list \<times> 'n list \<times> 'n list"

fun ejoin :: "'n evid \<Rightarrow> 'n evid \<Rightarrow> 'n evid" where
  "ejoin (X, A, U) (X', A', U') = (X @ X', A @ A', U @ U')"

primrec evidV :: "('n, 'v) vexp \<Rightarrow> ('n, 'v) state \<Rightarrow> 'n evid" where
  "evidV (VConst v) \<sigma> = ([], [], [])"
| "evidV (VName x) \<sigma> = (case \<sigma> x of Some _ \<Rightarrow> ([x], [], []) | None \<Rightarrow> ([], [], [x]))"
| "evidV (VDefault x a) \<sigma> =
     (case \<sigma> x of
        Some _ \<Rightarrow> ([x], [], [])
      | None \<Rightarrow> (case evidV a \<sigma> of (X, A, U) \<Rightarrow>
                  (case evalV a \<sigma> of None \<Rightarrow> (X, A, x # U) | Some _ \<Rightarrow> (X, x # A, U))))"

text \<open>A connective with one operand that decides the value takes the evidence of that
  operand alone, the left one when both decide; otherwise it joins both.\<close>

primrec evidence :: "('n, 'v :: value_order) expr \<Rightarrow> ('n, 'v) state \<Rightarrow> 'n evid" where
  "evidence ETrue \<sigma> = ([], [], [])"
| "evidence EFalse \<sigma> = ([], [], [])"
| "evidence (EEq a b) \<sigma> = ejoin (evidV a \<sigma>) (evidV b \<sigma>)"
| "evidence (ELt a b) \<sigma> = ejoin (evidV a \<sigma>) (evidV b \<sigma>)"
| "evidence (ELe a b) \<sigma> = ejoin (evidV a \<sigma>) (evidV b \<sigma>)"
| "evidence (ENot e) \<sigma> = evidence e \<sigma>"
| "evidence (EAnd e\<^sub>1 e\<^sub>2) \<sigma> =
     (if eval e\<^sub>1 \<sigma> = Some False then evidence e\<^sub>1 \<sigma>
      else if eval e\<^sub>2 \<sigma> = Some False then evidence e\<^sub>2 \<sigma>
      else ejoin (evidence e\<^sub>1 \<sigma>) (evidence e\<^sub>2 \<sigma>))"
| "evidence (EOr e\<^sub>1 e\<^sub>2) \<sigma> =
     (if eval e\<^sub>1 \<sigma> = Some True then evidence e\<^sub>1 \<sigma>
      else if eval e\<^sub>2 \<sigma> = Some True then evidence e\<^sub>2 \<sigma>
      else ejoin (evidence e\<^sub>1 \<sigma>) (evidence e\<^sub>2 \<sigma>))"
| "evidence (EImp e\<^sub>1 e\<^sub>2) \<sigma> =
     (if eval e\<^sub>1 \<sigma> = Some False then evidence e\<^sub>1 \<sigma>
      else if eval e\<^sub>2 \<sigma> = Some True then evidence e\<^sub>2 \<sigma>
      else ejoin (evidence e\<^sub>1 \<sigma>) (evidence e\<^sub>2 \<sigma>))"
| "evidence (EPresent x) \<sigma> = (case \<sigma> x of Some _ \<Rightarrow> ([x], [], []) | None \<Rightarrow> ([], [x], []))"

text \<open>A set of names supports a value when the condition has that value on the state
  restricted to them. Checking it needs only eval, not the construction of the evidence.\<close>

definition supports :: "'n set \<Rightarrow> ('n, 'v :: value_order) expr \<Rightarrow> ('n, 'v) state \<Rightarrow> bool \<Rightarrow> bool" where
  "supports X c \<sigma> b \<longleftrightarrow> eval c (\<sigma> |` X) = Some b"

text \<open>The decisions of the monitor of \<open>s MUST_NOT a WHEN c\<close>, each with the value of the
  condition and its evidence in the state of the entry before the action.\<close>

definition monitor_evidence :: "'s \<Rightarrow> 'a \<Rightarrow> ('n, 'v :: value_order) expr \<Rightarrow> ('n, 'v, 's, 'a) itrace
    \<Rightarrow> (nat \<times> bool option \<times> 'n evid) list" where
  "monitor_evidence s a c \<pi> =
     map (\<lambda>j. (j, eval c (st \<pi> (j - 1)), evidence c (st \<pi> (j - 1))))
       (filter (\<lambda>j. does s a (evt (\<pi> ! j))) [1..<length \<pi>])"

end
