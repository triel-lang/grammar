(*  Title:      TRIEL_MFOTL_Enc.thy
    Purpose:    The bridge from the TRIEL core to MFOTL (the AFP entry MFOTL_Checker),
                part 1: the values of MFOTL, the database of an entry of an
                implementation trace, and the MFOTL traces whose prefix encodes it.
    SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause
*)

theory TRIEL_MFOTL_Enc
  imports TRIEL_Core.TRIEL_Breach MFOTL_Checker.Formula
begin

section \<open>Values of MFOTL\<close>

text \<open>The values of the MFOTL traces of the bridge are the names, the values, the
  subjects and the actions of the core. Predicates and variables of MFOTL are strings.\<close>

datatype ('n, 'v, 's, 'a) mval = MN 'n | MV 'v | MS 's | MA 'a


section \<open>The database of an entry\<close>

text \<open>The database of entry \<open>j\<close> of an implementation trace \<open>\<pi>\<close>, for a set \<open>C\<close> of
  constants: a fact \<open>val(x, u)\<close> for every name \<open>x\<close> with the value \<open>u\<close> in the state; the
  facts \<open>lt(u, w)\<close> and \<open>le(u, w)\<close> for the values \<open>u\<close>, \<open>w\<close> of the state and of \<open>C\<close> with
  \<open>vless u w\<close> and \<open>vleq u w\<close>; \<open>arr(x)\<close> for the arrival of data for \<open>x\<close>; and \<open>act(s, a)\<close>
  for an action \<open>a\<close> of \<open>s\<close>. Entry 0 is the activation entry, so its event is not an
  action and is not encoded.\<close>

definition enc_db ::
  "'v set \<Rightarrow> ('n, 'v :: value_order, 's, 'a) itrace \<Rightarrow> nat \<Rightarrow> (string \<times> ('n, 'v, 's, 'a) mval list) set"
where
  "enc_db C \<pi> j =
     {(''val'', [MN x, MV u]) | x u. st \<pi> j x = Some u}
   \<union> {(''lt'', [MV u, MV w]) | u w. u \<in> ran (st \<pi> j) \<union> C \<and> w \<in> ran (st \<pi> j) \<union> C \<and> vless u w}
   \<union> {(''le'', [MV u, MV w]) | u w. u \<in> ran (st \<pi> j) \<union> C \<and> w \<in> ran (st \<pi> j) \<union> C \<and> vleq u w}
   \<union> (case evt (\<pi> ! j) of
        Arrival x \<Rightarrow> {(''arr'', [MN x])}
      | Deontic s a p \<Rightarrow> (if j = 0 then {} else {(''act'', [MS s, MA a])})
      | Tick \<Rightarrow> {})"

lemma enc_db_eq:
  "enc_db C \<pi> j =
     {(''val'', [MN x, MV u]) | x u. st \<pi> j x = Some u}
   \<union> {(''lt'', [MV u, MV w]) | u w. u \<in> ran (st \<pi> j) \<union> C \<and> w \<in> ran (st \<pi> j) \<union> C \<and> vless u w}
   \<union> {(''le'', [MV u, MV w]) | u w. u \<in> ran (st \<pi> j) \<union> C \<and> w \<in> ran (st \<pi> j) \<union> C \<and> vleq u w}
   \<union> (case evt (\<pi> ! j) of
        Arrival x \<Rightarrow> {(''arr'', [MN x])}
      | Deontic s a p \<Rightarrow> (if j = 0 then {} else {(''act'', [MS s, MA a])})
      | Tick \<Rightarrow> {})"
  unfolding enc_db_def by (rule refl)

text \<open>The facts \<open>val\<close>, \<open>lt\<close> and \<open>le\<close> of the database.\<close>

lemma enc_db_val:
  "(''val'', [MN x, z]) \<in> enc_db C \<pi> j \<longleftrightarrow> (\<exists>u. z = MV u \<and> st \<pi> j x = Some u)"
  by (auto simp: enc_db_def split: event.splits)

lemma enc_db_lt:
  assumes "u \<in> ran (st \<pi> j) \<union> C" and "w \<in> ran (st \<pi> j) \<union> C"
  shows "(''lt'', [MV u, MV w]) \<in> enc_db C \<pi> j \<longleftrightarrow> vless u w"
  using assms by (auto simp: enc_db_def split: event.splits)

lemma enc_db_le:
  assumes "u \<in> ran (st \<pi> j) \<union> C" and "w \<in> ran (st \<pi> j) \<union> C"
  shows "(''le'', [MV u, MV w]) \<in> enc_db C \<pi> j \<longleftrightarrow> vleq u w"
  using assms by (auto simp: enc_db_def split: event.splits)

text \<open>A state with finitely many names and a finite \<open>C\<close> give a finite database.\<close>

lemma enc_db_finite:
  fixes \<pi> :: "('n, 'v :: value_order, 's, 'a) itrace"
  assumes "finite (dom (st \<pi> j))" and "finite C"
  shows "finite (enc_db C \<pi> j)"
proof -
  let ?R = "ran (st \<pi> j) \<union> C"
  have R: "finite ?R"
    using assms by (simp add: finite_ran)
  have val: "finite ({(''val'', [MN x, MV u]) | x u. st \<pi> j x = Some u}
      :: (string \<times> ('n, 'v, 's, 'a) mval list) set)"
  proof (rule finite_subset)
    show "{(''val'', [MN x, MV u]) | x u. st \<pi> j x = Some u}
        \<subseteq> (\<lambda>(x, u). (''val'', [MN x, MV u])) ` (dom (st \<pi> j) \<times> ran (st \<pi> j))"
      by (auto intro: ranI)
    show "finite ((\<lambda>(x, u). (''val'', [MN x, MV u])) ` (dom (st \<pi> j) \<times> ran (st \<pi> j))
        :: (string \<times> ('n, 'v, 's, 'a) mval list) set)"
      using assms(1) by (simp add: finite_ran)
  qed
  have lt: "finite ({(''lt'', [MV u, MV w]) | u w. u \<in> ?R \<and> w \<in> ?R \<and> vless u w}
      :: (string \<times> ('n, 'v, 's, 'a) mval list) set)"
  proof (rule finite_subset)
    show "{(''lt'', [MV u, MV w]) | u w. u \<in> ?R \<and> w \<in> ?R \<and> vless u w}
        \<subseteq> (\<lambda>(u, w). (''lt'', [MV u, MV w])) ` (?R \<times> ?R)"
      by auto
    show "finite ((\<lambda>(u, w). (''lt'', [MV u, MV w])) ` (?R \<times> ?R)
        :: (string \<times> ('n, 'v, 's, 'a) mval list) set)"
      using R by simp
  qed
  have le: "finite ({(''le'', [MV u, MV w]) | u w. u \<in> ?R \<and> w \<in> ?R \<and> vleq u w}
      :: (string \<times> ('n, 'v, 's, 'a) mval list) set)"
  proof (rule finite_subset)
    show "{(''le'', [MV u, MV w]) | u w. u \<in> ?R \<and> w \<in> ?R \<and> vleq u w}
        \<subseteq> (\<lambda>(u, w). (''le'', [MV u, MV w])) ` (?R \<times> ?R)"
      by auto
    show "finite ((\<lambda>(u, w). (''le'', [MV u, MV w])) ` (?R \<times> ?R)
        :: (string \<times> ('n, 'v, 's, 'a) mval list) set)"
      using R by simp
  qed
  show ?thesis
    unfolding enc_db_def using val lt le by (simp split: event.split)
qed


section \<open>The encoded prefix\<close>

text \<open>An MFOTL trace \<open>\<sigma>\<close> encodes \<open>\<pi>\<close> when its first \<open>length \<pi>\<close> entries are the databases
  of the entries of \<open>\<pi>\<close>, with the time of each entry counted from the first as timestamp.
  The entries of \<open>\<sigma>\<close> after them are not constrained.\<close>

definition enc_pre ::
  "'v set \<Rightarrow> ('n, 'v :: value_order, 's, 'a) itrace \<Rightarrow> (string, ('n, 'v, 's, 'a) mval) Formula.trace \<Rightarrow> bool"
where
  "enc_pre C \<pi> \<sigma> \<longleftrightarrow> (\<forall>j < length \<pi>. \<Gamma> \<sigma> j = enc_db C \<pi> j \<and> \<tau> \<sigma> j = nat (time \<pi> j - time \<pi> 0))"

lemma enc_pre_iff:
  "enc_pre C \<pi> \<sigma> \<longleftrightarrow> (\<forall>j < length \<pi>. \<Gamma> \<sigma> j = enc_db C \<pi> j \<and> \<tau> \<sigma> j = nat (time \<pi> j - time \<pi> 0))"
  unfolding enc_pre_def by (rule refl)

text \<open>Every trace whose states have finitely many names, with a finite \<open>C\<close>, has an
  encoding: after the encoded entries come empty databases whose timestamps grow by one.\<close>

lemma enc_pre_exists:
  fixes \<pi> :: "('n, 'v :: value_order, 's, 'a) itrace"
  assumes "is_trace \<pi>" and "finite C" and "\<forall>j < length \<pi>. finite (dom (st \<pi> j))"
  shows "\<exists>\<sigma>. enc_pre C \<pi> \<sigma>"
proof -
  define n where "n = length \<pi>"
  define t where "t i = nat (time \<pi> i - time \<pi> 0)" for i
  define f :: "nat \<Rightarrow> (string \<times> ('n, 'v, 's, 'a) mval list) set \<times> nat" where
    "f i = (if i < n then (enc_db C \<pi> i, t i) else ({}, t (n - 1) + i))" for i
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
    using enc_db_finite[of \<pi> i C] assms(2,3) by (simp add: f_def n_def)
  let ?s = "smap f nats"
  have snth: "?s !! i = f i" for i
    by simp
  have s: "?s \<in> {s. ssorted (smap snd s) \<and> sincreasing (smap snd s) \<and> sfinite (smap fst s)}"
    using mono grows fin
    by (auto simp: snth ssorted_iff_mono sincreasing_def sfinite_def)
  define \<sigma> :: "(string, ('n, 'v, 's, 'a) mval) Formula.trace" where "\<sigma> = Abs_trace ?s"
  have rep: "Rep_trace \<sigma> = ?s"
    unfolding \<sigma>_def using s by (rule Abs_trace_inverse)
  have "\<Gamma> \<sigma> i = fst (f i)" and "\<tau> \<sigma> i = snd (f i)" for i
    by (simp_all add: \<Gamma>.rep_eq \<tau>.rep_eq rep snth)
  then have "enc_pre C \<pi> \<sigma>"
    by (simp add: enc_pre_def f_def t_def n_def)
  then show ?thesis ..
qed

text \<open>The timestamp of entry \<open>j\<close> is the time of entry \<open>j\<close> counted from the first.\<close>

lemma enc_time:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>" and "j < length \<pi>"
  shows "int (\<tau> \<sigma> j) = time \<pi> j - time \<pi> 0"
proof -
  have "time \<pi> 0 \<le> time \<pi> j"
    using time_mono[OF assms(1), of 0 j] assms(3) by simp
  moreover have "\<tau> \<sigma> j = nat (time \<pi> j - time \<pi> 0)"
    using assms(2,3) by (simp add: enc_pre_def)
  ultimately show ?thesis
    by simp
qed

end
