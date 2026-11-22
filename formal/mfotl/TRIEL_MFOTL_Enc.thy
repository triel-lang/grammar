(*  Title:      TRIEL_MFOTL_Enc.thy
    Purpose:    The bridge from the TRIEL core to MFOTL (the AFP entry MFOTL_Checker),
                part 1: the values of MFOTL, the database of an entry of an
                implementation trace, and the MFOTL traces whose prefix encodes it.
    SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause
*)

theory TRIEL_MFOTL_Enc
  imports TRIEL_Core.TRIEL_Breach MFOTL_Checker.Formula
begin

declare [[quick_and_dirty]]

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
  sorry

text \<open>The facts \<open>val\<close>, \<open>lt\<close> and \<open>le\<close> of the database.\<close>

lemma enc_db_val:
  "(''val'', [MN x, z]) \<in> enc_db C \<pi> j \<longleftrightarrow> (\<exists>u. z = MV u \<and> st \<pi> j x = Some u)"
  sorry

lemma enc_db_lt:
  assumes "u \<in> ran (st \<pi> j) \<union> C" and "w \<in> ran (st \<pi> j) \<union> C"
  shows "(''lt'', [MV u, MV w]) \<in> enc_db C \<pi> j \<longleftrightarrow> vless u w"
  sorry

lemma enc_db_le:
  assumes "u \<in> ran (st \<pi> j) \<union> C" and "w \<in> ran (st \<pi> j) \<union> C"
  shows "(''le'', [MV u, MV w]) \<in> enc_db C \<pi> j \<longleftrightarrow> vleq u w"
  sorry

text \<open>A state with finitely many names and a finite \<open>C\<close> give a finite database.\<close>

lemma enc_db_finite:
  assumes "finite (dom (st \<pi> j))" and "finite C"
  shows "finite (enc_db C \<pi> j)"
  sorry


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
  sorry

text \<open>Every trace whose states have finitely many names, with a finite \<open>C\<close>, has an
  encoding: after the encoded entries come empty databases whose timestamps grow by one.\<close>

lemma enc_pre_exists:
  assumes "is_trace \<pi>" and "finite C" and "\<forall>j < length \<pi>. finite (dom (st \<pi> j))"
  shows "\<exists>\<sigma>. enc_pre C \<pi> \<sigma>"
  sorry

text \<open>The timestamp of entry \<open>j\<close> is the time of entry \<open>j\<close> counted from the first.\<close>

lemma enc_time:
  assumes "is_trace \<pi>" and "enc_pre C \<pi> \<sigma>" and "j < length \<pi>"
  shows "int (\<tau> \<sigma> j) = time \<pi> j - time \<pi> 0"
  sorry

end
