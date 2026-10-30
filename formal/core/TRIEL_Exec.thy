(*  Title:      TRIEL_Exec.thy
    Purpose:    An executable evaluator for the formal core and its export to Haskell.
                Every function the evaluator uses is either defined in the other theories
                of formal/core, or proved equal to such a function by a code equation in
                this theory. Membership of a trace in the denotation of a composite term
                is three-valued: definite answers are proved sound for terms without AND, and
                for terms without UNLESS and AND the answer is always definite, so there
                the test is exact (mem3_eq).
    SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause
*)

theory TRIEL_Exec
  imports TRIEL_Terms TRIEL_ND TRIEL_Breach TRIEL_Invariants TRIEL_Numbers TRIEL_Penalty
    "HOL-Library.Code_Target_Numeral"
begin

section \<open>Executable equations for the verdicts\<close>

text \<open>Each lemma below restates a definition of TRIEL_Breach or TRIEL_Invariants with bounded
  quantifiers, \<open>find\<close> or \<open>filter\<close> instead of unbounded quantifiers, \<open>LEAST\<close> or
  \<open>GREATEST\<close>, and is used by the code generator in place of the definition.\<close>

lemma does_code [code]:
  "does s a e = (case e of Deontic s' a' p \<Rightarrow> s' = s \<and> a' = a | _ \<Rightarrow> False)"
  by (cases e) (auto simp: does_def)

lemma acted_code [code]:
  "acted s a lo d \<pi> =
     (\<exists>j \<in> set [1..<length \<pi>]. does s a (evt (\<pi> ! j)) \<and> after lo (time \<pi> j) \<and> time \<pi> j \<le> d)"
  by (auto simp: acted_def)

lemma passed_code [code]: "passed d \<pi> = (\<exists>j \<in> set [0..<length \<pi>]. d < time \<pi> j)"
  by (auto simp: passed_def)

lemma ob_verdict_code [code]:
  "ob_verdict s a lo D \<pi> =
     (case D of
        Some d \<Rightarrow> window s a lo d \<pi>
      | None \<Rightarrow> (if \<exists>j \<in> set [1..<length \<pi>]. does s a (evt (\<pi> ! j)) \<and> after lo (time \<pi> j)
                 then Fulfilled else Pending))"
  by (auto simp: ob_verdict_def split: option.splits)

lemma may_verdict_code [code]:
  "may_verdict s a c \<pi> =
     (if \<exists>j \<in> set [1..<length \<pi>]. does s a (evt (\<pi> ! j)) \<and> eval c (st \<pi> (j - 1)) = Some True
      then Fulfilled else Pending)"
  by (auto simp: may_verdict_def)

lemma find_upt_Some:
  "find P [0..<n] = Some j \<longleftrightarrow> j < n \<and> P j \<and> (\<forall>i < j. \<not> P i)"
  by (auto simp: find_Some_iff)

lemma find_upt_None: "find P [0..<n] = None \<longleftrightarrow> (\<forall>j < n. \<not> P j)"
  by (auto simp: find_None_iff)

lemma pr_verdict_code [code]:
  "pr_verdict s a c \<pi> =
     (case find (forbidden s a c \<pi>) [0..<length \<pi>] of
        None \<Rightarrow> Pending
      | Some j \<Rightarrow> Breached (time \<pi> j))"
proof (cases "find (forbidden s a c \<pi>) [0..<length \<pi>]")
  case None
  then have "\<not> forbidden s a c \<pi> j" for j
    using forbidden_less[of s a c \<pi> j] by (auto simp: find_upt_None)
  with None show ?thesis by (simp add: pr_verdict_def)
next
  case (Some j)
  then have j: "forbidden s a c \<pi> j" "\<And>i. i < j \<Longrightarrow> \<not> forbidden s a c \<pi> i"
    by (auto simp: find_upt_Some)
  have "(LEAST j. forbidden s a c \<pi> j) = j"
    by (rule Least_equality) (use j in \<open>auto simp: not_le[symmetric]\<close>)
  with Some j show ?thesis by (auto simp: pr_verdict_def)
qed

lemma sorted_upt_filter_last:
  assumes "filter P [0..<n] \<noteq> []"
  shows "P (last (filter P [0..<n]))" and "last (filter P [0..<n]) < n"
    and "\<And>y. y < n \<Longrightarrow> P y \<Longrightarrow> y \<le> last (filter P [0..<n])"
proof -
  have mem: "last (filter P [0..<n]) \<in> set (filter P [0..<n])" using assms by (rule last_in_set)
  then show "P (last (filter P [0..<n]))" and "last (filter P [0..<n]) < n" by auto
  have sorted: "sorted (filter P [0..<n])" by (rule sorted_wrt_filter[OF sorted_upt])
  fix y assume "y < n" "P y"
  then have "y \<in> set (filter P [0..<n])" by simp
  with sorted show "y \<le> last (filter P [0..<n])" by (rule sorted_le_last)
qed

lemma bound_to_code [code]:
  "bound_to blk i s =
     (let js = filter (\<lambda>j. binds s (blk ! j)) [0..<i] in if js = [] then None else Some (last js))"
proof (cases "filter (\<lambda>j. binds s (blk ! j)) [0..<i] = []")
  case True
  then have "\<forall>j < i. \<not> binds s (blk ! j)" by (auto simp: filter_empty_conv)
  with True show ?thesis by (simp add: bound_to_def)
next
  case False
  note f = sorted_upt_filter_last[OF False]
  have ex: "\<exists>j < i. binds s (blk ! j)" using f(1,2) by blast
  have "(GREATEST j. j < i \<and> binds s (blk ! j)) = last (filter (\<lambda>j. binds s (blk ! j)) [0..<i])"
    by (rule Greatest_equality) (use f in auto)
  with False ex show ?thesis by (simp add: bound_to_def)
qed

text \<open>Well-formedness of a block, with the injectivity of the binding stated by
  \<open>distinct\<close>.\<close>

definition handler_bound :: "('n, 'v, 's, 'a, 'p) sterm list \<Rightarrow> nat \<Rightarrow> nat option option" where
  "handler_bound blk i = (case blk ! i of SOnBreach s acts \<Rightarrow> Some (bound_to blk i s) | _ \<Rightarrow> None)"

lemma handler_bound_Some:
  "handler_bound blk i = Some b \<longleftrightarrow> (\<exists>s acts. blk ! i = SOnBreach s acts \<and> b = bound_to blk i s)"
  by (cases "blk ! i") (auto simp: handler_bound_def)

lemma wf_block_code [code]:
  "wf_block blk \<longleftrightarrow>
     (\<forall>i \<in> set [0..<length blk]. case blk ! i of
        SOnBreach s acts \<Rightarrow> wf_actions acts \<and> bound_to blk i s \<noteq> None
      | _ \<Rightarrow> \<not> has_handler (blk ! i))
     \<and> distinct (map (handler_bound blk) (filter (\<lambda>i. handler_bound blk i \<noteq> None) [0..<length blk]))"
proof -
  let ?H = "filter (\<lambda>i. handler_bound blk i \<noteq> None) [0..<length blk]"
  have "distinct (map (handler_bound blk) ?H) \<longleftrightarrow>
        (\<forall>i k s s' acts acts'. i < length blk \<longrightarrow> k < length blk \<longrightarrow>
          blk ! i = SOnBreach s acts \<longrightarrow> blk ! k = SOnBreach s' acts' \<longrightarrow>
          bound_to blk i s = bound_to blk k s' \<longrightarrow> i = k)"
    (is "?L \<longleftrightarrow> ?R")
  proof
    assume ?L
    then have inj: "inj_on (handler_bound blk) (set ?H)" by (simp add: distinct_map)
    show ?R
    proof (intro allI impI)
      fix i k s s' acts acts'
      assume i: "i < length blk" and k: "k < length blk"
        and bi: "blk ! i = SOnBreach s acts" and bk: "blk ! k = SOnBreach s' acts'"
        and eq: "bound_to blk i s = bound_to blk k s'"
      have hi: "handler_bound blk i = Some (bound_to blk i s)" using bi by (simp add: handler_bound_def)
      have hk: "handler_bound blk k = Some (bound_to blk k s')" using bk by (simp add: handler_bound_def)
      from i hi have "i \<in> set ?H" by simp
      moreover from k hk have "k \<in> set ?H" by simp
      moreover have "handler_bound blk i = handler_bound blk k" using hi hk eq by simp
      ultimately show "i = k" using inj by (auto dest: inj_onD)
    qed
  next
    assume R: ?R
    have "inj_on (handler_bound blk) (set ?H)"
    proof (rule inj_onI)
      fix i k assume "i \<in> set ?H" "k \<in> set ?H" and eq: "handler_bound blk i = handler_bound blk k"
      then have i: "i < length blk" "handler_bound blk i \<noteq> None"
        and k: "k < length blk" "handler_bound blk k \<noteq> None" by auto
      from i(2) obtain s acts where bi: "blk ! i = SOnBreach s acts"
        by (cases "blk ! i") (auto simp: handler_bound_def)
      from k(2) obtain s' acts' where bk: "blk ! k = SOnBreach s' acts'"
        by (cases "blk ! k") (auto simp: handler_bound_def)
      from eq bi bk have "bound_to blk i s = bound_to blk k s'" by (simp add: handler_bound_def)
      with R i(1) k(1) bi bk show "i = k" by blast
    qed
    then show ?L by (simp add: distinct_map)
  qed
  then show ?thesis unfolding wf_block_def by (simp add: Ball_def)
qed

lemma fresh_code [code]:
  "fresh m x \<pi> j = (\<exists>i \<in> set [0..<Suc j]. evt (\<pi> ! i) = Arrival x \<and> time \<pi> j - time \<pi> i \<le> m)"
  unfolding fresh_def set_upt Bex_def atLeastLessThan_iff by (simp add: less_Suc_eq_le)

lemma inv_eval_code [code]:
  "inv_eval (Always \<phi>) \<pi> =
     (if \<exists>j \<in> set [0..<length \<pi>]. eval \<phi> (st \<pi> j) = Some False then Some False else None)"
  "inv_eval (Eventually \<phi>) \<pi> =
     (if \<exists>j \<in> set [0..<length \<pi>]. eval \<phi> (st \<pi> j) = Some True then Some True else None)"
  "inv_eval (Next \<phi>) \<pi> = (if 1 < length \<pi> then eval \<phi> (st \<pi> 1) else None)"
  by auto

lemma ew_eval_code [code]:
  "ew_eval \<phi> D \<pi> =
     (if \<exists>j \<in> set [0..<length \<pi>]. time \<pi> j \<le> D \<and> eval \<phi> (st \<pi> j) = Some True then Some True
      else if passed D \<pi> \<and> (\<forall>j \<in> set [0..<length \<pi>]. time \<pi> j \<le> D \<longrightarrow> eval \<phi> (st \<pi> j) = Some False)
      then Some False
      else None)"
  unfolding ew_eval_def by auto

lemma else_handlers_ok_code [code]:
  "else_handlers_ok blk =
     list_all (\<lambda>k. case blk ! k of
                     SOnBreach s acts \<Rightarrow> (case bound_to blk k s of Some j \<Rightarrow> \<not> is_else (blk ! j) | None \<Rightarrow> True)
                   | _ \<Rightarrow> True) [0..<length blk]"
  unfolding else_handlers_ok_def list_all_iff by auto

lemma inv_activates_code [code]:
  "inv_activates T \<tau>\<^sub>0 \<sigma>\<^sub>0 invs = list_all (\<lambda>\<iota>. list_all (\<lambda>d. resolve T \<tau>\<^sub>0 \<sigma>\<^sub>0 d \<noteq> None) (sinv_deadlines \<iota>)) invs"
  unfolding inv_activates_def by (simp add: list_all_iff)


section \<open>Executable typing\<close>

text \<open>A functional version of the typing judgement \<open>wt\<close> of TRIEL_ND.\<close>

lemma size_ty_field: "(f, t) \<in> set fs \<Longrightarrow> size t < size (TRecord fs)"
proof (induction fs)
  case Nil
  then show ?case by simp
next
  case (Cons p fs)
  then show ?case by (cases p) auto
qed

function wt_fun :: "('p \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('n, 'p) ty \<Rightarrow> ('n, 'b) nd option \<Rightarrow> bool" where
  "wt_fun I (TPrim q) v = (case v of Some (Atom b) \<Rightarrow> I q b | _ \<Rightarrow> False)"
| "wt_fun I (TOptional t) v = (case v of None \<Rightarrow> True | Some d \<Rightarrow> wt_fun I t (Some d))"
| "wt_fun I (TRecord fs) v =
     (case v of Some (Nom m) \<Rightarrow> (\<forall>(f, t) \<in> set fs. wt_fun I t (fmlookup m f)) | _ \<Rightarrow> False)"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(I, t, v). size t)") (auto dest: size_ty_field)

theorem wt_fun_iff: "wt_fun I t v \<longleftrightarrow> wt I t v"
proof (induction t arbitrary: v)
  case (TPrim q)
  show ?case
    by (cases v) (auto split: nd.splits intro: wt.intros elim: wt.cases)
next
  case (TOptional t)
  show ?case
  proof (cases v)
    case None
    then show ?thesis by (auto intro: wt.intros)
  next
    case (Some d)
    with TOptional.IH[of "Some d"] show ?thesis by (auto intro: wt.intros elim: wt_OptionalE)
  qed
next
  case (TRecord fs)
  have IH: "\<And>f t v. (f, t) \<in> set fs \<Longrightarrow> wt_fun I t v \<longleftrightarrow> wt I t v"
    using TRecord.IH by fastforce
  show ?case
  proof
    assume w: "wt_fun I (TRecord fs) v"
    then obtain m where v: "v = Some (Nom m)"
      by (cases v) (auto split: nd.splits)
    show "wt I (TRecord fs) v"
      unfolding v
    proof (rule wt.wt_record)
      fix f t assume ft: "(f, t) \<in> set fs"
      with w v have "wt_fun I t (fmlookup m f)" by auto
      with IH[OF ft] show "wt I t (fmlookup m f)" by blast
    qed
  next
    assume w: "wt I (TRecord fs) v"
    then obtain m where v: "v = Some (Nom m)" and fields: "\<And>f t. (f, t) \<in> set fs \<Longrightarrow> wt I t (fmlookup m f)"
      by (cases rule: wt.cases) auto
    have "\<forall>(f, t) \<in> set fs. wt_fun I t (fmlookup m f)"
      using fields IH by blast
    with v show "wt_fun I (TRecord fs) v" by simp
  qed
qed


section \<open>Three-valued membership in the denotation of a term\<close>

subsection \<open>Kleene connectives on definite values\<close>

lemma kor_True_iff: "kor p q = Some True \<longleftrightarrow> p = Some True \<or> q = Some True"
  by (simp add: kor_def)

lemma kor_False_iff: "kor p q = Some False \<longleftrightarrow> p = Some False \<and> q = Some False"
  by (auto simp: kor_def)

lemma kand_True_iff: "kand p q = Some True \<longleftrightarrow> p = Some True \<and> q = Some True"
  by (auto simp: kand_def)

lemma kand_False_iff: "kand p q = Some False \<longleftrightarrow> p = Some False \<or> q = Some False"
  by (simp add: kand_def)

definition kors :: "bool option list \<Rightarrow> bool option" where
  "kors xs = foldr kor xs (Some False)"

lemma kors_True: "kors xs = Some True \<longleftrightarrow> (\<exists>x \<in> set xs. x = Some True)"
  unfolding kors_def by (induction xs) (auto simp: kor_True_iff)

lemma kors_False: "kors xs = Some False \<longleftrightarrow> (\<forall>x \<in> set xs. x = Some False)"
  unfolding kors_def by (induction xs) (auto simp: kor_False_iff)

lemma kors_map_True: "kors (map f xs) = Some True \<longleftrightarrow> (\<exists>x \<in> set xs. f x = Some True)"
  unfolding kors_True set_map by blast

lemma kors_map_False: "kors (map f xs) = Some False \<longleftrightarrow> (\<forall>x \<in> set xs. f x = Some False)"
  unfolding kors_False set_map by blast

lemma kors_defined: "(\<And>x. x \<in> set xs \<Longrightarrow> x \<noteq> None) \<Longrightarrow> kors xs \<noteq> None"
  unfolding kors_def
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then obtain a b where "x = Some a" "foldr kor xs (Some False) = Some b" by fastforce
  then show ?case by simp
qed

lemma kor_defined: "p \<noteq> None \<Longrightarrow> q \<noteq> None \<Longrightarrow> kor p q \<noteq> None"
  by auto

lemma kand_defined: "p \<noteq> None \<Longrightarrow> q \<noteq> None \<Longrightarrow> kand p q \<noteq> None"
  by auto

lemma Some_bool_cases: "p = Some b \<Longrightarrow> (b \<Longrightarrow> p = Some True \<Longrightarrow> P) \<Longrightarrow> (\<not> b \<Longrightarrow> p = Some False \<Longrightarrow> P) \<Longrightarrow> P"
  by (cases b) auto


subsection \<open>Decomposing traces\<close>

lemma drop_last_one: "p \<noteq> [] \<Longrightarrow> drop (length p - 1) p = [last p]"
proof -
  assume p: "p \<noteq> []"
  have "p = butlast p @ [last p]" using p by simp
  moreover have "length (butlast p) = length p - 1" by simp
  ultimately show ?thesis by (metis append_eq_conv_conj)
qed

lemma last_take_Suc: "k < length \<pi> \<Longrightarrow> last (take (Suc k) \<pi>) = \<pi> ! k"
  by (simp add: take_Suc_conv_app_nth)

text \<open>A fusion is a split of the fused trace at one entry.\<close>

lemma fuse_decomp:
  "(fusable p q \<and> \<pi> = fuse p q) \<longleftrightarrow> (\<exists>k < length \<pi>. p = take (Suc k) \<pi> \<and> q = drop k \<pi>)"
proof
  assume a: "fusable p q \<and> \<pi> = fuse p q"
  then have p: "p \<noteq> []" and q: "q \<noteq> []" and lq: "last p = hd q" and pi: "\<pi> = p @ tl q"
    by (auto simp: fusable_def fuse_def)
  define k where "k = length p - 1"
  have pk: "Suc k = length p" using p unfolding k_def by (cases p) auto
  have "k < length \<pi>" using pk pi by simp
  moreover have "take (Suc k) \<pi> = p" using pk pi by simp
  moreover have "drop k \<pi> = q"
  proof -
    have "drop k \<pi> = drop k p @ tl q" using pk pi by simp
    also have "drop k p = [last p]" unfolding k_def using p by (rule drop_last_one)
    finally show ?thesis using lq q by simp
  qed
  ultimately show "\<exists>k < length \<pi>. p = take (Suc k) \<pi> \<and> q = drop k \<pi>" by blast
next
  assume "\<exists>k < length \<pi>. p = take (Suc k) \<pi> \<and> q = drop k \<pi>"
  then obtain k where k: "k < length \<pi>" and p: "p = take (Suc k) \<pi>" and q: "q = drop k \<pi>" by blast
  have "p \<noteq> []" "q \<noteq> []" using k p q by auto
  moreover have "last p = hd q" using k p q by (simp add: last_take_Suc hd_drop_conv_nth)
  moreover have "fuse p q = \<pi>"
  proof -
    have "tl (drop k \<pi>) = drop (Suc k) \<pi>" by (simp add: drop_Suc tl_drop)
    then show ?thesis using p q by (simp add: fuse_def)
  qed
  ultimately show "fusable p q \<and> \<pi> = fuse p q" by (simp add: fusable_def)
qed

lemma then_d_split:
  "(\<pi>, r) \<in> then_d T\<^sub>1 T\<^sub>2 \<longleftrightarrow>
     (\<exists>k < length \<pi>. (take (Suc k) \<pi>, Done) \<in> T\<^sub>1 \<and> (drop k \<pi>, r) \<in> T\<^sub>2) \<or> ((\<pi>, r) \<in> T\<^sub>1 \<and> r \<noteq> Done)"
proof -
  have "(\<exists>\<pi>\<^sub>1 \<pi>\<^sub>2. (\<pi>\<^sub>1, Done) \<in> T\<^sub>1 \<and> (\<pi>\<^sub>2, r) \<in> T\<^sub>2 \<and> fusable \<pi>\<^sub>1 \<pi>\<^sub>2 \<and> \<pi> = fuse \<pi>\<^sub>1 \<pi>\<^sub>2)
      \<longleftrightarrow> (\<exists>k < length \<pi>. (take (Suc k) \<pi>, Done) \<in> T\<^sub>1 \<and> (drop k \<pi>, r) \<in> T\<^sub>2)"
  proof
    assume "\<exists>\<pi>\<^sub>1 \<pi>\<^sub>2. (\<pi>\<^sub>1, Done) \<in> T\<^sub>1 \<and> (\<pi>\<^sub>2, r) \<in> T\<^sub>2 \<and> fusable \<pi>\<^sub>1 \<pi>\<^sub>2 \<and> \<pi> = fuse \<pi>\<^sub>1 \<pi>\<^sub>2"
    then obtain \<pi>\<^sub>1 \<pi>\<^sub>2 where m: "(\<pi>\<^sub>1, Done) \<in> T\<^sub>1" "(\<pi>\<^sub>2, r) \<in> T\<^sub>2" and f: "fusable \<pi>\<^sub>1 \<pi>\<^sub>2 \<and> \<pi> = fuse \<pi>\<^sub>1 \<pi>\<^sub>2"
      by blast
    from f obtain k where "k < length \<pi>" "\<pi>\<^sub>1 = take (Suc k) \<pi>" "\<pi>\<^sub>2 = drop k \<pi>"
      unfolding fuse_decomp by blast
    with m show "\<exists>k < length \<pi>. (take (Suc k) \<pi>, Done) \<in> T\<^sub>1 \<and> (drop k \<pi>, r) \<in> T\<^sub>2" by blast
  next
    assume "\<exists>k < length \<pi>. (take (Suc k) \<pi>, Done) \<in> T\<^sub>1 \<and> (drop k \<pi>, r) \<in> T\<^sub>2"
    then obtain k where k: "k < length \<pi>" "(take (Suc k) \<pi>, Done) \<in> T\<^sub>1" "(drop k \<pi>, r) \<in> T\<^sub>2" by blast
    have "fusable (take (Suc k) \<pi>) (drop k \<pi>) \<and> \<pi> = fuse (take (Suc k) \<pi>) (drop k \<pi>)"
      unfolding fuse_decomp using k(1) by blast
    with k show "\<exists>\<pi>\<^sub>1 \<pi>\<^sub>2. (\<pi>\<^sub>1, Done) \<in> T\<^sub>1 \<and> (\<pi>\<^sub>2, r) \<in> T\<^sub>2 \<and> fusable \<pi>\<^sub>1 \<pi>\<^sub>2 \<and> \<pi> = fuse \<pi>\<^sub>1 \<pi>\<^sub>2" by blast
  qed
  then show ?thesis unfolding then_d_iff by blast
qed

text \<open>\<open>ext T \<rho>\<close>: the non-empty trace \<open>\<rho>\<close> is a proper prefix of a trace of \<open>T\<close>.\<close>

definition ext :: "('n, 'v, 't, 's, 'a) den \<Rightarrow> ('n, 'v, 't, 's, 'a) trace \<Rightarrow> bool" where
  "ext T \<rho> \<longleftrightarrow> (\<exists>\<pi>\<^sub>0 r\<^sub>0. (\<pi>\<^sub>0, r\<^sub>0) \<in> T \<and> length \<rho> < length \<pi>\<^sub>0 \<and> take (length \<rho>) \<pi>\<^sub>0 = \<rho>)"

text \<open>\<open>first_at c \<pi> k\<close>: the guard \<open>c\<close> is true at entry \<open>k\<close> of \<open>\<pi>\<close> and at no earlier entry.\<close>

definition first_at :: "('n, 'v :: value_order) expr \<Rightarrow> ('n, 'v, 't, 's, 'a) trace \<Rightarrow> nat \<Rightarrow> bool" where
  "first_at c \<pi> k \<longleftrightarrow> eval c (st \<pi> k) = Some True \<and> (\<forall>j < k. eval c (st \<pi> j) \<noteq> Some True)"

lemma st_take: "j < n \<Longrightarrow> st (take n \<pi>) j = st \<pi> j"
  by (simp add: st_def)

text \<open>The interrupted traces of UNLESS, described by the observed trace alone: the guard
  first holds at entry \<open>k\<close>, the observed prefix up to \<open>k\<close> can be continued by \<open>t\<^sub>1\<close>, and the
  rest of the trace is a run of the handler.\<close>

lemma unless_d_split:
  "(\<pi>, r) \<in> unless_d T c E \<longleftrightarrow>
     ((\<pi>, r) \<in> T \<and> (\<forall>j < length \<pi> - 1. eval c (st \<pi> j) \<noteq> Some True))
     \<or> (\<exists>k < length \<pi>. first_at c \<pi> k \<and> ext T (take (Suc k) \<pi>)
          \<and> (\<exists>r'. kappa r' = r \<and> (drop k \<pi>, r') \<in> E))"
  (is "?L \<longleftrightarrow> ?A \<or> ?B")
proof
  assume ?L
  then consider (keep) "(\<pi>, r) \<in> T" "\<forall>j. \<not> fires c \<pi> j"
    | (int) \<pi>\<^sub>0 r\<^sub>0 \<pi>' r' where "(\<pi>\<^sub>0, r\<^sub>0) \<in> T" "\<exists>j. fires c \<pi>\<^sub>0 j" "(\<pi>', r') \<in> E"
        "fusable (pre \<pi>\<^sub>0 (first_fire c \<pi>\<^sub>0)) \<pi>'" "\<pi> = fuse (pre \<pi>\<^sub>0 (first_fire c \<pi>\<^sub>0)) \<pi>'" "r = kappa r'"
    unfolding unless_d_iff by blast
  then show "?A \<or> ?B"
  proof cases
    case keep
    then have ?A by (auto simp: fires_def)
    then show ?thesis ..
  next
    case int
    from int(2) obtain j where fj: "fires c \<pi>\<^sub>0 j" ..
    define k where "k = first_fire c \<pi>\<^sub>0"
    have fk: "fires c \<pi>\<^sub>0 k" unfolding k_def by (rule first_fire_fires[OF fj])
    have kl: "k < length \<pi>\<^sub>0 - 1" using fk by (rule fires_less)
    define \<rho> where "\<rho> = pre \<pi>\<^sub>0 k"
    have l\<rho>: "length \<rho> = Suc k" unfolding \<rho>_def using kl by (simp add: length_pre)
    have "fusable \<rho> \<pi>' \<and> \<pi> = fuse \<rho> \<pi>'" using int(4,5) unfolding \<rho>_def k_def by simp
    then obtain k' where k': "k' < length \<pi>" "\<rho> = take (Suc k') \<pi>" "\<pi>' = drop k' \<pi>"
      unfolding fuse_decomp by blast
    have "k' = k" using k' l\<rho> by simp
    with k' have kpi: "k < length \<pi>" and tk: "take (Suc k) \<pi> = \<rho>" and dk: "drop k \<pi> = \<pi>'" by auto
    have st_eq: "st \<pi> j = st \<pi>\<^sub>0 j" if "j \<le> k" for j
    proof -
      have "st \<pi> j = st (take (Suc k) \<pi>) j" using that by (simp add: st_take)
      also have "\<dots> = st \<rho> j" using tk by simp
      also have "\<dots> = st \<pi>\<^sub>0 j" unfolding \<rho>_def pre_def using that by (simp add: st_take)
      finally show ?thesis .
    qed
    have "first_at c \<pi> k"
      unfolding first_at_def
    proof (intro conjI allI impI)
      show "eval c (st \<pi> k) = Some True" using fk st_eq[of k] by (simp add: fires_def)
    next
      fix i assume "i < k"
      then have "\<not> fires c \<pi>\<^sub>0 i" unfolding k_def by (rule not_fires_before)
      moreover have "i < length \<pi>\<^sub>0 - 1" using \<open>i < k\<close> kl by simp
      ultimately show "eval c (st \<pi> i) \<noteq> Some True" using st_eq[of i] \<open>i < k\<close> by (simp add: fires_def)
    qed
    moreover have "ext T (take (Suc k) \<pi>)"
      unfolding ext_def tk
    proof (intro exI conjI)
      show "(\<pi>\<^sub>0, r\<^sub>0) \<in> T" by (fact int(1))
      show "length \<rho> < length \<pi>\<^sub>0" using l\<rho> kl by simp
      show "take (length \<rho>) \<pi>\<^sub>0 = \<rho>" using l\<rho> unfolding \<rho>_def pre_def by simp
    qed
    moreover have "\<exists>r'. kappa r' = r \<and> (drop k \<pi>, r') \<in> E" using int(3,6) dk by blast
    ultimately have ?B using kpi by blast
    then show ?thesis ..
  qed
next
  assume "?A \<or> ?B"
  then show ?L
  proof
    assume ?A
    then show ?L unfolding unless_d_iff by (auto simp: fires_def)
  next
    assume ?B
    then obtain k r' where k: "k < length \<pi>" and fa: "first_at c \<pi> k"
      and ex: "ext T (take (Suc k) \<pi>)" and r': "kappa r' = r" "(drop k \<pi>, r') \<in> E" by blast
    from ex obtain \<pi>\<^sub>0 r\<^sub>0 where m0: "(\<pi>\<^sub>0, r\<^sub>0) \<in> T"
      and len: "length (take (Suc k) \<pi>) < length \<pi>\<^sub>0"
      and pref: "take (length (take (Suc k) \<pi>)) \<pi>\<^sub>0 = take (Suc k) \<pi>"
      unfolding ext_def by blast
    have lt: "length (take (Suc k) \<pi>) = Suc k" using k by simp
    have pre0: "pre \<pi>\<^sub>0 k = take (Suc k) \<pi>" using pref lt by (simp add: pre_def)
    have kl0: "k < length \<pi>\<^sub>0 - 1" using len lt by simp
    have st_eq: "st \<pi>\<^sub>0 j = st \<pi> j" if "j \<le> k" for j
    proof -
      have "st \<pi>\<^sub>0 j = st (take (Suc k) \<pi>\<^sub>0) j" using that by (simp add: st_take)
      also have "\<dots> = st (take (Suc k) \<pi>) j" using pre0 by (simp add: pre_def)
      also have "\<dots> = st \<pi> j" using that by (simp add: st_take)
      finally show ?thesis .
    qed
    have fk: "fires c \<pi>\<^sub>0 k" using fa kl0 st_eq[of k] by (simp add: fires_def first_at_def)
    have ff: "first_fire c \<pi>\<^sub>0 = k"
    proof (rule first_fire_eqI[OF fk])
      fix i assume "i < k"
      then show "\<not> fires c \<pi>\<^sub>0 i" using fa st_eq[of i] by (simp add: fires_def first_at_def)
    qed
    have fu: "fusable (take (Suc k) \<pi>) (drop k \<pi>) \<and> \<pi> = fuse (take (Suc k) \<pi>) (drop k \<pi>)"
      unfolding fuse_decomp using k by blast
    have ex: "\<exists>j. fires c \<pi>\<^sub>0 j" using fk by blast
    show ?L unfolding unless_d_iff
      by (intro disjI2 exI[of _ \<pi>\<^sub>0] exI[of _ r\<^sub>0] exI[of _ "drop k \<pi>"] exI[of _ r'])
         (use m0 ex r' fu ff pre0 in simp)
  qed
qed

lemma ext_or: "ext (or_d T\<^sub>1 T\<^sub>2) \<rho> \<longleftrightarrow> ext T\<^sub>1 \<rho> \<or> ext T\<^sub>2 \<rho>"
  by (auto simp: ext_def or_d_def)

lemma ext_then:
  assumes tot: "total T\<^sub>2"
  shows "ext (then_d T\<^sub>1 T\<^sub>2) \<rho> \<longleftrightarrow>
           ext T\<^sub>1 \<rho> \<or> (\<exists>k < length \<rho>. (take (Suc k) \<rho>, Done) \<in> T\<^sub>1 \<and> ext T\<^sub>2 (drop k \<rho>))"
proof
  assume "ext (then_d T\<^sub>1 T\<^sub>2) \<rho>"
  then obtain \<pi>\<^sub>0 r\<^sub>0 where m: "(\<pi>\<^sub>0, r\<^sub>0) \<in> then_d T\<^sub>1 T\<^sub>2" and len: "length \<rho> < length \<pi>\<^sub>0"
    and pref: "take (length \<rho>) \<pi>\<^sub>0 = \<rho>" unfolding ext_def by blast
  from m consider (seq) k where "k < length \<pi>\<^sub>0" "(take (Suc k) \<pi>\<^sub>0, Done) \<in> T\<^sub>1" "(drop k \<pi>\<^sub>0, r\<^sub>0) \<in> T\<^sub>2"
    | (left) "(\<pi>\<^sub>0, r\<^sub>0) \<in> T\<^sub>1"
    unfolding then_d_split by blast
  then show "ext T\<^sub>1 \<rho> \<or> (\<exists>k < length \<rho>. (take (Suc k) \<rho>, Done) \<in> T\<^sub>1 \<and> ext T\<^sub>2 (drop k \<rho>))"
  proof cases
    case left
    then have "ext T\<^sub>1 \<rho>" unfolding ext_def using len pref by blast
    then show ?thesis ..
  next
    case seq
    show ?thesis
    proof (cases "length \<rho> < Suc k")
      case True
      have "take (length \<rho>) (take (Suc k) \<pi>\<^sub>0) = \<rho>" using True pref by (simp add: min_def)
      moreover have "length \<rho> < length (take (Suc k) \<pi>\<^sub>0)" using True seq(1) by simp
      ultimately have "ext T\<^sub>1 \<rho>" unfolding ext_def using seq(2) by blast
      then show ?thesis ..
    next
      case False
      then have kr: "k < length \<rho>" by simp
      have "take (Suc k) \<rho> = take (Suc k) (take (length \<rho>) \<pi>\<^sub>0)" using pref by simp
      also have "\<dots> = take (Suc k) \<pi>\<^sub>0" using False by (simp add: min_def)
      finally have tk: "take (Suc k) \<rho> = take (Suc k) \<pi>\<^sub>0" .
      moreover have "ext T\<^sub>2 (drop k \<rho>)"
        unfolding ext_def
      proof (intro exI conjI)
        show "(drop k \<pi>\<^sub>0, r\<^sub>0) \<in> T\<^sub>2" by (fact seq(3))
        show "length (drop k \<rho>) < length (drop k \<pi>\<^sub>0)" using len kr by simp
        have "drop k \<rho> = drop k (take (length \<rho>) \<pi>\<^sub>0)" using pref by simp
        also have "\<dots> = take (length \<rho> - k) (drop k \<pi>\<^sub>0)" by (rule drop_take)
        finally have dk: "drop k \<rho> = take (length \<rho> - k) (drop k \<pi>\<^sub>0)" .
        show "take (length (drop k \<rho>)) (drop k \<pi>\<^sub>0) = drop k \<rho>"
          unfolding length_drop by (rule dk[symmetric])
      qed
      ultimately show ?thesis using kr seq(2) tk by auto
    qed
  qed
next
  assume "ext T\<^sub>1 \<rho> \<or> (\<exists>k < length \<rho>. (take (Suc k) \<rho>, Done) \<in> T\<^sub>1 \<and> ext T\<^sub>2 (drop k \<rho>))"
  then show "ext (then_d T\<^sub>1 T\<^sub>2) \<rho>"
  proof
    assume "ext T\<^sub>1 \<rho>"
    then obtain \<pi>\<^sub>1 r\<^sub>1 where m1: "(\<pi>\<^sub>1, r\<^sub>1) \<in> T\<^sub>1" and len: "length \<rho> < length \<pi>\<^sub>1"
      and pref: "take (length \<rho>) \<pi>\<^sub>1 = \<rho>" unfolding ext_def by blast
    show ?thesis
    proof (cases "r\<^sub>1 = Done")
      case False
      have "(\<pi>\<^sub>1, r\<^sub>1) \<in> then_d T\<^sub>1 T\<^sub>2"
        unfolding then_d_iff by (intro disjI2) (use m1 False in simp)
      with len pref show ?thesis unfolding ext_def by blast
    next
      case True
      have ne: "\<pi>\<^sub>1 \<noteq> []" using len by auto
      from tot obtain \<pi>\<^sub>2 r\<^sub>2 where m2: "(\<pi>\<^sub>2, r\<^sub>2) \<in> T\<^sub>2" "\<pi>\<^sub>2 \<noteq> []" "hd \<pi>\<^sub>2 = last \<pi>\<^sub>1"
        by (rule totalE)
      have fu: "fusable \<pi>\<^sub>1 \<pi>\<^sub>2" using ne m2 by (simp add: fusable_def)
      have "(fuse \<pi>\<^sub>1 \<pi>\<^sub>2, r\<^sub>2) \<in> then_d T\<^sub>1 T\<^sub>2"
        unfolding then_d_iff
        by (intro disjI1 exI[of _ \<pi>\<^sub>1] exI[of _ \<pi>\<^sub>2]) (use m1 True m2(1) fu in simp)
      moreover have "length \<rho> < length (fuse \<pi>\<^sub>1 \<pi>\<^sub>2)" using len by (simp add: fuse_def)
      moreover have "take (length \<rho>) (fuse \<pi>\<^sub>1 \<pi>\<^sub>2) = \<rho>" using len pref by (simp add: fuse_def)
      ultimately show ?thesis unfolding ext_def by blast
    qed
  next
    assume "\<exists>k < length \<rho>. (take (Suc k) \<rho>, Done) \<in> T\<^sub>1 \<and> ext T\<^sub>2 (drop k \<rho>)"
    then obtain k where kr: "k < length \<rho>" and m1: "(take (Suc k) \<rho>, Done) \<in> T\<^sub>1"
      and e2: "ext T\<^sub>2 (drop k \<rho>)" by blast
    from e2 obtain \<pi>\<^sub>2 r\<^sub>2 where m2: "(\<pi>\<^sub>2, r\<^sub>2) \<in> T\<^sub>2" and len2: "length (drop k \<rho>) < length \<pi>\<^sub>2"
      and pref2: "take (length (drop k \<rho>)) \<pi>\<^sub>2 = drop k \<rho>" unfolding ext_def by blast
    let ?p = "take (Suc k) \<rho>"
    have hd2: "hd \<pi>\<^sub>2 = \<rho> ! k"
    proof -
      have "hd \<pi>\<^sub>2 = hd (take (length (drop k \<rho>)) \<pi>\<^sub>2)" using kr by (cases \<pi>\<^sub>2) auto
      also have "\<dots> = hd (drop k \<rho>)" using pref2 by simp
      also have "\<dots> = \<rho> ! k" using kr by (simp add: hd_drop_conv_nth)
      finally show ?thesis .
    qed
    have fu: "fusable ?p \<pi>\<^sub>2" using kr len2 hd2 by (auto simp: fusable_def last_take_Suc)
    have "(fuse ?p \<pi>\<^sub>2, r\<^sub>2) \<in> then_d T\<^sub>1 T\<^sub>2"
      unfolding then_d_iff
      by (intro disjI1 exI[of _ ?p] exI[of _ \<pi>\<^sub>2]) (use m1 m2 fu in simp)
    moreover have "length \<rho> < length (fuse ?p \<pi>\<^sub>2)" using kr len2 by (simp add: fuse_def)
    moreover have "take (length \<rho>) (fuse ?p \<pi>\<^sub>2) = \<rho>"
    proof -
      have "take (length \<rho>) (fuse ?p \<pi>\<^sub>2) = ?p @ take (length \<rho> - Suc k) (tl \<pi>\<^sub>2)"
        using kr by (simp add: fuse_def)
      also have "take (length \<rho> - Suc k) (tl \<pi>\<^sub>2) = tl (take (length \<rho> - k) \<pi>\<^sub>2)"
        using kr by (simp add: take_tl Suc_diff_Suc)
      also have "\<dots> = tl (drop k \<rho>)" using pref2 by simp
      also have "\<dots> = drop (Suc k) \<rho>" by (simp add: tl_drop drop_Suc)
      finally show ?thesis by simp
    qed
    ultimately show ?thesis unfolding ext_def by blast
  qed
qed

lemma is_trace_take: "is_trace \<pi> \<Longrightarrow> 0 < n \<Longrightarrow> is_trace (take n \<pi>)"
  using is_trace_pre[of \<pi> "n - 1"] by (simp add: pre_def)

lemma ext_wf:
  assumes "wf_den T" and "\<rho> \<noteq> []" and "ext T \<rho>"
  shows "is_trace \<rho>"
proof -
  from assms(3) obtain \<pi>\<^sub>0 r\<^sub>0 where m: "(\<pi>\<^sub>0, r\<^sub>0) \<in> T"
    and pref: "take (length \<rho>) \<pi>\<^sub>0 = \<rho>" unfolding ext_def by blast
  have tr: "is_trace \<pi>\<^sub>0" using assms(1) m by (rule wf_denD)
  have "0 < length \<rho>" using assms(2) by simp
  then have "is_trace (take (length \<rho>) \<pi>\<^sub>0)" by (rule is_trace_take[OF tr])
  with pref show ?thesis by simp
qed

lemma is_trace_snoc:
  assumes "is_trace \<rho>" and "tstamp y = tstamp (last \<rho>)"
  shows "is_trace (\<rho> @ [y])"
proof -
  have ne: "\<rho> \<noteq> []" and s: "sorted (map tstamp \<rho>)" using assms(1) by (simp_all add: is_trace_def)
  have "\<forall>z \<in> set \<rho>. tstamp z \<le> tstamp y"
  proof
    fix z assume "z \<in> set \<rho>"
    then have "tstamp z \<le> last (map tstamp \<rho>)" using sorted_le_last[OF s] by simp
    then show "tstamp z \<le> tstamp y" using assms(2) ne by (simp add: last_map)
  qed
  with s show ?thesis by (simp add: is_trace_def sorted_append)
qed

lemma ext_must:
  assumes ne: "\<rho> \<noteq> []"
  shows "ext (must_d s a) \<rho> \<longleftrightarrow> is_trace \<rho>"
proof
  assume "ext (must_d s a) \<rho>"
  with wf_must ne show "is_trace \<rho>" by (rule ext_wf)
next
  assume tr: "is_trace \<rho>"
  let ?y = "(sta (last \<rho>), tstamp (last \<rho>), Deontic s a Must)"
  have "tstamp ?y = tstamp (last \<rho>)" by simp
  with tr have tr': "is_trace (\<rho> @ [?y])" by (rule is_trace_snoc)
  have ev: "does s a (evt (last (\<rho> @ [?y])))" by (simp add: does_def)
  have l2: "2 \<le> length (\<rho> @ [?y])" using ne by (cases \<rho>) simp_all
  have m: "(\<rho> @ [?y], Done) \<in> must_d s a" unfolding must_d_def using tr' l2 ev by blast
  have "length \<rho> < length (\<rho> @ [?y])" by simp
  moreover have "take (length \<rho>) (\<rho> @ [?y]) = \<rho>" by simp
  ultimately show "ext (must_d s a) \<rho>" unfolding ext_def using m by blast
qed

text \<open>A proper prefix of a violated trace of a prohibition is a trace with no forbidden
  action yet. It can be continued to a violation at once if the condition is true in its
  last state.\<close>

lemma ext_mustnot_forbidden:
  assumes "ext (mustnot_d s a c) \<rho>" and "j < length \<rho>"
  shows "\<not> forbidden s a c \<rho> j"
proof
  assume f: "forbidden s a c \<rho> j"
  from assms(1) obtain \<pi>\<^sub>0 r\<^sub>0 where m: "(\<pi>\<^sub>0, r\<^sub>0) \<in> mustnot_d s a c" and len: "length \<rho> < length \<pi>\<^sub>0"
    and tk: "take (length \<rho>) \<pi>\<^sub>0 = \<rho>"
    unfolding ext_def by blast
  have l2: "2 \<le> length \<pi>\<^sub>0" using len assms(2) by linarith
  have nf: "\<forall>i < length \<pi>\<^sub>0 - 1. \<not> forbidden s a c \<pi>\<^sub>0 i"
    using m l2 unfolding mustnot_d_def by auto
  have sp: "\<rho> @ drop (length \<rho>) \<pi>\<^sub>0 = \<pi>\<^sub>0" using tk by (metis append_take_drop_id)
  have "forbidden s a c (\<rho> @ drop (length \<rho>) \<pi>\<^sub>0) j"
    using forbidden_append[OF assms(2)] f by blast
  then have f0: "forbidden s a c \<pi>\<^sub>0 j" by (simp only: sp)
  have "j < length \<pi>\<^sub>0 - 1" using assms(2) len by linarith
  with nf f0 show False by blast
qed

lemma ext_mustnot:
  assumes tr: "is_trace \<rho>" and nf: "\<forall>j < length \<rho>. \<not> forbidden s a c \<rho> j"
    and c: "eval c (st \<rho> (length \<rho> - 1)) = Some True"
  shows "ext (mustnot_d s a c) \<rho>"
proof -
  let ?y = "(sta (last \<rho>), tstamp (last \<rho>), Deontic s a MustNot)"
  have lp: "0 < length \<rho>" using tr by (simp add: is_trace_def)
  have "tstamp ?y = tstamp (last \<rho>)" by simp
  with tr have tr': "is_trace (\<rho> @ [?y])" by (rule is_trace_snoc)
  have st_eq: "st (\<rho> @ [?y]) (length \<rho> - 1) = st \<rho> (length \<rho> - 1)"
    using lp by (simp add: st_def nth_append)
  have f: "forbidden s a c (\<rho> @ [?y]) (length (\<rho> @ [?y]) - 1)"
    using lp c st_eq by (cases \<rho>) (auto simp: forbidden_def does_def)
  have nf': "\<forall>j < length (\<rho> @ [?y]) - 1. \<not> forbidden s a c (\<rho> @ [?y]) j"
    using nf forbidden_append[of _ \<rho> s a c "[?y]"] by simp
  have m: "(\<rho> @ [?y], Violated) \<in> mustnot_d s a c" unfolding mustnot_d_def using tr' f nf' by blast
  have "length \<rho> < length (\<rho> @ [?y])" by simp
  moreover have "take (length \<rho>) (\<rho> @ [?y]) = \<rho>" by simp
  ultimately show ?thesis unfolding ext_def using m by blast
qed

lemma ext_may:
  assumes tr: "is_trace \<rho>" and c: "eval c (st \<rho> (length \<rho> - 1)) = Some True"
  shows "ext (may_d s a c) \<rho>"
proof -
  let ?y = "(sta (last \<rho>), tstamp (last \<rho>), Deontic s a May)"
  have lp: "0 < length \<rho>" using tr by (simp add: is_trace_def)
  have "tstamp ?y = tstamp (last \<rho>)" by simp
  with tr have tr': "is_trace (\<rho> @ [?y])" by (rule is_trace_snoc)
  have ev: "does s a (evt (last (\<rho> @ [?y])))" by (simp add: does_def)
  have e1: "length (\<rho> @ [?y]) - 1 = length \<rho>" by simp
  have l1: "1 \<le> length (\<rho> @ [?y]) - 1" unfolding e1 using lp by linarith
  have i: "length (\<rho> @ [?y]) - 2 = length \<rho> - 1" by (simp only: length_append_singleton)
  have "length \<rho> - 1 < length \<rho>" using lp by simp
  then have st_eq: "st (\<rho> @ [?y]) (length (\<rho> @ [?y]) - 2) = st \<rho> (length \<rho> - 1)"
    unfolding i by (simp add: st_def nth_append)
  have ce: "eval c (st (\<rho> @ [?y]) (length (\<rho> @ [?y]) - 2)) = Some True"
    by (simp only: st_eq c)
  have m: "(\<rho> @ [?y], Done) \<in> may_d s a c" unfolding may_d_def using tr' ev l1 ce by blast
  have "length \<rho> < length (\<rho> @ [?y])" by simp
  moreover have "take (length \<rho>) (\<rho> @ [?y]) = \<rho>" by simp
  ultimately show ?thesis unfolding ext_def using m by blast
qed

lemma mem_must:
  "(\<pi>, r) \<in> must_d s a \<longleftrightarrow> is_trace \<pi> \<and> 2 \<le> length \<pi> \<and> does s a (evt (last \<pi>)) \<and> r = Done"
  by (auto simp: must_d_def)

lemma len1: "(\<exists>x. \<pi> = [x]) \<longleftrightarrow> length \<pi> = 1"
  by (cases \<pi>) auto

lemma mem_may:
  "(\<pi>, r) \<in> may_d s a c \<longleftrightarrow>
     r = Done \<and> ((is_trace \<pi> \<and> does s a (evt (last \<pi>)) \<and> 1 \<le> length \<pi> - 1
                   \<and> eval c (st \<pi> (length \<pi> - 2)) = Some True) \<or> length \<pi> = 1)"
  unfolding may_d_def len1[symmetric] by auto

lemma mem_mustnot:
  "(\<pi>, r) \<in> mustnot_d s a c \<longleftrightarrow>
     (if r = Done then length \<pi> = 1
      else r = Violated \<and> is_trace \<pi> \<and> forbidden s a c \<pi> (length \<pi> - 1)
           \<and> (\<forall>j \<in> set [0..<length \<pi> - 1]. \<not> forbidden s a c \<pi> j))"
  unfolding mustnot_d_def len1[symmetric] by auto

lemma mem_skip: "(\<pi>, r) \<in> skip_d \<longleftrightarrow> r = Done \<and> length \<pi> = 1"
  unfolding skip_d_def len1[symmetric] by auto

lemma ext_skip:
  assumes "\<rho> \<noteq> []"
  shows "\<not> ext skip_d \<rho>"
proof
  assume "ext skip_d \<rho>"
  then obtain \<pi>\<^sub>0 r\<^sub>0 where m: "(\<pi>\<^sub>0, r\<^sub>0) \<in> skip_d" and len: "length \<rho> < length \<pi>\<^sub>0"
    and "take (length \<rho>) \<pi>\<^sub>0 = \<rho>"
    unfolding ext_def by blast
  from m obtain x where "\<pi>\<^sub>0 = [x]" unfolding skip_d_def by blast
  with len assms show False by simp
qed

lemma st_0: "\<pi> \<noteq> [] \<Longrightarrow> st \<pi> 0 = sta (hd \<pi>)"
  by (cases \<pi>) (simp_all add: st_def)

lemma take_hd: "take (length \<rho>) \<pi>\<^sub>0 = \<rho> \<Longrightarrow> \<rho> \<noteq> [] \<Longrightarrow> \<pi>\<^sub>0 \<noteq> [] \<and> hd \<pi>\<^sub>0 = hd \<rho>"
  by (cases \<pi>\<^sub>0; cases \<rho>) auto

text \<open>A proper prefix of a trace of IF starts where the trace does, so the condition is read
  in the first state of the prefix.\<close>

lemma ext_if_branch:
  assumes ne: "\<rho> \<noteq> []"
    and br: "\<And>\<pi>\<^sub>0 r\<^sub>0. \<pi>\<^sub>0 \<noteq> [] \<Longrightarrow> hd \<pi>\<^sub>0 = hd \<rho> \<Longrightarrow> (\<pi>\<^sub>0, r\<^sub>0) \<in> if_d c T E \<longleftrightarrow> (\<pi>\<^sub>0, r\<^sub>0) \<in> X"
  shows "ext (if_d c T E) \<rho> \<longleftrightarrow> ext X \<rho>"
proof
  assume "ext (if_d c T E) \<rho>"
  then obtain \<pi>\<^sub>0 r\<^sub>0 where m: "(\<pi>\<^sub>0, r\<^sub>0) \<in> if_d c T E" and l: "length \<rho> < length \<pi>\<^sub>0"
    and tk: "take (length \<rho>) \<pi>\<^sub>0 = \<rho>" unfolding ext_def by blast
  from take_hd[OF tk ne] m br have "(\<pi>\<^sub>0, r\<^sub>0) \<in> X" by blast
  with l tk show "ext X \<rho>" unfolding ext_def by blast
next
  assume "ext X \<rho>"
  then obtain \<pi>\<^sub>0 r\<^sub>0 where m: "(\<pi>\<^sub>0, r\<^sub>0) \<in> X" and l: "length \<rho> < length \<pi>\<^sub>0"
    and tk: "take (length \<rho>) \<pi>\<^sub>0 = \<rho>" unfolding ext_def by blast
  from take_hd[OF tk ne] m br have "(\<pi>\<^sub>0, r\<^sub>0) \<in> if_d c T E" by blast
  with l tk show "ext (if_d c T E) \<rho>" unfolding ext_def by blast
qed

lemma ext_if:
  assumes ne: "\<rho> \<noteq> []"
  shows "ext (if_d c T E) \<rho> \<longleftrightarrow> (if eval c (sta (hd \<rho>)) = Some True then ext T \<rho> else ext E \<rho>)"
proof (cases "eval c (sta (hd \<rho>)) = Some True")
  case True
  have "ext (if_d c T E) \<rho> \<longleftrightarrow> ext T \<rho>"
    by (rule ext_if_branch[OF ne]) (use True in \<open>auto simp: if_d_def\<close>)
  with True show ?thesis by simp
next
  case False
  have "ext (if_d c T E) \<rho> \<longleftrightarrow> ext E \<rho>"
    by (rule ext_if_branch[OF ne]) (use False in \<open>auto simp: if_d_def\<close>)
  with False show ?thesis by simp
qed


subsection \<open>The decision procedure\<close>

fun and_free :: "('n, 'v, 's, 'a) tm \<Rightarrow> bool" where
  "and_free (TThen t u) = (and_free t \<and> and_free u)"
| "and_free (TOr t u) = (and_free t \<and> and_free u)"
| "and_free (TUnless t c u) = (and_free t \<and> and_free u)"
| "and_free (TAnd t u) = False"
| "and_free (TIf c t u) = (and_free t \<and> and_free u)"
| "and_free _ = True"

fun unless_free :: "('n, 'v, 's, 'a) tm \<Rightarrow> bool" where
  "unless_free (TThen t u) = (unless_free t \<and> unless_free u)"
| "unless_free (TOr t u) = (unless_free t \<and> unless_free u)"
| "unless_free (TUnless t c u) = False"
| "unless_free (TIf c t u) = (unless_free t \<and> unless_free u)"
| "unless_free (TAnd t u) = (unless_free t \<and> unless_free u)"
| "unless_free _ = True"

text \<open>\<open>mem3 t \<pi> r\<close> decides whether \<open>(\<pi>, r)\<close> is in the denotation of \<open>t\<close>; \<open>ext3 t \<rho>\<close> decides
  whether \<open>\<rho>\<close> is a proper prefix of a trace of \<open>t\<close>. \<open>None\<close> means unknown. For UNLESS, an
  interrupted trace requires that the observed prefix can be continued by \<open>t\<^sub>1\<close>; this is
  decided exactly for MUST and THEN-chains of MUST, and left unknown where it would depend
  on the satisfiability of a guard.\<close>

fun mem3 :: "('n, 'v :: value_order, 's, 'a) tm \<Rightarrow> ('n, 'v, 't :: linorder, 's, 'a) trace \<Rightarrow> outcome \<Rightarrow> bool option"
and ext3 :: "('n, 'v :: value_order, 's, 'a) tm \<Rightarrow> ('n, 'v, 't :: linorder, 's, 'a) trace \<Rightarrow> bool option" where
  "mem3 (TMust s a) \<pi> r = Some (is_trace \<pi> \<and> 2 \<le> length \<pi> \<and> does s a (evt (last \<pi>)) \<and> r = Done)"
| "mem3 (TMay s a c) \<pi> r =
     Some (r = Done \<and> ((is_trace \<pi> \<and> does s a (evt (last \<pi>)) \<and> 1 \<le> length \<pi> - 1
                         \<and> eval c (st \<pi> (length \<pi> - 2)) = Some True) \<or> length \<pi> = 1))"
| "mem3 (TMustNot s a c) \<pi> r =
     Some (if r = Done then length \<pi> = 1
           else r = Violated \<and> is_trace \<pi> \<and> forbidden s a c \<pi> (length \<pi> - 1)
                \<and> (\<forall>j \<in> set [0..<length \<pi> - 1]. \<not> forbidden s a c \<pi> j))"
| "mem3 (TOr t u) \<pi> r = kor (mem3 t \<pi> r) (mem3 u \<pi> r)"
| "mem3 (TThen t u) \<pi> r =
     kor (kors (map (\<lambda>k. kand (mem3 t (take (Suc k) \<pi>) Done) (mem3 u (drop k \<pi>) r)) [0..<length \<pi>]))
         (kand (mem3 t \<pi> r) (Some (r \<noteq> Done)))"
| "mem3 (TUnless t c u) \<pi> r =
     kor (kand (mem3 t \<pi> r) (Some (\<forall>j \<in> set [0..<length \<pi> - 1]. eval c (st \<pi> j) \<noteq> Some True)))
         (kors (map (\<lambda>k. if first_at c \<pi> k
                         then kand (ext3 t (take (Suc k) \<pi>))
                                   (kors (map (\<lambda>r'. mem3 u (drop k \<pi>) r')
                                              (filter (\<lambda>r'. kappa r' = r) [Done, Interrupted, Violated])))
                         else Some False)
                    [0..<length \<pi>]))"
| "mem3 (TAnd t u) \<pi> r = None"
| "mem3 (TIf c t u) \<pi> r =
     (if \<pi> = [] then Some False
      else if eval c (st \<pi> 0) = Some True then mem3 t \<pi> r else mem3 u \<pi> r)"
| "mem3 TSkip \<pi> r = Some (r = Done \<and> length \<pi> = 1)"
| "ext3 (TMust s a) \<rho> = Some (is_trace \<rho>)"
| "ext3 (TMay s a c) \<rho> =
     (if \<not> is_trace \<rho> then Some False
      else if eval c (st \<rho> (length \<rho> - 1)) = Some True then Some True else None)"
| "ext3 (TMustNot s a c) \<rho> =
     (if \<not> is_trace \<rho> \<or> (\<exists>j \<in> set [0..<length \<rho>]. forbidden s a c \<rho> j) then Some False
      else if eval c (st \<rho> (length \<rho> - 1)) = Some True then Some True else None)"
| "ext3 (TOr t u) \<rho> = kor (ext3 t \<rho>) (ext3 u \<rho>)"
| "ext3 (TThen t u) \<rho> =
     kor (ext3 t \<rho>)
         (kors (map (\<lambda>k. kand (mem3 t (take (Suc k) \<rho>) Done) (ext3 u (drop k \<rho>))) [0..<length \<rho>]))"
| "ext3 (TUnless t c u) \<rho> = (if \<not> is_trace \<rho> then Some False else None)"
| "ext3 (TAnd t u) \<rho> = None"
| "ext3 (TIf c t u) \<rho> = (if eval c (st \<rho> 0) = Some True then ext3 t \<rho> else ext3 u \<rho>)"
| "ext3 TSkip \<rho> = Some False"

lemma kappa_exists:
  "(\<exists>r'. kappa r' = r \<and> P r') \<longleftrightarrow>
     (\<exists>r' \<in> set (filter (\<lambda>r'. kappa r' = r) [Done, Interrupted, Violated]). P r')"
proof
  assume "\<exists>r'. kappa r' = r \<and> P r'"
  then obtain r' where k: "kappa r' = r" and p: "P r'" by blast
  have "r' \<in> set (filter (\<lambda>r'. kappa r' = r) [Done, Interrupted, Violated])"
    using k by (cases r') simp_all
  with p show "\<exists>r' \<in> set (filter (\<lambda>r'. kappa r' = r) [Done, Interrupted, Violated]). P r'" by blast
next
  assume "\<exists>r' \<in> set (filter (\<lambda>r'. kappa r' = r) [Done, Interrupted, Violated]). P r'"
  then obtain r' where "r' \<in> set (filter (\<lambda>r'. kappa r' = r) [Done, Interrupted, Violated])" "P r'"
    by blast
  then show "\<exists>r'. kappa r' = r \<and> P r'" unfolding set_filter by blast
qed

lemma kappa_forall:
  "(\<forall>r'. kappa r' = r \<longrightarrow> P r') \<longleftrightarrow>
     (\<forall>r' \<in> set (filter (\<lambda>r'. kappa r' = r) [Done, Interrupted, Violated]). P r')"
proof
  assume a: "\<forall>r'. kappa r' = r \<longrightarrow> P r'"
  show "\<forall>r' \<in> set (filter (\<lambda>r'. kappa r' = r) [Done, Interrupted, Violated]). P r'"
  proof
    fix r' assume "r' \<in> set (filter (\<lambda>r'. kappa r' = r) [Done, Interrupted, Violated])"
    then have "kappa r' = r" unfolding set_filter by blast
    with a show "P r'" by blast
  qed
next
  assume a: "\<forall>r' \<in> set (filter (\<lambda>r'. kappa r' = r) [Done, Interrupted, Violated]). P r'"
  show "\<forall>r'. kappa r' = r \<longrightarrow> P r'"
  proof (intro allI impI)
    fix r' assume k: "kappa r' = r"
    have "r' \<in> set (filter (\<lambda>r'. kappa r' = r) [Done, Interrupted, Violated])"
      using k by (cases r') simp_all
    with a show "P r'" by blast
  qed
qed

context term_semantics
begin

lemma wf_den_den: "and_free t \<Longrightarrow> wf_den (den t)"
  by (induction t) (simp_all add: wf_must wf_may wf_mustnot wf_then wf_or wf_unless wf_if wf_skip)

text \<open>Soundness: a definite answer of \<open>mem3\<close> or \<open>ext3\<close> is the truth.\<close>

theorem mem3_ext3_sound:
  assumes "and_free t"
  shows "(mem3 t \<pi> r = Some b \<longrightarrow> ((\<pi>, r) \<in> den t \<longleftrightarrow> b))
       \<and> (\<rho> \<noteq> [] \<longrightarrow> ext3 t \<rho> = Some b' \<longrightarrow> (ext (den t) \<rho> \<longleftrightarrow> b'))"
  using assms
proof (induction t arbitrary: \<pi> r b \<rho> b')
  case (TMust s a)
  then show ?case by (auto simp: mem_must ext_must)
next
  case (TMay s a c)
  have e1: "\<not> ext (may_d s a c) \<rho>" if "\<rho> \<noteq> []" "\<not> is_trace \<rho>"
    using ext_wf[OF wf_may that(1)] that(2) by blast
  have e2: "ext (may_d s a c) \<rho>" if "is_trace \<rho>" "eval c (st \<rho> (length \<rho> - 1)) = Some True"
    using that by (rule ext_may)
  show ?case
    by (auto simp: mem_may e1 e2 split: if_splits)
next
  case (TMustNot s a c)
  have e1: "\<not> ext (mustnot_d s a c) \<rho>" if "\<rho> \<noteq> []" "\<not> is_trace \<rho>"
    using ext_wf[OF wf_mustnot that(1)] that(2) by blast
  have e2: "\<not> ext (mustnot_d s a c) \<rho>" if "j < length \<rho>" "forbidden s a c \<rho> j" for j
    using ext_mustnot_forbidden[of s a c \<rho> j] that by blast
  have e3: "ext (mustnot_d s a c) \<rho>"
    if "is_trace \<rho>" "\<forall>j < length \<rho>. \<not> forbidden s a c \<rho> j"
       "eval c (st \<rho> (length \<rho> - 1)) = Some True"
    using ext_mustnot[OF that] .
  show ?case
  proof (intro conjI impI)
    assume "mem3 (TMustNot s a c) \<pi> r = Some b"
    then show "(\<pi>, r) \<in> den (TMustNot s a c) \<longleftrightarrow> b"
      by (simp only: mem3.simps den.simps mem_mustnot) auto
  next
    assume ne: "\<rho> \<noteq> []" and e: "ext3 (TMustNot s a c) \<rho> = Some b'"
    show "ext (den (TMustNot s a c)) \<rho> \<longleftrightarrow> b'"
      using e e1[OF ne] e2 e3 by (auto split: if_splits)
  qed
next
  case (TOr t u)
  from TOr.prems have ft: "and_free t" and fu: "and_free u" by simp_all
  note IHt = TOr.IH(1)[OF ft] and IHu = TOr.IH(2)[OF fu]
  show ?case
  proof (intro conjI impI)
    assume m: "mem3 (TOr t u) \<pi> r = Some b"
    show "(\<pi>, r) \<in> den (TOr t u) \<longleftrightarrow> b"
    proof (cases b)
      case True
      with m have "mem3 t \<pi> r = Some True \<or> mem3 u \<pi> r = Some True" by (simp add: kor_True_iff)
      with IHt[of \<pi> r True] IHu[of \<pi> r True] True show ?thesis by (auto simp: or_d_def)
    next
      case False
      with m have "mem3 t \<pi> r = Some False \<and> mem3 u \<pi> r = Some False" by (simp add: kor_False_iff)
      with IHt[of \<pi> r False] IHu[of \<pi> r False] False show ?thesis by (auto simp: or_d_def)
    qed
  next
    assume ne: "\<rho> \<noteq> []" and e: "ext3 (TOr t u) \<rho> = Some b'"
    show "ext (den (TOr t u)) \<rho> \<longleftrightarrow> b'"
    proof (cases b')
      case True
      with e have "ext3 t \<rho> = Some True \<or> ext3 u \<rho> = Some True" by (simp add: kor_True_iff)
      with IHt[of _ _ _ \<rho> True] IHu[of _ _ _ \<rho> True] ne True show ?thesis by (auto simp: ext_or)
    next
      case False
      with e have "ext3 t \<rho> = Some False \<and> ext3 u \<rho> = Some False" by (simp add: kor_False_iff)
      with IHt[of _ _ _ \<rho> False] IHu[of _ _ _ \<rho> False] ne False show ?thesis by (auto simp: ext_or)
    qed
  qed
next
  case (TThen t u)
  from TThen.prems have ft: "and_free t" and fu: "and_free u" by simp_all
  note IHt = TThen.IH(1)[OF ft] and IHu = TThen.IH(2)[OF fu]
  show ?case
  proof (intro conjI impI)
    assume m: "mem3 (TThen t u) \<pi> r = Some b"
    show "(\<pi>, r) \<in> den (TThen t u) \<longleftrightarrow> b"
    proof (cases b)
      case True
      have "kor (kors (map (\<lambda>k. kand (mem3 t (take (Suc k) \<pi>) Done) (mem3 u (drop k \<pi>) r)) [0..<length \<pi>]))
                (kand (mem3 t \<pi> r) (Some (r \<noteq> Done))) = Some True"
        using m True by (simp only: mem3.simps)
      then have "(\<exists>k \<in> set [0..<length \<pi>].
                    kand (mem3 t (take (Suc k) \<pi>) Done) (mem3 u (drop k \<pi>) r) = Some True)
                 \<or> kand (mem3 t \<pi> r) (Some (r \<noteq> Done)) = Some True"
        unfolding kor_True_iff kors_map_True .
      then consider (seq) k where "k < length \<pi>" "mem3 t (take (Suc k) \<pi>) Done = Some True"
          "mem3 u (drop k \<pi>) r = Some True"
        | (left) "mem3 t \<pi> r = Some True" "r \<noteq> Done"
        unfolding kand_True_iff by fastforce
      then show ?thesis
      proof cases
        case seq
        then show ?thesis using IHt[of "take (Suc k) \<pi>" Done True] IHu[of "drop k \<pi>" r True] True
          by (auto simp: then_d_split)
      next
        case left
        then show ?thesis using IHt[of \<pi> r True] True by (auto simp: then_d_split)
      qed
    next
      case False
      have "kor (kors (map (\<lambda>k. kand (mem3 t (take (Suc k) \<pi>) Done) (mem3 u (drop k \<pi>) r)) [0..<length \<pi>]))
                (kand (mem3 t \<pi> r) (Some (r \<noteq> Done))) = Some False"
        using m False by (simp only: mem3.simps)
      then have c: "(\<forall>k \<in> set [0..<length \<pi>].
                       kand (mem3 t (take (Suc k) \<pi>) Done) (mem3 u (drop k \<pi>) r) = Some False)
                    \<and> kand (mem3 t \<pi> r) (Some (r \<noteq> Done)) = Some False"
        unfolding kor_False_iff kors_map_False .
      have all: "\<forall>k < length \<pi>. mem3 t (take (Suc k) \<pi>) Done = Some False \<or> mem3 u (drop k \<pi>) r = Some False"
        using conjunct1[OF c] unfolding kand_False_iff by auto
      have lft: "mem3 t \<pi> r = Some False \<or> r = Done"
        using conjunct2[OF c] unfolding kand_False_iff by simp
      have "\<not> ((\<exists>k < length \<pi>. (take (Suc k) \<pi>, Done) \<in> den t \<and> (drop k \<pi>, r) \<in> den u)
             \<or> ((\<pi>, r) \<in> den t \<and> r \<noteq> Done))"
      proof
        assume "(\<exists>k < length \<pi>. (take (Suc k) \<pi>, Done) \<in> den t \<and> (drop k \<pi>, r) \<in> den u)
             \<or> ((\<pi>, r) \<in> den t \<and> r \<noteq> Done)"
        then show False
        proof
          assume "\<exists>k < length \<pi>. (take (Suc k) \<pi>, Done) \<in> den t \<and> (drop k \<pi>, r) \<in> den u"
          then obtain k where "k < length \<pi>" "(take (Suc k) \<pi>, Done) \<in> den t" "(drop k \<pi>, r) \<in> den u"
            by blast
          with all IHt[of "take (Suc k) \<pi>" Done False] IHu[of "drop k \<pi>" r False] show False by blast
        next
          assume "(\<pi>, r) \<in> den t \<and> r \<noteq> Done"
          with lft IHt[of \<pi> r False] show False by blast
        qed
      qed
      with False show ?thesis by (simp add: then_d_split)
    qed
  next
    assume ne: "\<rho> \<noteq> []" and e: "ext3 (TThen t u) \<rho> = Some b'"
    have split: "ext (den (TThen t u)) \<rho> \<longleftrightarrow>
        ext (den t) \<rho> \<or> (\<exists>k < length \<rho>. (take (Suc k) \<rho>, Done) \<in> den t \<and> ext (den u) (drop k \<rho>))"
      using ext_then[OF den_total[of u]] by simp
    show "ext (den (TThen t u)) \<rho> \<longleftrightarrow> b'"
    proof (cases b')
      case True
      have "kor (ext3 t \<rho>)
                (kors (map (\<lambda>k. kand (mem3 t (take (Suc k) \<rho>) Done) (ext3 u (drop k \<rho>))) [0..<length \<rho>]))
              = Some True"
        using e True by (simp only: ext3.simps)
      then have "ext3 t \<rho> = Some True
                 \<or> (\<exists>k \<in> set [0..<length \<rho>].
                      kand (mem3 t (take (Suc k) \<rho>) Done) (ext3 u (drop k \<rho>)) = Some True)"
        unfolding kor_True_iff kors_map_True .
      then consider (left) "ext3 t \<rho> = Some True"
        | (seq) k where "k < length \<rho>" "mem3 t (take (Suc k) \<rho>) Done = Some True"
            "ext3 u (drop k \<rho>) = Some True"
        unfolding kand_True_iff by fastforce
      then show ?thesis
      proof cases
        case left
        with IHt[of _ _ _ \<rho> True] ne True split show ?thesis by blast
      next
        case seq
        have "drop k \<rho> \<noteq> []" using seq(1) by simp
        with seq IHt[of "take (Suc k) \<rho>" Done True] IHu[of _ _ _ "drop k \<rho>" True] True split
        show ?thesis by blast
      qed
    next
      case False
      with e have l: "ext3 t \<rho> = Some False"
        and all: "\<forall>k < length \<rho>. mem3 t (take (Suc k) \<rho>) Done = Some False \<or> ext3 u (drop k \<rho>) = Some False"
        by (auto simp: kor_False_iff kors_False kand_False_iff)
      have "\<not> ext (den t) \<rho>" using IHt[of _ _ _ \<rho> False] ne l by blast
      moreover have "\<not> (\<exists>k < length \<rho>. (take (Suc k) \<rho>, Done) \<in> den t \<and> ext (den u) (drop k \<rho>))"
      proof
        assume "\<exists>k < length \<rho>. (take (Suc k) \<rho>, Done) \<in> den t \<and> ext (den u) (drop k \<rho>)"
        then obtain k where k: "k < length \<rho>" "(take (Suc k) \<rho>, Done) \<in> den t" "ext (den u) (drop k \<rho>)"
          by blast
        have "drop k \<rho> \<noteq> []" using k(1) by simp
        with k all IHt[of "take (Suc k) \<rho>" Done False] IHu[of _ _ _ "drop k \<rho>" False] show False
          by blast
      qed
      ultimately show ?thesis using split False by blast
    qed
  qed
next
  case (TUnless t c u)
  from TUnless.prems have ft: "and_free t" and fu: "and_free u" by simp_all
  note IHt = TUnless.IH(1)[OF ft] and IHu = TUnless.IH(2)[OF fu]
  define nf where "nf = (\<forall>j \<in> set [0..<length \<pi> - 1]. eval c (st \<pi> j) \<noteq> Some True)"
  have nf_iff: "nf \<longleftrightarrow> (\<forall>j < length \<pi> - 1. eval c (st \<pi> j) \<noteq> Some True)" by (auto simp: nf_def)
  define R where "R = filter (\<lambda>r'. kappa r' = r) [Done, Interrupted, Violated]"
  define g where "g k = (if first_at c \<pi> k
                         then kand (ext3 t (take (Suc k) \<pi>)) (kors (map (\<lambda>r'. mem3 u (drop k \<pi>) r') R))
                         else Some False)" for k
  have m_eq: "mem3 (TUnless t c u) \<pi> r = kor (kand (mem3 t \<pi> r) (Some nf)) (kors (map g [0..<length \<pi>]))"
    unfolding nf_def R_def g_def by (simp only: mem3.simps)
  show ?case
  proof (intro conjI impI)
    assume m: "mem3 (TUnless t c u) \<pi> r = Some b"
    show "(\<pi>, r) \<in> den (TUnless t c u) \<longleftrightarrow> b"
    proof (cases b)
      case True
      have "kor (kand (mem3 t \<pi> r) (Some nf)) (kors (map g [0..<length \<pi>])) = Some True"
        using m True by (simp only: m_eq)
      then have "(mem3 t \<pi> r = Some True \<and> Some nf = Some True)
                 \<or> (\<exists>k \<in> set [0..<length \<pi>]. g k = Some True)"
        unfolding kor_True_iff kand_True_iff kors_map_True .
      then consider (keep) "mem3 t \<pi> r = Some True" "nf"
        | (int) k where "k < length \<pi>" "g k = Some True"
        by fastforce
      then show ?thesis
      proof cases
        case keep
        with IHt[of \<pi> r True] nf_iff True show ?thesis by (simp add: unless_d_split)
      next
        case int
        have fa: "first_at c \<pi> k"
        proof (rule ccontr)
          assume "\<not> first_at c \<pi> k"
          with int(2) show False by (simp add: g_def)
        qed
        with int(2) have "kand (ext3 t (take (Suc k) \<pi>)) (kors (map (\<lambda>r'. mem3 u (drop k \<pi>) r') R))
                          = Some True"
          by (simp add: g_def)
        then have e: "ext3 t (take (Suc k) \<pi>) = Some True"
          and r: "\<exists>r' \<in> set R. mem3 u (drop k \<pi>) r' = Some True"
          unfolding kand_True_iff kors_map_True by simp_all
        have "take (Suc k) \<pi> \<noteq> []" using int(1) by (cases \<pi>) simp_all
        with e IHt[of _ _ _ "take (Suc k) \<pi>" True] have ext_t: "ext (den t) (take (Suc k) \<pi>)" by blast
        from r obtain r' where rR: "r' \<in> set R" and mr: "mem3 u (drop k \<pi>) r' = Some True" by blast
        have kr: "kappa r' = r" using rR unfolding R_def set_filter by blast
        have "(drop k \<pi>, r') \<in> den u" using IHu[of "drop k \<pi>" r' True] mr by blast
        with kr have ex_u: "\<exists>r'. kappa r' = r \<and> (drop k \<pi>, r') \<in> den u" by blast
        have "\<exists>k < length \<pi>. first_at c \<pi> k \<and> ext (den t) (take (Suc k) \<pi>)
                \<and> (\<exists>r'. kappa r' = r \<and> (drop k \<pi>, r') \<in> den u)"
          using int(1) fa ext_t ex_u by blast
        then have "(\<pi>, r) \<in> den (TUnless t c u)" unfolding den.simps unless_d_split by (rule disjI2)
        with True show ?thesis by simp
      qed
    next
      case False
      have "kor (kand (mem3 t \<pi> r) (Some nf)) (kors (map g [0..<length \<pi>])) = Some False"
        using m False by (simp only: m_eq)
      then have c: "kand (mem3 t \<pi> r) (Some nf) = Some False
                    \<and> (\<forall>k \<in> set [0..<length \<pi>]. g k = Some False)"
        unfolding kor_False_iff kors_map_False .
      have keep: "mem3 t \<pi> r = Some False \<or> \<not> nf"
        using conjunct1[OF c] unfolding kand_False_iff by simp
      have all: "\<forall>k < length \<pi>. g k = Some False" using conjunct2[OF c] by simp
      have "\<not> ((\<pi>, r) \<in> den t \<and> (\<forall>j < length \<pi> - 1. eval c (st \<pi> j) \<noteq> Some True))"
        using keep IHt[of \<pi> r False] nf_iff by blast
      moreover have "\<not> (\<exists>k < length \<pi>. first_at c \<pi> k \<and> ext (den t) (take (Suc k) \<pi>)
                         \<and> (\<exists>r'. kappa r' = r \<and> (drop k \<pi>, r') \<in> den u))"
      proof
        assume "\<exists>k < length \<pi>. first_at c \<pi> k \<and> ext (den t) (take (Suc k) \<pi>)
                  \<and> (\<exists>r'. kappa r' = r \<and> (drop k \<pi>, r') \<in> den u)"
        then obtain k r' where k: "k < length \<pi>" "first_at c \<pi> k" "ext (den t) (take (Suc k) \<pi>)"
          and r': "kappa r' = r" "(drop k \<pi>, r') \<in> den u" by blast
        have "g k = Some False" using all k(1) by blast
        with k(2) have "kand (ext3 t (take (Suc k) \<pi>)) (kors (map (\<lambda>r'. mem3 u (drop k \<pi>) r') R))
                        = Some False"
          by (simp add: g_def)
        then have "ext3 t (take (Suc k) \<pi>) = Some False
             \<or> (\<forall>r' \<in> set R. mem3 u (drop k \<pi>) r' = Some False)"
          unfolding kand_False_iff kors_map_False .
        then show False
        proof
          assume "ext3 t (take (Suc k) \<pi>) = Some False"
          moreover have "take (Suc k) \<pi> \<noteq> []" using k(1) by (cases \<pi>) simp_all
          ultimately show False using IHt[of _ _ _ "take (Suc k) \<pi>" False] k(3) by blast
        next
          assume "\<forall>r' \<in> set R. mem3 u (drop k \<pi>) r' = Some False"
          moreover have "r' \<in> set R" unfolding R_def using r'(1) by (cases r') simp_all
          ultimately show False using IHu[of "drop k \<pi>" r' False] r'(2) by blast
        qed
      qed
      ultimately show ?thesis using False by (simp add: unless_d_split)
    qed
  next
    assume ne: "\<rho> \<noteq> []" and e: "ext3 (TUnless t c u) \<rho> = Some b'"
    have "(if \<not> is_trace \<rho> then Some False else None) = Some b'" using e by (simp only: ext3.simps)
    then have nt: "\<not> is_trace \<rho>" and b': "b' = False" by (cases "is_trace \<rho>"; simp)+
    have "wf_den (den (TUnless t c u))" using TUnless.prems by (rule wf_den_den)
    then have "\<not> ext (den (TUnless t c u)) \<rho>" using ext_wf[OF _ ne] nt by blast
    with b' show "ext (den (TUnless t c u)) \<rho> \<longleftrightarrow> b'" by simp
  qed
next
  case (TAnd t u)
  then show ?case by simp
next
  case (TIf c t u)
  from TIf.prems have ft: "and_free t" and fu: "and_free u" by simp_all
  note IHt = TIf.IH(1)[OF ft] and IHu = TIf.IH(2)[OF fu]
  show ?case
  proof (intro conjI impI)
    assume m: "mem3 (TIf c t u) \<pi> r = Some b"
    show "(\<pi>, r) \<in> den (TIf c t u) \<longleftrightarrow> b"
    proof (cases "\<pi> = []")
      case True
      with m den_if[of \<pi> r c t u] show ?thesis by simp
    next
      case False
      then have s0: "st \<pi> 0 = sta (hd \<pi>)" by (rule st_0)
      show ?thesis
      proof (cases "eval c (sta (hd \<pi>)) = Some True")
        case True
        with m False s0 have "mem3 t \<pi> r = Some b" by simp
        with IHt[of \<pi> r b] True False den_if[of \<pi> r c t u] show ?thesis by simp
      next
        case nt: False
        with m False s0 have "mem3 u \<pi> r = Some b" by simp
        with IHu[of \<pi> r b] nt False den_if[of \<pi> r c t u] show ?thesis by simp
      qed
    qed
  next
    assume ne: "\<rho> \<noteq> []" and e: "ext3 (TIf c t u) \<rho> = Some b'"
    have s0: "st \<rho> 0 = sta (hd \<rho>)" using ne by (rule st_0)
    show "ext (den (TIf c t u)) \<rho> \<longleftrightarrow> b'"
    proof (cases "eval c (sta (hd \<rho>)) = Some True")
      case True
      with e s0 have "ext3 t \<rho> = Some b'" by simp
      with IHt[of _ _ _ \<rho> b'] ne True show ?thesis by (simp add: ext_if)
    next
      case False
      with e s0 have "ext3 u \<rho> = Some b'" by simp
      with IHu[of _ _ _ \<rho> b'] ne False show ?thesis by (simp add: ext_if)
    qed
  qed
next
  case TSkip
  then show ?case by (auto simp: mem_skip ext_skip)
qed

corollary mem3_sound:
  "and_free t \<Longrightarrow> mem3 t \<pi> r = Some b \<Longrightarrow> ((\<pi>, r) \<in> den t \<longleftrightarrow> b)"
  using mem3_ext3_sound by blast

end


text \<open>Definiteness: for terms without UNLESS and AND the answer is always definite.\<close>

theorem mem3_definite: "unless_free t \<Longrightarrow> and_free t \<Longrightarrow> mem3 t \<pi> r \<noteq> None"
proof (induction t arbitrary: \<pi> r)
  case (TThen t u)
  from TThen.prems have ut: "unless_free t" and ft: "and_free t"
    and uu: "unless_free u" and fu: "and_free u" by simp_all
  note ht = TThen.IH(1)[OF ut ft] and hu = TThen.IH(2)[OF uu fu]
  show ?case unfolding mem3.simps
  proof (rule kor_defined)
    show "kors (map (\<lambda>k. kand (mem3 t (take (Suc k) \<pi>) Done) (mem3 u (drop k \<pi>) r)) [0..<length \<pi>])
          \<noteq> None"
    proof (rule kors_defined)
      fix x assume "x \<in> set (map (\<lambda>k. kand (mem3 t (take (Suc k) \<pi>) Done) (mem3 u (drop k \<pi>) r))
                               [0..<length \<pi>])"
      then obtain k where "x = kand (mem3 t (take (Suc k) \<pi>) Done) (mem3 u (drop k \<pi>) r)" by auto
      then show "x \<noteq> None" using kand_defined[OF ht hu] by blast
    qed
    show "kand (mem3 t \<pi> r) (Some (r \<noteq> Done)) \<noteq> None" using ht by (rule kand_defined) simp
  qed
next
  case (TOr t u)
  from TOr.prems have ut: "unless_free t" and ft: "and_free t"
    and uu: "unless_free u" and fu: "and_free u" by simp_all
  show ?case unfolding mem3.simps by (rule kor_defined[OF TOr.IH(1)[OF ut ft] TOr.IH(2)[OF uu fu]])
next
  case (TIf c t u)
  from TIf.prems have ut: "unless_free t" and ft: "and_free t"
    and uu: "unless_free u" and fu: "and_free u" by simp_all
  show ?case using TIf.IH(1)[OF ut ft, of \<pi> r] TIf.IH(2)[OF uu fu, of \<pi> r] by auto
qed simp_all

subsection \<open>The status of a composite term on the observed trace\<close>

text \<open>The membership of the whole observed trace says nothing about a violation in the middle
  of it: a trace that goes on after a forbidden action is not a violated trace of the term,
  and in \<open>MUST_NOT a THEN t\<close> the traces of \<open>t\<close> may contain \<open>a\<close>. The report therefore also
  gives the status of the term, read on the prefixes of the observed trace in order.

  The observation ends at the first prefix that is a violated trace of the term, or that
  completes the term by an executed action: an action of an obligation, or an exercised
  permission. A completion at once (a prohibition, a permission that is not exercised, the
  term that completes at once) does not end the observation, and a term whose last reached
  element is a prohibition stays under observation to the end of the trace, as a top-level
  prohibition does. To tell the completions apart, each trace of a term carries a mode: \<open>Exec\<close>
  if its last step is an executed action, \<open>Inst\<close> if the term completed at once without a
  prohibition at the last entry, and \<open>Held\<close> if a prohibition reached at the last entry
  completed at once there (\<open>fden\<close>). Forgetting the mode gives the denotation \<open>den\<close>
  (\<open>fden_den\<close>).

  A prefix can have several readings: the denotation of an obligation does not fix which of
  its actions discharges it, and the guard of UNLESS may fire at the entry of an action. When
  one reading completes the term by an executed action and another has reached a prohibition,
  the status is conservative: once a reading of some prefix has reached a prohibition as the
  last element of the term, only a violation ends the observation. So, for a term without
  AND, the status does not miss a violation that a reading of a prefix admits, unless it is
  unknown, which needs UNLESS, or the observation has ended before, on a completion by an
  executed action, when no reading had reached a prohibition
  (\<open>status_no_missed_violation\<close>).\<close>

datatype mode = Inst | Exec | Held

fun mrank :: "mode \<Rightarrow> nat" where
  "mrank Inst = 0"
| "mrank Exec = 1"
| "mrank Held = 2"

definition mmax :: "mode \<Rightarrow> mode \<Rightarrow> mode" where
  "mmax m\<^sub>1 m\<^sub>2 = (if mrank m\<^sub>1 \<le> mrank m\<^sub>2 then m\<^sub>2 else m\<^sub>1)"

definition modes :: "mode list" where
  "modes = [Inst, Exec, Held]"

lemma in_modes: "m \<in> set modes"
  by (cases m) (simp_all add: modes_def)

lemma mmax_Held: "mmax m Held = Held"
  by (cases m) (simp_all add: mmax_def)

lemma ex_mode_pairs:
  "(\<exists>p \<in> set (filter (\<lambda>(m\<^sub>1, m\<^sub>2). mmax m\<^sub>1 m\<^sub>2 = m) (List.product modes modes)).
       case p of (m\<^sub>1, m\<^sub>2) \<Rightarrow> P m\<^sub>1 m\<^sub>2)
   \<longleftrightarrow> (\<exists>m\<^sub>1 m\<^sub>2. m = mmax m\<^sub>1 m\<^sub>2 \<and> P m\<^sub>1 m\<^sub>2)"
proof
  assume "\<exists>p \<in> set (filter (\<lambda>(m\<^sub>1, m\<^sub>2). mmax m\<^sub>1 m\<^sub>2 = m) (List.product modes modes)).
            case p of (m\<^sub>1, m\<^sub>2) \<Rightarrow> P m\<^sub>1 m\<^sub>2"
  then show "\<exists>m\<^sub>1 m\<^sub>2. m = mmax m\<^sub>1 m\<^sub>2 \<and> P m\<^sub>1 m\<^sub>2" by auto
next
  assume "\<exists>m\<^sub>1 m\<^sub>2. m = mmax m\<^sub>1 m\<^sub>2 \<and> P m\<^sub>1 m\<^sub>2"
  then obtain m\<^sub>1 m\<^sub>2 where "m = mmax m\<^sub>1 m\<^sub>2" "P m\<^sub>1 m\<^sub>2" by blast
  then show "\<exists>p \<in> set (filter (\<lambda>(m\<^sub>1, m\<^sub>2). mmax m\<^sub>1 m\<^sub>2 = m) (List.product modes modes)).
               case p of (m\<^sub>1, m\<^sub>2) \<Rightarrow> P m\<^sub>1 m\<^sub>2"
    by (intro bexI[of _ "(m\<^sub>1, m\<^sub>2)"]) (simp_all add: in_modes)
qed

subsubsection \<open>Decisions in three-valued logic\<close>

text \<open>\<open>dec x P\<close>: a definite answer \<open>x\<close> is the truth value of \<open>P\<close>.\<close>

definition dec :: "bool option \<Rightarrow> bool \<Rightarrow> bool" where
  "dec x P \<longleftrightarrow> (\<forall>b. x = Some b \<longrightarrow> (P \<longleftrightarrow> b))"

lemma dec_Some: "dec (Some P) P"
  by (simp add: dec_def)

lemma dec_cong: "dec x P \<Longrightarrow> (P \<longleftrightarrow> Q) \<Longrightarrow> dec x Q"
  by simp

lemma dec_kor: "dec x P \<Longrightarrow> dec y Q \<Longrightarrow> dec (kor x y) (P \<or> Q)"
  by (cases x; cases y) (auto simp: dec_def kor_def)

lemma dec_kand: "dec x P \<Longrightarrow> dec y Q \<Longrightarrow> dec (kand x y) (P \<and> Q)"
  by (cases x; cases y) (auto simp: dec_def kand_def)

lemma dec_kors: "(\<And>a. a \<in> set xs \<Longrightarrow> dec (f a) (P a)) \<Longrightarrow> dec (kors (map f xs)) (\<exists>a \<in> set xs. P a)"
proof (induction xs)
  case Nil
  then show ?case by (simp add: kors_def dec_def)
next
  case (Cons a xs)
  have "dec (kor (f a) (kors (map f xs))) (P a \<or> (\<exists>a \<in> set xs. P a))"
    by (rule dec_kor) (use Cons in auto)
  then show ?case by (simp add: kors_def)
qed

lemma dec_if: "(c \<Longrightarrow> dec x P) \<Longrightarrow> (\<not> c \<Longrightarrow> dec y Q) \<Longrightarrow> dec (if c then x else y) (if c then P else Q)"
  by simp

subsubsection \<open>Membership with a mode\<close>

text \<open>\<open>mem3m t \<pi> r m\<close> decides whether \<open>(\<pi>, r)\<close> is a trace of \<open>t\<close> with the mode \<open>m\<close>.\<close>

fun mem3m :: "('n, 'v :: value_order, 's, 'a) tm \<Rightarrow> ('n, 'v, 't :: linorder, 's, 'a) trace
    \<Rightarrow> outcome \<Rightarrow> mode \<Rightarrow> bool option" where
  "mem3m (TMust s a) \<pi> r m = (if m = Exec then mem3 (TMust s a) \<pi> r else Some False)"
| "mem3m (TMay s a c) \<pi> r m =
     (if m = (if length \<pi> = 1 then Inst else Exec) then mem3 (TMay s a c) \<pi> r else Some False)"
| "mem3m (TMustNot s a c) \<pi> r m =
     (if m = (if r = Done then Held else Exec) then mem3 (TMustNot s a c) \<pi> r else Some False)"
| "mem3m (TOr t u) \<pi> r m = kor (mem3m t \<pi> r m) (mem3m u \<pi> r m)"
| "mem3m (TThen t u) \<pi> r m =
     kor (kors (map (\<lambda>k. kand (mem3 t (take (Suc k) \<pi>) Done) (mem3m u (drop k \<pi>) r m))
                    [0..<length \<pi> - 1]))
         (kor (if \<pi> = [] then Some False
               else kors (map (\<lambda>(m\<^sub>1, m\<^sub>2). kand (mem3m t \<pi> Done m\<^sub>1) (mem3m u [last \<pi>] r m\<^sub>2))
                              (filter (\<lambda>(m\<^sub>1, m\<^sub>2). mmax m\<^sub>1 m\<^sub>2 = m) (List.product modes modes))))
              (kand (mem3m t \<pi> r m) (Some (r \<noteq> Done))))"
| "mem3m (TUnless t c u) \<pi> r m =
     kor (kand (mem3m t \<pi> r m) (Some (\<forall>j \<in> set [0..<length \<pi> - 1]. eval c (st \<pi> j) \<noteq> Some True)))
         (kors (map (\<lambda>k. if first_at c \<pi> k
                         then kand (ext3 t (take (Suc k) \<pi>))
                                   (kors (map (\<lambda>r'. mem3m u (drop k \<pi>) r' m)
                                              (filter (\<lambda>r'. kappa r' = r) [Done, Interrupted, Violated])))
                         else Some False)
                    [0..<length \<pi>]))"
| "mem3m (TAnd t u) \<pi> r m = None"
| "mem3m (TIf c t u) \<pi> r m =
     (if \<pi> = [] then Some False
      else if eval c (st \<pi> 0) = Some True then mem3m t \<pi> r m else mem3m u \<pi> r m)"
| "mem3m TSkip \<pi> r m = Some (r = Done \<and> length \<pi> = 1 \<and> m = Inst)"

theorem mem3m_definite: "unless_free t \<Longrightarrow> and_free t \<Longrightarrow> mem3m t \<pi> r m \<noteq> None"
proof (induction t arbitrary: \<pi> r m)
  case (TMust s a)
  then show ?case by auto
next
  case (TMay s a c)
  then show ?case by auto
next
  case (TMustNot s a c)
  then show ?case by auto
next
  case (TOr t u)
  from TOr.prems have ut: "unless_free t" and ft: "and_free t"
    and uu: "unless_free u" and fu: "and_free u" by simp_all
  show ?case unfolding mem3m.simps by (rule kor_defined[OF TOr.IH(1)[OF ut ft] TOr.IH(2)[OF uu fu]])
next
  case (TThen t u)
  from TThen.prems have ut: "unless_free t" and ft: "and_free t"
    and uu: "unless_free u" and fu: "and_free u" by simp_all
  note ht = TThen.IH(1)[OF ut ft] and hu = TThen.IH(2)[OF uu fu] and mt = mem3_definite[OF ut ft]
  have a: "kors (map (\<lambda>k. kand (mem3 t (take (Suc k) \<pi>) Done) (mem3m u (drop k \<pi>) r m))
                     [0..<length \<pi> - 1]) \<noteq> None"
  proof (rule kors_defined)
    fix x assume "x \<in> set (map (\<lambda>k. kand (mem3 t (take (Suc k) \<pi>) Done) (mem3m u (drop k \<pi>) r m))
                                 [0..<length \<pi> - 1])"
    then obtain k where "x = kand (mem3 t (take (Suc k) \<pi>) Done) (mem3m u (drop k \<pi>) r m)" by auto
    with kand_defined[OF mt hu] show "x \<noteq> None" by blast
  qed
  have b: "(if \<pi> = [] then Some False
            else kors (map (\<lambda>(m\<^sub>1, m\<^sub>2). kand (mem3m t \<pi> Done m\<^sub>1) (mem3m u [last \<pi>] r m\<^sub>2))
                           (filter (\<lambda>(m\<^sub>1, m\<^sub>2). mmax m\<^sub>1 m\<^sub>2 = m) (List.product modes modes)))) \<noteq> None"
  proof (cases "\<pi> = []")
    case False
    have "kors (map (\<lambda>(m\<^sub>1, m\<^sub>2). kand (mem3m t \<pi> Done m\<^sub>1) (mem3m u [last \<pi>] r m\<^sub>2))
                    (filter (\<lambda>(m\<^sub>1, m\<^sub>2). mmax m\<^sub>1 m\<^sub>2 = m) (List.product modes modes))) \<noteq> None"
    proof (rule kors_defined)
      fix x assume "x \<in> set (map (\<lambda>(m\<^sub>1, m\<^sub>2). kand (mem3m t \<pi> Done m\<^sub>1) (mem3m u [last \<pi>] r m\<^sub>2))
                         (filter (\<lambda>(m\<^sub>1, m\<^sub>2). mmax m\<^sub>1 m\<^sub>2 = m) (List.product modes modes)))"
      then obtain m\<^sub>1 m\<^sub>2 where "x = kand (mem3m t \<pi> Done m\<^sub>1) (mem3m u [last \<pi>] r m\<^sub>2)" by auto
      with kand_defined[OF ht hu] show "x \<noteq> None" by blast
    qed
    with False show ?thesis by simp
  qed simp
  have c: "kand (mem3m t \<pi> r m) (Some (r \<noteq> Done)) \<noteq> None"
    by (rule kand_defined[OF ht]) simp
  show ?case unfolding mem3m.simps by (rule kor_defined[OF a kor_defined[OF b c]])
next
  case (TIf c t u)
  from TIf.prems have ut: "unless_free t" and ft: "and_free t"
    and uu: "unless_free u" and fu: "and_free u" by simp_all
  show ?case using TIf.IH(1)[OF ut ft, of \<pi> r m] TIf.IH(2)[OF uu fu, of \<pi> r m] by auto
qed simp_all

subsubsection \<open>The status\<close>

datatype cstatus = CAt outcome nat | COpen | CUnknown

text \<open>The answer for one prefix, from the answers for a violation, for a reading of this or an
  earlier prefix that has reached a prohibition, for a completion by interruption with mode
  \<open>Exec\<close>, and for a completion with mode \<open>Exec\<close>: \<open>None\<close> is unknown, \<open>Some None\<close> no end
  of the observation, \<open>Some (Some r)\<close> the end, with the outcome \<open>r\<close>. A violation ends the
  observation at once; a completion ends it only if no reading of this prefix or of an
  earlier one has reached a prohibition. A violation takes precedence over Interrupted, and
  Interrupted over Done, as in the order \<open>Done < Interrupted < Violated\<close> of \<open>ojoin\<close>.\<close>

definition step :: "bool option \<Rightarrow> bool option \<Rightarrow> bool option \<Rightarrow> bool option \<Rightarrow> outcome option option"
  where
  "step v h i d =
     (if v = Some True then Some (Some Violated)
      else if v = Some False \<and> i = Some False \<and> d = Some False then Some None
      else if v = Some False \<and> h = Some True then Some None
      else if v = Some False \<and> h = Some False \<and> i = Some True then Some (Some Interrupted)
      else if v = Some False \<and> h = Some False \<and> i = Some False \<and> d = Some True then Some (Some Done)
      else None)"

text \<open>\<open>hstep t \<rho>\<close> decides whether a reading of \<open>\<rho>\<close> has reached a prohibition as the last
  element of \<open>t\<close>, that is, whether \<open>\<rho>\<close> is a trace of \<open>t\<close> with the mode \<open>Held\<close>;
  \<open>held_upto t \<pi> k\<close> decides it for some prefix of \<open>\<pi>\<close> that ends at entry \<open>k\<close> or before.\<close>

definition hstep :: "('n, 'v :: value_order, 's, 'a) tm \<Rightarrow> ('n, 'v, 't :: linorder, 's, 'a) trace
    \<Rightarrow> bool option" where
  "hstep t \<rho> = kor (mem3m t \<rho> Done Held) (mem3m t \<rho> Interrupted Held)"

definition held_upto :: "('n, 'v :: value_order, 's, 'a) tm \<Rightarrow> ('n, 'v, 't :: linorder, 's, 'a) trace
    \<Rightarrow> nat \<Rightarrow> bool option" where
  "held_upto t \<pi> k = kors (map (\<lambda>j. hstep t (take (Suc j) \<pi>)) [0..<Suc k])"

definition pstep :: "('n, 'v :: value_order, 's, 'a) tm \<Rightarrow> ('n, 'v, 't :: linorder, 's, 'a) trace \<Rightarrow> nat
    \<Rightarrow> outcome option option" where
  "pstep t \<pi> k =
     step (mem3 t (take (Suc k) \<pi>) Violated) (held_upto t \<pi> k)
          (mem3m t (take (Suc k) \<pi>) Interrupted Exec) (mem3m t (take (Suc k) \<pi>) Done Exec)"

definition status :: "('n, 'v :: value_order, 's, 'a) tm \<Rightarrow> ('n, 'v, 't :: linorder, 's, 'a) trace \<Rightarrow> cstatus" where
  "status t \<pi> =
     (case find (\<lambda>k. pstep t \<pi> k \<noteq> Some None) [0..<length \<pi>] of
        None \<Rightarrow> COpen
      | Some k \<Rightarrow> (case pstep t \<pi> k of Some (Some r) \<Rightarrow> CAt r k | _ \<Rightarrow> CUnknown))"

lemma step_none:
  "step v h i d = Some None \<longleftrightarrow> v = Some False \<and> (i = Some False \<and> d = Some False \<or> h = Some True)"
  by (auto simp: step_def)

lemma step_Violated: "step v h i d = Some (Some Violated) \<longleftrightarrow> v = Some True"
  by (auto simp: step_def)

lemma step_Interrupted:
  "step v h i d = Some (Some Interrupted) \<longleftrightarrow> v = Some False \<and> h = Some False \<and> i = Some True"
  by (auto simp: step_def)

lemma step_Done:
  "step v h i d = Some (Some Done) \<longleftrightarrow> v = Some False \<and> h = Some False \<and> i = Some False \<and> d = Some True"
  by (auto simp: step_def)

lemma step_defined:
  "v \<noteq> None \<Longrightarrow> h \<noteq> None \<Longrightarrow> i \<noteq> None \<Longrightarrow> d \<noteq> None \<Longrightarrow> step v h i d \<noteq> None"
  by (cases v; cases h; cases i; cases d) (auto simp: step_def)

lemma held_upto_append: "k < length \<pi> \<Longrightarrow> held_upto t (\<pi> @ \<rho>) k = held_upto t \<pi> k"
  unfolding held_upto_def by (rule arg_cong[where f = kors], rule map_cong) auto

lemma held_upto_defined:
  assumes u: "unless_free t" and a: "and_free t"
  shows "held_upto t \<pi> k \<noteq> None"
  unfolding held_upto_def
proof (rule kors_defined)
  fix x assume "x \<in> set (map (\<lambda>j. hstep t (take (Suc j) \<pi>)) [0..<Suc k])"
  then obtain j where x: "x = hstep t (take (Suc j) \<pi>)" by auto
  show "x \<noteq> None" unfolding x hstep_def
    by (rule kor_defined) (rule mem3m_definite[OF u a])+
qed

lemma status_CAt:
  "status t \<pi> = CAt r k \<longleftrightarrow>
     k < length \<pi> \<and> pstep t \<pi> k = Some (Some r) \<and> (\<forall>j < k. pstep t \<pi> j = Some None)"
proof
  assume a: "status t \<pi> = CAt r k"
  then obtain k' where f: "find (\<lambda>k. pstep t \<pi> k \<noteq> Some None) [0..<length \<pi>] = Some k'"
    by (auto simp: status_def split: option.splits)
  with a have "(case pstep t \<pi> k' of Some (Some r) \<Rightarrow> CAt r k' | _ \<Rightarrow> CUnknown) = CAt r k"
    by (simp add: status_def)
  then have "k' = k" and "pstep t \<pi> k' = Some (Some r)"
    by (auto split: option.splits)
  with f show "k < length \<pi> \<and> pstep t \<pi> k = Some (Some r) \<and> (\<forall>j < k. pstep t \<pi> j = Some None)"
    by (simp add: find_upt_Some)
next
  assume "k < length \<pi> \<and> pstep t \<pi> k = Some (Some r) \<and> (\<forall>j < k. pstep t \<pi> j = Some None)"
  then have f: "find (\<lambda>k. pstep t \<pi> k \<noteq> Some None) [0..<length \<pi>] = Some k"
    and p: "pstep t \<pi> k = Some (Some r)"
    by (simp_all add: find_upt_Some)
  from f p show "status t \<pi> = CAt r k" by (simp add: status_def)
qed

lemma status_COpen: "status t \<pi> = COpen \<longleftrightarrow> (\<forall>k < length \<pi>. pstep t \<pi> k = Some None)"
proof
  assume a: "status t \<pi> = COpen"
  show "\<forall>k < length \<pi>. pstep t \<pi> k = Some None"
  proof (cases "find (\<lambda>k. pstep t \<pi> k \<noteq> Some None) [0..<length \<pi>]")
    case None
    then show ?thesis by (simp add: find_upt_None)
  next
    case (Some k)
    with a show ?thesis by (auto simp: status_def split: option.splits)
  qed
next
  assume "\<forall>k < length \<pi>. pstep t \<pi> k = Some None"
  then have "find (\<lambda>k. pstep t \<pi> k \<noteq> Some None) [0..<length \<pi>] = None"
    by (simp add: find_upt_None)
  then show "status t \<pi> = COpen" by (simp add: status_def)
qed

text \<open>The status is final once the observation has ended: the prefixes up to it do not change
  when the trace is extended.\<close>

theorem status_final:
  assumes "status t \<pi> = CAt r k"
  shows "status t (\<pi> @ \<rho>) = CAt r k"
proof -
  have ps: "pstep t (\<pi> @ \<rho>) j = pstep t \<pi> j" if "j < length \<pi>" for j
    using that by (simp add: pstep_def held_upto_append)
  from assms have k: "k < length \<pi>" "pstep t \<pi> k = Some (Some r)"
    and before: "\<forall>j < k. pstep t \<pi> j = Some None"
    by (simp_all add: status_CAt)
  show ?thesis
    unfolding status_CAt using k before ps by auto
qed

text \<open>For terms without UNLESS and AND the status is never unknown.\<close>

theorem status_definite: "unless_free t \<Longrightarrow> and_free t \<Longrightarrow> status t \<pi> \<noteq> CUnknown"
proof
  assume u: "unless_free t" and a: "and_free t" and c: "status t \<pi> = CUnknown"
  have d: "pstep t \<pi> k \<noteq> None" for k
    unfolding pstep_def
    by (rule step_defined)
      (simp_all add: mem3_definite[OF u a] mem3m_definite[OF u a] held_upto_defined[OF u a])
  from c obtain k where f: "find (\<lambda>k. pstep t \<pi> k \<noteq> Some None) [0..<length \<pi>] = Some k"
    by (auto simp: status_def split: option.splits)
  then have n: "pstep t \<pi> k \<noteq> Some None" by (simp add: find_upt_Some)
  from c f have "(case pstep t \<pi> k of Some (Some r) \<Rightarrow> CAt r k | _ \<Rightarrow> CUnknown) = CUnknown"
    by (simp add: status_def)
  with n d[of k] show False by (auto split: option.splits)
qed

context term_semantics
begin

subsubsection \<open>The traces of a term with their modes\<close>

text \<open>The modes of the traces of a term, defined on the decomposition of the observed trace
  that \<open>then_d_split\<close> and \<open>unless_d_split\<close> give. In a sequence, a trace whose second part
  has one entry ends where the first part ends, so its mode is the greater of the two modes.
  An interrupted trace has the mode of the handler.\<close>

primrec fden :: "('n, 'v, 's, 'a) tm \<Rightarrow> (('n, 'v, 't, 's, 'a) trace \<times> outcome \<times> mode) set" where
  "fden (TMust s a) = {(\<pi>, r, m). (\<pi>, r) \<in> must_d s a \<and> m = Exec}"
| "fden (TMay s a c) = {(\<pi>, r, m). (\<pi>, r) \<in> may_d s a c \<and> m = (if length \<pi> = 1 then Inst else Exec)}"
| "fden (TMustNot s a c) =
     {(\<pi>, r, m). (\<pi>, r) \<in> mustnot_d s a c \<and> m = (if r = Done then Held else Exec)}"
| "fden (TThen t u) =
     {(\<pi>, r, m).
        (\<exists>k. Suc k < length \<pi> \<and> (take (Suc k) \<pi>, Done) \<in> den t \<and> (drop k \<pi>, r, m) \<in> fden u)
      \<or> (\<pi> \<noteq> [] \<and> (\<exists>m\<^sub>1 m\<^sub>2. m = mmax m\<^sub>1 m\<^sub>2 \<and> (\<pi>, Done, m\<^sub>1) \<in> fden t \<and> ([last \<pi>], r, m\<^sub>2) \<in> fden u))
      \<or> ((\<pi>, r, m) \<in> fden t \<and> r \<noteq> Done)}"
| "fden (TOr t u) = fden t \<union> fden u"
| "fden (TUnless t c u) =
     {(\<pi>, r, m).
        ((\<pi>, r, m) \<in> fden t \<and> (\<forall>j < length \<pi> - 1. eval c (st \<pi> j) \<noteq> Some True))
      \<or> (\<exists>k < length \<pi>. first_at c \<pi> k \<and> ext (den t) (take (Suc k) \<pi>)
           \<and> (\<exists>r'. kappa r' = r \<and> (drop k \<pi>, r', m) \<in> fden u))}"
| "fden (TAnd t u) = {(\<pi>, r, m). (\<pi>, r) \<in> and_d (den t) (den u) \<and> m = Exec}"
| "fden (TIf c t u) =
     {(\<pi>, r, m). \<pi> \<noteq> [] \<and> (if eval c (sta (hd \<pi>)) = Some True then (\<pi>, r, m) \<in> fden t
                               else (\<pi>, r, m) \<in> fden u)}"
| "fden TSkip = {(\<pi>, r, m). (\<pi>, r) \<in> skip_d \<and> m = Inst}"

text \<open>Forgetting the mode gives the denotation.\<close>

theorem fden_den: "(\<pi>, r) \<in> den t \<longleftrightarrow> (\<exists>m. (\<pi>, r, m) \<in> fden t)"
proof (induction t arbitrary: \<pi> r)
  case (TThen t u)
  have split: "(\<pi>, r) \<in> den (TThen t u) \<longleftrightarrow>
      (\<exists>k < length \<pi>. (take (Suc k) \<pi>, Done) \<in> den t \<and> (drop k \<pi>, r) \<in> den u)
      \<or> ((\<pi>, r) \<in> den t \<and> r \<noteq> Done)"
    by (simp add: then_d_split)
  show ?case
  proof
    assume "(\<pi>, r) \<in> den (TThen t u)"
    then consider (seq) k where "k < length \<pi>" "(take (Suc k) \<pi>, Done) \<in> den t" "(drop k \<pi>, r) \<in> den u"
      | (left) "(\<pi>, r) \<in> den t" "r \<noteq> Done"
      using split by blast
    then show "\<exists>m. (\<pi>, r, m) \<in> fden (TThen t u)"
    proof cases
      case seq
      show ?thesis
      proof (cases "Suc k < length \<pi>")
        case True
        from seq(3) obtain m where "(drop k \<pi>, r, m) \<in> fden u" using TThen.IH(2) by blast
        with True seq(2) show ?thesis by auto
      next
        case False
        with seq(1) have k: "k = length \<pi> - 1" by simp
        have ne: "\<pi> \<noteq> []" using seq(1) by auto
        have tk: "take (Suc k) \<pi> = \<pi>" using k seq(1) by simp
        have dk: "drop k \<pi> = [last \<pi>]" using drop_last_one[OF ne] k by simp
        from seq(2) tk obtain m\<^sub>1 where m1: "(\<pi>, Done, m\<^sub>1) \<in> fden t" using TThen.IH(1) by fastforce
        from seq(3) dk obtain m\<^sub>2 where m2: "([last \<pi>], r, m\<^sub>2) \<in> fden u" using TThen.IH(2) by fastforce
        from ne m1 m2 show ?thesis by auto
      qed
    next
      case left
      then obtain m where "(\<pi>, r, m) \<in> fden t" using TThen.IH(1) by blast
      with left(2) show ?thesis by auto
    qed
  next
    assume "\<exists>m. (\<pi>, r, m) \<in> fden (TThen t u)"
    then obtain m where m: "(\<pi>, r, m) \<in> fden (TThen t u)" by blast
    then consider (seq) k where "Suc k < length \<pi>" "(take (Suc k) \<pi>, Done) \<in> den t" "(drop k \<pi>, r, m) \<in> fden u"
      | (last) m\<^sub>1 m\<^sub>2 where "\<pi> \<noteq> []" "(\<pi>, Done, m\<^sub>1) \<in> fden t" "([last \<pi>], r, m\<^sub>2) \<in> fden u"
      | (left) "(\<pi>, r, m) \<in> fden t" "r \<noteq> Done"
      by auto
    then show "(\<pi>, r) \<in> den (TThen t u)"
    proof cases
      case seq
      then have "k < length \<pi>" "(drop k \<pi>, r) \<in> den u" using TThen.IH(2) by auto
      with seq(2) split show ?thesis by blast
    next
      case last
      define k where "k = length \<pi> - 1"
      have kl: "k < length \<pi>" using last(1) by (simp add: k_def)
      have tk: "take (Suc k) \<pi> = \<pi>" using last(1) by (simp add: k_def)
      have dk: "drop k \<pi> = [last \<pi>]" using drop_last_one[OF last(1)] by (simp add: k_def)
      have "(take (Suc k) \<pi>, Done) \<in> den t" using last(2) tk TThen.IH(1) by auto
      moreover have "(drop k \<pi>, r) \<in> den u" using last(3) dk TThen.IH(2) by auto
      ultimately show ?thesis using kl split by blast
    next
      case left
      then show ?thesis using TThen.IH(1) split by blast
    qed
  qed
next
  case (TOr t u)
  then show ?case by (auto simp: or_d_def)
next
  case (TUnless t c u)
  have "(\<pi>, r) \<in> den (TUnless t c u) \<longleftrightarrow>
          ((\<exists>m. (\<pi>, r, m) \<in> fden t) \<and> (\<forall>j < length \<pi> - 1. eval c (st \<pi> j) \<noteq> Some True))
          \<or> (\<exists>k < length \<pi>. first_at c \<pi> k \<and> ext (den t) (take (Suc k) \<pi>)
               \<and> (\<exists>r'. kappa r' = r \<and> (\<exists>m. (drop k \<pi>, r', m) \<in> fden u)))"
    by (simp add: unless_d_split TUnless.IH)
  then show ?case by auto
next
  case (TIf c t u)
  then show ?case by (auto simp: if_d_def)
qed auto

lemma dec_mem3: "and_free t \<Longrightarrow> dec (mem3 t \<pi> r) ((\<pi>, r) \<in> den t)"
  using mem3_sound by (simp add: dec_def)

lemma dec_ext3: "and_free t \<Longrightarrow> \<rho> \<noteq> [] \<Longrightarrow> dec (ext3 t \<rho>) (ext (den t) \<rho>)"
  using mem3_ext3_sound by (simp add: dec_def)

text \<open>Soundness: a definite answer of \<open>mem3m\<close> is the truth.\<close>

theorem mem3m_dec: "and_free t \<Longrightarrow> dec (mem3m t \<pi> r m) ((\<pi>, r, m) \<in> fden t)"
proof (induction t arbitrary: \<pi> r m)
  case (TMust s a)
  then show ?case using dec_mem3[of "TMust s a" \<pi> r] by (simp add: dec_def)
next
  case (TMay s a c)
  then show ?case using dec_mem3[of "TMay s a c" \<pi> r] by (simp add: dec_def)
next
  case (TMustNot s a c)
  then show ?case using dec_mem3[of "TMustNot s a c" \<pi> r] by (simp add: dec_def)
next
  case TSkip
  then show ?case by (auto simp: dec_def mem_skip)
next
  case (TOr t u)
  from TOr.prems have ft: "and_free t" and fu: "and_free u" by simp_all
  have "dec (kor (mem3m t \<pi> r m) (mem3m u \<pi> r m)) ((\<pi>, r, m) \<in> fden t \<or> (\<pi>, r, m) \<in> fden u)"
    by (rule dec_kor[OF TOr.IH(1)[OF ft] TOr.IH(2)[OF fu]])
  then show ?case by simp
next
  case (TIf c t u)
  from TIf.prems have ft: "and_free t" and fu: "and_free u" by simp_all
  show ?case
  proof (cases "\<pi> = []")
    case True
    then show ?thesis by (simp add: dec_def)
  next
    case False
    then have s0: "st \<pi> 0 = sta (hd \<pi>)" by (rule st_0)
    show ?thesis
      using TIf.IH(1)[OF ft, of \<pi> r m] TIf.IH(2)[OF fu, of \<pi> r m] False s0
      by (cases "eval c (sta (hd \<pi>)) = Some True") (simp_all add: dec_def)
  qed
next
  case (TThen t u)
  from TThen.prems have ft: "and_free t" and fu: "and_free u" by simp_all
  note IHt = TThen.IH(1)[OF ft] and IHu = TThen.IH(2)[OF fu]
  have A: "dec (kors (map (\<lambda>k. kand (mem3 t (take (Suc k) \<pi>) Done) (mem3m u (drop k \<pi>) r m))
                    [0..<length \<pi> - 1]))
             (\<exists>k \<in> set [0..<length \<pi> - 1]. (take (Suc k) \<pi>, Done) \<in> den t \<and> (drop k \<pi>, r, m) \<in> fden u)"
    by (rule dec_kors) (rule dec_kand[OF dec_mem3[OF ft] IHu])
  have B: "dec (if \<pi> = [] then Some False
                else kors (map (\<lambda>(m\<^sub>1, m\<^sub>2). kand (mem3m t \<pi> Done m\<^sub>1) (mem3m u [last \<pi>] r m\<^sub>2))
                               (filter (\<lambda>(m\<^sub>1, m\<^sub>2). mmax m\<^sub>1 m\<^sub>2 = m) (List.product modes modes))))
             (if \<pi> = [] then False
              else \<exists>p \<in> set (filter (\<lambda>(m\<^sub>1, m\<^sub>2). mmax m\<^sub>1 m\<^sub>2 = m) (List.product modes modes)).
                     (case p of (m\<^sub>1, m\<^sub>2) \<Rightarrow> (\<pi>, Done, m\<^sub>1) \<in> fden t \<and> ([last \<pi>], r, m\<^sub>2) \<in> fden u))"
  proof (rule dec_if)
    show "dec (Some False) False" by (rule dec_Some)
  next
    show "dec (kors (map (\<lambda>(m\<^sub>1, m\<^sub>2). kand (mem3m t \<pi> Done m\<^sub>1) (mem3m u [last \<pi>] r m\<^sub>2))
                         (filter (\<lambda>(m\<^sub>1, m\<^sub>2). mmax m\<^sub>1 m\<^sub>2 = m) (List.product modes modes))))
              (\<exists>p \<in> set (filter (\<lambda>(m\<^sub>1, m\<^sub>2). mmax m\<^sub>1 m\<^sub>2 = m) (List.product modes modes)).
                 (case p of (m\<^sub>1, m\<^sub>2) \<Rightarrow> (\<pi>, Done, m\<^sub>1) \<in> fden t \<and> ([last \<pi>], r, m\<^sub>2) \<in> fden u))"
      by (rule dec_kors) (auto intro!: dec_kand IHt IHu split: prod.splits)
  qed
  have C: "dec (kand (mem3m t \<pi> r m) (Some (r \<noteq> Done))) ((\<pi>, r, m) \<in> fden t \<and> r \<noteq> Done)"
    by (rule dec_kand[OF IHt dec_Some])
  have eq: "((\<exists>k \<in> set [0..<length \<pi> - 1]. (take (Suc k) \<pi>, Done) \<in> den t \<and> (drop k \<pi>, r, m) \<in> fden u)
            \<or> ((if \<pi> = [] then False
                else \<exists>p \<in> set (filter (\<lambda>(m\<^sub>1, m\<^sub>2). mmax m\<^sub>1 m\<^sub>2 = m) (List.product modes modes)).
                       (case p of (m\<^sub>1, m\<^sub>2) \<Rightarrow> (\<pi>, Done, m\<^sub>1) \<in> fden t \<and> ([last \<pi>], r, m\<^sub>2) \<in> fden u))
               \<or> ((\<pi>, r, m) \<in> fden t \<and> r \<noteq> Done)))
          \<longleftrightarrow> (\<pi>, r, m) \<in> fden (TThen t u)"
    using ex_mode_pairs[of m "\<lambda>m\<^sub>1 m\<^sub>2. (\<pi>, Done, m\<^sub>1) \<in> fden t \<and> ([last \<pi>], r, m\<^sub>2) \<in> fden u"]
    by auto
  show ?case unfolding mem3m.simps
    by (rule dec_cong[OF dec_kor[OF A dec_kor[OF B C]] eq])
next
  case (TUnless t c u)
  from TUnless.prems have ft: "and_free t" and fu: "and_free u" by simp_all
  note IHt = TUnless.IH(1)[OF ft] and IHu = TUnless.IH(2)[OF fu]
  define R where "R = filter (\<lambda>r'. kappa r' = r) [Done, Interrupted, Violated]"
  have A: "dec (kand (mem3m t \<pi> r m) (Some (\<forall>j \<in> set [0..<length \<pi> - 1]. eval c (st \<pi> j) \<noteq> Some True)))
             ((\<pi>, r, m) \<in> fden t \<and> (\<forall>j \<in> set [0..<length \<pi> - 1]. eval c (st \<pi> j) \<noteq> Some True))"
    by (rule dec_kand[OF IHt dec_Some])
  have B: "dec (kors (map (\<lambda>k. if first_at c \<pi> k
                               then kand (ext3 t (take (Suc k) \<pi>)) (kors (map (\<lambda>r'. mem3m u (drop k \<pi>) r' m) R))
                               else Some False) [0..<length \<pi>]))
             (\<exists>k \<in> set [0..<length \<pi>]. if first_at c \<pi> k
                then ext (den t) (take (Suc k) \<pi>) \<and> (\<exists>r' \<in> set R. (drop k \<pi>, r', m) \<in> fden u)
                else False)"
  proof (rule dec_kors)
    fix k assume k: "k \<in> set [0..<length \<pi>]"
    then have ne: "take (Suc k) \<pi> \<noteq> []" by (cases \<pi>) auto
    show "dec (if first_at c \<pi> k
               then kand (ext3 t (take (Suc k) \<pi>)) (kors (map (\<lambda>r'. mem3m u (drop k \<pi>) r' m) R))
               else Some False)
              (if first_at c \<pi> k
               then ext (den t) (take (Suc k) \<pi>) \<and> (\<exists>r' \<in> set R. (drop k \<pi>, r', m) \<in> fden u)
               else False)"
      by (rule dec_if) (auto intro!: dec_kand dec_ext3[OF ft ne] dec_kors IHu dec_Some)
  qed
  have eq: "(((\<pi>, r, m) \<in> fden t \<and> (\<forall>j \<in> set [0..<length \<pi> - 1]. eval c (st \<pi> j) \<noteq> Some True))
             \<or> (\<exists>k \<in> set [0..<length \<pi>]. if first_at c \<pi> k
                  then ext (den t) (take (Suc k) \<pi>) \<and> (\<exists>r' \<in> set R. (drop k \<pi>, r', m) \<in> fden u)
                  else False))
            \<longleftrightarrow> (\<pi>, r, m) \<in> fden (TUnless t c u)"
  proof -
    have "(\<exists>r' \<in> set R. (drop k \<pi>, r', m) \<in> fden u) \<longleftrightarrow> (\<exists>r'. kappa r' = r \<and> (drop k \<pi>, r', m) \<in> fden u)" for k
      unfolding R_def using kappa_exists[of r "\<lambda>r'. (drop k \<pi>, r', m) \<in> fden u"] by simp
    then show ?thesis by auto
  qed
  show ?case unfolding mem3m.simps R_def[symmetric]
    by (rule dec_cong[OF dec_kor[OF A B] eq])
next
  case (TAnd t u)
  then show ?case by simp
qed

corollary mem3m_sound:
  "and_free t \<Longrightarrow> mem3m t \<pi> r m = Some b \<Longrightarrow> ((\<pi>, r, m) \<in> fden t \<longleftrightarrow> b)"
  using mem3m_dec by (simp add: dec_def)

text \<open>A sequence that ends with a prohibition is never completed by an executed action: every
  Done trace of it has the mode \<open>Held\<close>, so it stays under observation to the end of the
  trace. An obligation completes only by an executed action.\<close>

theorem then_mustnot_held:
  assumes "(\<pi>, Done, m) \<in> fden (TThen t (TMustNot s a c))"
  shows "m = Held"
proof -
  from assms consider (seq) k where "Suc k < length \<pi>" "(drop k \<pi>, Done) \<in> mustnot_d s a c"
    | (last) m\<^sub>1 m\<^sub>2 where "m = mmax m\<^sub>1 m\<^sub>2" "m\<^sub>2 = Held"
    by auto
  then show ?thesis
  proof cases
    case seq
    then have "length (drop k \<pi>) = 1" by (simp add: mem_mustnot)
    with seq(1) show ?thesis by simp
  next
    case last
    then show ?thesis by (simp add: mmax_Held)
  qed
qed

theorem must_exec: "(\<pi>, r, m) \<in> fden (TMust s a) \<Longrightarrow> m = Exec"
  by simp

text \<open>A reading of a prefix has reached a prohibition as the last element of the term: the
  prefix is a trace of the term, completed or interrupted, with the mode \<open>Held\<close>.\<close>

definition reached_prohibition :: "('n, 'v, 's, 'a) tm \<Rightarrow> ('n, 'v, 't, 's, 'a) trace \<Rightarrow> bool" where
  "reached_prohibition t \<rho> \<longleftrightarrow> (\<rho>, Done, Held) \<in> fden t \<or> (\<rho>, Interrupted, Held) \<in> fden t"

lemma hstep_dec:
  assumes "and_free t"
  shows "dec (hstep t \<rho>) (reached_prohibition t \<rho>)"
  unfolding hstep_def reached_prohibition_def by (intro dec_kor mem3m_dec assms)

lemma held_upto_dec:
  assumes "and_free t"
  shows "dec (held_upto t \<pi> k) (\<exists>j \<le> k. reached_prohibition t (take (Suc j) \<pi>))"
proof -
  have "dec (held_upto t \<pi> k) (\<exists>j \<in> set [0..<Suc k]. reached_prohibition t (take (Suc j) \<pi>))"
    unfolding held_upto_def by (rule dec_kors) (rule hstep_dec[OF assms])
  then show ?thesis by (rule dec_cong) (auto simp del: upt_Suc simp: less_Suc_eq_le)
qed

lemma pstep_none:
  assumes "and_free t" and "pstep t \<pi> j = Some None"
  shows "(take (Suc j) \<pi>, Violated) \<notin> den t"
    and "(take (Suc j) \<pi>, Interrupted, Exec) \<notin> fden t \<and> (take (Suc j) \<pi>, Done, Exec) \<notin> fden t
           \<or> (\<exists>i \<le> j. reached_prohibition t (take (Suc i) \<pi>))"
proof -
  from assms(2) have v: "mem3 t (take (Suc j) \<pi>) Violated = Some False"
    and r: "mem3m t (take (Suc j) \<pi>) Interrupted Exec = Some False
              \<and> mem3m t (take (Suc j) \<pi>) Done Exec = Some False
            \<or> held_upto t \<pi> j = Some True"
    by (simp_all add: pstep_def step_none)
  show "(take (Suc j) \<pi>, Violated) \<notin> den t" using mem3_sound[OF assms(1) v] by simp
  from r show "(take (Suc j) \<pi>, Interrupted, Exec) \<notin> fden t \<and> (take (Suc j) \<pi>, Done, Exec) \<notin> fden t
           \<or> (\<exists>i \<le> j. reached_prohibition t (take (Suc i) \<pi>))"
  proof
    assume c: "mem3m t (take (Suc j) \<pi>) Interrupted Exec = Some False
                 \<and> mem3m t (take (Suc j) \<pi>) Done Exec = Some False"
    have "(take (Suc j) \<pi>, Interrupted, Exec) \<notin> fden t"
      using mem3m_sound[OF assms(1) conjunct1[OF c]] by simp
    moreover have "(take (Suc j) \<pi>, Done, Exec) \<notin> fden t"
      using mem3m_sound[OF assms(1) conjunct2[OF c]] by simp
    ultimately show ?thesis by blast
  next
    assume "held_upto t \<pi> j = Some True"
    then show ?thesis using held_upto_dec[OF assms(1), of \<pi> j] by (auto simp: dec_def)
  qed
qed

text \<open>Soundness of the status. At the reported entry the prefix is a violated trace of the term,
  or a trace that completes it by an executed action, with Violated before Interrupted before
  Done; a completion is reported only if no reading of this prefix or of an earlier one has
  reached a prohibition. No shorter prefix is a violated trace, and none is completed by an
  executed action unless a reading of it or of an earlier prefix has reached a prohibition.\<close>

theorem status_sound:
  assumes "and_free t" and "status t \<pi> = CAt r k"
  shows "k < length \<pi>"
    and "r = Violated \<Longrightarrow> (take (Suc k) \<pi>, Violated) \<in> den t"
    and "r \<noteq> Violated \<Longrightarrow> (take (Suc k) \<pi>, r, Exec) \<in> fden t \<and> (take (Suc k) \<pi>, Violated) \<notin> den t
           \<and> (\<forall>i \<le> k. \<not> reached_prohibition t (take (Suc i) \<pi>))"
    and "r = Done \<Longrightarrow> (take (Suc k) \<pi>, Interrupted, Exec) \<notin> fden t"
    and "j < k \<Longrightarrow> (take (Suc j) \<pi>, Violated) \<notin> den t
           \<and> ((take (Suc j) \<pi>, Interrupted, Exec) \<notin> fden t \<and> (take (Suc j) \<pi>, Done, Exec) \<notin> fden t
              \<or> (\<exists>i \<le> j. reached_prohibition t (take (Suc i) \<pi>)))"
proof -
  from assms(2) have k: "k < length \<pi>" and p: "pstep t \<pi> k = Some (Some r)"
    and before: "\<forall>j < k. pstep t \<pi> j = Some None"
    by (simp_all add: status_CAt)
  let ?p = "take (Suc k) \<pi>"
  have hk: "\<forall>i \<le> k. \<not> reached_prohibition t (take (Suc i) \<pi>)" if "held_upto t \<pi> k = Some False"
    using that held_upto_dec[OF assms(1), of \<pi> k] by (auto simp: dec_def)
  show "k < length \<pi>" by (rule k)
  show "(?p, Violated) \<in> den t" if "r = Violated"
    using p that mem3_sound[OF assms(1)] by (simp add: pstep_def step_Violated)
  show "(?p, r, Exec) \<in> fden t \<and> (?p, Violated) \<notin> den t
          \<and> (\<forall>i \<le> k. \<not> reached_prohibition t (take (Suc i) \<pi>))" if "r \<noteq> Violated"
  proof (cases r)
    case Interrupted
    with p have "mem3 t ?p Violated = Some False" "held_upto t \<pi> k = Some False"
      "mem3m t ?p Interrupted Exec = Some True"
      by (simp_all add: pstep_def step_Interrupted)
    with Interrupted hk show ?thesis using mem3_sound[OF assms(1)] mem3m_sound[OF assms(1)] by blast
  next
    case Done
    with p have "mem3 t ?p Violated = Some False" "held_upto t \<pi> k = Some False"
      "mem3m t ?p Done Exec = Some True"
      by (simp_all add: pstep_def step_Done)
    with Done hk show ?thesis using mem3_sound[OF assms(1)] mem3m_sound[OF assms(1)] by blast
  qed (use that in simp)
  show "(?p, Interrupted, Exec) \<notin> fden t" if "r = Done"
  proof -
    from p that have "mem3m t ?p Interrupted Exec = Some False" by (simp add: pstep_def step_Done)
    then show ?thesis using mem3m_sound[OF assms(1)] by blast
  qed
  show "(take (Suc j) \<pi>, Violated) \<notin> den t
          \<and> ((take (Suc j) \<pi>, Interrupted, Exec) \<notin> fden t \<and> (take (Suc j) \<pi>, Done, Exec) \<notin> fden t
             \<or> (\<exists>i \<le> j. reached_prohibition t (take (Suc i) \<pi>)))" if "j < k"
  proof -
    from before that have "pstep t \<pi> j = Some None" by blast
    from pstep_none[OF assms(1) this] show ?thesis by blast
  qed
qed

theorem status_open:
  assumes "and_free t" and "status t \<pi> = COpen" and "k < length \<pi>"
  shows "(take (Suc k) \<pi>, Violated) \<notin> den t"
    and "(take (Suc k) \<pi>, Interrupted, Exec) \<notin> fden t \<and> (take (Suc k) \<pi>, Done, Exec) \<notin> fden t
           \<or> (\<exists>i \<le> k. reached_prohibition t (take (Suc i) \<pi>))"
proof -
  from assms(2,3) have "pstep t \<pi> k = Some None" by (simp add: status_COpen)
  from pstep_none[OF assms(1) this]
  show "(take (Suc k) \<pi>, Violated) \<notin> den t"
    and "(take (Suc k) \<pi>, Interrupted, Exec) \<notin> fden t \<and> (take (Suc k) \<pi>, Done, Exec) \<notin> fden t
           \<or> (\<exists>i \<le> k. reached_prohibition t (take (Suc i) \<pi>))"
    by blast+
qed

text \<open>The status does not miss a violation that a reading of a prefix admits. If a prefix of
  the observed trace is a violated trace of the term, the status is a violation at that entry
  or before it, unless it is unknown, or the observation has ended before, at an entry where
  the term is completed by an executed action and no reading of that prefix or of an earlier
  one has reached a prohibition. An unknown status needs UNLESS, and the exception for an
  earlier completion cannot be dropped (\<open>violation_after_completion\<close>).\<close>

theorem status_no_missed_violation:
  assumes "and_free t" and "k < length \<pi>" and "(take (Suc k) \<pi>, Violated) \<in> den t"
  shows "(\<exists>k' \<le> k. status t \<pi> = CAt Violated k') \<or> (status t \<pi> = CUnknown \<and> \<not> unless_free t)
    \<or> (\<exists>r k'. k' < k \<and> r \<noteq> Violated \<and> status t \<pi> = CAt r k' \<and> (take (Suc k') \<pi>, r, Exec) \<in> fden t
              \<and> (take (Suc k') \<pi>, Violated) \<notin> den t
              \<and> (\<forall>i \<le> k'. \<not> reached_prohibition t (take (Suc i) \<pi>)))"
proof (cases "status t \<pi>")
  case (CAt r k')
  have kk: "\<not> k < k'"
  proof
    assume "k < k'"
    with status_sound(5)[OF assms(1) CAt, of k] have "(take (Suc k) \<pi>, Violated) \<notin> den t" by blast
    with assms(3) show False by simp
  qed
  show ?thesis
  proof (cases "r = Violated")
    case True
    with CAt kk show ?thesis by auto
  next
    case False
    from status_sound(3)[OF assms(1) CAt False]
    have m: "(take (Suc k') \<pi>, r, Exec) \<in> fden t" and nv: "(take (Suc k') \<pi>, Violated) \<notin> den t"
      and nh: "\<forall>i \<le> k'. \<not> reached_prohibition t (take (Suc i) \<pi>)"
      by blast+
    from nv assms(3) have "k' \<noteq> k" by auto
    with kk have "k' < k" by simp
    with CAt False m nv nh show ?thesis by blast
  qed
next
  case COpen
  with status_open(1)[OF assms(1) COpen assms(2)] assms(3) show ?thesis by simp
next
  case CUnknown
  with status_definite[of t \<pi>] assms(1) show ?thesis by auto
qed

text \<open>The same principle from the side of the readings: once a reading of a prefix has reached
  a prohibition, every later violation is reported, unless the status is unknown or the
  observation ended at an earlier entry.\<close>

corollary reached_prohibition_watched:
  assumes "and_free t" and "reached_prohibition t (take (Suc j) \<pi>)"
    and "k < length \<pi>" and "(take (Suc k) \<pi>, Violated) \<in> den t"
  shows "(\<exists>k' \<le> k. status t \<pi> = CAt Violated k') \<or> status t \<pi> = CUnknown
    \<or> (\<exists>r k'. k' < j \<and> r \<noteq> Violated \<and> status t \<pi> = CAt r k')"
proof -
  from status_no_missed_violation[OF assms(1,3,4)]
  consider (v) "\<exists>k' \<le> k. status t \<pi> = CAt Violated k'" | (u) "status t \<pi> = CUnknown"
    | (c) r k' where "k' < k" "r \<noteq> Violated" "status t \<pi> = CAt r k'"
        "\<forall>i \<le> k'. \<not> reached_prohibition t (take (Suc i) \<pi>)"
    by blast
  then show ?thesis
  proof cases
    case c
    have "k' < j"
    proof (rule ccontr)
      assume "\<not> k' < j"
      then have "j \<le> k'" by simp
      with c(4) assms(2) show False by blast
    qed
    with c(2,3) show ?thesis by blast
  qed blast+
qed

text \<open>Without UNLESS and AND no trace is interrupted.\<close>

lemma no_interrupted: "unless_free t \<Longrightarrow> and_free t \<Longrightarrow> (\<pi>, Interrupted) \<notin> den t"
proof (induction t arbitrary: \<pi>)
  case (TThen t u)
  then show ?case by (auto simp: then_d_split)
next
  case (TOr t u)
  then show ?case by (auto simp: or_d_def)
next
  case (TIf c t u)
  then show ?case by (auto simp: if_d_def)
qed (auto simp: must_d_def may_d_def mustnot_d_def skip_d_def)

text \<open>A prohibition at the end of a sequence is watched to the end of the trace. If a prefix
  of the observed trace is a violated trace of \<open>t THEN s MUST_NOT a\<close> in a reading where
  \<open>t\<close> is completed at entry \<open>k\<^sub>0\<close> and the prohibition is violated later, the status is a
  violation at that entry or before it, unless it is unknown or the term was interrupted,
  with an executed handler, before entry \<open>k\<^sub>0\<close>. Both exceptions need UNLESS in \<open>t\<close>.\<close>

theorem then_mustnot_watched:
  assumes "and_free t" and "k\<^sub>0 < k" and "k < length \<pi>"
    and "(take (Suc k\<^sub>0) \<pi>, Done) \<in> den t"
    and "(drop k\<^sub>0 (take (Suc k) \<pi>), Violated) \<in> mustnot_d s a c"
  shows "(\<exists>k' \<le> k. status (TThen t (TMustNot s a c)) \<pi> = CAt Violated k')
    \<or> status (TThen t (TMustNot s a c)) \<pi> = CUnknown
    \<or> (\<exists>k' < k\<^sub>0. status (TThen t (TMustNot s a c)) \<pi> = CAt Interrupted k')"
proof -
  let ?T = "TThen t (TMustNot s a c)"
  let ?p = "take (Suc k) \<pi>"
  have f: "and_free ?T" using assms(1) by simp
  have tk: "take (Suc k\<^sub>0) ?p = take (Suc k\<^sub>0) \<pi>" using assms(2) by (simp add: min_def)
  have k0: "k\<^sub>0 < length ?p" using assms(2,3) by simp
  have "\<exists>k' < length ?p. (take (Suc k') ?p, Done) \<in> den t \<and> (drop k' ?p, Violated) \<in> mustnot_d s a c"
    by (intro exI[of _ k\<^sub>0]) (use k0 tk assms(4,5) in simp)
  then have v: "(?p, Violated) \<in> den ?T" by (simp add: then_d_split)
  have ne: "take (Suc k\<^sub>0) \<pi> \<noteq> []" using assms(3) by (cases \<pi>) auto
  from assms(4) obtain m\<^sub>1 where m1: "(take (Suc k\<^sub>0) \<pi>, Done, m\<^sub>1) \<in> fden t"
    using fden_den by blast
  have "([last (take (Suc k\<^sub>0) \<pi>)], Done, Held) \<in> fden (TMustNot s a c)"
    by (cases "last (take (Suc k\<^sub>0) \<pi>)") (simp add: mustnot_d_def)
  with ne m1 have "(take (Suc k\<^sub>0) \<pi>, Done, mmax m\<^sub>1 Held) \<in> fden ?T"
    by (simp only: fden.simps mem_Collect_eq prod.case) blast
  then have h: "reached_prohibition ?T (take (Suc k\<^sub>0) \<pi>)"
    by (simp add: reached_prohibition_def mmax_Held)
  from reached_prohibition_watched[OF f h assms(3) v]
  consider (v) "\<exists>k' \<le> k. status ?T \<pi> = CAt Violated k'" | (u) "status ?T \<pi> = CUnknown"
    | (c) r k' where "k' < k\<^sub>0" "r \<noteq> Violated" "status ?T \<pi> = CAt r k'"
    by blast
  then show ?thesis
  proof cases
    case c
    have "r = Interrupted"
    proof (cases r)
      case Done
      with status_sound(3)[OF f c(3) c(2)] have "(take (Suc k') \<pi>, Done, Exec) \<in> fden ?T" by blast
      from then_mustnot_held[OF this] show ?thesis by simp
    qed (use c(2) in simp_all)
    with c(1,3) show ?thesis by blast
  qed blast+
qed

text \<open>Without UNLESS and AND in \<open>t\<close> there is no exception: on the trace activation, pay,
  leak, \<open>alice MUST pay THEN bob MUST_NOT leak\<close> is reported violated at entry 2.\<close>

theorem then_mustnot_status:
  assumes "unless_free t" and "and_free t" and "k < length \<pi>"
    and "(take (Suc k) \<pi>, Violated) \<in> den (TThen t (TMustNot s a c))"
  shows "\<exists>k' \<le> k. status (TThen t (TMustNot s a c)) \<pi> = CAt Violated k'"
proof -
  let ?T = "TThen t (TMustNot s a c)"
  have u: "unless_free ?T" and f: "and_free ?T" using assms(1,2) by simp_all
  show ?thesis
  proof (cases "status ?T \<pi>")
    case (CAt r k')
    have "r = Violated"
    proof (rule ccontr)
      assume nv: "r \<noteq> Violated"
      then have mem: "(take (Suc k') \<pi>, r, Exec) \<in> fden ?T"
        using status_sound(3)[OF f CAt nv] by blast
      show False
      proof (cases r)
        case Done
        with mem have "(take (Suc k') \<pi>, Done, Exec) \<in> fden ?T" by simp
        from then_mustnot_held[OF this] show False by simp
      next
        case Interrupted
        with mem have "(take (Suc k') \<pi>, Interrupted) \<in> den ?T"
          unfolding fden_den by blast
        with no_interrupted[OF u f] show False by blast
      qed (use nv in simp)
    qed
    moreover have "k' \<le> k"
    proof (rule ccontr)
      assume "\<not> k' \<le> k"
      then have "(take (Suc k) \<pi>, Violated) \<notin> den ?T"
        using status_sound(5)[OF f CAt, of k] by simp
      with assms(4) show False by simp
    qed
    ultimately show ?thesis using CAt by blast
  next
    case COpen
    with status_open(1)[OF f COpen assms(3)] assms(4) show ?thesis by simp
  next
    case CUnknown
    from status_definite[OF u f, of \<pi>] CUnknown show ?thesis by simp
  qed
qed

text \<open>A prohibition in a branch of OR completes at once, so a reading of the first entry has
  reached it, and every violation of the term is reported, whatever the other branch does:
  on the trace activation, pay, leak, \<open>alice MUST pay OR bob MUST_NOT leak\<close> is reported
  violated at entry 2. This is the conservative reading of OR.\<close>

corollary or_mustnot_watched:
  assumes "and_free t" and "k < length \<pi>"
    and "(take (Suc k) \<pi>, Violated) \<in> den (TOr t (TMustNot s a c))"
  shows "(\<exists>k' \<le> k. status (TOr t (TMustNot s a c)) \<pi> = CAt Violated k')
    \<or> status (TOr t (TMustNot s a c)) \<pi> = CUnknown"
proof -
  let ?T = "TOr t (TMustNot s a c)"
  have f: "and_free ?T" using assms(1) by simp
  from assms(2) have "take (Suc 0) \<pi> = [hd \<pi>]" by (cases \<pi>) simp_all
  moreover obtain \<sigma> \<tau> e where "hd \<pi> = (\<sigma>, \<tau>, e)" by (cases "hd \<pi>")
  ultimately have h: "reached_prohibition ?T (take (Suc 0) \<pi>)"
    by (simp add: reached_prohibition_def mustnot_d_def)
  from reached_prohibition_watched[OF f h assms(2,3)] show ?thesis by simp
qed

text \<open>Without UNLESS and AND the three answers are the memberships themselves.\<close>

lemma mem3_eq: "unless_free t \<Longrightarrow> and_free t \<Longrightarrow> mem3 t \<rho> r = Some ((\<rho>, r) \<in> den t)"
  using mem3_definite[of t \<rho> r] mem3_sound[of t \<rho> r] by (cases "mem3 t \<rho> r") auto

lemma mem3m_eq:
  "unless_free t \<Longrightarrow> and_free t \<Longrightarrow> mem3m t \<rho> r m = Some ((\<rho>, r, m) \<in> fden t)"
  using mem3m_definite[of t \<rho> r m] mem3m_sound[of t \<rho> r m] by (cases "mem3m t \<rho> r m") auto

lemma held_upto_eq:
  "unless_free t \<Longrightarrow> and_free t
     \<Longrightarrow> held_upto t \<pi> k = Some (\<exists>j \<le> k. reached_prohibition t (take (Suc j) \<pi>))"
  using held_upto_defined[of t \<pi> k] held_upto_dec[of t \<pi> k]
  by (cases "held_upto t \<pi> k") (auto simp: dec_def)

text \<open>The exception of \<open>status_no_missed_violation\<close> for an earlier completion cannot be
  dropped: on the trace activation, \<open>a'\<close>, \<open>a\<close>, the term \<open>s MUST_NOT a THEN s' MUST a'\<close> is
  completed by the action \<open>a'\<close> at entry 1, when no reading has reached a prohibition, and its
  status is Done there, although the whole trace is a violated trace of the term.\<close>

theorem violation_after_completion:
  assumes "(s, a) \<noteq> (s', a')" and "\<tau>\<^sub>0 \<le> \<tau>\<^sub>1" and "\<tau>\<^sub>1 \<le> \<tau>\<^sub>2"
  shows "([(\<sigma>\<^sub>0, \<tau>\<^sub>0, e), (\<sigma>\<^sub>1, \<tau>\<^sub>1, Deontic s' a' p'), (\<sigma>\<^sub>2, \<tau>\<^sub>2, Deontic s a p)], Violated)
           \<in> den (TThen (TMustNot s a ETrue) (TMust s' a'))"
    and "status (TThen (TMustNot s a ETrue) (TMust s' a'))
           [(\<sigma>\<^sub>0, \<tau>\<^sub>0, e), (\<sigma>\<^sub>1, \<tau>\<^sub>1, Deontic s' a' p'), (\<sigma>\<^sub>2, \<tau>\<^sub>2, Deontic s a p)] = CAt Done 1"
proof -
  define \<pi> where "\<pi> = [(\<sigma>\<^sub>0, \<tau>\<^sub>0, e), (\<sigma>\<^sub>1, \<tau>\<^sub>1, Deontic s' a' p'), (\<sigma>\<^sub>2, \<tau>\<^sub>2, Deontic s a p)]"
  let ?T = "TThen (TMustNot s a ETrue) (TMust s' a')"
  let ?\<rho>\<^sub>0 = "[(\<sigma>\<^sub>0, \<tau>\<^sub>0, e)]"
  let ?\<rho>\<^sub>1 = "[(\<sigma>\<^sub>0, \<tau>\<^sub>0, e), (\<sigma>\<^sub>1, \<tau>\<^sub>1, Deontic s' a' p')]"
  have u: "unless_free ?T" and f: "and_free ?T" by simp_all
  have nd: "\<not> does s a (Deontic s' a' p')" using assms(1) by (auto simp: does_def)
  have "(\<pi>, Violated) \<in> mustnot_d s a ETrue"
    using assms(2,3) nd
    by (auto simp: \<pi>_def mustnot_d_def forbidden_def is_trace_def does_def less_Suc_eq)
  then have "(\<pi>, Violated) \<in> den ?T" by (simp add: then_d_split)
  then show "([(\<sigma>\<^sub>0, \<tau>\<^sub>0, e), (\<sigma>\<^sub>1, \<tau>\<^sub>1, Deontic s' a' p'), (\<sigma>\<^sub>2, \<tau>\<^sub>2, Deontic s a p)], Violated)
           \<in> den ?T" by (simp add: \<pi>_def)
  have nI: "(\<rho>, Interrupted, m) \<notin> fden ?T" for \<rho> m
    using no_interrupted[OF u f, of \<rho>] fden_den by blast
  have nH: "(\<rho>, Done, Held) \<notin> fden ?T" for \<rho>
    by (auto simp: must_d_def)
  have nR: "\<not> reached_prohibition ?T \<rho>" for \<rho>
    using nI nH by (simp add: reached_prohibition_def)
  have t0: "take (Suc 0) \<pi> = ?\<rho>\<^sub>0" and t1: "take (Suc 1) \<pi> = ?\<rho>\<^sub>1"
    by (simp_all add: \<pi>_def)
  have v0: "(?\<rho>\<^sub>0, Violated) \<notin> den ?T"
    by (simp add: then_d_split must_d_def mustnot_d_def forbidden_def)
  have v1: "(?\<rho>\<^sub>1, Violated) \<notin> den ?T"
    using nd by (auto simp: then_d_split must_d_def mustnot_d_def forbidden_def less_Suc_eq)
  have d0: "(?\<rho>\<^sub>0, Done, Exec) \<notin> fden ?T"
    by (auto simp: must_d_def)
  have "Suc 0 < length ?\<rho>\<^sub>1 \<and> (take (Suc 0) ?\<rho>\<^sub>1, Done) \<in> den (TMustNot s a ETrue)
        \<and> (drop 0 ?\<rho>\<^sub>1, Done, Exec) \<in> fden (TMust s' a')"
    using assms(2) by (simp add: mustnot_d_def must_d_def is_trace_def does_def)
  then have d1: "(?\<rho>\<^sub>1, Done, Exec) \<in> fden ?T"
    by (simp only: fden.simps mem_Collect_eq prod.case) blast
  have hF: "held_upto ?T \<pi> k = Some False" for k
    using nR by (simp add: held_upto_eq[OF u f])
  have p0: "pstep ?T \<pi> 0 = Some None"
    unfolding pstep_def mem3_eq[OF u f] mem3m_eq[OF u f] hF t0
    by (simp only: v0 d0 nI step_none simp_thms option.inject bool.distinct)
  have p1: "pstep ?T \<pi> 1 = Some (Some Done)"
    unfolding pstep_def mem3_eq[OF u f] mem3m_eq[OF u f] hF t1
    by (simp only: v1 d1 nI step_Done simp_thms option.inject bool.distinct)
  have "status ?T \<pi> = CAt Done 1"
    unfolding status_CAt using p0 p1 by (simp add: \<pi>_def)
  then show "status ?T
      [(\<sigma>\<^sub>0, \<tau>\<^sub>0, e), (\<sigma>\<^sub>1, \<tau>\<^sub>1, Deontic s' a' p'), (\<sigma>\<^sub>2, \<tau>\<^sub>2, Deontic s a p)] = CAt Done 1"
    by (simp add: \<pi>_def)
qed

text \<open>The precedence of a violation over Done is needed: in \<open>s MUST_NOT a THEN s' MUST a'\<close>,
  the trace activation, \<open>a\<close>, \<open>a'\<close> is a trace of the term with the outcome Done, and its
  prefix that ends with \<open>a\<close> is a violated trace.\<close>

theorem violation_over_done:
  assumes "\<tau>\<^sub>0 \<le> \<tau>\<^sub>1" and "\<tau>\<^sub>1 \<le> \<tau>\<^sub>2"
  shows "([(\<sigma>\<^sub>0, \<tau>\<^sub>0, e), (\<sigma>\<^sub>1, \<tau>\<^sub>1, Deontic s a p), (\<sigma>\<^sub>2, \<tau>\<^sub>2, Deontic s' a' p')], Done)
           \<in> den (TThen (TMustNot s a ETrue) (TMust s' a'))"
    and "([(\<sigma>\<^sub>0, \<tau>\<^sub>0, e), (\<sigma>\<^sub>1, \<tau>\<^sub>1, Deontic s a p)], Violated)
           \<in> den (TThen (TMustNot s a ETrue) (TMust s' a'))"
proof -
  define \<pi> where "\<pi> = [(\<sigma>\<^sub>0, \<tau>\<^sub>0, e), (\<sigma>\<^sub>1, \<tau>\<^sub>1, Deontic s a p), (\<sigma>\<^sub>2, \<tau>\<^sub>2, Deontic s' a' p')]"
  have m: "(\<pi>, Done) \<in> must_d s' a'"
    using assms(1,2) by (simp add: \<pi>_def must_d_def is_trace_def does_def)
  have n: "([(\<sigma>\<^sub>0, \<tau>\<^sub>0, e)], Done) \<in> mustnot_d s a ETrue" by (simp add: mustnot_d_def)
  have "fusable [(\<sigma>\<^sub>0, \<tau>\<^sub>0, e)] \<pi>" by (simp add: fusable_def \<pi>_def)
  moreover have "fuse [(\<sigma>\<^sub>0, \<tau>\<^sub>0, e)] \<pi> = \<pi>" by (simp add: fuse_def \<pi>_def)
  ultimately have "(\<pi>, Done) \<in> then_d (mustnot_d s a ETrue) (must_d s' a')"
    using m n unfolding then_d_def by force
  then show "([(\<sigma>\<^sub>0, \<tau>\<^sub>0, e), (\<sigma>\<^sub>1, \<tau>\<^sub>1, Deontic s a p), (\<sigma>\<^sub>2, \<tau>\<^sub>2, Deontic s' a' p')], Done)
           \<in> den (TThen (TMustNot s a ETrue) (TMust s' a'))"
    by (simp add: \<pi>_def)
  have "([(\<sigma>\<^sub>0, \<tau>\<^sub>0, e), (\<sigma>\<^sub>1, \<tau>\<^sub>1, Deontic s a p)], Violated) \<in> den (TMustNot s a ETrue)"
    using mustnot_violated[of ETrue \<sigma>\<^sub>0 \<tau>\<^sub>0 \<tau>\<^sub>1 e \<sigma>\<^sub>1 s a p] assms(1) by simp
  then show "([(\<sigma>\<^sub>0, \<tau>\<^sub>0, e), (\<sigma>\<^sub>1, \<tau>\<^sub>1, Deontic s a p)], Violated)
           \<in> den (TThen (TMustNot s a ETrue) (TMust s' a'))"
    unfolding den.simps then_d_def by auto
qed

end


section \<open>Executable equations for expressions and guards\<close>

lemma eval_present_code: "eval (EPresent x) \<sigma> = Some (\<sigma> x \<noteq> None)"
  by (simp add: domIff)

lemmas eval_code [code] = eval.simps(1-9) eval_present_code

lemma first_at_code [code]:
  "first_at c \<pi> k \<longleftrightarrow>
     eval c (st \<pi> k) = Some True \<and> (\<forall>j \<in> set [0..<k]. eval c (st \<pi> j) \<noteq> Some True)"
  by (auto simp: first_at_def)


section \<open>Blocking stale factors by complex name\<close>

text \<open>The evaluator names data by complex names. A factor \<open>f\<close> under \<open>MAX_AGE m\<close> and
  \<open>ON_STALE BLOCK\<close> is fresh at an entry if \<open>[f]\<close> arrived at most \<open>m\<close> time units earlier
  (\<open>fresh\<close> of TRIEL_Breach). When it is stale, every complex name that starts with \<open>f\<close>
  is absent. This lifts \<open>blocked\<close> from names to factors, and the safety claim of section
  2.9 carries over with the same proof.\<close>

definition blockp :: "('f \<Rightarrow> int option) \<Rightarrow> ('f list, 'v, 's, 'a) itrace \<Rightarrow> nat \<Rightarrow> ('f list, 'v) state" where
  "blockp M \<pi> j p =
     (case p of
        [] \<Rightarrow> st \<pi> j p
      | f # q \<Rightarrow> (case M f of None \<Rightarrow> st \<pi> j p | Some m \<Rightarrow> if fresh m [f] \<pi> j then st \<pi> j p else None))"

lemma blockp_le: "blockp M \<pi> j \<sqsubseteq> st \<pi> j"
  unfolding info_le_def blockp_def by (auto split: list.splits option.splits if_splits)

theorem blockp_stale_absent:
  "M f = Some m \<Longrightarrow> \<not> fresh m [f] \<pi> j \<Longrightarrow> eval (EPresent (f # q)) (blockp M \<pi> j) = Some False"
  by (simp add: blockp_def domIff)

theorem blockp_stale_safe:
  assumes "present_free e" and "eval e (blockp M \<pi> j) = Some b"
    and "\<And>f q. M f = None \<or> (\<exists>m. M f = Some m \<and> fresh m [f] \<pi> j) \<Longrightarrow> \<sigma>' (f # q) = st \<pi> j (f # q)"
    and "\<sigma>' [] = st \<pi> j []"
  shows "eval e \<sigma>' = Some b"
proof -
  have "blockp M \<pi> j \<sqsubseteq> \<sigma>'"
    unfolding info_le_def
  proof
    fix p assume p: "p \<in> dom (blockp M \<pi> j)"
    show "\<sigma>' p = blockp M \<pi> j p"
    proof (cases p)
      case Nil
      with assms(4) show ?thesis by (simp add: blockp_def)
    next
      case (Cons f q)
      have ok: "M f = None \<or> (\<exists>m. M f = Some m \<and> fresh m [f] \<pi> j)"
      proof (cases "M f")
        case (Some m)
        show ?thesis
        proof (cases "fresh m [f] \<pi> j")
          case False
          with p Cons Some have False by (simp add: blockp_def domIff)
          then show ?thesis ..
        next
          case True
          with Some show ?thesis by blast
        qed
      qed simp
      have "blockp M \<pi> j p = st \<pi> j p"
        using ok Cons by (auto simp: blockp_def)
      with ok assms(3) Cons show ?thesis by simp
    qed
  qed
  from T2_monotone[OF assms(1) this assms(2)] show ?thesis .
qed

text \<open>The blocked trace keeps the timestamps and events and replaces each state by its
  blocked state.\<close>

definition btrace :: "('f \<Rightarrow> int option) \<Rightarrow> ('f list, 'v, 's, 'a) itrace \<Rightarrow> ('f list, 'v, 's, 'a) itrace" where
  "btrace M \<pi> = map (\<lambda>j. (blockp M \<pi> j, time \<pi> j, evt (\<pi> ! j))) [0..<length \<pi>]"

lemma btrace_length [simp]: "length (btrace M \<pi>) = length \<pi>"
  by (simp add: btrace_def)

lemma btrace_st: "j < length \<pi> \<Longrightarrow> st (btrace M \<pi>) j = blockp M \<pi> j"
  by (simp add: btrace_def st_def)

lemma btrace_time: "j < length \<pi> \<Longrightarrow> time (btrace M \<pi>) j = time \<pi> j"
  by (simp add: btrace_def time_def)

lemma btrace_evt: "j < length \<pi> \<Longrightarrow> evt (btrace M \<pi> ! j) = evt (\<pi> ! j)"
  by (simp add: btrace_def)

lemma btrace_is_trace:
  assumes "is_trace \<pi>"
  shows "is_trace (btrace M \<pi>)"
proof -
  have "map tstamp (btrace M \<pi>) = map tstamp \<pi>"
    by (rule nth_equalityI) (simp_all add: btrace_def time_def)
  with assms show ?thesis by (simp add: is_trace_def btrace_def)
qed


section \<open>The evaluator\<close>

subsection \<open>Values, types and specifications\<close>

text \<open>Basic values are Booleans, exact numbers, strings and times. A number is a rational
  (TRIEL_Numbers): Integer and Decimal are its two types, an Integer is a number in \<open>\<int>\<close>,
  and a Decimal is a number with a finite decimal expansion, so every Integer is a
  Decimal. There is no floating point. A time is an integer number of seconds since
  1970-01-01T00:00:00Z; the translator converts DATETIME literals and DAYS, HOURS,
  MINUTES and SECONDS durations into seconds.\<close>

datatype atom = ABool bool | ANum rat | AStr String.literal | ATime int

datatype prim = PBool | PInt | PDec | PStr | PTime

fun interp :: "prim \<Rightarrow> atom \<Rightarrow> bool" where
  "interp PBool b = (case b of ABool _ \<Rightarrow> True | _ \<Rightarrow> False)"
| "interp PInt b = (case b of ANum q \<Rightarrow> int_rat q | _ \<Rightarrow> False)"
| "interp PDec b = (case b of ANum q \<Rightarrow> decimal q | _ \<Rightarrow> False)"
| "interp PStr b = (case b of AStr _ \<Rightarrow> True | _ \<Rightarrow> False)"
| "interp PTime b = (case b of ATime _ \<Rightarrow> True | _ \<Rightarrow> False)"

lemma interp_int_dec: "interp PInt b \<Longrightarrow> interp PDec b"
  by (cases b) (simp_all add: int_rat_decimal)

text \<open>The decimal literal \<open>m\<close> with \<open>k\<close> digits after the point.\<close>

definition dec_atom :: "int \<Rightarrow> nat \<Rightarrow> atom" where
  "dec_atom m k = ANum (of_int m / 10 ^ k)"

lemma dec_atom_Decimal: "interp PDec (dec_atom m k)"
  by (simp add: dec_atom_def decimal_literal)

text \<open>The ordering comparisons compare numbers as rationals. They are only applied to
  numbers: the translator rejects an ordering comparison whose operand is not of type
  Integer or Decimal, and the types of the data are checked before any verdict. On any
  other pair of values they are false.\<close>

instantiation atom :: value_order
begin

fun vless_atom :: "atom \<Rightarrow> atom \<Rightarrow> bool" where
  "vless_atom (ANum p) (ANum q) = (p < q)"
| "vless_atom _ _ = False"

fun vleq_atom :: "atom \<Rightarrow> atom \<Rightarrow> bool" where
  "vleq_atom (ANum p) (ANum q) = (p \<le> q)"
| "vleq_atom _ _ = False"

instance ..

end

text \<open>On numbers, \<open>=\<close>, \<open><\<close> and \<open>\<le>\<close> are the equality and the order of the rationals; so an
  Integer and a Decimal with the same value are equal (\<open>12 = 12.00\<close>). An operand without
  a value makes the comparison undefined (\<open>cmp_undefined\<close>).\<close>

theorem eval_cmp_num:
  assumes "evalV a \<sigma> = Some (ANum p)" and "evalV b \<sigma> = Some (ANum q)"
  shows "eval (EEq a b) \<sigma> = Some (p = q)" and "eval (ELt a b) \<sigma> = Some (p < q)"
    and "eval (ELe a b) \<sigma> = Some (p \<le> q)"
  using assms by simp_all

fun time_of :: "atom \<Rightarrow> int option" where
  "time_of (ATime t) = Some t"
| "time_of _ = None"

type_synonym name = String.literal
type_synonym path = "name list"
type_synonym datum = "(name, atom) nd"
text \<open>An action is a name with a list of arguments (TECHNICAL_REPORT.md section 2.6). An
  argument is a name (of a subject or a factor), which is not evaluated, or a value. An
  action without arguments has the empty list.\<close>

datatype arg = ArgName path | ArgVal atom

datatype act = Act name "arg list"

type_synonym cpen = "(path, atom) pen"
type_synonym cterm = "(path, atom, name, act, cpen) sterm"
type_synonym cevent = "(path, name, act) event"
type_synonym ctrace = "(path, atom, name, act) itrace"

text \<open>An event matches a norm only with the same subject, the same action name and the
  same arguments. Every theory of sections 4--8 is generic in the type of actions, so all
  of their theorems hold for these actions.\<close>

theorem does_args:
  "does s (Act a xs) (Deontic s' (Act a' ys) p) \<longleftrightarrow> s' = s \<and> a' = a \<and> ys = xs"
  by (simp add: does_def)

corollary other_args_no_fulfil:
  "ys \<noteq> xs \<Longrightarrow> \<not> does s (Act a xs) (Deontic s' (Act a ys) p)"
  by (simp add: does_args)

text \<open>A literal argument is compared by value: the arguments \<open>1200\<close> and \<open>1200.00\<close> are the
  same.\<close>

lemma dec_atom_eq: "dec_atom m k = dec_atom n l \<longleftrightarrow> (of_int m / 10 ^ k :: rat) = of_int n / 10 ^ l"
  by (simp add: dec_atom_def)

corollary arg_1200: "ArgVal (dec_atom 1200 0) = ArgVal (dec_atom 120000 2)"
  by (simp add: dec_atom_def)

text \<open>The number a value denotes, for the amounts of penalties.\<close>

fun num_of :: "atom \<Rightarrow> rat option" where
  "num_of (ANum q) = Some q"
| "num_of _ = None"
type_synonym observation = "datum \<times> int \<times> cevent"

text \<open>A factor declaration: the name, the declared type, the maximum age if the factor
  is under \<open>ON_STALE BLOCK\<close>, and whether the factor is hidden: a \<open>ZK<T>\<close> factor without
  \<open>WITHOUT REVEALING ALL\<close> (TECHNICAL_REPORT.md section 2.7), whose declared type is \<open>T\<close>. A
  specification: the factors, the TERMS block, and the named invariants. The penalty
  amount of a breach handler is an opaque value.\<close>

datatype fdecl = Fdecl name "(name, prim) ty" "int option" bool

fun fd_name :: "fdecl \<Rightarrow> name" where "fd_name (Fdecl f t m h) = f"
fun fd_ty :: "fdecl \<Rightarrow> (name, prim) ty" where "fd_ty (Fdecl f t m h) = t"
fun fd_age :: "fdecl \<Rightarrow> int option" where "fd_age (Fdecl f t m h) = m"
fun fd_hidden :: "fdecl \<Rightarrow> bool" where "fd_hidden (Fdecl f t m h) = h"

datatype spec = Spec "fdecl list" "cterm list" "(name \<times> (path, atom) sinv) list"

definition max_age :: "fdecl list \<Rightarrow> name \<Rightarrow> int option" where
  "max_age fs f = (case find (\<lambda>x. fd_name x = f) fs of Some x \<Rightarrow> fd_age x | None \<Rightarrow> None)"

text \<open>The raw trace: the state of an entry is its data flattened to complex names.\<close>

definition raw_trace :: "observation list \<Rightarrow> ctrace" where
  "raw_trace obs = map (\<lambda>(d, \<tau>, e). (flat d, \<tau>, e)) obs"


subsection \<open>Hidden factors\<close>

text \<open>The value of a hidden factor is checked by the proof system, not by the evaluator
  (decision 25 of CORE.md). The evaluator removes every hidden factor from the data of
  every entry before it does anything else. A complex name \<open>hides\<close> if it starts with a
  hidden factor.\<close>

definition hidden :: "fdecl list \<Rightarrow> name list" where
  "hidden fs = map fd_name (filter fd_hidden fs)"

fun erase :: "name list \<Rightarrow> datum \<Rightarrow> datum" where
  "erase H (Nom m) = Nom (fmfilter (\<lambda>x. x \<notin> set H) m)"
| "erase H (Atom b) = Atom b"

definition erase_obs :: "name list \<Rightarrow> observation list \<Rightarrow> observation list" where
  "erase_obs H obs = map (\<lambda>(d, \<tau>, e). (erase H d, \<tau>, e)) obs"

fun hides :: "name list \<Rightarrow> path \<Rightarrow> bool" where
  "hides H [] = False"
| "hides H (x # p) = (x \<in> set H)"

lemma hidden_iff: "x \<in> set (hidden fs) \<longleftrightarrow> (\<exists>y \<in> set fs. fd_hidden y \<and> fd_name y = x)"
  by (auto simp: hidden_def)

lemma erase_hidden: "x \<in> set H \<Longrightarrow> denaming x (erase H d) = None"
  by (cases d) simp_all

lemma erase_visible: "x \<notin> set H \<Longrightarrow> denaming x (erase H d) = denaming x d"
  by (cases d) simp_all

lemma erase_idem: "erase H (erase H d) = erase H d"
  by (cases d) (auto intro!: fmap_ext)

lemma length_erase_obs [simp]: "length (erase_obs H obs) = length obs"
  by (simp add: erase_obs_def)

lemma erase_obs_nth:
  "j < length obs \<Longrightarrow> erase_obs H obs ! j = (erase H (fst (obs ! j)), fst (snd (obs ! j)), snd (snd (obs ! j)))"
  by (simp add: erase_obs_def split: prod.splits)

lemma erase_obs_idem: "erase_obs H (erase_obs H obs) = erase_obs H obs"
  by (induction obs) (auto simp: erase_obs_def erase_idem split: prod.splits)

text \<open>After the removal a complex name that starts with a hidden factor has no value, and
  every other complex name keeps its value.\<close>

theorem erase_flat: "flat (erase H d) p = (if hides H p then None else flat d p)"
proof (cases p)
  case Nil
  then show ?thesis by (cases d) (simp_all add: flat_def)
next
  case (Cons x q)
  then show ?thesis
    by (cases "x \<in> set H") (simp_all add: flat_def erase_hidden erase_visible)
qed

text \<open>The trace the evaluator sees. Removing the hidden factors keeps the timestamps and the
  events, so it keeps freshness; blocking stale factors and removing hidden ones commute.\<close>

lemma raw_trace_erase_length [simp]: "length (raw_trace (erase_obs H obs)) = length (raw_trace obs)"
  by (simp add: raw_trace_def)

lemma erase_time_evt:
  assumes "j < length obs"
  shows "time (raw_trace (erase_obs H obs)) j = time (raw_trace obs) j"
    and "evt (raw_trace (erase_obs H obs) ! j) = evt (raw_trace obs ! j)"
proof -
  obtain d \<tau> e where o: "obs ! j = (d, \<tau>, e)" by (cases "obs ! j") auto
  show "time (raw_trace (erase_obs H obs)) j = time (raw_trace obs) j"
    using assms o by (simp add: raw_trace_def erase_obs_def time_def)
  show "evt (raw_trace (erase_obs H obs) ! j) = evt (raw_trace obs ! j)"
    using assms o by (simp add: raw_trace_def erase_obs_def)
qed

lemma erase_st:
  assumes "j < length obs"
  shows "st (raw_trace (erase_obs H obs)) j p = (if hides H p then None else st (raw_trace obs) j p)"
proof -
  obtain d \<tau> e where o: "obs ! j = (d, \<tau>, e)" by (cases "obs ! j") auto
  show ?thesis
    using assms o by (simp add: raw_trace_def erase_obs_def st_def erase_flat)
qed

lemma erase_fresh:
  assumes "j < length obs"
  shows "fresh m x (raw_trace (erase_obs H obs)) j = fresh m x (raw_trace obs) j"
proof -
  have "i \<le> j \<Longrightarrow> evt (raw_trace (erase_obs H obs) ! i) = evt (raw_trace obs ! i) \<and>
          time (raw_trace (erase_obs H obs)) i = time (raw_trace obs) i" for i
    using assms erase_time_evt[of i obs H] by simp
  then show ?thesis
    using erase_time_evt(1)[OF assms] unfolding fresh_def by auto
qed

theorem erase_btrace:
  assumes "j < length obs"
  shows "st (btrace M (raw_trace (erase_obs H obs))) j p =
           (if hides H p then None else st (btrace M (raw_trace obs)) j p)"
    and "time (btrace M (raw_trace (erase_obs H obs))) j = time (btrace M (raw_trace obs)) j"
    and "evt (btrace M (raw_trace (erase_obs H obs)) ! j) = evt (btrace M (raw_trace obs) ! j)"
proof -
  have j: "j < length (raw_trace obs)" "j < length (raw_trace (erase_obs H obs))"
    using assms by (simp_all add: raw_trace_def)
  show "st (btrace M (raw_trace (erase_obs H obs))) j p =
          (if hides H p then None else st (btrace M (raw_trace obs)) j p)"
    using j assms by (cases p) (auto simp: btrace_st blockp_def erase_st erase_fresh split: option.splits)
  show "time (btrace M (raw_trace (erase_obs H obs))) j = time (btrace M (raw_trace obs)) j"
    using j assms by (simp add: btrace_time erase_time_evt)
  show "evt (btrace M (raw_trace (erase_obs H obs)) ! j) = evt (btrace M (raw_trace obs) ! j)"
    using j assms by (simp add: btrace_evt erase_time_evt)
qed

text \<open>The flow rule (TECHNICAL_REPORT.md section 2.7), checked by the translator: a hidden
  factor is not read in a condition, an invariant or a value. An expression reads the names
  in \<open>names\<close> (operands of comparisons) and in \<open>pnames\<close> (PRESENT and the first argument
  of DEFAULT). Two states that agree on these names give the expression the same value.\<close>

lemma evalV_agree: "(\<forall>p \<in> vnames a \<union> vpnames a. \<sigma> p = \<sigma>' p) \<Longrightarrow> evalV a \<sigma> = evalV a \<sigma>'"
proof (induction a)
  case (VDefault x a)
  have "evalV a \<sigma> = evalV a \<sigma>'"
    by (rule VDefault.IH) (use VDefault.prems in auto)
  moreover have "\<sigma> x = \<sigma>' x"
    using VDefault.prems by auto
  ultimately show ?case by (simp cong: option.case_cong)
qed auto

lemma eval_agree: "(\<forall>p \<in> names e \<union> pnames e. \<sigma> p = \<sigma>' p) \<Longrightarrow> eval e \<sigma> = eval e \<sigma>'"
proof (induction e)
  case (EEq a b)
  have "evalV a \<sigma> = evalV a \<sigma>'" by (rule evalV_agree) (use EEq in auto)
  moreover have "evalV b \<sigma> = evalV b \<sigma>'" by (rule evalV_agree) (use EEq in auto)
  ultimately show ?case by (simp cong: option.case_cong)
next
  case (ELt a b)
  have "evalV a \<sigma> = evalV a \<sigma>'" by (rule evalV_agree) (use ELt in auto)
  moreover have "evalV b \<sigma> = evalV b \<sigma>'" by (rule evalV_agree) (use ELt in auto)
  ultimately show ?case by (simp cong: option.case_cong)
next
  case (ELe a b)
  have "evalV a \<sigma> = evalV a \<sigma>'" by (rule evalV_agree) (use ELe in auto)
  moreover have "evalV b \<sigma> = evalV b \<sigma>'" by (rule evalV_agree) (use ELe in auto)
  ultimately show ?case by (simp cong: option.case_cong)
next
  case (EAnd e\<^sub>1 e\<^sub>2)
  have "eval e\<^sub>1 \<sigma> = eval e\<^sub>1 \<sigma>'" by (rule EAnd.IH(1)) (use EAnd.prems in auto)
  moreover have "eval e\<^sub>2 \<sigma> = eval e\<^sub>2 \<sigma>'" by (rule EAnd.IH(2)) (use EAnd.prems in auto)
  ultimately show ?case by simp
next
  case (EOr e\<^sub>1 e\<^sub>2)
  have "eval e\<^sub>1 \<sigma> = eval e\<^sub>1 \<sigma>'" by (rule EOr.IH(1)) (use EOr.prems in auto)
  moreover have "eval e\<^sub>2 \<sigma> = eval e\<^sub>2 \<sigma>'" by (rule EOr.IH(2)) (use EOr.prems in auto)
  ultimately show ?case by simp
next
  case (EImp e\<^sub>1 e\<^sub>2)
  have "eval e\<^sub>1 \<sigma> = eval e\<^sub>1 \<sigma>'" by (rule EImp.IH(1)) (use EImp.prems in auto)
  moreover have "eval e\<^sub>2 \<sigma> = eval e\<^sub>2 \<sigma>'" by (rule EImp.IH(2)) (use EImp.prems in auto)
  ultimately show ?case by simp
next
  case (EPresent x)
  then show ?case by (simp add: domIff)
qed simp_all

text \<open>So a condition that passes the flow rule has the same value at every entry of the
  trace the evaluator sees, with the hidden factors removed and with them left in, and so
  does a value expression (an operand or a penalty amount).\<close>

theorem flow_safe_eval:
  assumes "\<forall>p \<in> names e \<union> pnames e. \<not> hides H p" and "j < length obs"
  shows "eval e (st (btrace M (raw_trace (erase_obs H obs))) j) = eval e (st (btrace M (raw_trace obs)) j)"
proof (rule eval_agree, intro ballI)
  fix p assume "p \<in> names e \<union> pnames e"
  with assms(1) have "\<not> hides H p" by blast
  with erase_btrace(1)[OF assms(2), of M H p]
  show "st (btrace M (raw_trace (erase_obs H obs))) j p = st (btrace M (raw_trace obs)) j p" by simp
qed

theorem flow_safe_evalV:
  assumes "\<forall>p \<in> vnames a \<union> vpnames a. \<not> hides H p" and "j < length obs"
  shows "evalV a (st (btrace M (raw_trace (erase_obs H obs))) j) = evalV a (st (btrace M (raw_trace obs)) j)"
proof (rule evalV_agree, intro ballI)
  fix p assume "p \<in> vnames a \<union> vpnames a"
  with assms(1) have "\<not> hides H p" by blast
  with erase_btrace(1)[OF assms(2), of M H p]
  show "st (btrace M (raw_trace (erase_obs H obs))) j p = st (btrace M (raw_trace obs)) j p" by simp
qed


subsection \<open>Types of the data\<close>

text \<open>A factor may be absent; a present factor must have its declared type. The first
  ill-typed pair of an entry and a factor is reported, entries first, then factors in
  declaration order.\<close>

definition ill_typed :: "fdecl list \<Rightarrow> observation list \<Rightarrow> (nat \<times> name) option" where
  "ill_typed fs obs =
     map_option (\<lambda>(j, x). (j, fd_name x))
       (find (\<lambda>(j, x). \<not> wt_fun interp (TOptional (fd_ty x)) (denaming (fd_name x) (fst (obs ! j))))
          (concat (map (\<lambda>j. map (\<lambda>x. (j, x)) fs) [0..<length obs])))"

lemma ill_typed_None:
  "ill_typed fs obs = None \<longleftrightarrow>
     (\<forall>j < length obs. \<forall>x \<in> set fs. wt interp (TOptional (fd_ty x)) (denaming (fd_name x) (fst (obs ! j))))"
proof -
  let ?P = "\<lambda>j x. wt_fun interp (TOptional (fd_ty x)) (denaming (fd_name x) (fst (obs ! j)))"
  let ?xs = "concat (map (\<lambda>j. map (\<lambda>x. (j, x)) fs) [0..<length obs])"
  have mem: "(j, x) \<in> set ?xs \<longleftrightarrow> j < length obs \<and> x \<in> set fs" for j x by auto
  have "ill_typed fs obs = None \<longleftrightarrow> find (\<lambda>(j, x). \<not> ?P j x) ?xs = None"
    by (simp add: ill_typed_def)
  also have "\<dots> \<longleftrightarrow> (\<forall>j x. (j, x) \<in> set ?xs \<longrightarrow> ?P j x)"
    by (auto simp: find_None_iff)
  also have "\<dots> \<longleftrightarrow> (\<forall>j < length obs. \<forall>x \<in> set fs. ?P j x)"
    using mem by blast
  finally show ?thesis by (simp add: wt_fun_iff)
qed


subsection \<open>Composite terms and named terms\<close>

text \<open>A composite element is translated into a term of the core under an environment
  \<open>\<Gamma>\<close>: \<open>\<Gamma> ! k\<close> is the term the element \<open>k\<close> of the block stands for, and \<open>REF k\<close> is
  replaced by it. A reference outside \<open>\<Gamma>\<close> has no term.\<close>

fun refs :: "('n, 'v, 's, 'a, 'p) sterm \<Rightarrow> nat set" where
  "refs (SRef k) = {k}"
| "refs (SThen t u) = refs t \<union> refs u"
| "refs (SOr t u) = refs t \<union> refs u"
| "refs (SAnd t u) = refs t \<union> refs u"
| "refs (SUnless t c u) = refs t \<union> refs u"
| "refs (SIf c t u) = refs t \<union> refs u"
| "refs _ = {}"

fun to_tm_env ::
    "('n, 'v, 's, 'a) tm option list \<Rightarrow> ('n, 'v, 's, 'a, 'p) sterm \<Rightarrow> ('n, 'v, 's, 'a) tm option" where
  "to_tm_env \<Gamma> (SMust s a D F) = Some (TMust s a)"
| "to_tm_env \<Gamma> (SMustNot s a c) = Some (TMustNot s a c)"
| "to_tm_env \<Gamma> (SMay s a c) = Some (TMay s a c)"
| "to_tm_env \<Gamma> (SThen t u) =
     (case (to_tm_env \<Gamma> t, to_tm_env \<Gamma> u) of (Some t', Some u') \<Rightarrow> Some (TThen t' u') | _ \<Rightarrow> None)"
| "to_tm_env \<Gamma> (SOr t u) =
     (case (to_tm_env \<Gamma> t, to_tm_env \<Gamma> u) of (Some t', Some u') \<Rightarrow> Some (TOr t' u') | _ \<Rightarrow> None)"
| "to_tm_env \<Gamma> (SAnd t u) =
     (case (to_tm_env \<Gamma> t, to_tm_env \<Gamma> u) of (Some t', Some u') \<Rightarrow> Some (TAnd t' u') | _ \<Rightarrow> None)"
| "to_tm_env \<Gamma> (SUnless t c u) =
     (case (to_tm_env \<Gamma> t, to_tm_env \<Gamma> u) of (Some t', Some u') \<Rightarrow> Some (TUnless t' c u') | _ \<Rightarrow> None)"
| "to_tm_env \<Gamma> (SIf c t u) =
     (case (to_tm_env \<Gamma> t, to_tm_env \<Gamma> u) of (Some t', Some u') \<Rightarrow> Some (TIf c t' u') | _ \<Rightarrow> None)"
| "to_tm_env \<Gamma> SSkip = Some TSkip"
| "to_tm_env \<Gamma> (SRef k) = (if k < length \<Gamma> then \<Gamma> ! k else None)"
| "to_tm_env \<Gamma> (SOnBreach s acts) = None"
| "to_tm_env \<Gamma> (SMustElse s a d s' a' D') = Some (TOr (TMust s a) (TMust s' a'))"

lemma to_tm_defined:
  "\<not> has_handler t \<Longrightarrow> (\<And>k. k \<in> refs t \<Longrightarrow> k < length \<Gamma> \<and> \<Gamma> ! k \<noteq> None) \<Longrightarrow> to_tm_env \<Gamma> t \<noteq> None"
  by (induction t) (auto split: option.splits)

text \<open>The environment of a block is built from left to right: the element \<open>i\<close> is
  translated under the terms of the elements before it.\<close>

fun benv_from :: "('n, 'v, 's, 'a) tm option list \<Rightarrow> ('n, 'v, 's, 'a, 'p) sterm list
    \<Rightarrow> ('n, 'v, 's, 'a) tm option list" where
  "benv_from \<Gamma> [] = \<Gamma>"
| "benv_from \<Gamma> (t # ts) = benv_from (\<Gamma> @ [to_tm_env \<Gamma> t]) ts"

definition benv :: "('n, 'v, 's, 'a, 'p) sterm list \<Rightarrow> ('n, 'v, 's, 'a) tm option list" where
  "benv blk = benv_from [] blk"

lemma benv_from_length: "length (benv_from \<Gamma> ts) = length \<Gamma> + length ts"
  by (induction ts arbitrary: \<Gamma>) auto

lemma benv_from_take: "take (length \<Gamma>) (benv_from \<Gamma> ts) = \<Gamma>"
proof (induction ts arbitrary: \<Gamma>)
  case (Cons t ts)
  have "take (length \<Gamma>) (benv_from \<Gamma> (t # ts))
      = take (length \<Gamma>) (take (length (\<Gamma> @ [to_tm_env \<Gamma> t])) (benv_from (\<Gamma> @ [to_tm_env \<Gamma> t]) ts))"
    by (simp add: min_def)
  also have "\<dots> = \<Gamma>" by (simp only: Cons.IH) simp
  finally show ?case .
qed simp

lemma benv_from_nth:
  "i < length ts \<Longrightarrow>
     benv_from \<Gamma> ts ! (length \<Gamma> + i) = to_tm_env (take (length \<Gamma> + i) (benv_from \<Gamma> ts)) (ts ! i)"
proof (induction ts arbitrary: \<Gamma> i)
  case (Cons t ts)
  let ?\<Gamma> = "\<Gamma> @ [to_tm_env \<Gamma> t]"
  show ?case
  proof (cases i)
    case 0
    have "benv_from ?\<Gamma> ts ! length \<Gamma> = take (length ?\<Gamma>) (benv_from ?\<Gamma> ts) ! length \<Gamma>"
      by (simp add: benv_from_length)
    also have "\<dots> = to_tm_env \<Gamma> t" by (simp only: benv_from_take) simp
    finally have a: "benv_from ?\<Gamma> ts ! length \<Gamma> = to_tm_env \<Gamma> t" .
    have "take (length \<Gamma>) (benv_from ?\<Gamma> ts) = take (length \<Gamma>) (take (length ?\<Gamma>) (benv_from ?\<Gamma> ts))"
      by (simp add: min_def)
    also have "\<dots> = \<Gamma>" by (simp only: benv_from_take) simp
    finally have b: "take (length \<Gamma>) (benv_from ?\<Gamma> ts) = \<Gamma>" .
    from a b 0 show ?thesis by simp
  next
    case (Suc j)
    with Cons.prems have "j < length ts" by simp
    from Cons.IH[OF this, of ?\<Gamma>] Suc show ?thesis by simp
  qed
qed simp

lemma benv_length: "length (benv blk) = length blk"
  by (simp add: benv_def benv_from_length)

lemma benv_nth: "i < length blk \<Longrightarrow> benv blk ! i = to_tm_env (take i (benv blk)) (blk ! i)"
  using benv_from_nth[of i blk "[]"] by (simp add: benv_def)

text \<open>The references of a block are well formed if every \<open>REF\<close> in the element \<open>i\<close> names
  an element \<open>k < i\<close> declared before it, and that element is a term, not a breach handler.
  The translator rejects an undeclared name and a name declared later; a cycle of
  references needs a reference to a later element, so it is rejected too.\<close>

definition refs_ok :: "('n, 'v, 's, 'a, 'p) sterm list \<Rightarrow> bool" where
  "refs_ok blk \<longleftrightarrow> (\<forall>i < length blk. \<forall>k \<in> refs (blk ! i). k < i \<and> \<not> has_handler (blk ! k))"

definition ref_graph :: "('n, 'v, 's, 'a, 'p) sterm list \<Rightarrow> (nat \<times> nat) set" where
  "ref_graph blk = {(k, i). i < length blk \<and> k \<in> refs (blk ! i)}"

theorem refs_forward_rejected:
  "i < length blk \<Longrightarrow> k \<in> refs (blk ! i) \<Longrightarrow> i \<le> k \<Longrightarrow> \<not> refs_ok blk"
  unfolding refs_ok_def by fastforce

theorem refs_ok_acyclic: "refs_ok blk \<Longrightarrow> wf (ref_graph blk)"
proof -
  assume ok: "refs_ok blk"
  have "ref_graph blk \<subseteq> less_than"
    using ok unfolding refs_ok_def ref_graph_def by auto
  then show ?thesis by (rule wf_subset[OF wf_less_than])
qed

theorem refs_no_cycle: "refs_ok blk \<Longrightarrow> (i, i) \<notin> (ref_graph blk)\<^sup>+"
  using wf_acyclic[OF refs_ok_acyclic] unfolding acyclic_def by blast

theorem benv_defined:
  assumes "refs_ok blk" and "i < length blk" and "\<not> has_handler (blk ! i)"
  shows "benv blk ! i \<noteq> None"
  using assms(2,3)
proof (induction i rule: less_induct)
  case (less i)
  have "to_tm_env (take i (benv blk)) (blk ! i) \<noteq> None"
  proof (rule to_tm_defined[OF less.prems(2)])
    fix k assume k: "k \<in> refs (blk ! i)"
    with assms(1) less.prems(1) have "k < i" and h: "\<not> has_handler (blk ! k)"
      unfolding refs_ok_def by auto
    with less.prems(1) less.IH[of k] h
    show "k < length (take i (benv blk)) \<and> take i (benv blk) ! k \<noteq> None"
      by (simp add: benv_length)
  qed
  with benv_nth[OF less.prems(1)] show ?case by simp
qed

context term_semantics
begin

text \<open>The reference semantics of an element of a block: \<open>D ! k\<close> is the denotation of the
  element \<open>k\<close>, and \<open>REF k\<close> denotes it.\<close>

fun sden :: "('n, 'v, 't, 's, 'a) den option list \<Rightarrow> ('n, 'v, 's, 'a, 'p) sterm
    \<Rightarrow> ('n, 'v, 't, 's, 'a) den option" where
  "sden D (SMust s a d f) = Some (must_d s a)"
| "sden D (SMustNot s a c) = Some (mustnot_d s a c)"
| "sden D (SMay s a c) = Some (may_d s a c)"
| "sden D (SThen t u) = (case (sden D t, sden D u) of (Some x, Some y) \<Rightarrow> Some (then_d x y) | _ \<Rightarrow> None)"
| "sden D (SOr t u) = (case (sden D t, sden D u) of (Some x, Some y) \<Rightarrow> Some (or_d x y) | _ \<Rightarrow> None)"
| "sden D (SAnd t u) = (case (sden D t, sden D u) of (Some x, Some y) \<Rightarrow> Some (and_d x y) | _ \<Rightarrow> None)"
| "sden D (SUnless t c u) =
     (case (sden D t, sden D u) of (Some x, Some y) \<Rightarrow> Some (unless_d x c y) | _ \<Rightarrow> None)"
| "sden D (SIf c t u) = (case (sden D t, sden D u) of (Some x, Some y) \<Rightarrow> Some (if_d c x y) | _ \<Rightarrow> None)"
| "sden D SSkip = Some skip_d"
| "sden D (SRef k) = (if k < length D then D ! k else None)"
| "sden D (SOnBreach s acts) = None"
| "sden D (SMustElse s a d s' a' D') = Some (or_d (must_d s a) (must_d s' a'))"

text \<open>Substitution preserves the denotation: the term obtained by replacing every
  \<open>REF k\<close> by the term of the element \<open>k\<close> denotes what the reference semantics gives.\<close>

theorem resolve_den: "map_option den (to_tm_env \<Gamma> t) = sden (map (map_option den) \<Gamma>) t"
  by (induction t) (auto split: option.splits, (metis)+)

theorem block_den:
  "i < length blk \<Longrightarrow>
     map_option den (benv blk ! i) = sden (map (map_option den) (take i (benv blk))) (blk ! i)"
  by (simp add: benv_nth resolve_den)

text \<open>A resolved element is a term of the core, so its denotation is total and the laws
  of UNLESS apply to it without conditions.\<close>

theorem benv_total: "benv blk ! i = Some u \<Longrightarrow> total (den u)"
  by (rule den_total)

end


subsection \<open>Time order\<close>

text \<open>A list of observations is an implementation trace only if its times do not decrease
  (\<open>is_trace\<close>). Every verdict depends on this: a breach is final only because no later
  entry can be earlier than the entry past the deadline (\<open>window_final\<close>). The evaluator
  checks it before anything else, and \<open>time_order\<close> is the first entry that is earlier than
  the entry before it.\<close>

definition obs_time :: "observation \<Rightarrow> int" where
  "obs_time x = fst (snd x)"

definition time_order :: "observation list \<Rightarrow> nat option" where
  "time_order obs = find (\<lambda>j. 0 < j \<and> obs_time (obs ! j) < obs_time (obs ! (j - 1))) [0..<length obs]"

lemma map_tstamp_raw_trace: "map tstamp (raw_trace obs) = map obs_time obs"
  by (induction obs) (auto simp: raw_trace_def obs_time_def split: prod.splits)

lemma time_order_None: "time_order obs = None \<longleftrightarrow> sorted (map obs_time obs)"
proof -
  have "time_order obs = None \<longleftrightarrow>
          (\<forall>j < length obs. \<not> (0 < j \<and> obs_time (obs ! j) < obs_time (obs ! (j - 1))))"
    by (simp add: time_order_def find_upt_None)
  also have "\<dots> \<longleftrightarrow> (\<forall>i. Suc i < length obs \<longrightarrow> obs_time (obs ! i) \<le> obs_time (obs ! Suc i))"
  proof
    assume a: "\<forall>j < length obs. \<not> (0 < j \<and> obs_time (obs ! j) < obs_time (obs ! (j - 1)))"
    show "\<forall>i. Suc i < length obs \<longrightarrow> obs_time (obs ! i) \<le> obs_time (obs ! Suc i)"
    proof (intro allI impI)
      fix i assume "Suc i < length obs"
      with a have "\<not> (0 < Suc i \<and> obs_time (obs ! Suc i) < obs_time (obs ! (Suc i - 1)))" by blast
      then show "obs_time (obs ! i) \<le> obs_time (obs ! Suc i)" by simp
    qed
  next
    assume a: "\<forall>i. Suc i < length obs \<longrightarrow> obs_time (obs ! i) \<le> obs_time (obs ! Suc i)"
    show "\<forall>j < length obs. \<not> (0 < j \<and> obs_time (obs ! j) < obs_time (obs ! (j - 1)))"
    proof (intro allI impI)
      fix j assume j: "j < length obs"
      show "\<not> (0 < j \<and> obs_time (obs ! j) < obs_time (obs ! (j - 1)))"
      proof (cases j)
        case (Suc i)
        with a j have "obs_time (obs ! i) \<le> obs_time (obs ! Suc i)" by blast
        with Suc show ?thesis by simp
      qed simp
    qed
  qed
  also have "\<dots> \<longleftrightarrow> sorted (map obs_time obs)" by (simp add: sorted_iff_nth_Suc)
  finally show ?thesis .
qed

theorem time_order_is_trace: "obs \<noteq> [] \<Longrightarrow> time_order obs = None \<longleftrightarrow> is_trace (raw_trace obs)"
  by (simp add: is_trace_def time_order_None map_tstamp_raw_trace) (simp add: raw_trace_def)

lemma obs_time_erase: "j < length obs \<Longrightarrow> obs_time (erase_obs H obs ! j) = obs_time (obs ! j)"
  by (simp add: erase_obs_def obs_time_def split: prod.splits)

lemma time_order_erase: "time_order (erase_obs H obs) = time_order obs"
  unfolding time_order_def by (rule find_cong) (auto simp: obs_time_erase)


subsection \<open>The report\<close>

datatype line =
    LTimeOrder nat
  | LActivation bool
  | LBlock bool
  | LTypes "(nat \<times> name) option"
  | LMust nat name act "int option" "name status" "name ract list"
  | LMustNot nat name act verdict "name ract list"
  | LMay nat name act verdict
  | LMustElse nat name act "int option" name act "int option" else_status
  | LOnBreach nat name "nat option"
  | LComposite nat "bool option" "bool option" "bool option" cstatus
  | LInvariant name "bool option"
  | LMonitor nat "(nat \<times> bool) list"

text \<open>The handler bound to the element \<open>i\<close> of a block, if any.\<close>

definition handler_of :: "('n, 'v, 's, 'a, 'p) sterm list \<Rightarrow> nat \<Rightarrow> ('s, 'p) baction list" where
  "handler_of blk i =
     (case find (\<lambda>k. case blk ! k of SOnBreach s acts \<Rightarrow> bound_to blk k s = Some i | _ \<Rightarrow> False)
                [0..<length blk] of
        Some k \<Rightarrow> (case blk ! k of SOnBreach s acts \<Rightarrow> acts | _ \<Rightarrow> [])
      | None \<Rightarrow> [])"

text \<open>Section 2.6 defines continuations only for obligations. In a handler bound to a
  prohibition only informational actions are allowed.\<close>

definition cont_free_prohibitions :: "('n, 'v, 's, 'a, 'p) sterm list \<Rightarrow> bool" where
  "cont_free_prohibitions blk \<longleftrightarrow>
     list_all (\<lambda>k. case blk ! k of
                       SMustNot s a c \<Rightarrow> list_all (\<lambda>x. \<not> is_cont x) (handler_of blk k)
                     | _ \<Rightarrow> True)
              [0..<length blk]"

text \<open>The actions reported with a breached prohibition: the informational actions of the
  handler bound to it.\<close>

definition pr_actions ::
    "('n, 'v, 's, 'a, 'p) sterm list \<Rightarrow> nat \<Rightarrow> verdict \<Rightarrow> ('s, 'p) baction list" where
  "pr_actions blk i v =
     (case v of Breached \<tau> \<Rightarrow> filter (\<lambda>x. \<not> is_cont x) (handler_of blk i) | _ \<Rightarrow> [])"

lemma pr_actions_informational: "x \<in> set (pr_actions blk i v) \<Longrightarrow> \<not> is_cont x"
  by (auto simp: pr_actions_def split: verdict.splits)

lemma pr_actions_breached: "pr_actions blk i v \<noteq> [] \<Longrightarrow> \<exists>\<tau>. v = Breached \<tau>"
  by (auto simp: pr_actions_def split: verdict.splits)

lemma pr_actions_cont_free:
  assumes "cont_free_prohibitions blk" and "i < length blk" and "blk ! i = SMustNot s a c"
  shows "pr_actions blk i (Breached \<tau>) = handler_of blk i"
proof -
  have "\<forall>x \<in> set (handler_of blk i). \<not> is_cont x"
    using bspec[OF assms(1)[unfolded cont_free_prohibitions_def list_all_iff], of i] assms(2,3)
    by simp
  then show ?thesis
    by (simp add: pr_actions_def)
qed

text \<open>The actions reported with a prohibition are those of \<open>pr_actions\<close>, with each
  penalty computed in the state of the breach.\<close>

lemma pr_report_actions:
  "pr_report num s a c (handler_of blk i) \<pi> =
     (case pr_verdict s a c \<pi> of
        Breached \<tau> \<Rightarrow> report_actions num (pr_pen_state s a c \<pi>) (pr_actions blk i (Breached \<tau>))
      | _ \<Rightarrow> [])"
  by (auto simp: pr_report_def pr_actions_def report_actions_informational[symmetric]
      split: verdict.splits)

definition composite_line :: "nat \<Rightarrow> (path, atom, name, act) tm option \<Rightarrow> ctrace \<Rightarrow> line" where
  "composite_line n t \<pi> =
     (case t of
        None \<Rightarrow> LComposite n None None None CUnknown
      | Some u \<Rightarrow> LComposite n (mem3 u \<pi> Done) (mem3 u \<pi> Interrupted) (mem3 u \<pi> Violated)
                                 (status u \<pi>))"

text \<open>The line of the element \<open>i\<close> of the block, numbered from 1 in the report. An
  obligation without a deadline is never breached, so its handler plays no role. An
  obligation with \<open>FROM\<close> has its start and window from \<open>start_of\<close> and \<open>lo_of\<close>, and its
  deadline from \<open>deadline_of\<close>. A breached obligation or prohibition is reported with the
  informational actions of its handler, the penalties computed in the state of the
  breach (TRIEL_Penalty).\<close>

definition must_line :: "int \<Rightarrow> (path, atom) state \<Rightarrow> cterm list \<Rightarrow> ctrace \<Rightarrow> nat
    \<Rightarrow> name \<Rightarrow> act \<Rightarrow> path deadline option \<Rightarrow> path deadline option \<Rightarrow> line" where
  "must_line \<tau>\<^sub>0 \<sigma>\<^sub>0 blk \<pi> i s a D F =
     (case start_of time_of \<tau>\<^sub>0 \<sigma>\<^sub>0 F of
        None \<Rightarrow> LMust (Suc i) s a None SPending []
      | Some b \<Rightarrow>
          (case deadline_of time_of \<tau>\<^sub>0 \<sigma>\<^sub>0 F D of
             None \<Rightarrow> LMust (Suc i) s a None
                       (case ob_verdict s a (lo_of F b) None \<pi> of Fulfilled \<Rightarrow> SFulfilled | _ \<Rightarrow> SPending) []
           | Some d \<Rightarrow>
               (let st = handle_breach b (lo_of F b) s a d (handler_of blk i) \<pi> in
                LMust (Suc i) s a (Some d) st (ob_report num_of d st (handler_of blk i) \<pi>))))"

text \<open>The line of an obligation with a fallback: its deadline, the deadline of the
  fallback (a duration counts from the first deadline), and \<open>else_verdict\<close>.\<close>

definition else_line :: "int \<Rightarrow> (path, atom) state \<Rightarrow> ctrace \<Rightarrow> nat \<Rightarrow> name \<Rightarrow> act
    \<Rightarrow> path deadline \<Rightarrow> name \<Rightarrow> act \<Rightarrow> path deadline option \<Rightarrow> line" where
  "else_line \<tau>\<^sub>0 \<sigma>\<^sub>0 \<pi> i s a d s' a' D' =
     (case resolve time_of \<tau>\<^sub>0 \<sigma>\<^sub>0 d of
        None \<Rightarrow> LMustElse (Suc i) s a None s' a' None EPending
      | Some e \<Rightarrow>
          (let e' = else_deadline time_of \<sigma>\<^sub>0 e D' in
           LMustElse (Suc i) s a (Some e) s' a' e' (else_verdict s a e s' a' e' \<pi>)))"

definition term_line :: "int \<Rightarrow> (path, atom) state \<Rightarrow> cterm list \<Rightarrow> ctrace \<Rightarrow> nat \<Rightarrow> line" where
  "term_line \<tau>\<^sub>0 \<sigma>\<^sub>0 blk \<pi> i =
     (case blk ! i of
        SMust s a D F \<Rightarrow> must_line \<tau>\<^sub>0 \<sigma>\<^sub>0 blk \<pi> i s a D F
      | SMustNot s a c \<Rightarrow>
          LMustNot (Suc i) s a (pr_verdict s a c \<pi>) (pr_report num_of s a c (handler_of blk i) \<pi>)
      | SMay s a c \<Rightarrow> LMay (Suc i) s a (may_verdict s a c \<pi>)
      | SMustElse s a d s' a' D' \<Rightarrow> else_line \<tau>\<^sub>0 \<sigma>\<^sub>0 \<pi> i s a d s' a' D'
      | SOnBreach s acts \<Rightarrow> LOnBreach (Suc i) s (map_option Suc (bound_to blk i s))
      | _ \<Rightarrow> composite_line (Suc i) (benv blk ! i) \<pi>)"

text \<open>The decisions of the fail-closed monitor of each top-level prohibition
  (\<open>monitor_decisions\<close>, TRIEL_Breach): for every action \<open>a\<close> of \<open>s\<close> in the trace, its entry
  and whether the monitor blocks it, decided in the blocked state of the entry before the
  action. They are reported after the invariants, one line per prohibition, in the order of
  the block. Prohibitions inside composite terms have no verdict of their own and no monitor
  line.\<close>

fun is_prohibition :: "('n, 'v, 's, 'a, 'p) sterm \<Rightarrow> bool" where
  "is_prohibition (SMustNot s a c) = True"
| "is_prohibition _ = False"

definition prohibitions :: "('n, 'v, 's, 'a, 'p) sterm list \<Rightarrow> nat list" where
  "prohibitions blk = filter (\<lambda>i. is_prohibition (blk ! i)) [0..<length blk]"

definition monitor_line :: "cterm list \<Rightarrow> ctrace \<Rightarrow> nat \<Rightarrow> line" where
  "monitor_line blk \<pi> i =
     (case blk ! i of
        SMustNot s a c \<Rightarrow> LMonitor (Suc i) (monitor_decisions s a c \<pi>)
      | _ \<Rightarrow> LMonitor (Suc i) [])"

definition monitor_lines :: "cterm list \<Rightarrow> ctrace \<Rightarrow> line list" where
  "monitor_lines blk \<pi> = map (monitor_line blk \<pi>) (prohibitions blk)"

lemma prohibitions_SMustNot:
  assumes "i \<in> set (prohibitions blk)"
  shows "\<exists>s a c. blk ! i = SMustNot s a c"
  using assms by (cases "blk ! i") (auto simp: prohibitions_def)

text \<open>The evaluator on data without hidden factors. Activation is checked first, in the
  blocked state of entry 0 at the time of entry 0, for the deadlines of the TERMS block and
  of the invariants, and for the order of the deadlines of each fallback; then the well-formedness of the block, with only informational actions
  in a handler bound to a prohibition; then the types of the data as given. The verdicts,
  the invariants, the membership of composite terms and the decisions of the monitors are
  computed on the blocked trace.\<close>

definition evaluate_trace :: "spec \<Rightarrow> observation list \<Rightarrow> line list" where
  "evaluate_trace sp obs =
     (case sp of Spec fs blk invs \<Rightarrow>
        (let \<pi> = btrace (max_age fs) (raw_trace obs); \<tau>\<^sub>0 = time \<pi> 0; \<sigma>\<^sub>0 = st \<pi> 0 in
         if obs = [] \<or> \<not> activates time_of \<tau>\<^sub>0 \<sigma>\<^sub>0 blk \<or> \<not> inv_activates time_of \<tau>\<^sub>0 \<sigma>\<^sub>0 (map snd invs)
            \<or> \<not> else_order_ok time_of \<tau>\<^sub>0 \<sigma>\<^sub>0 blk
         then [LActivation False]
         else LActivation True #
           (if \<not> wf_block blk \<or> \<not> cont_free_prohibitions blk \<or> \<not> else_handlers_ok blk \<or> \<not> refs_ok blk
            then [LBlock False]
            else LBlock True #
              (case ill_typed fs obs of
                 Some e \<Rightarrow> [LTypes (Some e)]
               | None \<Rightarrow> LTypes None # map (term_line \<tau>\<^sub>0 \<sigma>\<^sub>0 blk \<pi>) [0..<length blk]
                          @ map (\<lambda>(n, \<iota>). LInvariant n (sinv_eval time_of \<iota> \<pi>)) invs
                          @ monitor_lines blk \<pi>))))"

text \<open>A list of observations whose times decrease is rejected before anything else, with the
  first entry that is earlier than the entry before it.\<close>

definition evaluate :: "spec \<Rightarrow> observation list \<Rightarrow> line list" where
  "evaluate sp obs = (case time_order obs of Some j \<Rightarrow> [LTimeOrder j] | None \<Rightarrow> evaluate_trace sp obs)"

theorem evaluate_time_order:
  "time_order obs = Some j \<Longrightarrow> evaluate sp obs = [LTimeOrder j]"
  by (simp add: evaluate_def)

theorem time_order_rejected:
  assumes "j < length obs" and "0 < j" and "obs_time (obs ! j) < obs_time (obs ! (j - 1))"
  shows "\<exists>k \<le> j. evaluate sp obs = [LTimeOrder k]"
proof -
  have "time_order obs \<noteq> None"
    using assms by (auto simp: time_order_def find_upt_None)
  then obtain k where k: "time_order obs = Some k" by blast
  then have "\<forall>i < k. \<not> (0 < i \<and> obs_time (obs ! i) < obs_time (obs ! (i - 1)))"
    by (simp add: time_order_def find_upt_Some)
  then have "\<not> j < k" using assms(2,3) by blast
  then have "k \<le> j" by simp
  with k show ?thesis by (auto simp: evaluate_def)
qed

text \<open>The evaluator removes the hidden factors from the data of every entry, then evaluates.\<close>

definition run :: "spec \<Rightarrow> observation list \<Rightarrow> line list" where
  "run sp obs = (case sp of Spec fs blk invs \<Rightarrow> evaluate sp (erase_obs (hidden fs) obs))"

text \<open>Noninterference (decision 25 of CORE.md): two traces that differ only in the values of
  hidden factors get the same report, typing included. In particular the report is the
  same whether the hidden values are in the data or not.\<close>

theorem run_noninterference:
  assumes "erase_obs (hidden fs) obs = erase_obs (hidden fs) obs'"
  shows "run (Spec fs blk invs) obs = run (Spec fs blk invs) obs'"
  using assms by (simp add: run_def)

corollary run_erase: "run (Spec fs blk invs) (erase_obs (hidden fs) obs) = run (Spec fs blk invs) obs"
  by (rule run_noninterference) (simp add: erase_obs_idem)

text \<open>A hidden factor is never reported as ill-typed: after the removal it is absent from
  every entry, and an absent factor is well typed.\<close>

theorem hidden_well_typed:
  assumes "x \<in> set fs" and "fd_hidden x" and "j < length obs"
  shows "wt interp (TOptional (fd_ty x)) (denaming (fd_name x) (fst (erase_obs (hidden fs) obs ! j)))"
proof -
  have "fd_name x \<in> set (hidden fs)"
    using assms(1,2) by (auto simp: hidden_iff)
  then have "denaming (fd_name x) (fst (erase_obs (hidden fs) obs ! j)) = None"
    using assms(3) by (simp add: erase_obs_nth erase_hidden)
  then show ?thesis by (simp add: wt_none)
qed

subsection \<open>Verdicts are final in the report\<close>

text \<open>The theorems of finality (\<open>window_final\<close>, \<open>handle_breach_final\<close>, \<open>else_final\<close>,
  \<open>sinv_final\<close>) assume a trace, with non-decreasing times. The evaluator checks the order of
  the times itself, so finality holds for \<open>run\<close> on every list of observations, with no such
  assumption: a decided line of the report stays the same when observations are added at the
  end, unless the longer list is rejected for its time order or its types. In the line of a
  composite term, the answers for the whole observed trace are not verdicts and change when
  the trace grows; its status is a verdict, and once an outcome is found it stays
  (\<open>status_final\<close>). The line of a monitor lists its decisions on the observed entries; the
  list grows with the trace, but the decisions already made stay (\<open>monitor_decisions_append\<close>):
  the line of the longer trace begins with the line of the shorter one.\<close>

fun cont_decided :: "name continuation \<Rightarrow> bool" where
  "cont_decided (Cure v) = (v \<noteq> Pending)"
| "cont_decided (Escalated s v) = (v \<noteq> Pending)"
| "cont_decided _ = True"

fun status_decided :: "name status \<Rightarrow> bool" where
  "status_decided SFulfilled = True"
| "status_decided (SBreached \<tau> c) = cont_decided c"
| "status_decided SPending = False"

fun decided :: "line \<Rightarrow> bool" where
  "decided (LMust i s a d sts acts) = status_decided sts"
| "decided (LMustNot i s a v acts) = (v \<noteq> Pending)"
| "decided (LMay i s a v) = (v = Fulfilled)"
| "decided (LMustElse i s a d s' a' d' es) = (es \<noteq> EPending \<and> (\<forall>\<tau> v. es = EElse \<tau> v \<longrightarrow> v \<noteq> Pending))"
| "decided (LInvariant n b) = (b \<noteq> None)"
| "decided (LComposite n d it v p) = (\<exists>r k. p = CAt r k)"
| "decided (LMonitor i ds) = True"
| "decided _ = False"

text \<open>A decided line stays the same, except a composite line, where only the status is
  decided and the answers for the whole trace may change, and a monitor line, whose list of
  decisions is extended and never revised.\<close>

fun same_verdict :: "line \<Rightarrow> line \<Rightarrow> bool" where
  "same_verdict (LComposite n d it v p) l' = (\<exists>d' it' v'. l' = LComposite n d' it' v' p)"
| "same_verdict (LMonitor i ds) l' = (\<exists>ds'. l' = LMonitor i (ds @ ds'))"
| "same_verdict l l' = (l' = l)"

lemma same_verdict_refl: "same_verdict l l"
  by (cases l) simp_all

fun is_norm :: "('n, 'v, 's, 'a, 'p) sterm \<Rightarrow> bool" where
  "is_norm (SMust s a D F) = True"
| "is_norm (SMustNot s a c) = True"
| "is_norm (SMay s a c) = True"
| "is_norm (SMustElse s a d s' a' D') = True"
| "is_norm (SOnBreach s acts) = True"
| "is_norm _ = False"

lemma handle_breach_decided_final:
  assumes tr: "is_trace (\<pi> @ \<rho>)" and dec: "status_decided (handle_breach \<tau>\<^sub>0 lo s a d acts \<pi>)"
  shows "handle_breach \<tau>\<^sub>0 lo s a d acts (\<pi> @ \<rho>) = handle_breach \<tau>\<^sub>0 lo s a d acts \<pi>"
proof (cases "window s a lo d \<pi>")
  case Fulfilled
  then have "window s a lo d (\<pi> @ \<rho>) = Fulfilled" using window_final[OF tr] by simp
  with Fulfilled show ?thesis by (simp add: handle_breach_def)
next
  case Pending
  with dec show ?thesis by (simp add: handle_breach_def)
next
  case (Breached \<tau>\<^sub>b)
  then have tb: "\<tau>\<^sub>b = d" by (rule window_breached_at)
  show ?thesis
  proof (rule handle_breach_final[OF tr])
    show "window s a lo d \<pi> \<noteq> Pending" using Breached by simp
  next
    fix k assume "cont_of acts = Some (CureBy k)"
    with dec Breached tb show "window s a (Some d) (d + k) \<pi> \<noteq> Pending"
      by (simp add: handle_breach_def)
  next
    fix s' assume "cont_of acts = Some (EscalateTo s')"
    with dec Breached tb show "window s' a (Some d) (d + (d - \<tau>\<^sub>0)) \<pi> \<noteq> Pending"
      by (simp add: handle_breach_def)
  qed
qed

lemma may_verdict_final:
  assumes "may_verdict s a c \<pi> = Fulfilled"
  shows "may_verdict s a c (\<pi> @ \<rho>) = Fulfilled"
proof -
  from assms obtain j where j: "1 \<le> j" "j < length \<pi>" "does s a (evt (\<pi> ! j))"
    "eval c (st \<pi> (j - 1)) = Some True"
    unfolding may_verdict_def by (auto split: if_splits)
  then have "1 \<le> j \<and> j < length (\<pi> @ \<rho>) \<and> does s a (evt ((\<pi> @ \<rho>) ! j))
               \<and> eval c (st (\<pi> @ \<rho>) (j - 1)) = Some True"
    by (simp add: nth_append)
  then show ?thesis unfolding may_verdict_def by auto
qed

lemma ob_report_status_final:
  assumes tr: "is_trace (\<pi> @ \<rho>)" and dec: "status_decided (handle_breach \<tau>\<^sub>0 lo s a d acts \<pi>)"
  shows "ob_report num d (handle_breach \<tau>\<^sub>0 lo s a d acts (\<pi> @ \<rho>)) acts (\<pi> @ \<rho>)
           = ob_report num d (handle_breach \<tau>\<^sub>0 lo s a d acts \<pi>) acts \<pi>"
proof (cases "handle_breach \<tau>\<^sub>0 lo s a d acts \<pi>")
  case (SBreached \<tau> c)
  then show ?thesis by (rule ob_report_final[OF tr])
qed (use handle_breach_decided_final[OF tr dec] in \<open>simp_all add: ob_report_def\<close>)

lemma term_line_norm_final:
  assumes tr: "is_trace (\<pi> @ \<rho>)" and ne: "\<pi> \<noteq> []" and dec: "decided (term_line \<tau>\<^sub>0 \<sigma>\<^sub>0 blk \<pi> i)"
    and norm: "is_norm (blk ! i)"
  shows "term_line \<tau>\<^sub>0 \<sigma>\<^sub>0 blk (\<pi> @ \<rho>) i = term_line \<tau>\<^sub>0 \<sigma>\<^sub>0 blk \<pi> i"
proof (cases "blk ! i")
  case (SMust s a D F)
  show ?thesis
  proof (cases "start_of time_of \<tau>\<^sub>0 \<sigma>\<^sub>0 F")
    case None
    with SMust show ?thesis by (simp add: term_line_def must_line_def)
  next
    case (Some b)
    note sb = Some
    show ?thesis
    proof (cases "deadline_of time_of \<tau>\<^sub>0 \<sigma>\<^sub>0 F D")
      case None
      with SMust sb dec have "ob_verdict s a (lo_of F b) None \<pi> = Fulfilled"
        by (auto simp: term_line_def must_line_def split: verdict.splits)
      then have "ob_verdict s a (lo_of F b) None (\<pi> @ \<rho>) = Fulfilled"
        using ob_verdict_None_final[of s a "lo_of F b" \<pi> \<rho>] by simp
      with SMust sb None \<open>ob_verdict s a (lo_of F b) None \<pi> = Fulfilled\<close> show ?thesis
        by (simp add: term_line_def must_line_def)
    next
      case (Some d)
      note sd' = Some
      let ?h = "handler_of blk i"
      from SMust sb sd' dec
      have sd: "status_decided (handle_breach b (lo_of F b) s a d ?h \<pi>)"
        by (simp add: term_line_def must_line_def Let_def)
      note h = handle_breach_decided_final[OF tr sd]
      note r = ob_report_status_final[OF tr sd, of num_of]
      from SMust sb sd' h r show ?thesis
        by (simp add: term_line_def must_line_def Let_def)
    qed
  qed
next
  case (SMustNot s a c)
  with dec have v: "pr_verdict s a c \<pi> \<noteq> Pending" by (simp add: term_line_def)
  with SMustNot show ?thesis
    by (simp add: term_line_def pr_verdict_final[OF v] pr_report_final[OF v])
next
  case (SMay s a c)
  with dec have "may_verdict s a c \<pi> = Fulfilled" by (simp add: term_line_def)
  with SMay may_verdict_final[OF this] show ?thesis by (simp add: term_line_def)
next
  case (SMustElse s a d s' a' D')
  show ?thesis
  proof (cases "resolve time_of \<tau>\<^sub>0 \<sigma>\<^sub>0 d")
    case None
    with SMustElse show ?thesis by (simp add: term_line_def else_line_def)
  next
    case (Some e)
    let ?e' = "else_deadline time_of \<sigma>\<^sub>0 e D'"
    from SMustElse Some dec
    have d1: "else_verdict s a e s' a' ?e' \<pi> \<noteq> EPending"
      and d2: "\<And>v. else_verdict s a e s' a' ?e' \<pi> = EElse e v \<Longrightarrow> v \<noteq> Pending"
      by (auto simp: term_line_def else_line_def Let_def)
    from else_final[OF tr d1 d2] SMustElse Some show ?thesis
      by (simp add: term_line_def else_line_def Let_def)
  qed
qed (use dec norm in \<open>simp_all add: term_line_def\<close>)

lemma term_line_composite_final:
  assumes norm: "\<not> is_norm (blk ! i)" and dec: "decided (term_line \<tau>\<^sub>0 \<sigma>\<^sub>0 blk \<pi> i)"
  shows "same_verdict (term_line \<tau>\<^sub>0 \<sigma>\<^sub>0 blk \<pi> i) (term_line \<tau>\<^sub>0 \<sigma>\<^sub>0 blk (\<pi> @ \<rho>) i)"
proof -
  have tl: "term_line \<tau>\<^sub>0 \<sigma>\<^sub>0 blk p i = composite_line (Suc i) (benv blk ! i) p" for p
    using norm by (cases "blk ! i") (simp_all add: term_line_def)
  show ?thesis
  proof (cases "benv blk ! i")
    case None
    with dec show ?thesis by (simp add: tl composite_line_def)
  next
    case (Some u)
    from dec Some obtain r k where k: "status u \<pi> = CAt r k" by (auto simp: tl composite_line_def)
    then have "status u (\<pi> @ \<rho>) = CAt r k" by (rule status_final)
    with Some k show ?thesis by (simp add: tl composite_line_def)
  qed
qed

lemma term_line_final:
  assumes tr: "is_trace (\<pi> @ \<rho>)" and ne: "\<pi> \<noteq> []" and dec: "decided (term_line \<tau>\<^sub>0 \<sigma>\<^sub>0 blk \<pi> i)"
  shows "same_verdict (term_line \<tau>\<^sub>0 \<sigma>\<^sub>0 blk \<pi> i) (term_line \<tau>\<^sub>0 \<sigma>\<^sub>0 blk (\<pi> @ \<rho>) i)"
proof (cases "is_norm (blk ! i)")
  case True
  from term_line_norm_final[OF tr ne dec True] show ?thesis by (simp add: same_verdict_refl)
next
  case False
  from term_line_composite_final[OF False dec] show ?thesis .
qed

lemma monitor_line_final:
  assumes "i \<in> set (prohibitions blk)"
  shows "same_verdict (monitor_line blk \<pi> i) (monitor_line blk (\<pi> @ \<rho>) i)"
proof -
  from prohibitions_SMustNot[OF assms] obtain s a c where "blk ! i = SMustNot s a c" by blast
  then show ?thesis
    using monitor_decisions_append[of s a c \<pi> \<rho>] by (auto simp: monitor_line_def)
qed

lemma btrace_prefix:
  "take (length \<pi>) (btrace M (\<pi> @ \<rho>)) = btrace M \<pi>"
proof (rule nth_equalityI)
  show "length (take (length \<pi>) (btrace M (\<pi> @ \<rho>))) = length (btrace M \<pi>)" by simp
next
  fix j assume "j < length (take (length \<pi>) (btrace M (\<pi> @ \<rho>)))"
  then have j: "j < length \<pi>" by simp
  have e: "evt ((\<pi> @ \<rho>) ! i) = evt (\<pi> ! i) \<and> time (\<pi> @ \<rho>) i = time \<pi> i" if "i \<le> j" for i
    using that j by (simp add: nth_append)
  have fr: "fresh m x (\<pi> @ \<rho>) j \<longleftrightarrow> fresh m x \<pi> j" for m x
    unfolding fresh_def
  proof
    assume "\<exists>i \<le> j. evt ((\<pi> @ \<rho>) ! i) = Arrival x \<and> time (\<pi> @ \<rho>) j - time (\<pi> @ \<rho>) i \<le> m"
    then obtain i where "i \<le> j" "evt ((\<pi> @ \<rho>) ! i) = Arrival x" "time (\<pi> @ \<rho>) j - time (\<pi> @ \<rho>) i \<le> m"
      by blast
    with e[of i] e[OF order_refl] show "\<exists>i \<le> j. evt (\<pi> ! i) = Arrival x \<and> time \<pi> j - time \<pi> i \<le> m"
      by auto
  next
    assume "\<exists>i \<le> j. evt (\<pi> ! i) = Arrival x \<and> time \<pi> j - time \<pi> i \<le> m"
    then obtain i where "i \<le> j" "evt (\<pi> ! i) = Arrival x" "time \<pi> j - time \<pi> i \<le> m"
      by blast
    with e[of i] e[OF order_refl]
    show "\<exists>i \<le> j. evt ((\<pi> @ \<rho>) ! i) = Arrival x \<and> time (\<pi> @ \<rho>) j - time (\<pi> @ \<rho>) i \<le> m"
      by auto
  qed
  have "blockp M (\<pi> @ \<rho>) j = blockp M \<pi> j"
    using j by (auto simp: blockp_def fr split: list.splits option.splits)
  with j show "take (length \<pi>) (btrace M (\<pi> @ \<rho>)) ! j = btrace M \<pi> ! j"
    by (simp add: btrace_def nth_append)
qed

lemma btrace_append: "\<exists>\<rho>'. btrace M (\<pi> @ \<rho>) = btrace M \<pi> @ \<rho>'"
  using btrace_prefix[of \<pi> M \<rho>] by (metis append_take_drop_id)

theorem run_final:
  assumes i: "i < length (run sp obs)" and dec: "decided (run sp obs ! i)"
  shows "same_verdict (run sp obs ! i) (run sp (obs @ more) ! i)
         \<or> (\<exists>j. run sp (obs @ more) = [LTimeOrder j])
         \<or> (\<exists>e. LTypes (Some e) \<in> set (run sp (obs @ more)))"
proof -
  obtain fs blk invs where sp: "sp = Spec fs blk invs" by (cases sp)
  let ?H = "hidden fs"
  let ?O = "erase_obs ?H obs" and ?O' = "erase_obs ?H (obs @ more)"
  have O': "?O' = ?O @ erase_obs ?H more" by (simp add: erase_obs_def)
  have run: "run sp obs = evaluate sp ?O" "run sp (obs @ more) = evaluate sp ?O'"
    by (simp_all add: run_def sp)
  show ?thesis
  proof (cases "time_order ?O'")
    case (Some j)
    then show ?thesis by (simp add: run evaluate_def)
  next
    case None
    note None' = None
    have to: "time_order ?O = None"
    proof (rule ccontr)
      assume "time_order ?O \<noteq> None"
      then obtain j where "time_order ?O = Some j" by blast
      then have "run sp obs = [LTimeOrder j]" by (simp add: run evaluate_def)
      with i dec show False by simp
    qed
    define M where "M = max_age fs"
    define \<pi> where "\<pi> = btrace M (raw_trace ?O)"
    define \<pi>' where "\<pi>' = btrace M (raw_trace ?O')"
    have ne: "obs \<noteq> []"
    proof
      assume "obs = []"
      then have "run sp obs = [LActivation False]"
        by (simp add: run_def evaluate_def time_order_def evaluate_trace_def sp erase_obs_def)
      with i dec show False by simp
    qed
    then have neO: "?O \<noteq> []" and neO': "?O' \<noteq> []" by (simp_all add: erase_obs_def)
    obtain \<rho> where pr: "\<pi>' = \<pi> @ \<rho>"
      using btrace_append[of M "raw_trace ?O" "raw_trace (erase_obs ?H more)"]
      unfolding \<pi>_def \<pi>'_def O' by (auto simp: raw_trace_def)
    have tr': "is_trace \<pi>'"
      unfolding \<pi>'_def by (rule btrace_is_trace) (use None neO' time_order_is_trace in blast)
    have lp: "0 < length \<pi>" using ne by (simp add: \<pi>_def raw_trace_def erase_obs_def)
    then have nep: "\<pi> \<noteq> []" by auto
    have t0: "time \<pi>' 0 = time \<pi> 0" and s0: "st \<pi>' 0 = st \<pi> 0"
      using lp pr by simp_all
    have ev: "evaluate sp ?O = evaluate_trace sp ?O" "evaluate sp ?O' = evaluate_trace sp ?O'"
      using to None by (simp_all add: evaluate_def)
    let ?act = "activates time_of (time \<pi> 0) (st \<pi> 0) blk
                \<and> inv_activates time_of (time \<pi> 0) (st \<pi> 0) (map snd invs)
                \<and> else_order_ok time_of (time \<pi> 0) (st \<pi> 0) blk"
    let ?blk = "wf_block blk \<and> cont_free_prohibitions blk \<and> else_handlers_ok blk \<and> refs_ok blk"
    let ?lines = "\<lambda>p. map (term_line (time \<pi> 0) (st \<pi> 0) blk p) [0..<length blk]
                     @ map (\<lambda>(n, \<iota>). LInvariant n (sinv_eval time_of \<iota> p)) invs
                     @ monitor_lines blk p"
    have E: "evaluate_trace sp ?O =
               (if \<not> ?act then [LActivation False]
                else LActivation True # (if \<not> ?blk then [LBlock False] else LBlock True #
                  (case ill_typed fs ?O of Some e \<Rightarrow> [LTypes (Some e)]
                   | None \<Rightarrow> LTypes None # ?lines \<pi>)))"
      using neO by (simp add: evaluate_trace_def sp Let_def flip: \<pi>_def M_def)
    have E': "evaluate_trace sp ?O' =
               (if \<not> ?act then [LActivation False]
                else LActivation True # (if \<not> ?blk then [LBlock False] else LBlock True #
                  (case ill_typed fs ?O' of Some e \<Rightarrow> [LTypes (Some e)]
                   | None \<Rightarrow> LTypes None # ?lines \<pi>')))"
      using neO' by (simp add: evaluate_trace_def sp Let_def t0 s0 flip: \<pi>'_def M_def
                         split: option.split)
    have act: "?act" and blk: "?blk" and ty: "ill_typed fs ?O = None"
      using i dec unfolding run ev E by (auto split: if_splits option.splits simp: nth_Cons')
    then have R: "run sp obs = LActivation True # LBlock True # LTypes None # ?lines \<pi>"
      unfolding run ev E by simp
    show ?thesis
    proof (cases "ill_typed fs ?O'")
      case (Some e)
      with act blk have "LTypes (Some e) \<in> set (run sp (obs @ more))"
        unfolding run ev E' by simp
      then show ?thesis by blast
    next
      case None
      with act blk have R': "run sp (obs @ more) = LActivation True # LBlock True # LTypes None # ?lines \<pi>'"
        unfolding run ev E' by simp
      have "3 \<le> i" using i dec unfolding R by (cases i; cases "i - 1"; cases "i - 2") auto
      define k where "k = i - 3"
      with \<open>3 \<le> i\<close> have k: "i = Suc (Suc (Suc k))" by arith
      have kl: "k < length (?lines \<pi>)" using i unfolding R k by simp
      have dk: "decided (?lines \<pi> ! k)" using dec unfolding R k by simp
      have "same_verdict (?lines \<pi> ! k) (?lines \<pi>' ! k)"
      proof (cases "k < length blk")
        case True
        have "decided (term_line (time \<pi> 0) (st \<pi> 0) blk \<pi> k)" using dk True by (simp add: nth_append)
        from term_line_final[OF tr'[unfolded pr] nep this] True show ?thesis
          by (simp add: nth_append pr)
      next
        case False
        define n where "n = k - length blk"
        let ?rest = "\<lambda>p. map (\<lambda>(n, \<iota>). LInvariant n (sinv_eval time_of \<iota> p)) invs @ monitor_lines blk p"
        have kn: "?lines p ! k = ?rest p ! n" for p
          using False by (simp add: nth_append n_def)
        have nl: "n < length invs + length (prohibitions blk)"
          using kl False by (simp add: n_def monitor_lines_def)
        show ?thesis
        proof (cases "n < length invs")
          case True
          obtain nm \<iota> where inv: "invs ! n = (nm, \<iota>)" by (cases "invs ! n")
          have l: "?lines p ! k = LInvariant nm (sinv_eval time_of \<iota> p)" for p
            unfolding kn using True inv by (simp add: nth_append)
          from dk obtain b where b: "sinv_eval time_of \<iota> \<pi> = Some b" by (auto simp: l)
          from sinv_final[OF tr'[unfolded pr] nep b] show ?thesis by (simp add: l pr b same_verdict_refl)
        next
          case False
          define m where "m = n - length invs"
          have ml: "m < length (prohibitions blk)" using nl False unfolding m_def by arith
          have l: "?lines p ! k = monitor_line blk p (prohibitions blk ! m)" for p
            unfolding kn using False ml by (simp add: nth_append monitor_lines_def m_def)
          have "prohibitions blk ! m \<in> set (prohibitions blk)" using ml by (rule nth_mem)
          from monitor_line_final[OF this] show ?thesis by (simp add: l pr)
        qed
      qed
      then show ?thesis unfolding R R' k by simp
    qed
  qed
qed

text \<open>A composite line reports \<open>mem3\<close> on the blocked trace. By \<open>mem3_sound\<close> its definite
  answers are membership in the denotation of the term, for terms without AND, and by
  \<open>mem3_definite\<close> they are always definite for terms without UNLESS and AND.\<close>


subsection \<open>The monitor outside the evaluator\<close>

text \<open>The decision of the fail-closed monitor on one action, at the types of the evaluator:
  \<open>check_action c \<sigma>\<close> is true if the monitor of a prohibition with the condition \<open>c\<close> blocks an
  action taken in a state \<open>\<sigma>\<close> after it, that is, unless \<open>c\<close> is false in \<open>\<sigma>\<close>. It is \<open>blocks\<close>
  under the name it is exported with, executed by its code equation (\<open>check_action_code\<close>).
  With \<open>enforce\<close> it lets the monitor be applied to a trace outside \<open>run\<close>.\<close>

definition check_action :: "(path, atom) expr \<Rightarrow> (path, atom) state \<Rightarrow> bool" where
  "check_action c \<sigma> \<longleftrightarrow> blocks c \<sigma>"

lemma check_action_code [code]:
  "check_action c \<sigma> = (case eval c \<sigma> of Some False \<Rightarrow> False | _ \<Rightarrow> True)"
  by (auto simp: check_action_def blocks_def split: option.split bool.split)


subsection \<open>Verdicts survive more data in the report\<close>

text \<open>Finality (\<open>run_final\<close>) is about appending observations. The second kind of stability is
  about reading the same observations with more data: \<open>obs_le obs obs'\<close> says that \<open>obs'\<close> has
  the observations of \<open>obs\<close>, with the same times and events, and at each one data with more
  values (the information order on the flattened data). Hidden factors are removed from both
  lists alike, and the blocking of stale factors reads only times and events, so the blocked
  trace of \<open>obs'\<close> carries more data than the blocked trace of \<open>obs\<close> at every entry
  (\<open>btrace_data_le\<close>). Activation on more data succeeds with the same deadlines. The verdicts
  then behave as on traces: an obligation does not change; a breached prohibition stays
  breached, at the same or an earlier time; a fulfilled permission stays fulfilled; a definite
  invariant stays the same. For the conditions of prohibitions and permissions and the
  formulas of invariants this needs PRESENT-freedom (\<open>present_free_spec\<close>); the lines of
  composite terms are not covered, since \<open>IF\<close> takes its ELSE branch on an undefined
  condition. The actions reported with a breach (penalties) are not compared: a penalty is
  computed in the state of the breach, which can move.\<close>

definition obs_le :: "observation list \<Rightarrow> observation list \<Rightarrow> bool" where
  "obs_le obs obs' \<longleftrightarrow>
     length obs' = length obs \<and>
     (\<forall>j < length obs. fst (snd (obs' ! j)) = fst (snd (obs ! j)) \<and> snd (snd (obs' ! j)) = snd (snd (obs ! j))
        \<and> flat (fst (obs ! j)) \<sqsubseteq> flat (fst (obs' ! j)))"

text \<open>More data in the sense of nominative data (\<open>nd_le\<close>, section 7) gives more data in the
  flattened state (\<open>flat_mono\<close>).\<close>

lemma obs_leI_nd:
  assumes "length obs' = length obs"
    and "\<And>j. j < length obs \<Longrightarrow> fst (snd (obs' ! j)) = fst (snd (obs ! j)) \<and> snd (snd (obs' ! j)) = snd (snd (obs ! j))
          \<and> nd_le (fst (obs ! j)) (fst (obs' ! j))"
  shows "obs_le obs obs'"
  unfolding obs_le_def using assms flat_mono by blast

lemma obs_time_obs_le: "obs_le obs obs' \<Longrightarrow> j < length obs \<Longrightarrow> obs_time (obs' ! j) = obs_time (obs ! j)"
  unfolding obs_le_def obs_time_def by blast

lemma length_raw_trace: "length (raw_trace obs) = length obs"
  by (simp add: raw_trace_def)

lemma raw_trace_nth:
  "j < length obs \<Longrightarrow> raw_trace obs ! j = (flat (fst (obs ! j)), fst (snd (obs ! j)), snd (snd (obs ! j)))"
  by (simp add: raw_trace_def split: prod.splits)

lemma raw_trace_data_le:
  assumes o: "obs_le obs obs'"
  shows "data_le (raw_trace obs) (raw_trace obs')"
proof -
  have l: "length obs' = length obs" using o by (simp add: obs_le_def)
  have "tstamp (raw_trace obs' ! j) = tstamp (raw_trace obs ! j) \<and> evt (raw_trace obs' ! j) = evt (raw_trace obs ! j)
        \<and> st (raw_trace obs) j \<sqsubseteq> st (raw_trace obs') j" if j: "j < length obs" for j
  proof -
    have "fst (snd (obs' ! j)) = fst (snd (obs ! j)) \<and> snd (snd (obs' ! j)) = snd (snd (obs ! j))
          \<and> flat (fst (obs ! j)) \<sqsubseteq> flat (fst (obs' ! j))"
      using o j unfolding obs_le_def by blast
    then show ?thesis
      using raw_trace_nth[OF j] raw_trace_nth[where j = j and obs = obs'] j l by (simp add: st_def)
  qed
  with l show ?thesis unfolding data_le_def length_raw_trace by blast
qed

lemma erase_flat_mono:
  assumes "flat d \<sqsubseteq> flat d'"
  shows "flat (erase H d) \<sqsubseteq> flat (erase H d')"
  unfolding info_le_def
proof
  fix p assume "p \<in> dom (flat (erase H d))"
  then have h: "\<not> hides H p" and "p \<in> dom (flat d)" by (auto simp: erase_flat domIff split: if_splits)
  with assms have "flat d' p = flat d p" by (simp add: info_le_def)
  with h show "flat (erase H d') p = flat (erase H d) p" by (simp add: erase_flat)
qed

lemma erase_obs_le:
  assumes o: "obs_le obs obs'"
  shows "obs_le (erase_obs H obs) (erase_obs H obs')"
proof -
  have l: "length obs' = length obs" using o by (simp add: obs_le_def)
  have "fst (snd (erase_obs H obs' ! j)) = fst (snd (erase_obs H obs ! j))
        \<and> snd (snd (erase_obs H obs' ! j)) = snd (snd (erase_obs H obs ! j))
        \<and> flat (fst (erase_obs H obs ! j)) \<sqsubseteq> flat (fst (erase_obs H obs' ! j))" if j: "j < length obs" for j
  proof -
    have "fst (snd (obs' ! j)) = fst (snd (obs ! j)) \<and> snd (snd (obs' ! j)) = snd (snd (obs ! j))
          \<and> flat (fst (obs ! j)) \<sqsubseteq> flat (fst (obs' ! j))"
      using o j unfolding obs_le_def by blast
    then show ?thesis
      using erase_obs_nth[where j = j and obs = obs and H = H] erase_obs_nth[where j = j and obs = obs' and H = H] j l
      by (simp add: erase_flat_mono)
  qed
  with l show ?thesis unfolding obs_le_def length_erase_obs by blast
qed

lemma time_order_obs_le:
  assumes o: "obs_le obs obs'"
  shows "time_order obs' = time_order obs"
proof -
  have l: "length obs' = length obs" using o by (simp add: obs_le_def)
  show ?thesis
    unfolding time_order_def l
  proof (rule find_cong)
    show "[0..<length obs] = [0..<length obs]" by (rule refl)
  next
    fix j assume "j \<in> set [0..<length obs]"
    then have j: "j < length obs" by simp
    then have j1: "j - 1 < length obs" by simp
    show "(0 < j \<and> obs_time (obs' ! j) < obs_time (obs' ! (j - 1)))
          = (0 < j \<and> obs_time (obs ! j) < obs_time (obs ! (j - 1)))"
      by (simp add: obs_time_obs_le[OF o j] obs_time_obs_le[OF o j1])
  qed
qed

text \<open>Freshness reads only times and events, so blocking the stale factors of two traces with
  the same entries blocks the same names; the blocked states keep the information order.\<close>

lemma fresh_data_le:
  assumes le: "data_le \<pi> \<pi>'" and j: "j < length \<pi>"
  shows "fresh m x \<pi>' j \<longleftrightarrow> fresh m x \<pi> j"
proof -
  have "evt (\<pi>' ! i) = Arrival x \<and> time \<pi>' j - time \<pi>' i \<le> m \<longleftrightarrow> evt (\<pi> ! i) = Arrival x \<and> time \<pi> j - time \<pi> i \<le> m"
    if "i \<le> j" for i
  proof -
    have i: "i < length \<pi>" using that j by simp
    show ?thesis by (simp add: data_le_evt[OF le i] data_le_time[OF le i] data_le_time[OF le j])
  qed
  then show ?thesis unfolding fresh_def by blast
qed

lemma blockp_data_le:
  assumes le: "data_le \<pi> \<pi>'" and j: "j < length \<pi>"
  shows "blockp M \<pi> j \<sqsubseteq> blockp M \<pi>' j"
proof -
  define ok where "ok = (\<lambda>p. case p of [] \<Rightarrow> True | f # q \<Rightarrow> (case M f of None \<Rightarrow> True | Some m \<Rightarrow> fresh m [f] \<pi> j))"
  have e: "blockp M \<pi> j p = (if ok p then st \<pi> j p else None)" for p
    by (simp add: blockp_def ok_def split: list.splits option.splits)
  have e': "blockp M \<pi>' j p = (if ok p then st \<pi>' j p else None)" for p
    by (simp add: blockp_def ok_def fresh_data_le[OF le j] split: list.splits option.splits)
  show ?thesis
    unfolding info_le_def
  proof
    fix p assume "p \<in> dom (blockp M \<pi> j)"
    then obtain v where ok: "ok p" and v: "st \<pi> j p = Some v" by (auto simp: domIff e split: if_splits)
    have "st \<pi>' j p = Some v" by (rule info_leD[OF data_le_st[OF le j] v])
    with ok v show "blockp M \<pi>' j p = blockp M \<pi> j p" by (simp add: e e')
  qed
qed

lemma btrace_data_le:
  assumes le: "data_le \<pi> \<pi>'"
  shows "data_le (btrace M \<pi>) (btrace M \<pi>')"
proof -
  have l: "length \<pi>' = length \<pi>" by (rule data_le_length[OF le])
  have "tstamp (btrace M \<pi>' ! j) = tstamp (btrace M \<pi> ! j) \<and> evt (btrace M \<pi>' ! j) = evt (btrace M \<pi> ! j)
        \<and> st (btrace M \<pi>) j \<sqsubseteq> st (btrace M \<pi>') j" if j: "j < length \<pi>" for j
  proof -
    have j': "j < length \<pi>'" using j l by simp
    show ?thesis
      using btrace_st[OF j] btrace_st[OF j'] blockp_data_le[OF le j] btrace_evt[OF j] btrace_evt[OF j']
        data_le_evt[OF le j] btrace_time[OF j] btrace_time[OF j'] data_le_time[OF le j]
      by (simp add: time_def)
  qed
  with l show ?thesis unfolding data_le_def btrace_length by blast
qed

text \<open>Activation on more data: every deadline that resolves still resolves to the same time
  (\<open>resolve_mono\<close>), so the block, its fallbacks and the invariants stay activated.\<close>

lemma start_of_mono:
  assumes le: "\<sigma> \<sqsubseteq> \<sigma>'" and s: "start_of T \<tau>\<^sub>0 \<sigma> F = Some b"
  shows "start_of T \<tau>\<^sub>0 \<sigma>' F = Some b"
proof (cases F)
  case None
  with s show ?thesis by (simp add: start_of_def)
next
  case (Some f)
  with s have "resolve T \<tau>\<^sub>0 \<sigma> f = Some b" by (simp add: start_of_def)
  from resolve_mono[OF le this] Some show ?thesis by (simp add: start_of_def)
qed

lemma deadline_of_mono:
  assumes le: "\<sigma> \<sqsubseteq> \<sigma>'" and s: "start_of T \<tau>\<^sub>0 \<sigma> F = Some b" and d: "deadline_of T \<tau>\<^sub>0 \<sigma> F D = Some d"
  shows "deadline_of T \<tau>\<^sub>0 \<sigma>' F D = Some d"
proof (cases D)
  case None
  with d show ?thesis by (simp add: deadline_of_def split: option.splits)
next
  case (Some d\<^sub>0)
  with d s have "resolve T b \<sigma> d\<^sub>0 = Some d" by (simp add: deadline_of_def)
  from resolve_mono[OF le this] start_of_mono[OF le s] Some show ?thesis by (simp add: deadline_of_def)
qed

lemma activates_mono:
  assumes le: "\<sigma> \<sqsubseteq> \<sigma>'" and act: "activates T \<tau>\<^sub>0 \<sigma> blk"
  shows "activates T \<tau>\<^sub>0 \<sigma>' blk"
proof -
  have "resolve T \<tau>\<^sub>0 \<sigma>' d \<noteq> None" if "t \<in> set blk" "d \<in> set (deadlines t)" for t d
  proof -
    have "resolve T \<tau>\<^sub>0 \<sigma> d \<noteq> None" using act that unfolding activates_def by blast
    then obtain D where "resolve T \<tau>\<^sub>0 \<sigma> d = Some D" by blast
    from resolve_mono[OF le this] show ?thesis by simp
  qed
  then show ?thesis unfolding activates_def by blast
qed

lemma inv_activates_mono:
  assumes le: "\<sigma> \<sqsubseteq> \<sigma>'" and act: "inv_activates T \<tau>\<^sub>0 \<sigma> invs"
  shows "inv_activates T \<tau>\<^sub>0 \<sigma>' invs"
proof -
  have "resolve T \<tau>\<^sub>0 \<sigma>' d \<noteq> None" if "\<iota> \<in> set invs" "d \<in> set (sinv_deadlines \<iota>)" for \<iota> d
  proof -
    have "resolve T \<tau>\<^sub>0 \<sigma> d \<noteq> None" using act that unfolding inv_activates_def by blast
    then obtain D where "resolve T \<tau>\<^sub>0 \<sigma> d = Some D" by blast
    from resolve_mono[OF le this] show ?thesis by simp
  qed
  then show ?thesis unfolding inv_activates_def by blast
qed

lemma else_order_okI:
  assumes "\<And>s a d s' a' D' e e'. SMustElse s a d s' a' D' \<in> set blk \<Longrightarrow> resolve T \<tau>\<^sub>0 \<sigma> d = Some e \<Longrightarrow>
             else_deadline T \<sigma> e D' = Some e' \<Longrightarrow> e < e'"
  shows "else_order_ok T \<tau>\<^sub>0 \<sigma> blk"
  unfolding else_order_ok_def using assms by (auto split: sterm.splits option.splits)

lemma else_order_ok_mono:
  assumes le: "\<sigma> \<sqsubseteq> \<sigma>'" and act: "activates T \<tau>\<^sub>0 \<sigma> blk" and ok: "else_order_ok T \<tau>\<^sub>0 \<sigma> blk"
  shows "else_order_ok T \<tau>\<^sub>0 \<sigma>' blk"
proof (rule else_order_okI)
  fix s a d s' a' D' e e'
  assume m: "SMustElse s a d s' a' D' \<in> set blk" and r': "resolve T \<tau>\<^sub>0 \<sigma>' d = Some e"
    and d': "else_deadline T \<sigma>' e D' = Some e'"
  from activates_resolves_else[OF act m] obtain e\<^sub>0 where r: "resolve T \<tau>\<^sub>0 \<sigma> d = Some e\<^sub>0"
    and dd: "D' \<noteq> None \<longrightarrow> else_deadline T \<sigma> e\<^sub>0 D' \<noteq> None" by blast
  from resolve_mono[OF le r] r' have e: "e\<^sub>0 = e" by simp
  from d' obtain d\<^sub>0 where D': "D' = Some d\<^sub>0" by (cases D') (auto simp: else_deadline_def)
  with dd e obtain e\<^sub>1 where r1: "resolve T e \<sigma> d\<^sub>0 = Some e\<^sub>1"
    by (cases "resolve T e \<sigma> d\<^sub>0") (auto simp: else_deadline_def)
  from resolve_mono[OF le r1] d' D' have "e\<^sub>1 = e'" by (simp add: else_deadline_def)
  with r1 D' have "else_deadline T \<sigma> e D' = Some e'" by (simp add: else_deadline_def)
  from else_order_window[OF ok m r[unfolded e] this] show "e < e'" .
qed

text \<open>The conditions a specification reads for its verdicts: those of its top-level
  prohibitions and permissions, and the formulas of its invariants.\<close>

fun norm_present_free :: "('n, 'v, 's, 'a, 'p) sterm \<Rightarrow> bool" where
  "norm_present_free (SMustNot s a c) = present_free c"
| "norm_present_free (SMay s a c) = present_free c"
| "norm_present_free _ = True"

fun present_free_spec :: "spec \<Rightarrow> bool" where
  "present_free_spec (Spec fs blk invs) =
     ((\<forall>t \<in> set blk. norm_present_free t) \<and> (\<forall>x \<in> set invs. present_free (sinv_formula (snd x))))"

text \<open>How a line may change when the data is refined. The verdict of a prohibition is
  \<open>pr_refines v v'\<close>: Pending may become anything, and Breached \<open>\<tau>\<close> becomes Breached \<open>\<tau>'\<close> with
  \<open>\<tau>' \<le> \<tau>\<close>. The status of an obligation and of a fallback does not change; a fulfilled
  permission and a definite invariant do not change; the reported actions and the lines of
  composite terms are not compared.\<close>

fun pr_refines :: "verdict \<Rightarrow> verdict \<Rightarrow> bool" where
  "pr_refines Pending v' = True"
| "pr_refines (Breached \<tau>) v' = (\<exists>\<tau>' \<le> \<tau>. v' = Breached \<tau>')"
| "pr_refines Fulfilled v' = (v' = Fulfilled)"

fun line_refines :: "line \<Rightarrow> line \<Rightarrow> bool" where
  "line_refines (LMust i s a d sts acts) l' = (\<exists>acts'. l' = LMust i s a d sts acts')"
| "line_refines (LMustNot i s a v acts) l' = (\<exists>v' acts'. l' = LMustNot i s a v' acts' \<and> pr_refines v v')"
| "line_refines (LMay i s a v) l' = (\<exists>v'. l' = LMay i s a v' \<and> (v = Pending \<or> v' = v))"
| "line_refines (LInvariant n b) l' = (\<exists>b'. l' = LInvariant n b' \<and> (b = None \<or> b' = b))"
| "line_refines (LComposite n d it v p) l' = (\<exists>d' it' v' p'. l' = LComposite n d' it' v' p')"
| "line_refines l l' = (l' = l)"

lemma pr_refines_refl: "pr_refines v v"
  by (cases v) auto

lemma line_refines_refl: "line_refines l l"
  by (cases l) (auto simp: pr_refines_refl)

lemma pr_refines_not_pending: "pr_refines v v' \<Longrightarrow> v \<noteq> Pending \<Longrightarrow> v' \<noteq> Pending"
  by (cases v) auto

text \<open>A decided line, other than the line of a composite term, stays decided.\<close>

lemma line_refines_decided:
  assumes "line_refines l l'" and "decided l" and "\<And>n d it v p. l \<noteq> LComposite n d it v p"
  shows "decided l'"
  using assms by (cases l) (auto dest: pr_refines_not_pending)

text \<open>The line of a top-level element on the same trace with more data, after an activation
  on the same time and a state with more data.\<close>

lemma term_line_data_mono:
  assumes act: "activates time_of \<tau>\<^sub>0 \<sigma>\<^sub>0 blk" and s0: "\<sigma>\<^sub>0 \<sqsubseteq> \<sigma>\<^sub>0'"
    and tr: "is_trace \<pi>" and le: "data_le \<pi> \<pi>'" and i: "i < length blk"
    and pf: "norm_present_free (blk ! i)"
  shows "line_refines (term_line \<tau>\<^sub>0 \<sigma>\<^sub>0 blk \<pi> i) (term_line \<tau>\<^sub>0 \<sigma>\<^sub>0' blk \<pi>' i)"
proof (cases "blk ! i")
  case (SMust s a D F)
  then have m: "SMust s a D F \<in> set blk" using i nth_mem by metis
  from activates_resolves[OF act m] obtain b where b: "start_of time_of \<tau>\<^sub>0 \<sigma>\<^sub>0 F = Some b"
    and dd: "D \<noteq> None \<longrightarrow> deadline_of time_of \<tau>\<^sub>0 \<sigma>\<^sub>0 F D \<noteq> None" by blast
  have b': "start_of time_of \<tau>\<^sub>0 \<sigma>\<^sub>0' F = Some b" by (rule start_of_mono[OF s0 b])
  show ?thesis
  proof (cases D)
    case None
    have "deadline_of time_of \<tau>\<^sub>0 \<sigma>\<^sub>0 F None = None" "deadline_of time_of \<tau>\<^sub>0 \<sigma>\<^sub>0' F None = None"
      by (simp_all add: deadline_of_def b b')
    with SMust None b b' show ?thesis
      by (simp add: term_line_def must_line_def ob_verdict_data_indep[OF le])
  next
    case (Some d\<^sub>0)
    with dd obtain d where d: "deadline_of time_of \<tau>\<^sub>0 \<sigma>\<^sub>0 F D = Some d"
      by (cases "deadline_of time_of \<tau>\<^sub>0 \<sigma>\<^sub>0 F D") auto
    have d': "deadline_of time_of \<tau>\<^sub>0 \<sigma>\<^sub>0' F D = Some d" by (rule deadline_of_mono[OF s0 b d])
    with SMust b b' d show ?thesis
      by (simp add: term_line_def must_line_def Let_def handle_breach_data_indep[OF le])
  qed
next
  case (SMustNot s a c)
  with pf have c: "present_free c" by simp
  have "pr_refines (pr_verdict s a c \<pi>) (pr_verdict s a c \<pi>')"
  proof (cases "pr_verdict s a c \<pi>")
    case Pending
    then show ?thesis by simp
  next
    case (Breached \<tau>)
    from pr_verdict_data_mono[OF c tr le Breached] Breached show ?thesis by simp
  next
    case Fulfilled
    with pr_verdict_not_fulfilled[of s a c \<pi>] show ?thesis by simp
  qed
  with SMustNot show ?thesis by (simp add: term_line_def)
next
  case (SMay s a c)
  with pf have c: "present_free c" by simp
  have "may_verdict s a c \<pi> = Pending \<or> may_verdict s a c \<pi>' = may_verdict s a c \<pi>"
  proof (cases "may_verdict s a c \<pi>")
    case Fulfilled
    with may_verdict_data_mono(1)[OF c le] show ?thesis by simp
  next
    case Pending
    then show ?thesis by simp
  next
    case (Breached \<tau>)
    with may_never_breached[of s a c \<pi> \<tau>] show ?thesis by simp
  qed
  with SMay show ?thesis by (simp add: term_line_def)
next
  case (SMustElse s a d s' a' D')
  then have m: "SMustElse s a d s' a' D' \<in> set blk" using i nth_mem by metis
  from activates_resolves_else[OF act m] obtain e where e: "resolve time_of \<tau>\<^sub>0 \<sigma>\<^sub>0 d = Some e"
    and dd: "D' \<noteq> None \<longrightarrow> else_deadline time_of \<sigma>\<^sub>0 e D' \<noteq> None" by blast
  have e': "resolve time_of \<tau>\<^sub>0 \<sigma>\<^sub>0' d = Some e" by (rule resolve_mono[OF s0 e])
  have ed: "else_deadline time_of \<sigma>\<^sub>0' e D' = else_deadline time_of \<sigma>\<^sub>0 e D'"
  proof (cases D')
    case None
    then show ?thesis by (simp add: else_deadline_def)
  next
    case (Some d')
    with dd obtain e\<^sub>1 where r1: "resolve time_of e \<sigma>\<^sub>0 d' = Some e\<^sub>1"
      by (cases "resolve time_of e \<sigma>\<^sub>0 d'") (auto simp: else_deadline_def)
    from resolve_mono[OF s0 r1] r1 Some show ?thesis by (simp add: else_deadline_def)
  qed
  from SMustElse e e' ed show ?thesis
    by (simp add: term_line_def else_line_def Let_def else_verdict_data_indep[OF le])
qed (simp_all add: term_line_def composite_line_def split: option.splits)

text \<open>A line of a report is never a type line, and a report that passes the type check
  contains \<open>LTypes None\<close>.\<close>

lemma term_line_not_LTypes:
  "term_line \<tau>\<^sub>0 \<sigma>\<^sub>0 blk \<pi> i \<noteq> LTypes x" "LTypes x \<noteq> term_line \<tau>\<^sub>0 \<sigma>\<^sub>0 blk \<pi> i"
  by (cases "blk ! i"; simp add: term_line_def must_line_def else_line_def composite_line_def Let_def
      split: option.splits)+

lemma run_norm_accepted:
  assumes "l \<in> set (run sp obs)" and "\<And>b. l \<noteq> LActivation b" and "\<And>b. l \<noteq> LBlock b"
    and "\<And>j. l \<noteq> LTimeOrder j" and "\<And>x. l \<noteq> LTypes x"
  shows "LTypes None \<in> set (run sp obs)"
proof -
  obtain fs blk invs where sp: "sp = Spec fs blk invs" by (cases sp)
  show ?thesis
    using assms unfolding sp run_def evaluate_def evaluate_trace_def
    by (auto simp: Let_def split: option.splits if_splits)
qed

lemma run_decided_accepted:
  assumes i: "i < length (run sp obs)" and dec: "decided (run sp obs ! i)"
  shows "LTypes None \<in> set (run sp obs)"
proof (rule run_norm_accepted[of "run sp obs ! i"])
  show "run sp obs ! i \<in> set (run sp obs)" using i by (rule nth_mem)
qed (use dec in auto)

lemma run_LTypes_Some:
  assumes "LTypes (Some e) \<in> set (run sp obs)"
  shows "run sp obs = [LActivation True, LBlock True, LTypes (Some e)]"
proof -
  obtain fs blk invs where sp: "sp = Spec fs blk invs" by (cases sp)
  show ?thesis
    using assms unfolding sp run_def evaluate_def evaluate_trace_def
    by (auto simp: Let_def term_line_not_LTypes split: option.splits if_splits prod.splits)
qed

text \<open>The report on the same observations with more data. If the observations \<open>obs\<close> were
  accepted (their report has the line \<open>LTypes None\<close>), then either \<open>obs'\<close> is rejected for the
  types of its data, or every line of the report on \<open>obs'\<close> refines the corresponding line of
  the report on \<open>obs\<close>. \<open>obs'\<close> cannot be rejected for its time order or its activation: the
  times are the same, and activation succeeds on more data.\<close>

theorem run_data_mono:
  assumes pf: "present_free_spec sp" and le: "obs_le obs obs'"
    and ok: "LTypes None \<in> set (run sp obs)" and i: "i < length (run sp obs)"
  shows "line_refines (run sp obs ! i) (run sp obs' ! i) \<or> (\<exists>e. LTypes (Some e) \<in> set (run sp obs'))"
proof -
  obtain fs blk invs where sp: "sp = Spec fs blk invs" by (cases sp)
  let ?H = "hidden fs"
  let ?O = "erase_obs ?H obs" and ?O' = "erase_obs ?H obs'"
  have leO: "obs_le ?O ?O'" by (rule erase_obs_le[OF le])
  have run: "run sp obs = evaluate sp ?O" "run sp obs' = evaluate sp ?O'"
    by (simp_all add: run_def sp)
  have to': "time_order ?O' = time_order ?O" by (rule time_order_obs_le[OF leO])
  have to: "time_order ?O = None"
  proof (rule ccontr)
    assume "time_order ?O \<noteq> None"
    then obtain j where "time_order ?O = Some j" by blast
    then have "run sp obs = [LTimeOrder j]" by (simp add: run evaluate_def)
    with ok show False by simp
  qed
  define M where "M = max_age fs"
  define \<pi> where "\<pi> = btrace M (raw_trace ?O)"
  define \<pi>' where "\<pi>' = btrace M (raw_trace ?O')"
  have ne: "obs \<noteq> []"
  proof
    assume "obs = []"
    then have "run sp obs = [LActivation False]"
      by (simp add: run_def evaluate_def time_order_def evaluate_trace_def sp erase_obs_def)
    with ok show False by simp
  qed
  then have neO: "?O \<noteq> []" by (simp add: erase_obs_def)
  have lO: "length ?O' = length ?O" using leO by (simp add: obs_le_def)
  have neO': "?O' \<noteq> []" using lO neO length_0_conv by metis
  have lp: "data_le \<pi> \<pi>'"
    unfolding \<pi>_def \<pi>'_def by (rule btrace_data_le[OF raw_trace_data_le[OF leO]])
  have tr: "is_trace \<pi>"
    unfolding \<pi>_def by (rule btrace_is_trace) (use to neO time_order_is_trace in blast)
  have lp0: "0 < length \<pi>" using neO by (simp add: \<pi>_def length_raw_trace)
  then have nep: "\<pi> \<noteq> []" by auto
  have t0: "time \<pi>' 0 = time \<pi> 0" by (rule data_le_time[OF lp lp0])
  have s0: "st \<pi> 0 \<sqsubseteq> st \<pi>' 0" by (rule data_le_st[OF lp lp0])
  have ev: "evaluate sp ?O = evaluate_trace sp ?O" "evaluate sp ?O' = evaluate_trace sp ?O'"
    using to to' by (simp_all add: evaluate_def)
  let ?act = "\<lambda>\<sigma>. activates time_of (time \<pi> 0) \<sigma> blk
                \<and> inv_activates time_of (time \<pi> 0) \<sigma> (map snd invs)
                \<and> else_order_ok time_of (time \<pi> 0) \<sigma> blk"
  let ?blk = "wf_block blk \<and> cont_free_prohibitions blk \<and> else_handlers_ok blk \<and> refs_ok blk"
  let ?lines = "\<lambda>\<sigma> p. map (term_line (time \<pi> 0) \<sigma> blk p) [0..<length blk]
                     @ map (\<lambda>(n, \<iota>). LInvariant n (sinv_eval time_of \<iota> p)) invs"
  have E: "evaluate_trace sp ?O =
             (if \<not> ?act (st \<pi> 0) then [LActivation False]
              else LActivation True # (if \<not> ?blk then [LBlock False] else LBlock True #
                (case ill_typed fs ?O of Some e \<Rightarrow> [LTypes (Some e)]
                 | None \<Rightarrow> LTypes None # ?lines (st \<pi> 0) \<pi>)))"
    using neO by (simp add: evaluate_trace_def sp Let_def flip: \<pi>_def M_def)
  have E': "evaluate_trace sp ?O' =
             (if \<not> ?act (st \<pi>' 0) then [LActivation False]
              else LActivation True # (if \<not> ?blk then [LBlock False] else LBlock True #
                (case ill_typed fs ?O' of Some e \<Rightarrow> [LTypes (Some e)]
                 | None \<Rightarrow> LTypes None # ?lines (st \<pi>' 0) \<pi>')))"
    using neO' by (simp add: evaluate_trace_def sp Let_def t0 flip: \<pi>'_def M_def
                       split: option.split)
  have act: "?act (st \<pi> 0)" and blk: "?blk" and ty: "ill_typed fs ?O = None"
    using ok unfolding run ev E by (auto split: if_splits option.splits)
  have act': "?act (st \<pi>' 0)"
    using act activates_mono[OF s0] inv_activates_mono[OF s0] else_order_ok_mono[OF s0] by blast
  have R: "run sp obs = LActivation True # LBlock True # LTypes None # ?lines (st \<pi> 0) \<pi>"
    unfolding run ev E using act blk ty by simp
  show ?thesis
  proof (cases "ill_typed fs ?O'")
    case (Some e)
    with act' blk have "LTypes (Some e) \<in> set (run sp obs')" unfolding run ev E' by simp
    then show ?thesis by blast
  next
    case None
    with act' blk have R': "run sp obs' = LActivation True # LBlock True # LTypes None # ?lines (st \<pi>' 0) \<pi>'"
      unfolding run ev E' by simp
    have "line_refines (run sp obs ! i) (run sp obs' ! i)"
    proof (cases "3 \<le> i")
      case False
      then have "i = 0 \<or> i = Suc 0 \<or> i = Suc (Suc 0)" by presburger
      then show ?thesis unfolding R R' by (auto simp: line_refines_refl)
    next
      case True
      define k where "k = i - 3"
      with True have k: "i = Suc (Suc (Suc k))" by arith
      have kl: "k < length (?lines (st \<pi> 0) \<pi>)" using i unfolding R k by simp
      have act0: "activates time_of (time \<pi> 0) (st \<pi> 0) blk" using act by blast
      have "line_refines (?lines (st \<pi> 0) \<pi> ! k) (?lines (st \<pi>' 0) \<pi>' ! k)"
      proof (cases "k < length blk")
        case True
        from pf have "\<forall>t \<in> set blk. norm_present_free t" by (simp add: sp)
        from bspec[OF this nth_mem[OF True]] have npf: "norm_present_free (blk ! k)" .
        from term_line_data_mono[OF act0 s0 tr lp True npf] True show ?thesis
          by (simp add: nth_append)
      next
        case False
        define n where "n = k - length blk"
        have nl: "n < length invs" using kl False by (simp add: n_def)
        obtain nm \<iota> where inv: "invs ! n = (nm, \<iota>)" by (cases "invs ! n")
        have l: "?lines \<sigma> p ! k = LInvariant nm (sinv_eval time_of \<iota> p)" for \<sigma> p
          using False nl inv by (simp add: nth_append n_def)
        from pf have "\<forall>x \<in> set invs. present_free (sinv_formula (snd x))" by (simp add: sp)
        from bspec[OF this nth_mem[OF nl]] inv have pfi: "present_free (sinv_formula \<iota>)" by simp
        show ?thesis
        proof (cases "sinv_eval time_of \<iota> \<pi>")
          case None
          then show ?thesis by (simp add: l)
        next
          case (Some b)
          from sinv_data_mono_le[OF pfi nep lp Some] Some show ?thesis by (simp add: l)
        qed
      qed
      then show ?thesis unfolding R R' k by simp
    qed
    then show ?thesis by (rule disjI1)
  qed
qed

text \<open>Three readings of \<open>run_data_mono\<close> for a report on accepted observations. A decided line
  of an obligation, a prohibition, a permission, a fallback or an invariant stays decided; a
  breach of a prohibition reported at \<open>\<tau>\<close> is reported at some \<open>\<tau>' \<le> \<tau>\<close>; a prohibition that is
  pending on the observations with more data was pending before. In each case the only
  exception is that the richer observations fail the type check.\<close>

corollary run_data_mono_decided:
  assumes pf: "present_free_spec sp" and le: "obs_le obs obs'" and i: "i < length (run sp obs)"
    and dec: "decided (run sp obs ! i)" and nc: "\<And>n d it v p. run sp obs ! i \<noteq> LComposite n d it v p"
  shows "decided (run sp obs' ! i) \<or> (\<exists>e. LTypes (Some e) \<in> set (run sp obs'))"
  using run_data_mono[OF pf le run_decided_accepted[OF i dec] i] line_refines_decided[OF _ dec nc]
  by blast

corollary run_data_mono_breach:
  assumes pf: "present_free_spec sp" and le: "obs_le obs obs'" and i: "i < length (run sp obs)"
    and l: "run sp obs ! i = LMustNot n s a (Breached \<tau>) acts"
  shows "(\<exists>\<tau>' acts'. \<tau>' \<le> \<tau> \<and> run sp obs' ! i = LMustNot n s a (Breached \<tau>') acts')
         \<or> (\<exists>e. LTypes (Some e) \<in> set (run sp obs'))"
proof -
  have dec: "decided (run sp obs ! i)" by (simp add: l)
  from run_data_mono[OF pf le run_decided_accepted[OF i dec] i] show ?thesis
    unfolding l by auto
qed

corollary run_data_mono_pending:
  assumes pf: "present_free_spec sp" and le: "obs_le obs obs'"
    and i: "i < length (run sp obs)" and i': "i < length (run sp obs')"
    and l: "run sp obs ! i = LMustNot n s a v acts" and l': "run sp obs' ! i = LMustNot n s a Pending acts'"
  shows "v = Pending"
proof -
  have "run sp obs ! i \<in> set (run sp obs)" using i by (rule nth_mem)
  then have ok: "LTypes None \<in> set (run sp obs)" by (rule run_norm_accepted) (simp_all add: l)
  from run_data_mono[OF pf le ok i] show ?thesis
  proof
    assume "line_refines (run sp obs ! i) (run sp obs' ! i)"
    then show ?thesis unfolding l l' by (cases v) auto
  next
    assume "\<exists>e. LTypes (Some e) \<in> set (run sp obs')"
    then obtain e where "LTypes (Some e) \<in> set (run sp obs')" ..
    from run_LTypes_Some[OF this] i' have "run sp obs' ! i \<in> set [LActivation True, LBlock True, LTypes (Some e)]"
      using nth_mem by metis
    with l' show ?thesis by simp
  qed
qed


subsection \<open>Export\<close>

export_code run Spec Fdecl Act ArgName ArgVal Pen PVal PAdd PSub PMul PNeg num_of
  PAmount PUndefined PNegative RNotify RPenalty
  SMust SMustNot SMay SThen SOr SAnd SUnless SOnBreach SIf SSkip SRef SMustElse DAt DAfter DFactor
  Notify Penalty Terminate CureBy EscalateTo
  ETrue EFalse EEq ELt ELe ENot EAnd EOr EImp EPresent VConst VName VDefault
  Always Eventually Next SInv SEventuallyWithin TPrim TOptional TRecord PBool PInt PDec PStr PTime
  ABool ANum AStr ATime dec_atom quotient_of Atom Nom fmap_of_list Deontic Arrival Tick
  Must May MustNot
  LTimeOrder LActivation LBlock LTypes LMust LMustNot LMay LMustElse LOnBreach LComposite LInvariant LMonitor
  CAt COpen CUnknown Done Interrupted Violated
  check_action enforce
  EFulfilled EPending EElse
  SFulfilled SPending SBreached NoContinuation Terminated Cure Escalated
  Fulfilled Breached Pending
  integer_of_nat nat_of_integer int_of_integer integer_of_int
  in Haskell module_name TRIEL

end
