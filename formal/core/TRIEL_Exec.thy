(*  Title:      TRIEL_Exec.thy
    Purpose:    An executable evaluator for the formal core and its export to Haskell.
                Every function the evaluator uses is either defined in the other theories
                of formal/core, or proved equal to such a function by a code equation in
                this theory. Membership of a trace in the denotation of a composite term
                is three-valued: definite answers are proved sound, and for terms without
                UNLESS the answer is always definite.
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
  have ev: "evt (last (\<rho> @ [?y])) = Deontic s a Must" by simp
  have m: "(\<rho> @ [?y], Done) \<in> must_d s a" unfolding must_d_def using tr' ev by blast
  have "length \<rho> < length (\<rho> @ [?y])" by simp
  moreover have "take (length \<rho>) (\<rho> @ [?y]) = \<rho>" by simp
  ultimately show "ext (must_d s a) \<rho>" unfolding ext_def using m by blast
qed

lemma ext_mustnot:
  assumes ne: "\<rho> \<noteq> []"
  shows "\<not> ext (mustnot_d s a c) \<rho>"
proof
  assume "ext (mustnot_d s a c) \<rho>"
  then obtain \<pi>\<^sub>0 r\<^sub>0 where m: "(\<pi>\<^sub>0, r\<^sub>0) \<in> mustnot_d s a c" and len: "length \<rho> < length \<pi>\<^sub>0"
    and "take (length \<rho>) \<pi>\<^sub>0 = \<rho>"
    unfolding ext_def by blast
  from m obtain x where "\<pi>\<^sub>0 = [x]" unfolding mustnot_d_def by blast
  with len ne show False by simp
qed

lemma ext_may:
  assumes tr: "is_trace \<rho>" and c: "eval c (st \<rho> (length \<rho> - 1)) = Some True"
  shows "ext (may_d s a c) \<rho>"
proof -
  let ?y = "(sta (last \<rho>), tstamp (last \<rho>), Deontic s a May)"
  have lp: "0 < length \<rho>" using tr by (simp add: is_trace_def)
  have "tstamp ?y = tstamp (last \<rho>)" by simp
  with tr have tr': "is_trace (\<rho> @ [?y])" by (rule is_trace_snoc)
  have ev: "evt (last (\<rho> @ [?y])) = Deontic s a May" by simp
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

lemma mem_must: "(\<pi>, r) \<in> must_d s a \<longleftrightarrow> is_trace \<pi> \<and> evt (last \<pi>) = Deontic s a Must \<and> r = Done"
  by (auto simp: must_d_def)

lemma len1: "(\<exists>x. \<pi> = [x]) \<longleftrightarrow> length \<pi> = 1"
  by (cases \<pi>) auto

lemma mem_may:
  "(\<pi>, r) \<in> may_d s a c \<longleftrightarrow>
     r = Done \<and> ((is_trace \<pi> \<and> evt (last \<pi>) = Deontic s a May \<and> 1 \<le> length \<pi> - 1
                   \<and> eval c (st \<pi> (length \<pi> - 2)) = Some True) \<or> length \<pi> = 1)"
  unfolding may_d_def len1[symmetric] by auto

lemma mem_mustnot: "(\<pi>, r) \<in> mustnot_d s a c \<longleftrightarrow> r = Done \<and> length \<pi> = 1"
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
  "mem3 (TMust s a) \<pi> r = Some (is_trace \<pi> \<and> evt (last \<pi>) = Deontic s a Must \<and> r = Done)"
| "mem3 (TMay s a c) \<pi> r =
     Some (r = Done \<and> ((is_trace \<pi> \<and> evt (last \<pi>) = Deontic s a May \<and> 1 \<le> length \<pi> - 1
                         \<and> eval c (st \<pi> (length \<pi> - 2)) = Some True) \<or> length \<pi> = 1))"
| "mem3 (TMustNot s a c) \<pi> r = Some (r = Done \<and> length \<pi> = 1)"
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
| "ext3 (TMustNot s a c) \<rho> = Some False"
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
  then show ?case by (auto simp: mem_mustnot ext_mustnot)
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


text \<open>Completeness: for terms without UNLESS and AND the answer is always definite.\<close>

theorem mem3_complete: "unless_free t \<Longrightarrow> and_free t \<Longrightarrow> mem3 t \<pi> r \<noteq> None"
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

text \<open>A factor declaration: the name, the declared type, and the maximum age if the factor
  is under \<open>ON_STALE BLOCK\<close>. A specification: the factors, the TERMS block, and the named
  invariants. The penalty amount of a breach handler is an opaque value.\<close>

datatype fdecl = Fdecl name "(name, prim) ty" "int option"

fun fd_name :: "fdecl \<Rightarrow> name" where "fd_name (Fdecl f t m) = f"
fun fd_ty :: "fdecl \<Rightarrow> (name, prim) ty" where "fd_ty (Fdecl f t m) = t"
fun fd_age :: "fdecl \<Rightarrow> int option" where "fd_age (Fdecl f t m) = m"

datatype spec = Spec "fdecl list" "cterm list" "(name \<times> (path, atom) inv) list"

definition max_age :: "fdecl list \<Rightarrow> name \<Rightarrow> int option" where
  "max_age fs f = (case find (\<lambda>x. fd_name x = f) fs of Some x \<Rightarrow> fd_age x | None \<Rightarrow> None)"

text \<open>The raw trace: the state of an entry is its data flattened to complex names.\<close>

definition raw_trace :: "observation list \<Rightarrow> ctrace" where
  "raw_trace obs = map (\<lambda>(d, \<tau>, e). (flat d, \<tau>, e)) obs"


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


subsection \<open>The report\<close>

datatype line =
    LActivation bool
  | LBlock bool
  | LTypes "(nat \<times> name) option"
  | LMust nat name act "int option" "name status" "name ract list"
  | LMustNot nat name act verdict "name ract list"
  | LMay nat name act verdict
  | LOnBreach nat name "nat option"
  | LComposite nat "bool option" "bool option" "bool option"
  | LInvariant name "bool option"

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
        None \<Rightarrow> LComposite n None None None
      | Some u \<Rightarrow> LComposite n (mem3 u \<pi> Done) (mem3 u \<pi> Interrupted) (mem3 u \<pi> Violated))"

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

definition term_line :: "int \<Rightarrow> (path, atom) state \<Rightarrow> cterm list \<Rightarrow> ctrace \<Rightarrow> nat \<Rightarrow> line" where
  "term_line \<tau>\<^sub>0 \<sigma>\<^sub>0 blk \<pi> i =
     (case blk ! i of
        SMust s a D F \<Rightarrow> must_line \<tau>\<^sub>0 \<sigma>\<^sub>0 blk \<pi> i s a D F
      | SMustNot s a c \<Rightarrow>
          LMustNot (Suc i) s a (pr_verdict s a c \<pi>) (pr_report num_of s a c (handler_of blk i) \<pi>)
      | SMay s a c \<Rightarrow> LMay (Suc i) s a (may_verdict s a c \<pi>)
      | SOnBreach s acts \<Rightarrow> LOnBreach (Suc i) s (map_option Suc (bound_to blk i s))
      | _ \<Rightarrow> composite_line (Suc i) (benv blk ! i) \<pi>)"

text \<open>The evaluator. Activation is checked first, in the blocked state of entry 0 at the
  time of entry 0; then the well-formedness of the block, with only informational actions
  in a handler bound to a prohibition; then the types of the data as given. The verdicts, the invariants and the membership of composite terms are computed
  on the blocked trace.\<close>

definition run :: "spec \<Rightarrow> observation list \<Rightarrow> line list" where
  "run sp obs =
     (case sp of Spec fs blk invs \<Rightarrow>
        (let \<pi> = btrace (max_age fs) (raw_trace obs); \<tau>\<^sub>0 = time \<pi> 0; \<sigma>\<^sub>0 = st \<pi> 0 in
         if obs = [] \<or> \<not> activates time_of \<tau>\<^sub>0 \<sigma>\<^sub>0 blk then [LActivation False]
         else LActivation True #
           (if \<not> wf_block blk \<or> \<not> cont_free_prohibitions blk \<or> \<not> refs_ok blk then [LBlock False]
            else LBlock True #
              (case ill_typed fs obs of
                 Some e \<Rightarrow> [LTypes (Some e)]
               | None \<Rightarrow> LTypes None # map (term_line \<tau>\<^sub>0 \<sigma>\<^sub>0 blk \<pi>) [0..<length blk]
                          @ map (\<lambda>(n, \<iota>). LInvariant n (inv_eval \<iota> \<pi>)) invs))))"

text \<open>A composite line reports \<open>mem3\<close> on the blocked trace. By \<open>mem3_sound\<close> its definite
  answers are membership in the denotation of the term, for terms without AND, and by
  \<open>mem3_complete\<close> they are always definite for terms without UNLESS and AND.\<close>


subsection \<open>Export\<close>

export_code run Spec Fdecl Act ArgName ArgVal Pen PVal PAdd PSub PMul PNeg num_of
  PAmount PUndefined PNegative RNotify RPenalty
  SMust SMustNot SMay SThen SOr SAnd SUnless SOnBreach SIf SSkip SRef DAt DAfter DFactor
  Notify Penalty Terminate CureBy EscalateTo
  ETrue EFalse EEq ELt ELe ENot EAnd EOr EImp EPresent VConst VName VDefault
  Always Eventually Next TPrim TOptional TRecord PBool PInt PDec PStr PTime
  ABool ANum AStr ATime dec_atom quotient_of Atom Nom fmap_of_list Deontic Arrival Tick
  Must May MustNot
  LActivation LBlock LTypes LMust LMustNot LMay LOnBreach LComposite LInvariant
  SFulfilled SPending SBreached NoContinuation Terminated Cure Escalated
  Fulfilled Breached Pending
  integer_of_nat nat_of_integer int_of_integer integer_of_int
  in Haskell module_name TRIEL

end
