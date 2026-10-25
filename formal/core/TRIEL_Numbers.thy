(*  Title:      TRIEL_Numbers.thy
    Purpose:    The numeric types of TRIEL, Integer and Decimal, modelled exactly by
                rational numbers: an Integer is a rational in the integers, a Decimal a
                rational with a finite decimal expansion. There is no floating point.
                Both predicates are executable, with code equations proved equal to
                the definitions.
    SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause
*)

theory TRIEL_Numbers
  imports Main "HOL.Rat"
begin

section \<open>Integer and Decimal\<close>

text \<open>A number is a rational \<open>q\<close>. It is an Integer if \<open>q \<in> \<int>\<close>, and a Decimal if it can be
  written \<open>m / 10\<^sup>k\<close> with \<open>m\<close> an integer: this is what a decimal literal such as \<open>12.50\<close>
  denotes (\<open>1250 / 10\<^sup>2\<close>). Every Integer is a Decimal. \<open>1/3\<close> is not a Decimal, so the
  model has no rounding.\<close>

definition int_rat :: "rat \<Rightarrow> bool" where
  "int_rat q \<longleftrightarrow> q \<in> \<int>"

definition decimal :: "rat \<Rightarrow> bool" where
  "decimal q \<longleftrightarrow> (\<exists>(m :: int) (k :: nat). q = of_int m / 10 ^ k)"

lemma decimal_literal: "decimal (of_int m / 10 ^ k)"
  unfolding decimal_def by blast

theorem int_rat_decimal: "int_rat q \<Longrightarrow> decimal q"
proof -
  assume "int_rat q"
  then obtain z where "q = of_int z" by (auto simp: int_rat_def elim: Ints_cases)
  then have "q = of_int z / 10 ^ 0" by simp
  then show "decimal q" unfolding decimal_def by blast
qed

lemma int_rat_code [code]: "int_rat q \<longleftrightarrow> of_int \<lfloor>q\<rfloor> = q"
proof
  assume "int_rat q"
  then obtain z where "q = of_int z" by (auto simp: int_rat_def elim: Ints_cases)
  then show "of_int \<lfloor>q\<rfloor> = q" by simp
next
  assume "of_int \<lfloor>q\<rfloor> = q"
  then show "int_rat q" unfolding int_rat_def by (metis Ints_of_int)
qed


section \<open>Denominators of decimals\<close>

text \<open>A positive integer divides a power of 10 if and only if it has no prime factor
  other than 2 and 5. \<open>dec_den\<close> decides this by removing the factors 2 and 5.\<close>

function dec_den :: "nat \<Rightarrow> bool" where
  "dec_den d =
     (if d \<le> 1 then d = 1
      else if 2 dvd d then dec_den (d div 2)
      else if 5 dvd d then dec_den (d div 5)
      else False)"
  by pat_completeness auto
termination
  by (relation "measure id") auto

declare dec_den.simps [simp del]

lemma dvd_two_cases: "(n :: nat) dvd 2 \<Longrightarrow> n = 1 \<or> n = 2"
proof -
  assume a: "n dvd 2"
  then have "n \<le> 2" by (rule dvd_imp_le) simp
  moreover have "n \<noteq> 0"
  proof
    assume "n = 0"
    with a show False by simp
  qed
  ultimately show "n = 1 \<or> n = 2" by arith
qed

lemma dvd_five_cases: "(n :: nat) dvd 5 \<Longrightarrow> n = 1 \<or> n = 5"
proof -
  assume a: "n dvd 5"
  then have "n \<le> 5" by (rule dvd_imp_le) simp
  moreover have "n \<noteq> 0"
  proof
    assume "n = 0"
    with a show False by simp
  qed
  ultimately have "n = 1 \<or> n = 2 \<or> n = 3 \<or> n = 4 \<or> n = 5" by arith
  with a show "n = 1 \<or> n = 5" by (elim disjE) (simp_all add: dvd_eq_mod_eq_0)
qed

text \<open>A number with neither 2 nor 5 as a factor is coprime to 10, so it divides a power
  of 10 only if it is 1.\<close>

lemma coprime10_dvd_power:
  fixes d :: nat
  assumes "\<not> 2 dvd d" and "\<not> 5 dvd d" and "d dvd 10 ^ k"
  shows "d = 1"
proof -
  have g2: "gcd d 2 = 1"
  proof -
    have "gcd d 2 = 1 \<or> gcd d 2 = 2" by (rule dvd_two_cases) simp
    moreover have "gcd d 2 \<noteq> 2" using assms(1) by (metis gcd_dvd1)
    ultimately show ?thesis by blast
  qed
  have g5: "gcd d 5 = 1"
  proof -
    have "gcd d 5 = 1 \<or> gcd d 5 = 5" by (rule dvd_five_cases) simp
    moreover have "gcd d 5 \<noteq> 5" using assms(2) by (metis gcd_dvd1)
    ultimately show ?thesis by blast
  qed
  have "coprime d 2" and "coprime d 5"
    using g2 g5 coprime_iff_gcd_eq_1 by blast+
  then have "coprime d 10"
    using coprime_mult_right_iff[of d "2 :: nat" 5] by simp
  then have "coprime d (10 ^ k)" by simp
  then have g: "gcd d (10 ^ k) = 1" using coprime_iff_gcd_eq_1 by blast
  have "d dvd gcd d (10 ^ k)" using assms(3) by (rule gcd_greatest[OF dvd_refl])
  with g show "d = 1" by simp
qed

lemma two_dvd_ten: "(2 :: nat) dvd 10" and five_dvd_ten: "(5 :: nat) dvd 10"
  using dvd_triv_left[of "2 :: nat" 5] dvd_triv_left[of "5 :: nat" 2] by simp_all

theorem dec_den_iff: "0 < d \<Longrightarrow> dec_den d \<longleftrightarrow> (\<exists>k. d dvd 10 ^ k)"
proof (induction d rule: dec_den.induct)
  case (1 d)
  show ?case
  proof (cases "d \<le> 1")
    case True
    with "1.prems" have d1: "d = 1" by simp
    have "dec_den 1" by (subst dec_den.simps) simp
    moreover have "(1 :: nat) dvd 10 ^ 0" by simp
    ultimately show ?thesis unfolding d1 by blast
  next
    case d: False
    show ?thesis
    proof (cases "2 dvd d")
      case two: True
      then obtain e where e: "d = 2 * e" by blast
      have e0: "0 < e" using d e by arith
      have de: "d div 2 = e" using e by simp
      have IH: "dec_den e \<longleftrightarrow> (\<exists>k. e dvd 10 ^ k)"
        using "1.IH"(1)[OF d two] e0 de by simp
      have "dec_den d \<longleftrightarrow> dec_den e"
        using d two de by (simp add: dec_den.simps[of d])
      also have "\<dots> \<longleftrightarrow> (\<exists>k. d dvd 10 ^ k)"
      proof
        assume "dec_den e"
        with IH obtain k where k: "e dvd 10 ^ k" by blast
        have "2 * e dvd 10 * 10 ^ k" by (rule mult_dvd_mono[OF two_dvd_ten k])
        then have "d dvd 10 ^ Suc k" using e by simp
        then show "\<exists>k. d dvd 10 ^ k" by blast
      next
        assume "\<exists>k. d dvd 10 ^ k"
        then obtain k where k: "d dvd 10 ^ k" by blast
        have "e dvd d" using e by simp
        then have "e dvd 10 ^ k" using k by (rule dvd_trans)
        with IH show "dec_den e" by blast
      qed
      finally show ?thesis .
    next
      case ntwo: False
      show ?thesis
      proof (cases "5 dvd d")
        case five: True
        then obtain e where e: "d = 5 * e" by blast
        have e0: "0 < e" using d e by arith
        have de: "d div 5 = e" using e by simp
        have IH: "dec_den e \<longleftrightarrow> (\<exists>k. e dvd 10 ^ k)"
          using "1.IH"(2)[OF d ntwo five] e0 de by simp
        have "dec_den d \<longleftrightarrow> dec_den e"
          using d ntwo five de by (simp add: dec_den.simps[of d])
        also have "\<dots> \<longleftrightarrow> (\<exists>k. d dvd 10 ^ k)"
        proof
          assume "dec_den e"
          with IH obtain k where k: "e dvd 10 ^ k" by blast
          have "5 * e dvd 10 * 10 ^ k" by (rule mult_dvd_mono[OF five_dvd_ten k])
          then have "d dvd 10 ^ Suc k" using e by simp
          then show "\<exists>k. d dvd 10 ^ k" by blast
        next
          assume "\<exists>k. d dvd 10 ^ k"
          then obtain k where k: "d dvd 10 ^ k" by blast
          have "e dvd d" using e by simp
          then have "e dvd 10 ^ k" using k by (rule dvd_trans)
          with IH show "dec_den e" by blast
        qed
        finally show ?thesis .
      next
        case nfive: False
        have "\<not> dec_den d" using d ntwo nfive by (simp add: dec_den.simps[of d])
        moreover have "\<not> d dvd 10 ^ k" for k
        proof
          assume "d dvd 10 ^ k"
          with ntwo nfive have "d = 1" by (rule coprime10_dvd_power)
          with d show False by simp
        qed
        ultimately show ?thesis by blast
      qed
    qed
  qed
qed


section \<open>Executable Decimal\<close>

text \<open>A rational in lowest terms \<open>a / b\<close> is a Decimal exactly when its denominator \<open>b\<close>
  divides a power of 10.\<close>

theorem decimal_iff_denominator:
  assumes qo: "quotient_of q = (a, b)"
  shows "decimal q \<longleftrightarrow> (\<exists>k. b dvd 10 ^ k)"
proof -
  have b0: "0 < b" using qo by (rule quotient_of_denom_pos)
  have q: "q = of_int a / of_int b" using qo by (rule quotient_of_div)
  have cop: "coprime a b" using qo by (rule quotient_of_coprime)
  show ?thesis
  proof
    assume "decimal q"
    then obtain m k where mk: "q = of_int m / 10 ^ k" by (auto simp: decimal_def)
    have "of_int a / of_int b = (of_int m / 10 ^ k :: rat)" using q mk by metis
    then have "of_int a * 10 ^ k = (of_int m * of_int b :: rat)"
      using b0 by (simp add: frac_eq_eq)
    then have "(of_int (a * 10 ^ k) :: rat) = of_int (m * b)" by simp
    then have eq: "a * 10 ^ k = m * b" by (simp only: of_int_eq_iff)
    have "b dvd a * 10 ^ k" unfolding eq by simp
    moreover have "coprime b a" using cop coprime_commute by blast
    ultimately have "b dvd 10 ^ k" by (metis coprime_dvd_mult_right_iff)
    then show "\<exists>k. b dvd 10 ^ k" by blast
  next
    assume "\<exists>k. b dvd 10 ^ k"
    then obtain k c where c: "10 ^ k = b * c" by (auto elim: dvdE)
    have "(of_int (10 ^ k) :: rat) = of_int (b * c)" using c by simp
    then have tk: "(10 :: rat) ^ k = of_int b * of_int c" by simp
    have c0: "of_int c \<noteq> (0 :: rat)" using tk by auto
    have "q = of_int a * of_int c / (of_int b * of_int c)" using q c0 by simp
    also have "\<dots> = of_int (a * c) / 10 ^ k" using tk by simp
    finally show "decimal q" unfolding decimal_def by blast
  qed
qed

lemma decimal_code [code]: "decimal q \<longleftrightarrow> dec_den (nat (snd (quotient_of q)))"
proof -
  obtain a b where qo: "quotient_of q = (a, b)" by (cases "quotient_of q")
  have b0: "0 < b" using qo by (rule quotient_of_denom_pos)
  have nat_dvd: "nat b dvd 10 ^ k \<longleftrightarrow> b dvd 10 ^ k" for k
    using int_dvd_int_iff[of "nat b" "10 ^ k"] b0 by simp
  show ?thesis
    using decimal_iff_denominator[OF qo] dec_den_iff[of "nat b"] b0 qo nat_dvd by simp
qed

text \<open>\<open>1/3\<close> has no finite decimal expansion.\<close>

theorem not_decimal_third: "\<not> decimal (1 / 3)"
proof
  assume "decimal (1 / 3)"
  then obtain m k where "(1 / 3 :: rat) = of_int m / 10 ^ k" by (auto simp: decimal_def)
  then have "(10 ^ k :: rat) = of_int m * 3" by (simp add: frac_eq_eq)
  then have "(of_int (10 ^ k) :: rat) = of_int (m * 3)" by simp
  then have "(10 ^ k :: int) = m * 3" by (simp only: of_int_eq_iff)
  then have "int (3 :: nat) dvd int (10 ^ k)" by simp
  then have "(3 :: nat) dvd 10 ^ k" by (simp only: int_dvd_int_iff)
  then have "(3 :: nat) = 1"
    by (rule coprime10_dvd_power[rotated 2]) (simp_all add: dvd_eq_mod_eq_0)
  then show False by simp
qed

section \<open>Arithmetic on decimals\<close>

text \<open>The Decimals are closed under addition, subtraction, negation and multiplication,
  but not under division (\<open>not_decimal_third\<close>). So an amount computed from Integer and
  Decimal values with \<open>+\<close>, \<open>-\<close> and \<open>*\<close> is a Decimal: no rounding is ever needed.\<close>

lemma decimal_common:
  assumes "decimal p" and "decimal q"
  obtains m n k where "p = of_int m / 10 ^ k" and "q = of_int n / 10 ^ k"
proof -
  from assms obtain m\<^sub>1 k\<^sub>1 m\<^sub>2 k\<^sub>2 where p: "p = of_int m\<^sub>1 / 10 ^ k\<^sub>1"
    and q: "q = of_int m\<^sub>2 / 10 ^ k\<^sub>2"
    unfolding decimal_def by blast
  have "p = of_int (m\<^sub>1 * 10 ^ k\<^sub>2) / 10 ^ (k\<^sub>1 + k\<^sub>2)"
    unfolding p by (simp add: power_add)
  moreover have "q = of_int (m\<^sub>2 * 10 ^ k\<^sub>1) / 10 ^ (k\<^sub>1 + k\<^sub>2)"
    unfolding q by (simp add: power_add)
  ultimately show ?thesis by (rule that)
qed

theorem decimal_add: "decimal p \<Longrightarrow> decimal q \<Longrightarrow> decimal (p + q)"
proof -
  assume "decimal p" "decimal q"
  then obtain m n k where "p = of_int m / 10 ^ k" "q = of_int n / 10 ^ k"
    by (rule decimal_common)
  then have "p + q = of_int (m + n) / 10 ^ k" by (simp add: add_divide_distrib)
  then show "decimal (p + q)" unfolding decimal_def by blast
qed

theorem decimal_uminus: "decimal p \<Longrightarrow> decimal (- p)"
proof -
  assume "decimal p"
  then obtain m k where "p = of_int m / 10 ^ k" unfolding decimal_def by blast
  then have "- p = of_int (- m) / 10 ^ k" by simp
  then show "decimal (- p)" unfolding decimal_def by blast
qed

theorem decimal_diff: "decimal p \<Longrightarrow> decimal q \<Longrightarrow> decimal (p - q)"
  using decimal_add[of p "- q"] decimal_uminus[of q] by simp

theorem decimal_mult: "decimal p \<Longrightarrow> decimal q \<Longrightarrow> decimal (p * q)"
proof -
  assume "decimal p" "decimal q"
  then obtain m\<^sub>1 k\<^sub>1 m\<^sub>2 k\<^sub>2 where "p = of_int m\<^sub>1 / 10 ^ k\<^sub>1" "q = of_int m\<^sub>2 / 10 ^ k\<^sub>2"
    unfolding decimal_def by blast
  then have "p * q = of_int (m\<^sub>1 * m\<^sub>2) / 10 ^ (k\<^sub>1 + k\<^sub>2)" by (simp add: power_add)
  then show "decimal (p * q)" unfolding decimal_def by blast
qed

end
