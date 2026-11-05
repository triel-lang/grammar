(*  Title:      TRIEL_Signals.thy
    Purpose:    Continuous signals between samples. A factor read from a sensor is
                sampled at the arrival entries of a trace, and a declared rate bound L
                bounds the change of the quantity behind it: between two times the
                quantity moves by at most L times the time difference. The admissible
                signals are the L-Lipschitz functions through the samples; at every time
                the quantity lies in an enclosure computed by exact rational arithmetic;
                a condition is evaluated on enclosures in three values. Proved: the
                interval evaluation extends the evaluation on states, is sound for every
                admissible signal and monotone under narrowing; the enclosure contains
                every admissible signal, narrows with more samples, is the sample at a
                sample time, is non-empty and tight for consistent samples; what the
                monitor of a prohibition allows on the enclosures is false for every
                admissible signal, and a breach it records is certain; the verdicts
                computed from the enclosures are final under extension of the trace,
                where inconsistent samples are a rejection; the enclosures are
                executable.
    SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause
*)

theory TRIEL_Signals
  imports TRIEL_Exec "HOL.Real"
begin

section \<open>Signals under a rate bound\<close>

text \<open>A signal is a function from real time to real values. It respects the rate bound
  \<open>L\<close> if between any two times it moves by at most \<open>L\<close> times the time difference: it is
  \<open>L\<close>-Lipschitz.\<close>

definition lip :: "real \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> bool" where
  "lip L f \<longleftrightarrow> (\<forall>s t. \<bar>f t - f s\<bar> \<le> L * \<bar>t - s\<bar>)"

lemma lipD: "lip L f \<Longrightarrow> \<bar>f t - f s\<bar> \<le> L * \<bar>t - s\<bar>"
  by (simp add: lip_def)

lemma lip_const: "0 \<le> L \<Longrightarrow> lip L (\<lambda>_. c)"
  by (simp add: lip_def)

text \<open>A sample is a time with the value read at that time. A signal passes through a set
  of samples if it has each sampled value at its time. A set of samples is consistent
  with \<open>L\<close> if every two of them differ by at most \<open>L\<close> times their time difference, which
  is necessary for a signal under \<open>L\<close> to pass through them.\<close>

type_synonym rsamples = "(real \<times> real) set"

definition through :: "rsamples \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> bool" where
  "through S f \<longleftrightarrow> (\<forall>p \<in> S. f (fst p) = snd p)"

definition rcons :: "real \<Rightarrow> rsamples \<Rightarrow> bool" where
  "rcons L S \<longleftrightarrow> (\<forall>p \<in> S. \<forall>q \<in> S. \<bar>snd p - snd q\<bar> \<le> L * \<bar>fst p - fst q\<bar>)"

lemma rcons_subset: "S \<subseteq> S' \<Longrightarrow> rcons L S' \<Longrightarrow> rcons L S"
  by (auto simp: rcons_def)

lemma lip_through_rcons:
  assumes "lip L f" "through S f"
  shows "rcons L S"
  unfolding rcons_def
proof (intro ballI)
  fix p q assume "p \<in> S" "q \<in> S"
  with assms(2) have "f (fst p) = snd p" "f (fst q) = snd q" by (simp_all add: through_def)
  with lipD[OF assms(1), of "fst p" "fst q"] show "\<bar>snd p - snd q\<bar> \<le> L * \<bar>fst p - fst q\<bar>" by simp
qed


subsection \<open>Cones and envelopes\<close>

text \<open>A sample \<open>p\<close> confines a signal under \<open>L\<close> to the cone between \<open>snd p - L \<cdot> \<bar>t - fst p\<bar>\<close>
  and \<open>snd p + L \<cdot> \<bar>t - fst p\<bar>\<close>. The upper envelope of a set of samples is the least of
  their upper cones, the lower envelope the greatest of their lower cones.\<close>

definition cone_up :: "real \<Rightarrow> real \<Rightarrow> real \<times> real \<Rightarrow> real" where
  "cone_up L t p = snd p + L * \<bar>t - fst p\<bar>"

definition cone_lo :: "real \<Rightarrow> real \<Rightarrow> real \<times> real \<Rightarrow> real" where
  "cone_lo L t p = snd p - L * \<bar>t - fst p\<bar>"

definition upper :: "real \<Rightarrow> rsamples \<Rightarrow> real \<Rightarrow> real" where
  "upper L S t = Min (cone_up L t ` S)"

definition lower :: "real \<Rightarrow> rsamples \<Rightarrow> real \<Rightarrow> real" where
  "lower L S t = Max (cone_lo L t ` S)"

lemma lip_le_cone_up: "lip L f \<Longrightarrow> f (fst p) = snd p \<Longrightarrow> f t \<le> cone_up L t p"
  using lipD[of L f t "fst p"] by (simp add: cone_up_def)

lemma lip_ge_cone_lo: "lip L f \<Longrightarrow> f (fst p) = snd p \<Longrightarrow> cone_lo L t p \<le> f t"
  using lipD[of L f t "fst p"] by (simp add: cone_lo_def)

text \<open>Every signal under \<open>L\<close> through the samples runs between the envelopes.\<close>

lemma lip_le_upper:
  assumes "finite S" "S \<noteq> {}" "lip L f" "through S f"
  shows "f t \<le> upper L S t"
  unfolding upper_def using assms by (intro Min.boundedI) (auto simp: through_def lip_le_cone_up)

lemma lower_le_lip:
  assumes "finite S" "S \<noteq> {}" "lip L f" "through S f"
  shows "lower L S t \<le> f t"
  unfolding lower_def using assms by (intro Max.boundedI) (auto simp: through_def lip_ge_cone_lo)

text \<open>At the time of a sample of a consistent set the envelopes have the sampled value.\<close>

lemma cone_up_at: "cone_up L (fst p) p = snd p"
  by (simp add: cone_up_def)

lemma cone_lo_at: "cone_lo L (fst p) p = snd p"
  by (simp add: cone_lo_def)

lemma upper_sample:
  assumes "finite S" "rcons L S" "p \<in> S"
  shows "upper L S (fst p) = snd p"
  unfolding upper_def
proof (rule Min_eqI)
  show "finite (cone_up L (fst p) ` S)" using assms(1) by simp
  show "snd p \<in> cone_up L (fst p) ` S" using assms(3) cone_up_at[of L p] by force
  fix y assume "y \<in> cone_up L (fst p) ` S"
  then obtain q where q: "q \<in> S" "y = cone_up L (fst p) q" by blast
  from assms(2,3) q(1) have "\<bar>snd p - snd q\<bar> \<le> L * \<bar>fst p - fst q\<bar>" by (simp add: rcons_def)
  then show "snd p \<le> y" unfolding q(2) cone_up_def by (simp add: abs_le_iff)
qed

lemma lower_sample:
  assumes "finite S" "rcons L S" "p \<in> S"
  shows "lower L S (fst p) = snd p"
  unfolding lower_def
proof (rule Max_eqI)
  show "finite (cone_lo L (fst p) ` S)" using assms(1) by simp
  show "snd p \<in> cone_lo L (fst p) ` S" using assms(3) cone_lo_at[of L p] by force
  fix y assume "y \<in> cone_lo L (fst p) ` S"
  then obtain q where q: "q \<in> S" "y = cone_lo L (fst p) q" by blast
  from assms(2,3) q(1) have "\<bar>snd p - snd q\<bar> \<le> L * \<bar>fst p - fst q\<bar>" by (simp add: rcons_def)
  then show "y \<le> snd p" unfolding q(2) cone_lo_def by (simp add: abs_le_iff)
qed

text \<open>The envelopes are signals under \<open>L\<close> themselves: a cone moves by at most \<open>L\<close> times
  the time difference, and so does the least or greatest of finitely many cones.\<close>

lemma abs_diff_triangle: "\<bar>t - s\<bar> \<le> \<bar>t' - s\<bar> + \<bar>t - t'\<bar>" for t t' s :: real
  using abs_triangle_ineq[of "t - t'" "t' - s"] by simp

lemma cone_up_shift: "0 \<le> L \<Longrightarrow> cone_up L t p \<le> cone_up L t' p + L * \<bar>t - t'\<bar>"
  unfolding cone_up_def
  using mult_left_mono[OF abs_diff_triangle[of t "fst p" t'], of L] by (simp add: algebra_simps)

lemma cone_lo_shift: "0 \<le> L \<Longrightarrow> cone_lo L t' p - L * \<bar>t - t'\<bar> \<le> cone_lo L t p"
  unfolding cone_lo_def
  using mult_left_mono[OF abs_diff_triangle[of t "fst p" t'], of L] by (simp add: algebra_simps)

lemma upper_shift:
  assumes "finite S" "S \<noteq> {}" "0 \<le> L"
  shows "upper L S t \<le> upper L S t' + L * \<bar>t - t'\<bar>"
proof -
  have "upper L S t' \<in> cone_up L t' ` S"
    unfolding upper_def using assms(1,2) by (intro Min_in) simp_all
  then obtain p where p: "p \<in> S" "upper L S t' = cone_up L t' p" by blast
  have "upper L S t \<le> cone_up L t p"
    unfolding upper_def using assms(1) p(1) by (intro Min_le) simp_all
  also have "\<dots> \<le> cone_up L t' p + L * \<bar>t - t'\<bar>" by (rule cone_up_shift[OF assms(3)])
  finally show ?thesis using p(2) by simp
qed

lemma lower_shift:
  assumes "finite S" "S \<noteq> {}" "0 \<le> L"
  shows "lower L S t' - L * \<bar>t - t'\<bar> \<le> lower L S t"
proof -
  have "lower L S t' \<in> cone_lo L t' ` S"
    unfolding lower_def using assms(1,2) by (intro Max_in) simp_all
  then obtain p where p: "p \<in> S" "lower L S t' = cone_lo L t' p" by blast
  have "cone_lo L t' p - L * \<bar>t - t'\<bar> \<le> cone_lo L t p" by (rule cone_lo_shift[OF assms(3)])
  also have "\<dots> \<le> lower L S t"
    unfolding lower_def using assms(1) p(1) by (intro Max_ge) simp_all
  finally show ?thesis using p(2) by simp
qed

lemma abs_minus_commute_real: "\<bar>t - s\<bar> = \<bar>s - t\<bar>" for s t :: real
  by (rule abs_minus_commute)

theorem upper_lip:
  assumes "finite S" "S \<noteq> {}" "0 \<le> L"
  shows "lip L (upper L S)"
  unfolding lip_def
proof (intro allI)
  fix s t
  have "upper L S t - upper L S s \<le> L * \<bar>t - s\<bar>"
    using upper_shift[OF assms, of t s] by simp
  moreover have "upper L S s - upper L S t \<le> L * \<bar>t - s\<bar>"
    using upper_shift[OF assms, of s t] by (simp add: abs_minus_commute_real)
  ultimately show "\<bar>upper L S t - upper L S s\<bar> \<le> L * \<bar>t - s\<bar>" by (simp add: abs_le_iff)
qed

theorem lower_lip:
  assumes "finite S" "S \<noteq> {}" "0 \<le> L"
  shows "lip L (lower L S)"
  unfolding lip_def
proof (intro allI)
  fix s t
  have "lower L S s - L * \<bar>t - s\<bar> \<le> lower L S t"
    using lower_shift[OF assms, of s t] .
  moreover have "lower L S t - L * \<bar>t - s\<bar> \<le> lower L S s"
    using lower_shift[OF assms, of t s] unfolding abs_minus_commute[of s t] .
  ultimately show "\<bar>lower L S t - lower L S s\<bar> \<le> L * \<bar>t - s\<bar>" by (simp add: abs_le_iff)
qed

theorem envelope_lip:
  assumes "finite S" "S \<noteq> {}" "0 \<le> L"
  shows "lip L (lower L S)" and "lip L (upper L S)"
  by (rule lower_lip[OF assms]) (rule upper_lip[OF assms])

text \<open>So the envelopes of a consistent set of samples are signals under \<open>L\<close> through the
  samples: the extremal admissible signals. Hence the lower envelope is below the upper
  one, and a set of samples is consistent exactly when some signal under \<open>L\<close> passes
  through it.\<close>

lemma upper_through:
  assumes "finite S" "rcons L S"
  shows "through S (upper L S)"
  using upper_sample[OF assms] by (simp add: through_def)

lemma lower_through:
  assumes "finite S" "rcons L S"
  shows "through S (lower L S)"
  using lower_sample[OF assms] by (simp add: through_def)

theorem lower_le_upper:
  assumes "finite S" "S \<noteq> {}" "0 \<le> L" "rcons L S"
  shows "lower L S t \<le> upper L S t"
  by (rule lower_le_lip[OF assms(1,2) upper_lip[OF assms(1,2,3)] upper_through[OF assms(1,4)]])

theorem rcons_iff_lip:
  assumes "finite S" "0 \<le> L"
  shows "rcons L S \<longleftrightarrow> (\<exists>f. lip L f \<and> through S f)"
proof
  assume c: "rcons L S"
  show "\<exists>f. lip L f \<and> through S f"
  proof (cases "S = {}")
    case True
    then show ?thesis using lip_const[OF assms(2), of 0]
      by (intro exI[of _ "\<lambda>_. 0"]) (simp add: through_def)
  next
    case False
    then show ?thesis using upper_lip[OF assms(1) False assms(2)] upper_through[OF assms(1) c]
      by blast
  qed
next
  assume "\<exists>f. lip L f \<and> through S f"
  then show "rcons L S" using lip_through_rcons by blast
qed

text \<open>Tightness: every value between the envelopes at a time is the value there of some
  signal under \<open>L\<close> through the samples, namely of the upper envelope of the samples with
  that value added as a sample, which is a consistent set.\<close>

lemma rcons_insert:
  assumes "finite S" "S \<noteq> {}" "0 \<le> L" "rcons L S"
    and w: "lower L S t \<le> w" "w \<le> upper L S t"
  shows "rcons L (insert (t, w) S)"
  unfolding rcons_def
proof (intro ballI)
  fix p q assume p: "p \<in> insert (t, w) S" and q: "q \<in> insert (t, w) S"
  have cone: "\<bar>w - snd r\<bar> \<le> L * \<bar>t - fst r\<bar>" if r: "r \<in> S" for r
  proof -
    have "w \<le> cone_up L t r"
      using w(2) Min_le[OF _ imageI[OF r], of "cone_up L t"] assms(1)
      unfolding upper_def by simp
    moreover have "cone_lo L t r \<le> w"
      using w(1) Max_ge[OF _ imageI[OF r], of "cone_lo L t"] assms(1)
      unfolding lower_def by simp
    ultimately show ?thesis by (simp add: cone_up_def cone_lo_def abs_le_iff)
  qed
  show "\<bar>snd p - snd q\<bar> \<le> L * \<bar>fst p - fst q\<bar>"
  proof (cases "p = (t, w)")
    case True
    show ?thesis
    proof (cases "q = (t, w)")
      case True
      with \<open>p = (t, w)\<close> show ?thesis by simp
    next
      case False
      with q have "q \<in> S" by simp
      with True cone[of q] show ?thesis by simp
    qed
  next
    case False
    with p have pS: "p \<in> S" by simp
    show ?thesis
    proof (cases "q = (t, w)")
      case True
      with cone[OF pS] show ?thesis by (simp add: abs_minus_commute)
    next
      case False
      with q have "q \<in> S" by simp
      with pS assms(4) show ?thesis by (simp add: rcons_def)
    qed
  qed
qed

theorem envelope_tight:
  assumes "finite S" "S \<noteq> {}" "0 \<le> L" "rcons L S"
    and w: "lower L S t \<le> w" "w \<le> upper L S t"
  shows "\<exists>f. lip L f \<and> through S f \<and> f t = w"
proof -
  let ?S = "insert (t, w) S"
  have fin: "finite ?S" and ne: "?S \<noteq> {}" using assms(1) by simp_all
  have c: "rcons L ?S" by (rule rcons_insert[OF assms])
  have "lip L (upper L ?S)" by (rule upper_lip[OF fin ne assms(3)])
  moreover have "through ?S (upper L ?S)" by (rule upper_through[OF fin c])
  ultimately show ?thesis
    by (intro exI[of _ "upper L ?S"]) (auto simp: through_def)
qed

text \<open>More samples narrow the envelopes.\<close>

theorem envelope_antitone:
  assumes "finite S'" "S \<subseteq> S'" "S \<noteq> {}"
  shows "lower L S t \<le> lower L S' t" and "upper L S' t \<le> upper L S t"
proof -
  show "lower L S t \<le> lower L S' t"
    unfolding lower_def using assms by (intro Max_mono image_mono) simp_all
  show "upper L S' t \<le> upper L S t"
    unfolding upper_def using assms by (intro Min_antimono image_mono) simp_all
qed


section \<open>Enclosures from samples at integer times\<close>

text \<open>The samples of a factor come from a trace: integer times and rational values. The
  rate bound is a rational. The enclosure of the quantity at a rational time is the pair
  of the two envelopes there, computed by exact rational arithmetic; the signals are
  real-valued, and the enclosure is cast to the reals once, in \<open>adm_in_enc\<close>.\<close>

type_synonym samples = "(int \<times> rat) set"

definition real_samples :: "samples \<Rightarrow> rsamples" where
  "real_samples S = (\<lambda>p. (of_int (fst p), of_rat (snd p))) ` S"

definition adm :: "rat \<Rightarrow> samples \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> bool" where
  "adm L S f \<longleftrightarrow> lip (of_rat L) f \<and> through (real_samples S) f"

definition consistent :: "rat \<Rightarrow> samples \<Rightarrow> bool" where
  "consistent L S \<longleftrightarrow> (\<forall>p \<in> S. \<forall>q \<in> S. \<bar>snd p - snd q\<bar> \<le> L * \<bar>of_int (fst p) - of_int (fst q)\<bar>)"

definition qcone_up :: "rat \<Rightarrow> rat \<Rightarrow> int \<times> rat \<Rightarrow> rat" where
  "qcone_up L t p = snd p + L * \<bar>t - of_int (fst p)\<bar>"

definition qcone_lo :: "rat \<Rightarrow> rat \<Rightarrow> int \<times> rat \<Rightarrow> rat" where
  "qcone_lo L t p = snd p - L * \<bar>t - of_int (fst p)\<bar>"

definition lo :: "rat \<Rightarrow> samples \<Rightarrow> rat \<Rightarrow> rat" where
  "lo L S t = Max (qcone_lo L t ` S)"

definition hi :: "rat \<Rightarrow> samples \<Rightarrow> rat \<Rightarrow> rat" where
  "hi L S t = Min (qcone_up L t ` S)"

definition enc :: "rat \<Rightarrow> samples \<Rightarrow> rat \<Rightarrow> rat \<times> rat" where
  "enc L S t = (lo L S t, hi L S t)"

lemma abs_of_rat_eq: "x = of_rat r \<Longrightarrow> \<bar>x\<bar> = of_rat \<bar>r\<bar>" for x :: real
  by simp

lemma real_samples_finite [simp]: "finite S \<Longrightarrow> finite (real_samples S)"
  by (simp add: real_samples_def)

lemma real_samples_empty [simp]: "real_samples S = {} \<longleftrightarrow> S = {}"
  by (simp add: real_samples_def)

lemma real_samples_mono: "S \<subseteq> S' \<Longrightarrow> real_samples S \<subseteq> real_samples S'"
  by (auto simp: real_samples_def)

lemma consistent_rcons: "consistent L S \<longleftrightarrow> rcons (of_rat L) (real_samples S)"
proof -
  have "(\<bar>snd p - snd q\<bar> \<le> L * \<bar>of_int (fst p) - of_int (fst q)\<bar>) \<longleftrightarrow>
        (\<bar>of_rat (snd p) - of_rat (snd q)\<bar> \<le> of_rat L * \<bar>(of_int (fst p) :: real) - of_int (fst q)\<bar>)"
    for p q :: "int \<times> rat"
  proof -
    have l: "\<bar>of_rat (snd p) - of_rat (snd q)\<bar> = (of_rat \<bar>snd p - snd q\<bar> :: real)"
      by (rule abs_of_rat_eq) (simp add: of_rat_diff)
    have "\<bar>(of_int (fst p) :: real) - of_int (fst q)\<bar> = of_rat \<bar>of_int (fst p) - of_int (fst q)\<bar>"
      by (rule abs_of_rat_eq) (simp add: of_rat_diff)
    then have r: "of_rat L * \<bar>(of_int (fst p) :: real) - of_int (fst q)\<bar>
             = of_rat (L * \<bar>of_int (fst p) - of_int (fst q)\<bar>)"
      by (simp add: of_rat_mult)
    show ?thesis unfolding l r by (rule of_rat_less_eq[symmetric])
  qed
  then show ?thesis by (simp add: consistent_def rcons_def real_samples_def)
qed

lemma consistent_subset: "S \<subseteq> S' \<Longrightarrow> consistent L S' \<Longrightarrow> consistent L S"
  by (auto simp: consistent_def)

lemma abs_of_rat_diff_int: "\<bar>of_rat t - (of_int k :: real)\<bar> = of_rat \<bar>t - of_int k\<bar>"
  by (rule abs_of_rat_eq) (simp add: of_rat_diff)

lemma qcone_up_cast: "of_rat (qcone_up L t p) = cone_up (of_rat L) (of_rat t) (of_int (fst p), of_rat (snd p))"
  by (simp add: qcone_up_def cone_up_def of_rat_add of_rat_mult abs_of_rat_diff_int)

lemma qcone_lo_cast: "of_rat (qcone_lo L t p) = cone_lo (of_rat L) (of_rat t) (of_int (fst p), of_rat (snd p))"
  by (simp add: qcone_lo_def cone_lo_def of_rat_diff of_rat_mult abs_of_rat_diff_int)

lemma mono_of_rat: "mono (of_rat :: rat \<Rightarrow> real)"
  by (simp add: mono_def of_rat_less_eq)

lemma of_rat_nonneg: "0 \<le> q \<Longrightarrow> 0 \<le> (of_rat q :: real)"
  using of_rat_less_eq[of 0 q] by simp

lemma hi_cast:
  assumes "finite S" "S \<noteq> {}"
  shows "of_rat (hi L S t) = upper (of_rat L) (real_samples S) (of_rat t)"
proof -
  have "(of_rat (hi L S t) :: real) = Min (of_rat ` qcone_up L t ` S)"
    unfolding hi_def by (rule mono_Min_commute[OF mono_of_rat]) (simp_all add: assms)
  also have "of_rat ` qcone_up L t ` S = cone_up (of_rat L) (of_rat t) ` real_samples S"
    by (simp add: image_image real_samples_def qcone_up_cast)
  finally show ?thesis by (simp add: upper_def)
qed

lemma lo_cast:
  assumes "finite S" "S \<noteq> {}"
  shows "of_rat (lo L S t) = lower (of_rat L) (real_samples S) (of_rat t)"
proof -
  have "(of_rat (lo L S t) :: real) = Max (of_rat ` qcone_lo L t ` S)"
    unfolding lo_def by (rule mono_Max_commute[OF mono_of_rat]) (simp_all add: assms)
  also have "of_rat ` qcone_lo L t ` S = cone_lo (of_rat L) (of_rat t) ` real_samples S"
    by (simp add: image_image real_samples_def qcone_lo_cast)
  finally show ?thesis by (simp add: lower_def)
qed

text \<open>Every admissible signal lies in the enclosure at every rational time.\<close>

theorem adm_in_enc:
  assumes "finite S" "S \<noteq> {}" "adm L S f"
  shows "of_rat (lo L S t) \<le> f (of_rat t)" and "f (of_rat t) \<le> of_rat (hi L S t)"
  using lower_le_lip[of "real_samples S" "of_rat L" f "of_rat t"]
    lip_le_upper[of "real_samples S" "of_rat L" f "of_rat t"] assms
  by (simp_all add: adm_def lo_cast hi_cast)

text \<open>More samples narrow the enclosure.\<close>

theorem enc_antitone:
  assumes "finite S'" "S \<subseteq> S'" "S \<noteq> {}"
  shows "lo L S t \<le> lo L S' t" and "hi L S' t \<le> hi L S t"
proof -
  show "lo L S t \<le> lo L S' t"
    unfolding lo_def using assms by (intro Max_mono image_mono) simp_all
  show "hi L S' t \<le> hi L S t"
    unfolding hi_def using assms by (intro Min_antimono image_mono) simp_all
qed

text \<open>At the time of a sample of a consistent set the enclosure is the sampled value.\<close>

theorem enc_sample:
  assumes "finite S" "consistent L S" "p \<in> S"
  shows "enc L S (of_int (fst p)) = (snd p, snd p)"
proof -
  have ne: "S \<noteq> {}" using assms(3) by blast
  let ?p = "(of_int (fst p), of_rat (snd p)) :: real \<times> real"
  have pS: "?p \<in> real_samples S" using assms(3) by (auto simp: real_samples_def)
  have c: "rcons (of_rat L) (real_samples S)" using assms(2) by (simp add: consistent_rcons)
  have "of_rat (lo L S (of_int (fst p))) = lower (of_rat L) (real_samples S) (fst ?p)"
    by (simp add: lo_cast[OF assms(1) ne] of_rat_of_int_eq)
  also have "\<dots> = snd ?p" by (rule lower_sample[OF _ c pS]) (simp add: assms(1))
  finally have lo: "lo L S (of_int (fst p)) = snd p" by (simp add: of_rat_eq_iff)
  have "of_rat (hi L S (of_int (fst p))) = upper (of_rat L) (real_samples S) (fst ?p)"
    by (simp add: hi_cast[OF assms(1) ne] of_rat_of_int_eq)
  also have "\<dots> = snd ?p" by (rule upper_sample[OF _ c pS]) (simp add: assms(1))
  finally have hi: "hi L S (of_int (fst p)) = snd p" by (simp add: of_rat_eq_iff)
  show ?thesis by (simp add: enc_def lo hi)
qed

text \<open>For consistent samples under a non-negative bound the enclosure is never empty.\<close>

theorem enc_nonempty:
  assumes "finite S" "S \<noteq> {}" "0 \<le> L" "consistent L S"
  shows "lo L S t \<le> hi L S t"
proof -
  have "lower (of_rat L) (real_samples S) (of_rat t) \<le> upper (of_rat L) (real_samples S) (of_rat t)"
    using assms by (intro lower_le_upper) (simp_all add: of_rat_nonneg consistent_rcons)
  then have "(of_rat (lo L S t) :: real) \<le> of_rat (hi L S t)"
    by (simp add: lo_cast[OF assms(1,2)] hi_cast[OF assms(1,2)])
  then show ?thesis by (simp add: of_rat_less_eq)
qed

text \<open>Non-vacuity: a consistent set of samples has an admissible signal, so the theorems
  about every admissible signal are statements about something. Tightness: every real
  value in the enclosure at a time is the value of an admissible signal there, so the
  enclosure is exactly the set of values the admissible signals take.\<close>

theorem adm_exists:
  assumes "finite S" "0 \<le> L" "consistent L S"
  shows "\<exists>f. adm L S f"
  using rcons_iff_lip[of "real_samples S" "of_rat L"] assms
  by (simp add: adm_def consistent_rcons of_rat_less_eq)

theorem enc_tight:
  assumes "finite S" "S \<noteq> {}" "0 \<le> L" "consistent L S"
    and "of_rat (lo L S t) \<le> w" "w \<le> of_rat (hi L S t)"
  shows "\<exists>f. adm L S f \<and> f (of_rat t) = w"
  using envelope_tight[of "real_samples S" "of_rat L" "of_rat t" w] assms
  by (simp add: adm_def consistent_rcons of_rat_less_eq lo_cast hi_cast)

corollary enc_values:
  assumes "finite S" "S \<noteq> {}" "0 \<le> L" "consistent L S"
  shows "{f (of_rat t) | f. adm L S f} = {w. of_rat (lo L S t) \<le> w \<and> w \<le> of_rat (hi L S t)}"
  using adm_in_enc[OF assms(1,2)] enc_tight[OF assms] by blast

text \<open>The theorem \<open>adm_exists\<close> also says that consistency is exactly admissibility of some
  signal, so a set of samples that no signal under \<open>L\<close> can pass through is detected by
  the executable check.\<close>

theorem consistent_iff_adm:
  assumes "finite S" "0 \<le> L"
  shows "consistent L S \<longleftrightarrow> (\<exists>f. adm L S f)"
  using rcons_iff_lip[of "real_samples S" "of_rat L"] assms
  by (simp add: adm_def consistent_rcons of_rat_less_eq)


section \<open>Interval evaluation\<close>

text \<open>An interval state maps a name to a closed interval of rationals, given by its
  bounds, or to nothing. The point state of a state maps a name with a numeric value to
  the interval of that value alone; a name with a value that is not a number is unmapped,
  like an absent name.\<close>

type_synonym 'n istate = "'n \<rightharpoonup> rat \<times> rat"

definition point :: "('n, atom) state \<Rightarrow> 'n istate" where
  "point \<sigma> x = (case \<sigma> x of None \<Rightarrow> None | Some v \<Rightarrow> (case num_of v of None \<Rightarrow> None | Some q \<Rightarrow> Some (q, q)))"

text \<open>A comparison of two intervals is true when it holds for every pair of values in
  them, false when it fails for every pair, and undefined otherwise.\<close>

definition ilt :: "rat \<times> rat \<Rightarrow> rat \<times> rat \<Rightarrow> bool option" where
  "ilt a b = (if snd a < fst b then Some True else if snd b \<le> fst a then Some False else None)"

definition ile :: "rat \<times> rat \<Rightarrow> rat \<times> rat \<Rightarrow> bool option" where
  "ile a b = (if snd a \<le> fst b then Some True else if snd b < fst a then Some False else None)"

definition ieq :: "rat \<times> rat \<Rightarrow> rat \<times> rat \<Rightarrow> bool option" where
  "ieq a b =
     (if fst a = snd a \<and> fst b = snd b \<and> fst a = fst b then Some True
      else if snd a < fst b \<or> snd b < fst a then Some False else None)"

primrec evalVI :: "('n, atom) vexp \<Rightarrow> 'n istate \<Rightarrow> (rat \<times> rat) option" where
  "evalVI (VConst v) I = (case num_of v of None \<Rightarrow> None | Some q \<Rightarrow> Some (q, q))"
| "evalVI (VName x) I = I x"
| "evalVI (VDefault x a) I = (case I x of Some i \<Rightarrow> Some i | None \<Rightarrow> evalVI a I)"

primrec evalI :: "('n, atom) expr \<Rightarrow> 'n istate \<Rightarrow> bool option" where
  "evalI ETrue I = Some True"
| "evalI EFalse I = Some False"
| "evalI (EEq a b) I =
     (case evalVI a I of None \<Rightarrow> None | Some u \<Rightarrow> (case evalVI b I of None \<Rightarrow> None | Some w \<Rightarrow> ieq u w))"
| "evalI (ELt a b) I =
     (case evalVI a I of None \<Rightarrow> None | Some u \<Rightarrow> (case evalVI b I of None \<Rightarrow> None | Some w \<Rightarrow> ilt u w))"
| "evalI (ELe a b) I =
     (case evalVI a I of None \<Rightarrow> None | Some u \<Rightarrow> (case evalVI b I of None \<Rightarrow> None | Some w \<Rightarrow> ile u w))"
| "evalI (ENot e) I = knot (evalI e I)"
| "evalI (EAnd e\<^sub>1 e\<^sub>2) I = kand (evalI e\<^sub>1 I) (evalI e\<^sub>2 I)"
| "evalI (EOr e\<^sub>1 e\<^sub>2) I = kor (evalI e\<^sub>1 I) (evalI e\<^sub>2 I)"
| "evalI (EImp e\<^sub>1 e\<^sub>2) I = kimp (evalI e\<^sub>1 I) (evalI e\<^sub>2 I)"
| "evalI (EPresent x) I = Some (x \<in> dom I)"


subsection \<open>The point case: the evaluation on states\<close>

text \<open>On a state whose values are numbers, and an expression whose constants are numbers,
  the interval evaluation of the point state is the evaluation of the state: the
  three-valued evaluation of the core is the special case of exact readings.\<close>

definition numeric :: "('n, atom) state \<Rightarrow> bool" where
  "numeric \<sigma> \<longleftrightarrow> (\<forall>x v. \<sigma> x = Some v \<longrightarrow> num_of v \<noteq> None)"

primrec num_vexp :: "('n, atom) vexp \<Rightarrow> bool" where
  "num_vexp (VConst v) = (num_of v \<noteq> None)"
| "num_vexp (VName x) = True"
| "num_vexp (VDefault x a) = num_vexp a"

primrec num_expr :: "('n, atom) expr \<Rightarrow> bool" where
  "num_expr ETrue = True"
| "num_expr EFalse = True"
| "num_expr (EEq a b) = (num_vexp a \<and> num_vexp b)"
| "num_expr (ELt a b) = (num_vexp a \<and> num_vexp b)"
| "num_expr (ELe a b) = (num_vexp a \<and> num_vexp b)"
| "num_expr (ENot e) = num_expr e"
| "num_expr (EAnd e\<^sub>1 e\<^sub>2) = (num_expr e\<^sub>1 \<and> num_expr e\<^sub>2)"
| "num_expr (EOr e\<^sub>1 e\<^sub>2) = (num_expr e\<^sub>1 \<and> num_expr e\<^sub>2)"
| "num_expr (EImp e\<^sub>1 e\<^sub>2) = (num_expr e\<^sub>1 \<and> num_expr e\<^sub>2)"
| "num_expr (EPresent x) = True"

lemma num_of_Some: "num_of v = Some q \<longleftrightarrow> v = ANum q"
  by (cases v) simp_all

lemma numericD:
  assumes "numeric \<sigma>" "\<sigma> x = Some v"
  shows "\<exists>q. v = ANum q"
proof -
  have "num_of v \<noteq> None" using assms unfolding numeric_def by blast
  then show ?thesis by (cases v) simp_all
qed

lemma point_dom: "numeric \<sigma> \<Longrightarrow> dom (point \<sigma>) = dom \<sigma>"
  by (auto simp: point_def numeric_def domIff split: option.splits)

lemma evalVI_point:
  assumes "numeric \<sigma>"
  shows "evalVI a (point \<sigma>) =
           (case evalV a \<sigma> of None \<Rightarrow> None | Some v \<Rightarrow> (case num_of v of None \<Rightarrow> None | Some q \<Rightarrow> Some (q, q)))"
proof (induction a)
  case (VDefault x a)
  show ?case
  proof (cases "\<sigma> x")
    case None
    then show ?thesis using VDefault by (simp add: point_def)
  next
    case (Some v)
    then obtain q where "v = ANum q" using numericD[OF assms] by blast
    with Some show ?thesis by (simp add: point_def)
  qed
qed (simp_all add: point_def)

lemma evalV_numeric:
  assumes "numeric \<sigma>" "num_vexp a" "evalV a \<sigma> = Some v"
  shows "\<exists>q. v = ANum q"
  using assms by (induction a) (auto simp: numeric_def num_of_Some split: option.splits)

lemma ilt_point: "ilt (p, p) (q, q) = Some (p < q)"
  by (simp add: ilt_def)

lemma ile_point: "ile (p, p) (q, q) = Some (p \<le> q)"
  by (simp add: ile_def)

lemma ieq_point: "ieq (p, p) (q, q) = Some (p = q)"
  by (simp add: ieq_def)

theorem evalI_point:
  assumes "numeric \<sigma>" "num_expr e"
  shows "evalI e (point \<sigma>) = eval e \<sigma>"
  using assms(2)
proof (induction e)
  case (EEq a b)
  show ?case
    using evalV_numeric[OF assms(1), of a] evalV_numeric[OF assms(1), of b] EEq
    by (auto simp: evalVI_point[OF assms(1)] ieq_point split: option.splits)
next
  case (ELt a b)
  show ?case
    using evalV_numeric[OF assms(1), of a] evalV_numeric[OF assms(1), of b] ELt
    by (auto simp: evalVI_point[OF assms(1)] ilt_point split: option.splits)
next
  case (ELe a b)
  show ?case
    using evalV_numeric[OF assms(1), of a] evalV_numeric[OF assms(1), of b] ELe
    by (auto simp: evalVI_point[OF assms(1)] ile_point split: option.splits)
qed (simp_all add: point_dom[OF assms(1)])


subsection \<open>Soundness for real values\<close>

text \<open>A signal has real values, so a condition read on signals is evaluated on a real
  valuation: a partial map from names to reals, with the numeric constants of the
  condition cast to the reals, the comparisons of the reals, and the strong Kleene
  connectives. On rational values this reading is the evaluation of the core
  (\<open>evalR_eval\<close>).\<close>

type_synonym 'n rstate = "'n \<rightharpoonup> real"

primrec evalVR :: "('n, atom) vexp \<Rightarrow> 'n rstate \<Rightarrow> real option" where
  "evalVR (VConst v) \<rho> = (case num_of v of None \<Rightarrow> None | Some q \<Rightarrow> Some (of_rat q))"
| "evalVR (VName x) \<rho> = \<rho> x"
| "evalVR (VDefault x a) \<rho> = (case \<rho> x of Some r \<Rightarrow> Some r | None \<Rightarrow> evalVR a \<rho>)"

primrec evalR :: "('n, atom) expr \<Rightarrow> 'n rstate \<Rightarrow> bool option" where
  "evalR ETrue \<rho> = Some True"
| "evalR EFalse \<rho> = Some False"
| "evalR (EEq a b) \<rho> =
     (case evalVR a \<rho> of None \<Rightarrow> None | Some u \<Rightarrow> (case evalVR b \<rho> of None \<Rightarrow> None | Some w \<Rightarrow> Some (u = w)))"
| "evalR (ELt a b) \<rho> =
     (case evalVR a \<rho> of None \<Rightarrow> None | Some u \<Rightarrow> (case evalVR b \<rho> of None \<Rightarrow> None | Some w \<Rightarrow> Some (u < w)))"
| "evalR (ELe a b) \<rho> =
     (case evalVR a \<rho> of None \<Rightarrow> None | Some u \<Rightarrow> (case evalVR b \<rho> of None \<Rightarrow> None | Some w \<Rightarrow> Some (u \<le> w)))"
| "evalR (ENot e) \<rho> = knot (evalR e \<rho>)"
| "evalR (EAnd e\<^sub>1 e\<^sub>2) \<rho> = kand (evalR e\<^sub>1 \<rho>) (evalR e\<^sub>2 \<rho>)"
| "evalR (EOr e\<^sub>1 e\<^sub>2) \<rho> = kor (evalR e\<^sub>1 \<rho>) (evalR e\<^sub>2 \<rho>)"
| "evalR (EImp e\<^sub>1 e\<^sub>2) \<rho> = kimp (evalR e\<^sub>1 \<rho>) (evalR e\<^sub>2 \<rho>)"
| "evalR (EPresent x) \<rho> = Some (x \<in> dom \<rho>)"

text \<open>The real valuation of a state: each numeric value cast to the reals.\<close>

definition real_state :: "('n, atom) state \<Rightarrow> 'n rstate" where
  "real_state \<sigma> x = (case \<sigma> x of None \<Rightarrow> None | Some v \<Rightarrow> (case num_of v of None \<Rightarrow> None | Some q \<Rightarrow> Some (of_rat q)))"

lemma real_state_dom: "numeric \<sigma> \<Longrightarrow> dom (real_state \<sigma>) = dom \<sigma>"
  by (auto simp: real_state_def numeric_def domIff split: option.splits)

lemma evalVR_real_state:
  assumes "numeric \<sigma>"
  shows "evalVR a (real_state \<sigma>) =
           (case evalV a \<sigma> of None \<Rightarrow> None | Some v \<Rightarrow> (case num_of v of None \<Rightarrow> None | Some q \<Rightarrow> Some (of_rat q)))"
proof (induction a)
  case (VDefault x a)
  show ?case
  proof (cases "\<sigma> x")
    case None
    then show ?thesis using VDefault by (simp add: real_state_def)
  next
    case (Some v)
    then obtain q where "v = ANum q" using numericD[OF assms] by blast
    with Some show ?thesis by (simp add: real_state_def)
  qed
qed (simp_all add: real_state_def)

theorem evalR_eval:
  assumes "numeric \<sigma>" "num_expr e"
  shows "evalR e (real_state \<sigma>) = eval e \<sigma>"
  using assms(2)
proof (induction e)
  case (EEq a b)
  show ?case
    using evalV_numeric[OF assms(1), of a] evalV_numeric[OF assms(1), of b] EEq
    by (auto simp: evalVR_real_state[OF assms(1)] of_rat_eq_iff split: option.splits)
next
  case (ELt a b)
  show ?case
    using evalV_numeric[OF assms(1), of a] evalV_numeric[OF assms(1), of b] ELt
    by (auto simp: evalVR_real_state[OF assms(1)] of_rat_less split: option.splits)
next
  case (ELe a b)
  show ?case
    using evalV_numeric[OF assms(1), of a] evalV_numeric[OF assms(1), of b] ELe
    by (auto simp: evalVR_real_state[OF assms(1)] of_rat_less_eq split: option.splits)
qed (simp_all add: real_state_dom[OF assms(1)])

text \<open>A real valuation lies inside an interval state if every name with an interval has
  a value in it.\<close>

definition inside :: "'n istate \<Rightarrow> 'n rstate \<Rightarrow> bool" where
  "inside I \<rho> \<longleftrightarrow> (\<forall>x p q. I x = Some (p, q) \<longrightarrow> (\<exists>r. \<rho> x = Some r \<and> of_rat p \<le> r \<and> r \<le> of_rat q))"

lemma evalVI_inside:
  assumes "inside I \<rho>" "default_free a" "evalVI a I = Some (p, q)"
  shows "\<exists>r. evalVR a \<rho> = Some r \<and> of_rat p \<le> r \<and> r \<le> of_rat q"
  using assms by (cases a) (auto simp: inside_def split: option.splits)

lemma ilt_sound:
  fixes r r' :: real
  assumes "ilt (p, q) (p', q') = Some b" "of_rat p \<le> r" "r \<le> of_rat q" "of_rat p' \<le> r'" "r' \<le> of_rat q'"
  shows "(r < r') = b"
proof (cases b)
  case True
  with assms(1) have "q < p'" by (simp add: ilt_def split: if_splits)
  then have "(of_rat q :: real) < of_rat p'" by (simp add: of_rat_less)
  with assms(3,4) have "r < r'" by linarith
  with True show ?thesis by simp
next
  case False
  with assms(1) have "q' \<le> p" by (simp add: ilt_def split: if_splits)
  then have "(of_rat q' :: real) \<le> of_rat p" by (simp add: of_rat_less_eq)
  with assms(2,5) have "\<not> r < r'" by linarith
  with False show ?thesis by simp
qed

lemma ile_sound:
  fixes r r' :: real
  assumes "ile (p, q) (p', q') = Some b" "of_rat p \<le> r" "r \<le> of_rat q" "of_rat p' \<le> r'" "r' \<le> of_rat q'"
  shows "(r \<le> r') = b"
proof (cases b)
  case True
  with assms(1) have "q \<le> p'" by (simp add: ile_def split: if_splits)
  then have "(of_rat q :: real) \<le> of_rat p'" by (simp add: of_rat_less_eq)
  with assms(3,4) have "r \<le> r'" by linarith
  with True show ?thesis by simp
next
  case False
  with assms(1) have "q' < p" by (simp add: ile_def split: if_splits)
  then have "(of_rat q' :: real) < of_rat p" by (simp add: of_rat_less)
  with assms(2,5) have "\<not> r \<le> r'" by linarith
  with False show ?thesis by simp
qed

lemma ieq_sound:
  fixes r r' :: real
  assumes "ieq (p, q) (p', q') = Some b" "of_rat p \<le> r" "r \<le> of_rat q" "of_rat p' \<le> r'" "r' \<le> of_rat q'"
  shows "(r = r') = b"
proof (cases b)
  case True
  with assms(1) have eq: "p = q" "p' = q'" "p = p'" by (simp_all add: ieq_def split: if_splits)
  then have eq': "p' = q" "q' = q" by simp_all
  have "r = of_rat q" using assms(2,3) eq(1) by (simp add: order_antisym)
  moreover have "r' = of_rat q" using assms(4,5) eq' by (simp add: order_antisym)
  ultimately show ?thesis using True by simp
next
  case False
  with assms(1) have "q < p' \<or> q' < p" by (simp add: ieq_def split: if_splits)
  then have "(of_rat q :: real) < of_rat p' \<or> (of_rat q' :: real) < of_rat p" by (simp add: of_rat_less)
  with assms(2-5) have "r \<noteq> r'" by linarith
  with False show ?thesis by simp
qed

text \<open>Soundness: a definite value of a PRESENT-free condition on an interval state is its
  value on every real valuation inside the intervals.\<close>

theorem evalI_sound:
  assumes "present_free e" "inside I \<rho>"
  shows "evalI e I \<preceq> evalR e \<rho>"
  using assms(1)
proof (induction e)
  case (EEq a b)
  show ?case
  proof (cases "evalI (EEq a b) I")
    case (Some b')
    then obtain p q p' q' where u: "evalVI a I = Some (p, q)" and w: "evalVI b I = Some (p', q')"
      and c: "ieq (p, q) (p', q') = Some b'"
      by (auto split: option.splits)
    from EEq have "default_free a" "default_free b" by simp_all
    with evalVI_inside[OF assms(2) _ u] evalVI_inside[OF assms(2) _ w] obtain r r'
      where rr: "evalVR a \<rho> = Some r" "of_rat p \<le> r" "r \<le> of_rat q"
        and rr': "evalVR b \<rho> = Some r'" "of_rat p' \<le> r'" "r' \<le> of_rat q'" by blast
    from ieq_sound[OF c rr(2,3) rr'(2,3)] rr(1) rr'(1) Some show ?thesis by (simp add: approx_def)
  qed (simp add: approx_def)
next
  case (ELt a b)
  show ?case
  proof (cases "evalI (ELt a b) I")
    case (Some b')
    then obtain p q p' q' where u: "evalVI a I = Some (p, q)" and w: "evalVI b I = Some (p', q')"
      and c: "ilt (p, q) (p', q') = Some b'"
      by (auto split: option.splits)
    from ELt have "default_free a" "default_free b" by simp_all
    with evalVI_inside[OF assms(2) _ u] evalVI_inside[OF assms(2) _ w] obtain r r'
      where rr: "evalVR a \<rho> = Some r" "of_rat p \<le> r" "r \<le> of_rat q"
        and rr': "evalVR b \<rho> = Some r'" "of_rat p' \<le> r'" "r' \<le> of_rat q'" by blast
    from ilt_sound[OF c rr(2,3) rr'(2,3)] rr(1) rr'(1) Some show ?thesis by (simp add: approx_def)
  qed (simp add: approx_def)
next
  case (ELe a b)
  show ?case
  proof (cases "evalI (ELe a b) I")
    case (Some b')
    then obtain p q p' q' where u: "evalVI a I = Some (p, q)" and w: "evalVI b I = Some (p', q')"
      and c: "ile (p, q) (p', q') = Some b'"
      by (auto split: option.splits)
    from ELe have "default_free a" "default_free b" by simp_all
    with evalVI_inside[OF assms(2) _ u] evalVI_inside[OF assms(2) _ w] obtain r r'
      where rr: "evalVR a \<rho> = Some r" "of_rat p \<le> r" "r \<le> of_rat q"
        and rr': "evalVR b \<rho> = Some r'" "of_rat p' \<le> r'" "r' \<le> of_rat q'" by blast
    from ile_sound[OF c rr(2,3) rr'(2,3)] rr(1) rr'(1) Some show ?thesis by (simp add: approx_def)
  qed (simp add: approx_def)
qed (simp_all add: knot_mono kand_mono kor_mono kimp_mono)

corollary evalI_sound_value:
  assumes "present_free e" "inside I \<rho>" "evalI e I = Some b"
  shows "evalR e \<rho> = Some b"
  using evalI_sound[OF assms(1,2)] assms(3) by (simp add: approx_def)


subsection \<open>Monotonicity under narrowing\<close>

text \<open>An interval state narrows to another if every name with an interval keeps an
  interval inside it: the interval form of the information order. A definite value of a
  PRESENT-free condition survives narrowing.\<close>

definition narrows :: "'n istate \<Rightarrow> 'n istate \<Rightarrow> bool" where
  "narrows I I' \<longleftrightarrow> (\<forall>x p q. I x = Some (p, q) \<longrightarrow> (\<exists>p' q'. I' x = Some (p', q') \<and> p \<le> p' \<and> q' \<le> q))"

lemma narrows_refl: "narrows I I"
  by (simp add: narrows_def)

lemma narrows_trans: "narrows I I' \<Longrightarrow> narrows I' I'' \<Longrightarrow> narrows I I''"
  unfolding narrows_def by (meson order_trans)

lemma evalVI_narrows:
  assumes "narrows I I'" "default_free a" "evalVI a I = Some (p, q)"
  shows "\<exists>p' q'. evalVI a I' = Some (p', q') \<and> p \<le> p' \<and> q' \<le> q"
  using assms by (cases a) (auto simp: narrows_def split: option.splits)

lemma ilt_narrows:
  assumes "ilt (p, q) (p', q') = Some b" "p \<le> u" "u \<le> v" "v \<le> q" "p' \<le> u'" "u' \<le> v'" "v' \<le> q'"
  shows "ilt (u, v) (u', v') = Some b"
proof (cases b)
  case True
  with assms(1) have "q < p'" by (simp add: ilt_def split: if_splits)
  with assms(4,5) have "v < u'" by linarith
  with True show ?thesis by (simp add: ilt_def)
next
  case False
  with assms(1) have "\<not> q < p'" "q' \<le> p" by (simp_all add: ilt_def split: if_splits)
  with assms(2-7) have "\<not> v < u'" "v' \<le> u" by linarith+
  with False show ?thesis by (simp add: ilt_def)
qed

lemma ile_narrows:
  assumes "ile (p, q) (p', q') = Some b" "p \<le> u" "u \<le> v" "v \<le> q" "p' \<le> u'" "u' \<le> v'" "v' \<le> q'"
  shows "ile (u, v) (u', v') = Some b"
proof (cases b)
  case True
  with assms(1) have "q \<le> p'" by (simp add: ile_def split: if_splits)
  with assms(4,5) have "v \<le> u'" by linarith
  with True show ?thesis by (simp add: ile_def)
next
  case False
  with assms(1) have "\<not> q \<le> p'" "q' < p" by (simp_all add: ile_def split: if_splits)
  with assms(2-7) have "\<not> v \<le> u'" "v' < u" by linarith+
  with False show ?thesis by (simp add: ile_def)
qed

lemma ieq_narrows:
  assumes "ieq (p, q) (p', q') = Some b" "p \<le> u" "u \<le> v" "v \<le> q" "p' \<le> u'" "u' \<le> v'" "v' \<le> q'"
  shows "ieq (u, v) (u', v') = Some b"
  using assms by (auto simp: ieq_def split: if_splits)

text \<open>Narrowing an interval to an empty one would make \<open>=\<close> jump from undefined to true, so
  monotonicity is stated for interval states whose intervals are non-empty.\<close>

definition proper :: "'n istate \<Rightarrow> bool" where
  "proper I \<longleftrightarrow> (\<forall>x p q. I x = Some (p, q) \<longrightarrow> p \<le> q)"

lemma evalVI_proper:
  assumes "proper I" "default_free a" "evalVI a I = Some (p, q)"
  shows "p \<le> q"
  using assms by (cases a) (auto simp: proper_def split: option.splits)

theorem evalI_mono:
  assumes "present_free e" "narrows I I'" "proper I'"
  shows "evalI e I \<preceq> evalI e I'"
  using assms(1)
proof (induction e)
  case (EEq a b)
  show ?case
  proof (cases "evalI (EEq a b) I")
    case (Some b')
    then obtain p q p' q' where u: "evalVI a I = Some (p, q)" and w: "evalVI b I = Some (p', q')"
      and c: "ieq (p, q) (p', q') = Some b'"
      by (auto split: option.splits)
    from EEq have df: "default_free a" "default_free b" by simp_all
    from evalVI_narrows[OF assms(2) df(1) u] evalVI_narrows[OF assms(2) df(2) w] obtain u1 v1 u2 v2
      where n1: "evalVI a I' = Some (u1, v1)" "p \<le> u1" "v1 \<le> q"
        and n2: "evalVI b I' = Some (u2, v2)" "p' \<le> u2" "v2 \<le> q'" by blast
    have "u1 \<le> v1" "u2 \<le> v2" using evalVI_proper[OF assms(3) df(1) n1(1)] evalVI_proper[OF assms(3) df(2) n2(1)] .
    with ieq_narrows[OF c n1(2) _ n1(3) n2(2) _ n2(3)] n1(1) n2(1) Some show ?thesis by (simp add: approx_def)
  qed (simp add: approx_def)
next
  case (ELt a b)
  show ?case
  proof (cases "evalI (ELt a b) I")
    case (Some b')
    then obtain p q p' q' where u: "evalVI a I = Some (p, q)" and w: "evalVI b I = Some (p', q')"
      and c: "ilt (p, q) (p', q') = Some b'"
      by (auto split: option.splits)
    from ELt have df: "default_free a" "default_free b" by simp_all
    from evalVI_narrows[OF assms(2) df(1) u] evalVI_narrows[OF assms(2) df(2) w] obtain u1 v1 u2 v2
      where n1: "evalVI a I' = Some (u1, v1)" "p \<le> u1" "v1 \<le> q"
        and n2: "evalVI b I' = Some (u2, v2)" "p' \<le> u2" "v2 \<le> q'" by blast
    have "u1 \<le> v1" "u2 \<le> v2" using evalVI_proper[OF assms(3) df(1) n1(1)] evalVI_proper[OF assms(3) df(2) n2(1)] .
    with ilt_narrows[OF c n1(2) _ n1(3) n2(2) _ n2(3)] n1(1) n2(1) Some show ?thesis by (simp add: approx_def)
  qed (simp add: approx_def)
next
  case (ELe a b)
  show ?case
  proof (cases "evalI (ELe a b) I")
    case (Some b')
    then obtain p q p' q' where u: "evalVI a I = Some (p, q)" and w: "evalVI b I = Some (p', q')"
      and c: "ile (p, q) (p', q') = Some b'"
      by (auto split: option.splits)
    from ELe have df: "default_free a" "default_free b" by simp_all
    from evalVI_narrows[OF assms(2) df(1) u] evalVI_narrows[OF assms(2) df(2) w] obtain u1 v1 u2 v2
      where n1: "evalVI a I' = Some (u1, v1)" "p \<le> u1" "v1 \<le> q"
        and n2: "evalVI b I' = Some (u2, v2)" "p' \<le> u2" "v2 \<le> q'" by blast
    have "u1 \<le> v1" "u2 \<le> v2" using evalVI_proper[OF assms(3) df(1) n1(1)] evalVI_proper[OF assms(3) df(2) n2(1)] .
    with ile_narrows[OF c n1(2) _ n1(3) n2(2) _ n2(3)] n1(1) n2(1) Some show ?thesis by (simp add: approx_def)
  qed (simp add: approx_def)
qed (simp_all add: knot_mono kand_mono kor_mono kimp_mono)

text \<open>The monitor on an interval state blocks unless the condition is known to be false,
  as \<open>blocks\<close> does on a state.\<close>

definition blocksI :: "('n, atom) expr \<Rightarrow> 'n istate \<Rightarrow> bool" where
  "blocksI c I \<longleftrightarrow> evalI c I \<noteq> Some False"

theorem blocksI_point: "numeric \<sigma> \<Longrightarrow> num_expr c \<Longrightarrow> blocksI c (point \<sigma>) \<longleftrightarrow> blocks c \<sigma>"
  by (simp add: blocksI_def blocks_def evalI_point)


section \<open>Enclosures on a trace\<close>

text \<open>The rate bounds are a partial map \<open>R\<close> from names to rational bounds: \<open>R x = Some L\<close>
  declares the bound \<open>L\<close> on the quantity behind \<open>x\<close>. The samples of \<open>x\<close> up to entry \<open>j\<close>
  are the numeric values of \<open>x\<close> at the entries up to \<open>j\<close> whose event is an arrival of
  \<open>x\<close>, each with the time of its entry: the reading of arrivals of \<open>fresh\<close>. A value present
  without an arrival is not a sample.\<close>

definition samples :: "('n, atom, 's, 'a) itrace \<Rightarrow> nat \<Rightarrow> 'n \<Rightarrow> samples" where
  "samples \<pi> j x = {(time \<pi> i, q) | i q. i \<le> j \<and> evt (\<pi> ! i) = Arrival x \<and> st \<pi> i x = Some (ANum q)}"

lemma samples_finite: "finite (samples \<pi> j x)"
proof -
  have "samples \<pi> j x \<subseteq> (\<lambda>i. (time \<pi> i, the (num_of (the (st \<pi> i x))))) ` {..j}"
    by (auto simp: samples_def)
  then show ?thesis by (rule finite_subset) simp
qed

lemma samples_mono:
  assumes "i \<le> j"
  shows "samples \<pi> i x \<subseteq> samples \<pi> j x"
proof
  fix p assume "p \<in> samples \<pi> i x"
  then obtain k q where p: "p = (time \<pi> k, q)" "k \<le> i" "evt (\<pi> ! k) = Arrival x" "st \<pi> k x = Some (ANum q)"
    unfolding samples_def by blast
  from p(2) assms have "k \<le> j" by simp
  with p(1,3,4) show "p \<in> samples \<pi> j x" unfolding samples_def by blast
qed

lemma samples_append: "j < length \<pi> \<Longrightarrow> samples (\<pi> @ \<rho>) j x = samples \<pi> j x"
  by (auto simp: samples_def st_def nth_append)

lemma samples_arrival:
  "i \<le> j \<Longrightarrow> evt (\<pi> ! i) = Arrival x \<Longrightarrow> st \<pi> i x = Some (ANum q) \<Longrightarrow> (time \<pi> i, q) \<in> samples \<pi> j x"
  by (auto simp: samples_def)

text \<open>The interval state of entry \<open>j\<close>, read at a rational time \<open>t\<close>: for a name with a rate
  bound and at least one sample, the enclosure at \<open>t\<close> of its samples up to \<open>j\<close>; for a
  name with a bound and no sample, nothing; for a name without a bound, the point of its
  value at \<open>j\<close>. The interval state of entry \<open>j\<close> is read at the time of the entry.\<close>

definition enclosed_at :: "('n \<Rightarrow> rat option) \<Rightarrow> ('n, atom, 's, 'a) itrace \<Rightarrow> nat \<Rightarrow> rat \<Rightarrow> 'n istate" where
  "enclosed_at R \<pi> j t x =
     (case R x of
        None \<Rightarrow> point (st \<pi> j) x
      | Some L \<Rightarrow> if samples \<pi> j x = {} then None else Some (enc L (samples \<pi> j x) t))"

definition enclosed :: "('n \<Rightarrow> rat option) \<Rightarrow> ('n, atom, 's, 'a) itrace \<Rightarrow> nat \<Rightarrow> 'n istate" where
  "enclosed R \<pi> j = enclosed_at R \<pi> j (of_int (time \<pi> j))"

text \<open>Without rate bounds the interval state is the point state of the entry.\<close>

theorem enclosed_no_bounds: "enclosed (\<lambda>_. None) \<pi> j = point (st \<pi> j)"
  by (simp add: enclosed_def enclosed_at_def fun_eq_iff)

text \<open>Finality of the interval states: the samples up to an entry are those of every
  longer trace, so appending entries changes no interval state of the prefix.\<close>

theorem enclosed_at_append: "j < length \<pi> \<Longrightarrow> enclosed_at R (\<pi> @ \<rho>) j t = enclosed_at R \<pi> j t"
  by (simp add: enclosed_at_def samples_append fun_eq_iff split: option.splits)

theorem enclosed_append: "j < length \<pi> \<Longrightarrow> enclosed R (\<pi> @ \<rho>) j = enclosed R \<pi> j"
  by (simp add: enclosed_def enclosed_at_append)

text \<open>Consistency of the samples with the bounds, up to an entry and on a whole trace. A
  prefix of a consistent trace is consistent.\<close>

definition consistent_upto :: "('n \<Rightarrow> rat option) \<Rightarrow> ('n, atom, 's, 'a) itrace \<Rightarrow> nat \<Rightarrow> bool" where
  "consistent_upto R \<pi> j \<longleftrightarrow> (\<forall>x L. R x = Some L \<longrightarrow> consistent L (samples \<pi> j x))"

definition consistent_trace :: "('n \<Rightarrow> rat option) \<Rightarrow> ('n, atom, 's, 'a) itrace \<Rightarrow> bool" where
  "consistent_trace R \<pi> \<longleftrightarrow> consistent_upto R \<pi> (length \<pi> - 1)"

lemma consistent_upto_mono:
  assumes "i \<le> j" "consistent_upto R \<pi> j"
  shows "consistent_upto R \<pi> i"
  unfolding consistent_upto_def
proof (intro allI impI)
  fix x L assume "R x = Some L"
  with assms(2) have "consistent L (samples \<pi> j x)" by (simp add: consistent_upto_def)
  then show "consistent L (samples \<pi> i x)" by (rule consistent_subset[OF samples_mono[OF assms(1)]])
qed

lemma consistent_trace_upto:
  assumes "consistent_trace R \<pi>" "j < length \<pi>"
  shows "consistent_upto R \<pi> j"
proof -
  have "j \<le> length \<pi> - 1" using assms(2) by arith
  moreover have "consistent_upto R \<pi> (length \<pi> - 1)" using assms(1) by (simp add: consistent_trace_def)
  ultimately show ?thesis by (rule consistent_upto_mono)
qed

text \<open>At an arrival of \<open>x\<close> with consistent samples the interval of \<open>x\<close> is the point of its
  value, as in the point state: at sample times the readings on enclosures agree with the
  readings on states for that name.\<close>

theorem enclosed_at_sample:
  assumes "R x = Some L" "consistent_upto R \<pi> j" "evt (\<pi> ! j) = Arrival x" "st \<pi> j x = Some (ANum q)"
  shows "enclosed R \<pi> j x = Some (q, q)" and "enclosed R \<pi> j x = point (st \<pi> j) x"
proof -
  have p: "(time \<pi> j, q) \<in> samples \<pi> j x" using assms(3,4) by (rule samples_arrival[OF order_refl])
  have c: "consistent L (samples \<pi> j x)" using assms(1,2) by (simp add: consistent_upto_def)
  from enc_sample[OF samples_finite c p] have "enc L (samples \<pi> j x) (of_int (time \<pi> j)) = (q, q)"
    by simp
  with p assms(1) show "enclosed R \<pi> j x = Some (q, q)"
    by (auto simp: enclosed_def enclosed_at_def)
  then show "enclosed R \<pi> j x = point (st \<pi> j) x" using assms(4) by (simp add: point_def)
qed


section \<open>Soundness for every admissible signal\<close>

text \<open>A family of signals, one per name, is admissible at entry \<open>j\<close> if the signal of
  every name with a rate bound is admissible for its samples up to \<open>j\<close>. The real valuation
  it induces at time \<open>t\<close> reads each name with a bound from its signal, and each other name
  from the state of entry \<open>j\<close>.\<close>

definition adm_family :: "('n \<Rightarrow> rat option) \<Rightarrow> ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> ('n, atom, 's, 'a) itrace \<Rightarrow> nat \<Rightarrow> bool" where
  "adm_family R F \<pi> j \<longleftrightarrow> (\<forall>x L. R x = Some L \<longrightarrow> adm L (samples \<pi> j x) (F x))"

definition signal_state :: "('n \<Rightarrow> rat option) \<Rightarrow> ('n \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> ('n, atom, 's, 'a) itrace \<Rightarrow> nat
    \<Rightarrow> real \<Rightarrow> 'n rstate" where
  "signal_state R F \<pi> j t x = (case R x of None \<Rightarrow> real_state (st \<pi> j) x | Some L \<Rightarrow> Some (F x t))"

text \<open>The induced valuation at the time of the entry lies inside the interval state of
  the entry: the enclosure part is \<open>adm_in_enc\<close>, the rest is the point state.\<close>

lemma point_inside_real_state: "point \<sigma> x = Some (p, q) \<Longrightarrow> real_state \<sigma> x = Some (of_rat p) \<and> p = q"
  by (auto simp: point_def real_state_def split: option.splits)

theorem enclosed_inside:
  assumes "adm_family R F \<pi> j"
  shows "inside (enclosed R \<pi> j) (signal_state R F \<pi> j (of_int (time \<pi> j)))"
  unfolding inside_def
proof (intro allI impI)
  fix x p q assume e: "enclosed R \<pi> j x = Some (p, q)"
  show "\<exists>r. signal_state R F \<pi> j (of_int (time \<pi> j)) x = Some r \<and> of_rat p \<le> r \<and> r \<le> of_rat q"
  proof (cases "R x")
    case None
    with e have "point (st \<pi> j) x = Some (p, q)" by (simp add: enclosed_def enclosed_at_def)
    with None show ?thesis by (auto simp: signal_state_def dest: point_inside_real_state)
  next
    case (Some L)
    with e have ne: "samples \<pi> j x \<noteq> {}" and pq: "enc L (samples \<pi> j x) (of_int (time \<pi> j)) = (p, q)"
      by (auto simp: enclosed_def enclosed_at_def split: if_splits)
    have a: "adm L (samples \<pi> j x) (F x)" using assms Some by (simp add: adm_family_def)
    from adm_in_enc[OF samples_finite ne a, of "of_int (time \<pi> j)"] pq Some show ?thesis
      by (auto simp: signal_state_def enc_def of_rat_of_int_eq)
  qed
qed

text \<open>So a definite value of a PRESENT-free condition on the interval state of an entry is
  its value for every admissible family of signals at the time of the entry.\<close>

theorem evalI_sound_signals:
  assumes "present_free c" "adm_family R F \<pi> j" "evalI c (enclosed R \<pi> j) = Some b"
  shows "evalR c (signal_state R F \<pi> j (of_int (time \<pi> j))) = Some b"
  by (rule evalI_sound_value[OF assms(1) enclosed_inside[OF assms(2)] assms(3)])

text \<open>Non-vacuity on a trace: with consistent samples and non-negative bounds there is an
  admissible family.\<close>

definition bounds_nonneg :: "('n \<Rightarrow> rat option) \<Rightarrow> bool" where
  "bounds_nonneg R \<longleftrightarrow> (\<forall>x L. R x = Some L \<longrightarrow> 0 \<le> L)"

theorem adm_family_exists:
  assumes "bounds_nonneg R" "consistent_upto R \<pi> j"
  shows "\<exists>F. adm_family R F \<pi> j"
proof -
  have ex: "\<exists>f. adm L (samples \<pi> j x) f" if "R x = Some L" for x L
    using assms that by (intro adm_exists[OF samples_finite]) (simp_all add: bounds_nonneg_def consistent_upto_def)
  have "adm_family R (\<lambda>x. SOME f. adm (the (R x)) (samples \<pi> j x) f) \<pi> j"
    unfolding adm_family_def
  proof (intro allI impI)
    fix x L assume R: "R x = Some L"
    from someI_ex[OF ex[OF R]] show "adm L (samples \<pi> j x) (SOME f. adm (the (R x)) (samples \<pi> j x) f)"
      by (simp add: R)
  qed
  then show ?thesis by blast
qed


subsection \<open>The monitor and the verdict of a prohibition\<close>

text \<open>The monitor of \<open>s MUST_NOT a WHEN c\<close> on enclosures reads, before an action at entry
  \<open>j\<close>, the interval state of entry \<open>j - 1\<close> at the time of that entry, from the samples up
  to it, as \<open>blocked_action\<close> reads the state of entry \<open>j - 1\<close>. It blocks the action unless
  \<open>c\<close> is false on that interval state. The verdict records a breach at the first action
  before which \<open>c\<close> is true on the interval state.\<close>

definition blocked_actionI :: "('n \<Rightarrow> rat option) \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> ('n, atom) expr \<Rightarrow> ('n, atom, 's, 'a) itrace \<Rightarrow> nat \<Rightarrow> bool" where
  "blocked_actionI R s a c \<pi> j \<longleftrightarrow>
     1 \<le> j \<and> j < length \<pi> \<and> does s a (evt (\<pi> ! j)) \<and> blocksI c (enclosed R \<pi> (j - 1))"

definition forbiddenI :: "('n \<Rightarrow> rat option) \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> ('n, atom) expr \<Rightarrow> ('n, atom, 's, 'a) itrace \<Rightarrow> nat \<Rightarrow> bool" where
  "forbiddenI R s a c \<pi> j \<longleftrightarrow>
     1 \<le> j \<and> j < length \<pi> \<and> does s a (evt (\<pi> ! j)) \<and> evalI c (enclosed R \<pi> (j - 1)) = Some True"

definition pr_verdictI :: "('n \<Rightarrow> rat option) \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> ('n, atom) expr \<Rightarrow> ('n, atom, 's, 'a) itrace \<Rightarrow> verdict" where
  "pr_verdictI R s a c \<pi> =
     (if \<exists>j. forbiddenI R s a c \<pi> j then Breached (time \<pi> (LEAST j. forbiddenI R s a c \<pi> j)) else Pending)"

definition monitor_decisionsI :: "('n \<Rightarrow> rat option) \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> ('n, atom) expr \<Rightarrow> ('n, atom, 's, 'a) itrace
    \<Rightarrow> (nat \<times> bool) list" where
  "monitor_decisionsI R s a c \<pi> =
     map (\<lambda>j. (j, blocksI c (enclosed R \<pi> (j - 1)))) (filter (\<lambda>j. does s a (evt (\<pi> ! j))) [1..<length \<pi>])"

text \<open>What the monitor allows is false for every admissible family of signals at the time
  of the entry before the action; the condition of a breach is true for every admissible
  family there. These are the analogues of \<open>monitor_sound_completions\<close> and
  \<open>breach_certain_completions\<close>, with the signals through the samples in place of the
  completions of the data.\<close>

theorem monitor_sound_signals:
  assumes "present_free c" and j: "1 \<le> j" "j < length \<pi>" and "does s a (evt (\<pi> ! j))"
    and "\<not> blocked_actionI R s a c \<pi> j" and "adm_family R F \<pi> (j - 1)"
  shows "evalR c (signal_state R F \<pi> (j - 1) (of_int (time \<pi> (j - 1)))) = Some False"
proof -
  have "evalI c (enclosed R \<pi> (j - 1)) = Some False"
    using assms(2-5) by (simp add: blocked_actionI_def blocksI_def)
  from evalI_sound_signals[OF assms(1,6) this] show ?thesis .
qed

theorem breach_certain_signals:
  assumes "present_free c" "forbiddenI R s a c \<pi> j" "adm_family R F \<pi> (j - 1)"
  shows "evalR c (signal_state R F \<pi> (j - 1) (of_int (time \<pi> (j - 1)))) = Some True"
proof -
  have "evalI c (enclosed R \<pi> (j - 1)) = Some True" using assms(2) by (simp add: forbiddenI_def)
  from evalI_sound_signals[OF assms(1,3) this] show ?thesis .
qed

text \<open>Without rate bounds the monitor and the verdict are those of the core, on numeric
  data and a numeric condition.\<close>

theorem blocked_actionI_no_bounds:
  assumes "\<And>i. i < length \<pi> \<Longrightarrow> numeric (st \<pi> i)" "num_expr c"
  shows "blocked_actionI (\<lambda>_. None) s a c \<pi> j \<longleftrightarrow> blocked_action s a c \<pi> j"
  using assms by (auto simp: blocked_actionI_def blocked_action_def enclosed_no_bounds blocksI_point)

theorem forbiddenI_no_bounds:
  assumes "\<And>i. i < length \<pi> \<Longrightarrow> numeric (st \<pi> i)" "num_expr c"
  shows "forbiddenI (\<lambda>_. None) s a c \<pi> j \<longleftrightarrow> forbidden s a c \<pi> j"
  using assms by (auto simp: forbiddenI_def forbidden_def enclosed_no_bounds evalI_point)

theorem pr_verdictI_no_bounds:
  assumes "\<And>i. i < length \<pi> \<Longrightarrow> numeric (st \<pi> i)" "num_expr c"
  shows "pr_verdictI (\<lambda>_. None) s a c \<pi> = pr_verdict s a c \<pi>"
proof -
  have "forbiddenI (\<lambda>_. None) s a c \<pi> = forbidden s a c \<pi>"
    by (rule ext) (rule forbiddenI_no_bounds[OF assms])
  then show ?thesis by (simp add: pr_verdictI_def pr_verdict_def)
qed


subsection \<open>Finality of the monitor and of the verdict\<close>

lemma forbiddenI_append:
  "j < length \<pi> \<Longrightarrow> forbiddenI R s a c (\<pi> @ \<rho>) j \<longleftrightarrow> forbiddenI R s a c \<pi> j"
  by (auto simp: forbiddenI_def nth_append enclosed_append)

lemma forbiddenI_less: "forbiddenI R s a c \<pi> j \<Longrightarrow> j < length \<pi>"
  by (simp add: forbiddenI_def)

theorem pr_verdictI_final:
  assumes "pr_verdictI R s a c \<pi> \<noteq> Pending"
  shows "pr_verdictI R s a c (\<pi> @ \<rho>) = pr_verdictI R s a c \<pi>"
proof -
  from assms obtain j where j: "forbiddenI R s a c \<pi> j" by (auto simp: pr_verdictI_def split: if_splits)
  define k where "k = (LEAST j. forbiddenI R s a c \<pi> j)"
  have fk: "forbiddenI R s a c \<pi> k" unfolding k_def using j by (rule LeastI)
  have kl: "k < length \<pi>" using fk by (rule forbiddenI_less)
  have least: "(LEAST j. forbiddenI R s a c (\<pi> @ \<rho>) j) = k"
  proof (rule Least_equality)
    show "forbiddenI R s a c (\<pi> @ \<rho>) k" using fk kl by (simp add: forbiddenI_append)
  next
    fix y assume y: "forbiddenI R s a c (\<pi> @ \<rho>) y"
    show "k \<le> y"
    proof (rule ccontr)
      assume "\<not> k \<le> y"
      then have "y < k" by simp
      with kl y have "forbiddenI R s a c \<pi> y" by (simp add: forbiddenI_append)
      then have "k \<le> y" unfolding k_def by (rule Least_le)
      with \<open>y < k\<close> show False by simp
    qed
  qed
  have ex: "\<exists>j. forbiddenI R s a c (\<pi> @ \<rho>) j"
    by (intro exI[of _ k]) (simp add: forbiddenI_append[OF kl] fk)
  have "pr_verdictI R s a c (\<pi> @ \<rho>) = Breached (time (\<pi> @ \<rho>) k)"
    using ex least by (simp add: pr_verdictI_def)
  also have "\<dots> = Breached (time \<pi> k)" using kl by simp
  also have "\<dots> = pr_verdictI R s a c \<pi>" using j by (auto simp: pr_verdictI_def k_def)
  finally show ?thesis .
qed

theorem monitor_decisionsI_append:
  "\<exists>ds. monitor_decisionsI R s a c (\<pi> @ \<rho>) = monitor_decisionsI R s a c \<pi> @ ds"
proof (cases "\<pi> = []")
  case True
  then show ?thesis by (simp add: monitor_decisionsI_def)
next
  case False
  then have l1: "1 \<le> length \<pi>" by (cases \<pi>) simp_all
  have u: "[1..<length (\<pi> @ \<rho>)] = [1..<length \<pi>] @ [length \<pi>..<length \<pi> + length \<rho>]"
    unfolding length_append by (rule upt_add_eq_append[OF l1])
  have f: "filter (\<lambda>j. does s a (evt ((\<pi> @ \<rho>) ! j))) [1..<length \<pi>]
           = filter (\<lambda>j. does s a (evt (\<pi> ! j))) [1..<length \<pi>]"
    by (rule filter_cong) simp_all
  have m: "map (\<lambda>j. (j, blocksI c (enclosed R (\<pi> @ \<rho>) (j - 1)))) (filter (\<lambda>j. does s a (evt (\<pi> ! j))) [1..<length \<pi>])
           = map (\<lambda>j. (j, blocksI c (enclosed R \<pi> (j - 1)))) (filter (\<lambda>j. does s a (evt (\<pi> ! j))) [1..<length \<pi>])"
    by (rule map_cong) (auto simp: enclosed_append less_imp_diff_less)
  show ?thesis
    unfolding monitor_decisionsI_def u filter_append map_append f m by blast
qed


section \<open>Invariants on enclosures\<close>

text \<open>\<open>ALWAYS\<close>, \<open>EVENTUALLY\<close> and \<open>NEXT\<close>, and \<open>EVENTUALLY \<dots> WITHIN\<close> with a resolved deadline,
  read on the interval states of the entries as \<open>inv_eval\<close> and \<open>ew_eval\<close> read the
  states.\<close>

fun inv_evalI :: "('n \<Rightarrow> rat option) \<Rightarrow> ('n, atom) inv \<Rightarrow> ('n, atom, 's, 'a) itrace \<Rightarrow> bool option" where
  "inv_evalI R (Always \<phi>) \<pi> =
     (if \<exists>j < length \<pi>. evalI \<phi> (enclosed R \<pi> j) = Some False then Some False else None)"
| "inv_evalI R (Eventually \<phi>) \<pi> =
     (if \<exists>j < length \<pi>. evalI \<phi> (enclosed R \<pi> j) = Some True then Some True else None)"
| "inv_evalI R (Next \<phi>) \<pi> = (if 1 < length \<pi> then evalI \<phi> (enclosed R \<pi> 1) else None)"

definition ew_evalI :: "('n \<Rightarrow> rat option) \<Rightarrow> ('n, atom) expr \<Rightarrow> int \<Rightarrow> ('n, atom, 's, 'a) itrace \<Rightarrow> bool option" where
  "ew_evalI R \<phi> D \<pi> =
     (if \<exists>j < length \<pi>. time \<pi> j \<le> D \<and> evalI \<phi> (enclosed R \<pi> j) = Some True then Some True
      else if passed D \<pi> \<and> (\<forall>j < length \<pi>. time \<pi> j \<le> D \<longrightarrow> evalI \<phi> (enclosed R \<pi> j) = Some False)
      then Some False
      else None)"

text \<open>Without rate bounds, on numeric data, they are the invariants of the core.\<close>

lemma evalI_point_entry:
  assumes "numeric (st \<pi> j)" "num_expr \<phi>"
  shows "evalI \<phi> (enclosed (\<lambda>_. None) \<pi> j) = eval \<phi> (st \<pi> j)"
  unfolding enclosed_no_bounds by (rule evalI_point[OF assms])

theorem inv_evalI_no_bounds:
  assumes "\<And>i. i < length \<pi> \<Longrightarrow> numeric (st \<pi> i)" "num_expr (inv_formula \<iota>)"
  shows "inv_evalI (\<lambda>_. None) \<iota> \<pi> = inv_eval \<iota> \<pi>"
proof (cases \<iota>)
  case (Always \<phi>)
  with assms(2) have f: "num_expr \<phi>" by simp
  show ?thesis unfolding Always by (simp cong: conj_cong add: evalI_point_entry[OF assms(1) f])
next
  case (Eventually \<phi>)
  with assms(2) have f: "num_expr \<phi>" by simp
  show ?thesis unfolding Eventually by (simp cong: conj_cong add: evalI_point_entry[OF assms(1) f])
next
  case (Next \<phi>)
  with assms(2) have f: "num_expr \<phi>" by simp
  show ?thesis
  proof (cases "1 < length \<pi>")
    case True
    with evalI_point_entry[OF assms(1) f, of 1] Next show ?thesis by simp
  next
    case False
    with Next show ?thesis by simp
  qed
qed

theorem ew_evalI_no_bounds:
  assumes "\<And>i. i < length \<pi> \<Longrightarrow> numeric (st \<pi> i)" "num_expr \<phi>"
  shows "ew_evalI (\<lambda>_. None) \<phi> D \<pi> = ew_eval \<phi> D \<pi>"
  unfolding ew_evalI_def ew_eval_def
  by (simp cong: conj_cong imp_cong add: evalI_point_entry[OF assms(1) assms(2)])

text \<open>The verdicts are sound for every admissible family at the entries that decide them:
  \<open>ALWAYS\<close> is false only at an entry where every admissible family violates the formula,
  \<open>EVENTUALLY\<close> and \<open>EVENTUALLY \<dots> WITHIN\<close> are true only at an entry where every admissible
  family satisfies it.\<close>

theorem always_false_signals:
  assumes "present_free \<phi>" "inv_evalI R (Always \<phi>) \<pi> = Some False"
  shows "\<exists>j < length \<pi>. \<forall>F. adm_family R F \<pi> j \<longrightarrow> evalR \<phi> (signal_state R F \<pi> j (of_int (time \<pi> j))) = Some False"
proof -
  from assms(2) obtain j where "j < length \<pi>" "evalI \<phi> (enclosed R \<pi> j) = Some False"
    by (auto split: if_splits)
  with evalI_sound_signals[OF assms(1)] show ?thesis by blast
qed

theorem eventually_true_signals:
  assumes "present_free \<phi>" "inv_evalI R (Eventually \<phi>) \<pi> = Some True"
  shows "\<exists>j < length \<pi>. \<forall>F. adm_family R F \<pi> j \<longrightarrow> evalR \<phi> (signal_state R F \<pi> j (of_int (time \<pi> j))) = Some True"
proof -
  from assms(2) obtain j where "j < length \<pi>" "evalI \<phi> (enclosed R \<pi> j) = Some True"
    by (auto split: if_splits)
  with evalI_sound_signals[OF assms(1)] show ?thesis by blast
qed

theorem ew_true_signals:
  assumes "present_free \<phi>" "ew_evalI R \<phi> D \<pi> = Some True"
  shows "\<exists>j < length \<pi>. time \<pi> j \<le> D \<and>
           (\<forall>F. adm_family R F \<pi> j \<longrightarrow> evalR \<phi> (signal_state R F \<pi> j (of_int (time \<pi> j))) = Some True)"
proof -
  from assms(2) obtain j where "j < length \<pi>" "time \<pi> j \<le> D" "evalI \<phi> (enclosed R \<pi> j) = Some True"
    unfolding ew_evalI_def by (auto split: if_splits)
  with evalI_sound_signals[OF assms(1)] show ?thesis by blast
qed

text \<open>The false verdict of \<open>EVENTUALLY \<dots> WITHIN\<close> says that at every entry of the window the
  formula is false for every admissible family at the time of that entry. It says nothing
  about the times between the entries.\<close>

theorem ew_false_signals:
  assumes "present_free \<phi>" "ew_evalI R \<phi> D \<pi> = Some False"
  shows "passed D \<pi>" and
    "\<And>j F. j < length \<pi> \<Longrightarrow> time \<pi> j \<le> D \<Longrightarrow> adm_family R F \<pi> j \<Longrightarrow>
       evalR \<phi> (signal_state R F \<pi> j (of_int (time \<pi> j))) = Some False"
proof -
  show "passed D \<pi>" using assms(2) unfolding ew_evalI_def by (auto split: if_splits)
  fix j F assume "j < length \<pi>" "time \<pi> j \<le> D" "adm_family R F \<pi> j"
  moreover have "\<forall>j < length \<pi>. time \<pi> j \<le> D \<longrightarrow> evalI \<phi> (enclosed R \<pi> j) = Some False"
    using assms(2) unfolding ew_evalI_def by (auto split: if_splits)
  ultimately show "evalR \<phi> (signal_state R F \<pi> j (of_int (time \<pi> j))) = Some False"
    using evalI_sound_signals[OF assms(1)] by blast
qed


subsection \<open>Finality of the invariants\<close>

theorem inv_evalI_final:
  assumes "inv_evalI R \<iota> \<pi> = Some b"
  shows "inv_evalI R \<iota> (\<pi> @ \<rho>) = Some b"
proof (cases \<iota>)
  case (Always \<phi>)
  let ?P = "\<exists>j < length \<pi>. evalI \<phi> (enclosed R \<pi> j) = Some False"
  from assms Always have "(if ?P then Some False else None) = Some b" by simp
  then have ex: ?P and b: "b = False" by (cases ?P; simp)+
  from ex obtain j where "j < length \<pi>" "evalI \<phi> (enclosed R \<pi> j) = Some False" by blast
  then have "\<exists>j < length (\<pi> @ \<rho>). evalI \<phi> (enclosed R (\<pi> @ \<rho>) j) = Some False"
    by (intro exI[of _ j]) (simp add: enclosed_append)
  with Always b show ?thesis by simp
next
  case (Eventually \<phi>)
  let ?P = "\<exists>j < length \<pi>. evalI \<phi> (enclosed R \<pi> j) = Some True"
  from assms Eventually have "(if ?P then Some True else None) = Some b" by simp
  then have ex: ?P and b: "b = True" by (cases ?P; simp)+
  from ex obtain j where "j < length \<pi>" "evalI \<phi> (enclosed R \<pi> j) = Some True" by blast
  then have "\<exists>j < length (\<pi> @ \<rho>). evalI \<phi> (enclosed R (\<pi> @ \<rho>) j) = Some True"
    by (intro exI[of _ j]) (simp add: enclosed_append)
  with Eventually b show ?thesis by simp
next
  case (Next \<phi>)
  from assms Next have "(if 1 < length \<pi> then evalI \<phi> (enclosed R \<pi> 1) else None) = Some b" by simp
  then have "1 < length \<pi>" "evalI \<phi> (enclosed R \<pi> 1) = Some b" by (cases "1 < length \<pi>"; simp)+
  with Next show ?thesis by (simp add: enclosed_append)
qed

theorem ew_evalI_final:
  assumes tr: "is_trace (\<pi> @ \<rho>)" and v: "ew_evalI R \<phi> D \<pi> = Some b"
  shows "ew_evalI R \<phi> D (\<pi> @ \<rho>) = Some b"
proof (cases "\<exists>j < length \<pi>. time \<pi> j \<le> D \<and> evalI \<phi> (enclosed R \<pi> j) = Some True")
  case True
  then obtain j where j: "j < length \<pi>" "time \<pi> j \<le> D" "evalI \<phi> (enclosed R \<pi> j) = Some True" by blast
  from True v have b: "b = True" unfolding ew_evalI_def by simp
  have "\<exists>j < length (\<pi> @ \<rho>). time (\<pi> @ \<rho>) j \<le> D \<and> evalI \<phi> (enclosed R (\<pi> @ \<rho>) j) = Some True"
    using j by (intro exI[of _ j]) (simp add: enclosed_append)
  with b show ?thesis unfolding ew_evalI_def by simp
next
  case False
  let ?F = "passed D \<pi> \<and> (\<forall>j < length \<pi>. time \<pi> j \<le> D \<longrightarrow> evalI \<phi> (enclosed R \<pi> j) = Some False)"
  from v False have "(if ?F then Some False else None) = Some b" unfolding ew_evalI_def by simp
  then have F: ?F and b: "b = False" by (cases ?F; simp)+
  from F have p: "passed D \<pi>"
    and allF: "\<forall>j < length \<pi>. time \<pi> j \<le> D \<longrightarrow> evalI \<phi> (enclosed R \<pi> j) = Some False"
    by blast+
  from p obtain i where i: "i < length \<pi>" "D < time \<pi> i" unfolding passed_def by blast
  have allF': "evalI \<phi> (enclosed R (\<pi> @ \<rho>) j) = Some False"
    if j: "j < length (\<pi> @ \<rho>)" "time (\<pi> @ \<rho>) j \<le> D" for j
  proof (cases "j < length \<pi>")
    case True
    with j allF show ?thesis by (simp add: enclosed_append)
  next
    case False
    then have "i \<le> j" using i(1) by simp
    from time_mono[OF tr this j(1)] i have "D < time (\<pi> @ \<rho>) j" by simp
    with j(2) show ?thesis by simp
  qed
  have noT: "\<not> (\<exists>j < length (\<pi> @ \<rho>). time (\<pi> @ \<rho>) j \<le> D \<and> evalI \<phi> (enclosed R (\<pi> @ \<rho>) j) = Some True)"
    using allF' by fastforce
  moreover have "passed D (\<pi> @ \<rho>)" using passed_append[OF p] .
  ultimately show ?thesis using allF' b unfolding ew_evalI_def by auto
qed


section \<open>Inconsistent samples are a rejection\<close>

text \<open>Samples that no signal under the declared bounds can pass through make every
  statement about the admissible signals vacuous (\<open>adm_family\<close> is then empty, by
  \<open>consistent_iff_adm\<close>). So the verdicts on enclosures are reported only for a consistent
  trace; an inconsistent trace is rejected, as the evaluator rejects a trace for its time
  order or the types of its data, and no verdict is given on it. A checked verdict then
  has the finality of \<open>run_final\<close>: a decided verdict on a trace is the verdict on every
  longer trace, unless the longer trace is rejected. A consistent trace can become
  inconsistent by a later sample; that is a property of the data, and the decided
  verdicts of the shorter trace are not contradicted, only withheld.\<close>

definition checked :: "('n \<Rightarrow> rat option) \<Rightarrow> ('n, atom, 's, 'a) itrace \<Rightarrow> 'r \<Rightarrow> 'r option" where
  "checked R \<pi> v = (if consistent_trace R \<pi> then Some v else None)"

lemma checked_rejected: "checked R \<pi> v = None \<longleftrightarrow> \<not> consistent_trace R \<pi>"
  by (simp add: checked_def)

theorem checked_pr_verdictI_final:
  assumes "checked R \<pi> (pr_verdictI R s a c \<pi>) = Some v" "v \<noteq> Pending"
  shows "checked R (\<pi> @ \<rho>) (pr_verdictI R s a c (\<pi> @ \<rho>)) = Some v
         \<or> checked R (\<pi> @ \<rho>) (pr_verdictI R s a c (\<pi> @ \<rho>)) = None"
  using assms pr_verdictI_final[of R s a c \<pi> \<rho>] by (auto simp: checked_def split: if_splits)

theorem checked_inv_evalI_final:
  assumes "checked R \<pi> (inv_evalI R \<iota> \<pi>) = Some (Some b)"
  shows "checked R (\<pi> @ \<rho>) (inv_evalI R \<iota> (\<pi> @ \<rho>)) = Some (Some b)
         \<or> checked R (\<pi> @ \<rho>) (inv_evalI R \<iota> (\<pi> @ \<rho>)) = None"
  using assms inv_evalI_final[of R \<iota> \<pi> b \<rho>] by (auto simp: checked_def split: if_splits)

theorem checked_ew_evalI_final:
  assumes "is_trace (\<pi> @ \<rho>)" "checked R \<pi> (ew_evalI R \<phi> D \<pi>) = Some (Some b)"
  shows "checked R (\<pi> @ \<rho>) (ew_evalI R \<phi> D (\<pi> @ \<rho>)) = Some (Some b)
         \<or> checked R (\<pi> @ \<rho>) (ew_evalI R \<phi> D (\<pi> @ \<rho>)) = None"
  using assms ew_evalI_final[of \<pi> \<rho> R \<phi> D b] by (auto simp: checked_def split: if_splits)

theorem checked_monitor_decisionsI_final:
  assumes "checked R \<pi> (monitor_decisionsI R s a c \<pi>) = Some ds"
  shows "(\<exists>ds'. checked R (\<pi> @ \<rho>) (monitor_decisionsI R s a c (\<pi> @ \<rho>)) = Some (ds @ ds'))
         \<or> checked R (\<pi> @ \<rho>) (monitor_decisionsI R s a c (\<pi> @ \<rho>)) = None"
  using assms monitor_decisionsI_append[of R s a c \<pi> \<rho>] by (auto simp: checked_def split: if_splits)


section \<open>Executable equations\<close>

text \<open>The samples of a name up to an entry, as a list; consistency, the bounds of the
  enclosure and the interval state of an entry, on lists. Every computation is in exact
  rational arithmetic.\<close>

definition sample_list :: "('n, atom, 's, 'a) itrace \<Rightarrow> nat \<Rightarrow> 'n \<Rightarrow> (int \<times> rat) list" where
  "sample_list \<pi> j x =
     concat (map (\<lambda>i. if evt (\<pi> ! i) = Arrival x
                      then (case st \<pi> i x of Some (ANum q) \<Rightarrow> [(time \<pi> i, q)] | _ \<Rightarrow> [])
                      else []) [0..<Suc j])"


lemma sample_elem:
  "set (if evt (\<pi> ! i) = Arrival x then (case st \<pi> i x of Some (ANum q) \<Rightarrow> [(time \<pi> i, q)] | _ \<Rightarrow> []) else [])
   = {(time \<pi> i, q) | q. evt (\<pi> ! i) = Arrival x \<and> st \<pi> i x = Some (ANum q)}"
proof (cases "evt (\<pi> ! i) = Arrival x")
  case False
  then show ?thesis by simp
next
  case True
  show ?thesis
  proof (cases "st \<pi> i x")
    case None
    with True show ?thesis by simp
  next
    case (Some v)
    with True show ?thesis by (cases v) auto
  qed
qed

lemma sample_list_0:
  "sample_list \<pi> 0 x =
     (if evt (\<pi> ! 0) = Arrival x then (case st \<pi> 0 x of Some (ANum q) \<Rightarrow> [(time \<pi> 0, q)] | _ \<Rightarrow> []) else [])"
  by (simp add: sample_list_def)

lemma sample_list_Suc:
  "sample_list \<pi> (Suc j) x = sample_list \<pi> j x @
     (if evt (\<pi> ! Suc j) = Arrival x then (case st \<pi> (Suc j) x of Some (ANum q) \<Rightarrow> [(time \<pi> (Suc j), q)] | _ \<Rightarrow> [])
      else [])"
  by (simp add: sample_list_def)

lemma samples_0:
  "samples \<pi> 0 x = {(time \<pi> 0, q) | q. evt (\<pi> ! 0) = Arrival x \<and> st \<pi> 0 x = Some (ANum q)}"
  unfolding samples_def by auto

lemma samples_Suc:
  "samples \<pi> (Suc j) x = samples \<pi> j x \<union>
     {(time \<pi> (Suc j), q) | q. evt (\<pi> ! Suc j) = Arrival x \<and> st \<pi> (Suc j) x = Some (ANum q)}"
  unfolding samples_def by (auto simp: le_Suc_eq)

lemma set_sample_list: "set (sample_list \<pi> j x) = samples \<pi> j x"
proof (induction j)
  case 0
  show ?case by (simp only: sample_list_0 sample_elem samples_0)
next
  case (Suc j)
  show ?case by (simp only: sample_list_Suc set_append Suc.IH sample_elem samples_Suc)
qed

lemma samples_code [code]: "samples \<pi> j x = set (sample_list \<pi> j x)"
  by (simp add: set_sample_list)

lemma consistent_code [code]:
  "consistent L (set ps) \<longleftrightarrow>
     list_all (\<lambda>p. list_all (\<lambda>q. \<bar>snd p - snd q\<bar> \<le> L * \<bar>of_int (fst p) - of_int (fst q)\<bar>) ps) ps"
  by (simp add: consistent_def list_all_iff)

lemma lo_code [code]: "lo L (set (p # ps)) t = fold max (map (qcone_lo L t) ps) (qcone_lo L t p)"
proof -
  have eq: "qcone_lo L t ` set (p # ps) = set (qcone_lo L t p # map (qcone_lo L t) ps)" by simp
  show ?thesis unfolding lo_def eq by (simp only: Max.set_eq_fold)
qed

lemma hi_code [code]: "hi L (set (p # ps)) t = fold min (map (qcone_up L t) ps) (qcone_up L t p)"
proof -
  have eq: "qcone_up L t ` set (p # ps) = set (qcone_up L t p # map (qcone_up L t) ps)" by simp
  show ?thesis unfolding hi_def eq by (simp only: Min.set_eq_fold)
qed

lemma enclosed_at_code [code]:
  "enclosed_at R \<pi> j t x =
     (case R x of
        None \<Rightarrow> point (st \<pi> j) x
      | Some L \<Rightarrow> (case sample_list \<pi> j x of [] \<Rightarrow> None | p # ps \<Rightarrow> Some (enc L (set (p # ps)) t)))"
  by (simp add: enclosed_at_def samples_code split: option.splits list.splits)

lemma pr_verdictI_code [code]:
  "pr_verdictI R s a c \<pi> =
     (case find (forbiddenI R s a c \<pi>) [0..<length \<pi>] of
        None \<Rightarrow> Pending
      | Some j \<Rightarrow> Breached (time \<pi> j))"
proof (cases "find (forbiddenI R s a c \<pi>) [0..<length \<pi>]")
  case None
  then have "\<not> forbiddenI R s a c \<pi> j" for j
    using forbiddenI_less[of R s a c \<pi> j] by (auto simp: find_upt_None)
  with None show ?thesis by (simp add: pr_verdictI_def)
next
  case (Some j)
  then have j: "forbiddenI R s a c \<pi> j" "\<And>i. i < j \<Longrightarrow> \<not> forbiddenI R s a c \<pi> i"
    by (auto simp: find_upt_Some)
  have "(LEAST j. forbiddenI R s a c \<pi> j) = j"
  proof (rule Least_equality)
    show "forbiddenI R s a c \<pi> j" by (rule j(1))
    fix y assume "forbiddenI R s a c \<pi> y"
    with j(2)[of y] show "j \<le> y" by (cases "y < j") auto
  qed
  with Some j(1) show ?thesis by (auto simp: pr_verdictI_def)
qed

lemma inv_evalI_code [code]:
  "inv_evalI R (Always \<phi>) \<pi> =
     (if \<exists>j \<in> set [0..<length \<pi>]. evalI \<phi> (enclosed R \<pi> j) = Some False then Some False else None)"
  "inv_evalI R (Eventually \<phi>) \<pi> =
     (if \<exists>j \<in> set [0..<length \<pi>]. evalI \<phi> (enclosed R \<pi> j) = Some True then Some True else None)"
  "inv_evalI R (Next \<phi>) \<pi> = (if 1 < length \<pi> then evalI \<phi> (enclosed R \<pi> 1) else None)"
  by auto

lemma ew_evalI_code [code]:
  "ew_evalI R \<phi> D \<pi> =
     (if \<exists>j \<in> set [0..<length \<pi>]. time \<pi> j \<le> D \<and> evalI \<phi> (enclosed R \<pi> j) = Some True then Some True
      else if passed D \<pi> \<and> (\<forall>j \<in> set [0..<length \<pi>]. time \<pi> j \<le> D \<longrightarrow> evalI \<phi> (enclosed R \<pi> j) = Some False)
      then Some False
      else None)"
  unfolding ew_evalI_def by auto

text \<open>Consistency quantifies over all names; only the names that arrive up to the entry
  have samples, and an empty set of samples is consistent.\<close>

definition arrivals :: "('n, atom, 's, 'a) itrace \<Rightarrow> nat \<Rightarrow> 'n list" where
  "arrivals \<pi> j = concat (map (\<lambda>i. case evt (\<pi> ! i) of Arrival x \<Rightarrow> [x] | _ \<Rightarrow> []) [0..<Suc j])"

lemma arrivals_0: "arrivals \<pi> 0 = (case evt (\<pi> ! 0) of Arrival x \<Rightarrow> [x] | _ \<Rightarrow> [])"
  by (simp add: arrivals_def)

lemma arrivals_Suc: "arrivals \<pi> (Suc j) = arrivals \<pi> j @ (case evt (\<pi> ! Suc j) of Arrival x \<Rightarrow> [x] | _ \<Rightarrow> [])"
  by (simp add: arrivals_def)

lemma arrivals_member:
  assumes "i \<le> j" "evt (\<pi> ! i) = Arrival x"
  shows "x \<in> set (arrivals \<pi> j)"
  using assms
proof (induction j)
  case 0
  then show ?case by (simp add: arrivals_0)
next
  case (Suc j)
  show ?case
  proof (cases "i \<le> j")
    case True
    with Suc show ?thesis by (simp add: arrivals_Suc)
  next
    case False
    with Suc.prems have "i = Suc j" by simp
    with Suc.prems(2) show ?thesis by (simp add: arrivals_Suc)
  qed
qed

lemma samples_no_arrival: "x \<notin> set (arrivals \<pi> j) \<Longrightarrow> samples \<pi> j x = {}"
  by (auto simp: samples_def dest: arrivals_member)

lemma consistent_upto_code [code]:
  "consistent_upto R \<pi> j \<longleftrightarrow>
     (\<forall>x \<in> set (arrivals \<pi> j). case R x of None \<Rightarrow> True | Some L \<Rightarrow> consistent L (samples \<pi> j x))"
proof
  assume "consistent_upto R \<pi> j"
  then show "\<forall>x \<in> set (arrivals \<pi> j). case R x of None \<Rightarrow> True | Some L \<Rightarrow> consistent L (samples \<pi> j x)"
    by (auto simp: consistent_upto_def split: option.splits)
next
  assume a: "\<forall>x \<in> set (arrivals \<pi> j). case R x of None \<Rightarrow> True | Some L \<Rightarrow> consistent L (samples \<pi> j x)"
  show "consistent_upto R \<pi> j"
    unfolding consistent_upto_def
  proof (intro allI impI)
    fix x L assume R: "R x = Some L"
    show "consistent L (samples \<pi> j x)"
    proof (cases "x \<in> set (arrivals \<pi> j)")
      case True
      with a R show ?thesis by auto
    next
      case False
      then show ?thesis by (simp add: samples_no_arrival consistent_def)
    qed
  qed
qed


section \<open>The sensor example in numbers\<close>

text \<open>The scenarios of \<open>examples/core/sensor_overheat.triel\<close>, with the rate bound 0.1 degrees
  per second on the temperature, which the specification does not declare: the bound is
  a parameter of this theory, not of the language. The condition of the prohibition is
  \<open>motor_temp >= limit_c\<close>, translated to \<open>(le limit_c motor_temp)\<close>. The times are seconds
  since 1970-01-01T00:00:00Z: 08:00:00 on 2026-11-09 is 1794211200. The activation entry
  is a tick, as the driver of the scenarios translates it.\<close>

definition temp :: path where "temp = [STR ''motor_temp'']"
definition lim :: path where "lim = [STR ''limit_c'']"

definition sensor_bounds :: "path \<Rightarrow> rat option" where
  "sensor_bounds x = (if x = temp then Some (1 / 10) else None)"

definition over_limit :: "(path, atom) expr" where
  "over_limit = ELe (VName lim) (VName temp)"

definition sensor_data :: "rat \<Rightarrow> (path, atom) state" where
  "sensor_data v = [temp \<mapsto> ANum v, lim \<mapsto> ANum 90]"

definition arm_move :: cevent where
  "arm_move = Deontic (STR ''arm'') (Act (STR ''move'') []) MustNot"

definition stop_drive :: cevent where
  "stop_drive = Deontic (STR ''controller'') (Act (STR ''stop_drive'') []) Must"

text \<open>Scenario \<open>sensor_stale\<close>: a reading of 85.0 at 08:04:00, a tick at 08:04:10, the arm
  moves at 08:04:11. The reading is stale at 08:04:10 under \<open>MAX_AGE 5 SECONDS\<close>, and the
  monitor of the core blocks the movement. Under the rate bound the enclosure of the
  temperature at 08:04:10 is [84.0, 86.0] and at 08:04:11 [83.9, 86.1]; the condition is
  false on the enclosure read before the action, so the monitor on enclosures allows the
  movement, and by \<open>monitor_sound_signals\<close> the temperature was below the limit at
  08:04:10 for every signal under the bound through the reading.\<close>

definition stale_trace :: ctrace where
  "stale_trace =
     [(sensor_data (195 / 2), 1794211200, Tick),
      (sensor_data (195 / 2), 1794211205, stop_drive),
      (sensor_data 85, 1794211440, Arrival temp),
      (sensor_data 85, 1794211450, Tick),
      (sensor_data 85, 1794211451, arm_move)]"

value "sample_list stale_trace 4 temp"
value "enclosed sensor_bounds stale_trace 3 temp"
value "enclosed sensor_bounds stale_trace 4 temp"
value "evalI over_limit (enclosed sensor_bounds stale_trace 3)"
value "monitor_decisionsI sensor_bounds (STR ''arm'') (Act (STR ''move'') []) over_limit stale_trace"
value "pr_verdictI sensor_bounds (STR ''arm'') (Act (STR ''move'') []) over_limit stale_trace"
value "consistent_trace sensor_bounds stale_trace"

lemma stale_enclosure:
  "enclosed sensor_bounds stale_trace 3 temp = Some (84, 86)"
  "enclosed sensor_bounds stale_trace 4 temp = Some (839 / 10, 861 / 10)"
  "evalI over_limit (enclosed sensor_bounds stale_trace 3) = Some False"
  "monitor_decisionsI sensor_bounds (STR ''arm'') (Act (STR ''move'') []) over_limit stale_trace = [(4, False)]"
  "pr_verdictI sensor_bounds (STR ''arm'') (Act (STR ''move'') []) over_limit stale_trace = Pending"
  "consistent_trace sensor_bounds stale_trace"
  by code_simp+

text \<open>Scenario \<open>sensor_max_age_boundary\<close>: the reading of 85.0 at 08:04:00 is exactly 5 seconds
  old at 08:04:05, still fresh, and the arm moves at 08:04:06. The core allows the
  movement, reading the value 85.0 as exact. Under the rate bound the enclosure at
  08:04:05 is [84.5, 85.5] and at 08:04:06 [84.4, 85.6]; the same decision, now for every
  signal under the bound. Had the limit been 85.3, the core would still allow, and on the
  enclosure the condition is undefined and the monitor blocks.\<close>

definition boundary_trace :: ctrace where
  "boundary_trace =
     [(sensor_data (195 / 2), 1794211200, Tick),
      (sensor_data (195 / 2), 1794211210, stop_drive),
      (sensor_data 85, 1794211440, Arrival temp),
      (sensor_data 85, 1794211445, Tick),
      (sensor_data 85, 1794211446, arm_move)]"

value "enclosed sensor_bounds boundary_trace 3 temp"
value "enclosed sensor_bounds boundary_trace 4 temp"
value "evalI over_limit (enclosed sensor_bounds boundary_trace 3)"
value "evalI (ELe (VConst (ANum (853 / 10))) (VName temp)) (enclosed sensor_bounds boundary_trace 3)"

lemma boundary_enclosure:
  "enclosed sensor_bounds boundary_trace 3 temp = Some (169 / 2, 171 / 2)"
  "enclosed sensor_bounds boundary_trace 4 temp = Some (422 / 5, 428 / 5)"
  "evalI over_limit (enclosed sensor_bounds boundary_trace 3) = Some False"
  "evalI (ELe (VConst (ANum (853 / 10))) (VName temp)) (enclosed sensor_bounds boundary_trace 3) = None"
  "blocksI (ELe (VConst (ANum (853 / 10))) (VName temp)) (enclosed sensor_bounds boundary_trace 3)"
  by code_simp+

text \<open>Scenario \<open>sensor_at_limit\<close>: a reading exactly at the limit, 90.0, at 08:00:20, and the
  arm moves at 08:00:21. The core records a breach. On the enclosures the monitor reads
  the interval state of the entry before the action, at its time 08:00:20, where the
  enclosure is the point [90.0, 90.0] (\<open>enclosed_at_sample\<close>): the condition is true, the
  breach stands, and by \<open>breach_certain_signals\<close> every signal under the bound through the
  reading was at the limit then. Read instead at the time of the action, 08:00:21, the
  enclosure is [89.9, 90.1] and the condition is undefined: the temperature may have
  fallen below the limit in that second. The theory reads the entry before the action;
  the other reading is computed by \<open>enclosed_at\<close> and is not a verdict of this theory.\<close>

definition at_limit_trace :: ctrace where
  "at_limit_trace =
     [(sensor_data (195 / 2), 1794211200, Tick),
      (sensor_data (195 / 2), 1794211210, stop_drive),
      (sensor_data 90, 1794211220, Arrival temp),
      (sensor_data 90, 1794211221, arm_move),
      (sensor_data 90, 1794211860, Tick)]"

value "enclosed sensor_bounds at_limit_trace 2 temp"
value "enclosed_at sensor_bounds at_limit_trace 2 1794211221 temp"
value "evalI over_limit (enclosed sensor_bounds at_limit_trace 2)"
value "evalI over_limit (enclosed_at sensor_bounds at_limit_trace 2 1794211221)"
value "pr_verdictI sensor_bounds (STR ''arm'') (Act (STR ''move'') []) over_limit at_limit_trace"
value "monitor_decisionsI sensor_bounds (STR ''arm'') (Act (STR ''move'') []) over_limit at_limit_trace"

lemma at_limit_enclosure:
  "enclosed sensor_bounds at_limit_trace 2 temp = Some (90, 90)"
  "enclosed_at sensor_bounds at_limit_trace 2 1794211221 temp = Some (899 / 10, 901 / 10)"
  "evalI over_limit (enclosed sensor_bounds at_limit_trace 2) = Some True"
  "evalI over_limit (enclosed_at sensor_bounds at_limit_trace 2 1794211221) = None"
  "pr_verdictI sensor_bounds (STR ''arm'') (Act (STR ''move'') []) over_limit at_limit_trace = Breached 1794211221"
  "monitor_decisionsI sensor_bounds (STR ''arm'') (Act (STR ''move'') []) over_limit at_limit_trace = [(3, True)]"
  by code_simp+

text \<open>Inconsistent samples: readings of 97.5 at 08:10:00 and 85.0 at 08:10:01 would need a
  fall of 12.5 degrees in one second, more than the bound allows; no signal under the bound
  passes through them (\<open>consistent_iff_adm\<close>), and the trace is rejected.\<close>

definition fall_trace :: ctrace where
  "fall_trace =
     [(sensor_data (195 / 2), 1794211200, Tick),
      (sensor_data (195 / 2), 1794211800, Arrival temp),
      (sensor_data 85, 1794211801, Arrival temp)]"

value "consistent_trace sensor_bounds fall_trace"
value "checked sensor_bounds fall_trace (inv_evalI sensor_bounds (Eventually (ELt (VName temp) (VName lim))) fall_trace)"

lemma fall_rejected:
  "\<not> consistent_trace sensor_bounds fall_trace"
  "checked sensor_bounds fall_trace (inv_evalI sensor_bounds (Eventually (ELt (VName temp) (VName lim))) fall_trace) = None"
  by code_simp+

end
