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
                where inconsistent samples are a rejection; between two neighbouring
                samples the envelopes are the two neighbouring cones, with the peak
                and the valley as their extremes; whether the lower envelope stays at
                or above a level throughout a window of real time is decided exactly by
                finitely many rational comparisons, which gives a continuous false
                verdict of EVENTUALLY (x < c) WITHIN d, sound for every admissible
                signal at every time of the window and final under more consistent
                samples; a signal with a bounded derivative is a signal under the
                bound; the enclosures and the decision are executable.
    SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause
*)

theory TRIEL_Signals
  imports TRIEL_Exec "HOL.Deriv"
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

text \<open>A signal with a derivative bounded by \<open>L\<close> everywhere is a signal under \<open>L\<close>, by the mean
  value theorem: this is how a bound on the rate of a physical quantity, or on the
  right-hand side of its differential equation, gives the rate bound of this theory.\<close>

theorem deriv_bound_lip:
  assumes der: "\<And>x. DERIV f x :> f' x" and bound: "\<And>x. \<bar>f' x\<bar> \<le> L"
  shows "lip L f"
  unfolding lip_def
proof (intro allI)
  fix s t
  have mvt: "\<bar>f b - f a\<bar> \<le> L * \<bar>b - a\<bar>" if "a < b" for a b
  proof -
    from MVT2[OF that, of f f'] der obtain z where z: "f b - f a = (b - a) * f' z" by blast
    have "\<bar>f b - f a\<bar> = \<bar>b - a\<bar> * \<bar>f' z\<bar>" by (simp add: z abs_mult)
    also have "\<dots> \<le> \<bar>b - a\<bar> * L" by (rule mult_left_mono[OF bound]) simp
    finally show ?thesis by (simp add: mult.commute)
  qed
  show "\<bar>f t - f s\<bar> \<le> L * \<bar>t - s\<bar>"
  proof (cases s t rule: linorder_cases)
    case less
    then show ?thesis by (rule mvt)
  next
    case equal
    have "0 \<le> L" using bound[of s] by simp
    with equal show ?thesis by simp
  next
    case greater
    from mvt[OF greater] show ?thesis by (simp add: abs_minus_commute)
  qed
qed

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


subsection \<open>Between two samples\<close>

text \<open>Of two samples on the same side of a time, the farther one confines no more than the
  nearer one: its cone at that time is at least as high above and at least as low below.
  So between two consecutive samples the envelopes are the two neighbouring cones, before
  the first sample and after the last one they are the one cone. Consistency of the two
  samples is what makes the nearer cone the lower one.\<close>

lemma cone_up_farther:
  assumes "0 \<le> L" "rcons L S" "p \<in> S" "q \<in> S"
    and "\<bar>t - fst q\<bar> = \<bar>t - fst p\<bar> + \<bar>fst p - fst q\<bar>"
  shows "cone_up L t p \<le> cone_up L t q"
proof -
  have "\<bar>snd p - snd q\<bar> \<le> L * \<bar>fst p - fst q\<bar>" using assms(2-4) by (simp add: rcons_def)
  then have le: "snd p \<le> snd q + L * \<bar>fst p - fst q\<bar>" by (simp add: abs_le_iff)
  have "L * (\<bar>t - fst p\<bar> + \<bar>fst p - fst q\<bar>) = L * \<bar>t - fst p\<bar> + L * \<bar>fst p - fst q\<bar>"
    by (simp add: distrib_left)
  with le show ?thesis unfolding cone_up_def assms(5) by linarith
qed

lemma cone_lo_farther:
  assumes "0 \<le> L" "rcons L S" "p \<in> S" "q \<in> S"
    and "\<bar>t - fst q\<bar> = \<bar>t - fst p\<bar> + \<bar>fst p - fst q\<bar>"
  shows "cone_lo L t q \<le> cone_lo L t p"
proof -
  have "\<bar>snd p - snd q\<bar> \<le> L * \<bar>fst p - fst q\<bar>" using assms(2-4) by (simp add: rcons_def)
  then have le: "snd q - L * \<bar>fst p - fst q\<bar> \<le> snd p" by (simp add: abs_le_iff)
  have "L * (\<bar>t - fst p\<bar> + \<bar>fst p - fst q\<bar>) = L * \<bar>t - fst p\<bar> + L * \<bar>fst p - fst q\<bar>"
    by (simp add: distrib_left)
  with le show ?thesis unfolding cone_lo_def assms(5) by linarith
qed

lemma abs_split_left: "r \<le> p \<Longrightarrow> p \<le> t \<Longrightarrow> \<bar>t - r\<bar> = \<bar>t - p\<bar> + \<bar>p - r\<bar>" for r p t :: real
proof -
  assume "r \<le> p" "p \<le> t"
  then have "0 \<le> t - r" "0 \<le> t - p" "0 \<le> p - r" by linarith+
  then show ?thesis by (simp add: abs_of_nonneg)
qed

lemma abs_split_right: "t \<le> p \<Longrightarrow> p \<le> r \<Longrightarrow> \<bar>t - r\<bar> = \<bar>t - p\<bar> + \<bar>p - r\<bar>" for r p t :: real
proof -
  assume "t \<le> p" "p \<le> r"
  then have "0 \<le> r - t" "0 \<le> p - t" "0 \<le> r - p" by linarith+
  then show ?thesis by (simp add: abs_minus_commute[of t] abs_minus_commute[of p r] abs_of_nonneg)
qed

text \<open>Two samples are neighbours of a time if one is at or before it, the other at or after
  it, and no sample is strictly between them.\<close>

definition neighbours :: "rsamples \<Rightarrow> real \<times> real \<Rightarrow> real \<times> real \<Rightarrow> bool" where
  "neighbours S p q \<longleftrightarrow> p \<in> S \<and> q \<in> S \<and> fst p \<le> fst q \<and> (\<forall>r \<in> S. fst r \<le> fst p \<or> fst q \<le> fst r)"

theorem upper_neighbours:
  assumes "finite S" "0 \<le> L" "rcons L S" "neighbours S p q" "fst p \<le> t" "t \<le> fst q"
  shows "upper L S t = min (cone_up L t p) (cone_up L t q)"
  unfolding upper_def
proof (rule Min_eqI)
  show "finite (cone_up L t ` S)" using assms(1) by simp
  show "min (cone_up L t p) (cone_up L t q) \<in> cone_up L t ` S"
    using assms(4) by (auto simp: neighbours_def min_def)
  fix y assume "y \<in> cone_up L t ` S"
  then obtain r where r: "r \<in> S" "y = cone_up L t r" by blast
  have pq: "p \<in> S" "q \<in> S" using assms(4) by (simp_all add: neighbours_def)
  from assms(4) r(1) have "fst r \<le> fst p \<or> fst q \<le> fst r" by (simp add: neighbours_def)
  then show "min (cone_up L t p) (cone_up L t q) \<le> y"
  proof
    assume "fst r \<le> fst p"
    then have "cone_up L t p \<le> cone_up L t r"
      by (intro cone_up_farther[OF assms(2,3) pq(1) r(1)] abs_split_left[OF _ assms(5)])
    then show ?thesis unfolding r(2) by (simp add: min_le_iff_disj)
  next
    assume "fst q \<le> fst r"
    then have "cone_up L t q \<le> cone_up L t r"
      by (intro cone_up_farther[OF assms(2,3) pq(2) r(1)] abs_split_right[OF assms(6)])
    then show ?thesis unfolding r(2) by (simp add: min_le_iff_disj)
  qed
qed

theorem lower_neighbours:
  assumes "finite S" "0 \<le> L" "rcons L S" "neighbours S p q" "fst p \<le> t" "t \<le> fst q"
  shows "lower L S t = max (cone_lo L t p) (cone_lo L t q)"
  unfolding lower_def
proof (rule Max_eqI)
  show "finite (cone_lo L t ` S)" using assms(1) by simp
  show "max (cone_lo L t p) (cone_lo L t q) \<in> cone_lo L t ` S"
    using assms(4) by (auto simp: neighbours_def max_def)
  fix y assume "y \<in> cone_lo L t ` S"
  then obtain r where r: "r \<in> S" "y = cone_lo L t r" by blast
  have pq: "p \<in> S" "q \<in> S" using assms(4) by (simp_all add: neighbours_def)
  from assms(4) r(1) have "fst r \<le> fst p \<or> fst q \<le> fst r" by (simp add: neighbours_def)
  then show "y \<le> max (cone_lo L t p) (cone_lo L t q)"
  proof
    assume "fst r \<le> fst p"
    then have "cone_lo L t r \<le> cone_lo L t p"
      by (intro cone_lo_farther[OF assms(2,3) pq(1) r(1)] abs_split_left[OF _ assms(5)])
    then show ?thesis unfolding r(2) by (simp add: le_max_iff_disj)
  next
    assume "fst q \<le> fst r"
    then have "cone_lo L t r \<le> cone_lo L t q"
      by (intro cone_lo_farther[OF assms(2,3) pq(2) r(1)] abs_split_right[OF assms(6)])
    then show ?thesis unfolding r(2) by (simp add: le_max_iff_disj)
  qed
qed

text \<open>Before the first sample and after the last one, the envelopes are the cones of that
  sample.\<close>

theorem upper_first:
  assumes "finite S" "0 \<le> L" "rcons L S" "p \<in> S" "\<And>r. r \<in> S \<Longrightarrow> fst p \<le> fst r" "t \<le> fst p"
  shows "upper L S t = cone_up L t p"
  unfolding upper_def
proof (rule Min_eqI)
  show "finite (cone_up L t ` S)" using assms(1) by simp
  show "cone_up L t p \<in> cone_up L t ` S" using assms(4) by simp
  fix y assume "y \<in> cone_up L t ` S"
  then obtain r where r: "r \<in> S" "y = cone_up L t r" by blast
  show "cone_up L t p \<le> y" unfolding r(2)
    by (intro cone_up_farther[OF assms(2,3,4) r(1)] abs_split_right[OF assms(6) assms(5)[OF r(1)]])
qed

theorem upper_last:
  assumes "finite S" "0 \<le> L" "rcons L S" "p \<in> S" "\<And>r. r \<in> S \<Longrightarrow> fst r \<le> fst p" "fst p \<le> t"
  shows "upper L S t = cone_up L t p"
  unfolding upper_def
proof (rule Min_eqI)
  show "finite (cone_up L t ` S)" using assms(1) by simp
  show "cone_up L t p \<in> cone_up L t ` S" using assms(4) by simp
  fix y assume "y \<in> cone_up L t ` S"
  then obtain r where r: "r \<in> S" "y = cone_up L t r" by blast
  show "cone_up L t p \<le> y" unfolding r(2)
    by (intro cone_up_farther[OF assms(2,3,4) r(1)] abs_split_left[OF assms(5)[OF r(1)] assms(6)])
qed

theorem lower_first:
  assumes "finite S" "0 \<le> L" "rcons L S" "p \<in> S" "\<And>r. r \<in> S \<Longrightarrow> fst p \<le> fst r" "t \<le> fst p"
  shows "lower L S t = cone_lo L t p"
  unfolding lower_def
proof (rule Max_eqI)
  show "finite (cone_lo L t ` S)" using assms(1) by simp
  show "cone_lo L t p \<in> cone_lo L t ` S" using assms(4) by simp
  fix y assume "y \<in> cone_lo L t ` S"
  then obtain r where r: "r \<in> S" "y = cone_lo L t r" by blast
  show "y \<le> cone_lo L t p" unfolding r(2)
    by (intro cone_lo_farther[OF assms(2,3,4) r(1)] abs_split_right[OF assms(6) assms(5)[OF r(1)]])
qed

theorem lower_last:
  assumes "finite S" "0 \<le> L" "rcons L S" "p \<in> S" "\<And>r. r \<in> S \<Longrightarrow> fst r \<le> fst p" "fst p \<le> t"
  shows "lower L S t = cone_lo L t p"
  unfolding lower_def
proof (rule Max_eqI)
  show "finite (cone_lo L t ` S)" using assms(1) by simp
  show "cone_lo L t p \<in> cone_lo L t ` S" using assms(4) by simp
  fix y assume "y \<in> cone_lo L t ` S"
  then obtain r where r: "r \<in> S" "y = cone_lo L t r" by blast
  show "y \<le> cone_lo L t p" unfolding r(2)
    by (intro cone_lo_farther[OF assms(2,3,4) r(1)] abs_split_left[OF assms(5)[OF r(1)] assms(6)])
qed


subsection \<open>The extremes between two samples\<close>

text \<open>On the segment between two samples, the two upper cones add up to a constant: twice
  the mean of the two values plus \<open>L\<close> times the gap. So the least of them is at most that
  constant divided by two, the peak, with equality where the cones cross; the greatest of
  the two lower cones is at least the valley, the mean minus \<open>L\<close> times half the gap. For
  consistent samples the crossing is inside the segment. Between two consecutive samples
  these are the extremes of the envelopes.\<close>

definition peak :: "real \<Rightarrow> real \<times> real \<Rightarrow> real \<times> real \<Rightarrow> real" where
  "peak L p q = (snd p + snd q) / 2 + L * (fst q - fst p) / 2"

definition valley :: "real \<Rightarrow> real \<times> real \<Rightarrow> real \<times> real \<Rightarrow> real" where
  "valley L p q = (snd p + snd q) / 2 - L * (fst q - fst p) / 2"

definition peak_time :: "real \<Rightarrow> real \<times> real \<Rightarrow> real \<times> real \<Rightarrow> real" where
  "peak_time L p q = (fst p + fst q) / 2 + (snd q - snd p) / (2 * L)"

definition valley_time :: "real \<Rightarrow> real \<times> real \<Rightarrow> real \<times> real \<Rightarrow> real" where
  "valley_time L p q = (fst p + fst q) / 2 + (snd p - snd q) / (2 * L)"

lemma abs_segment:
  fixes p q :: "real \<times> real"
  assumes "fst p \<le> t" "t \<le> fst q"
  shows "\<bar>t - fst p\<bar> = t - fst p" and "\<bar>t - fst q\<bar> = fst q - t"
proof -
  show "\<bar>t - fst p\<bar> = t - fst p" by (rule abs_of_nonneg) (use assms(1) in simp)
  show "\<bar>t - fst q\<bar> = fst q - t"
    unfolding abs_minus_commute[of t] by (rule abs_of_nonneg) (use assms(2) in simp)
qed

lemma cones_up_sum:
  assumes "fst p \<le> t" "t \<le> fst q"
  shows "cone_up L t p + cone_up L t q = 2 * peak L p q"
  unfolding cone_up_def peak_def abs_segment[OF assms] by (simp add: field_simps)

lemma cones_lo_sum:
  assumes "fst p \<le> t" "t \<le> fst q"
  shows "cone_lo L t p + cone_lo L t q = 2 * valley L p q"
  unfolding cone_lo_def valley_def abs_segment[OF assms] by (simp add: field_simps)

lemma min_cones_le_peak:
  assumes "fst p \<le> t" "t \<le> fst q"
  shows "min (cone_up L t p) (cone_up L t q) \<le> peak L p q"
  using cones_up_sum[OF assms, of L] min.cobounded1[of "cone_up L t p" "cone_up L t q"]
    min.cobounded2[of "cone_up L t p" "cone_up L t q"] by linarith

lemma valley_le_max_cones:
  assumes "fst p \<le> t" "t \<le> fst q"
  shows "valley L p q \<le> max (cone_lo L t p) (cone_lo L t q)"
  using cones_lo_sum[OF assms, of L] max.cobounded1[of "cone_lo L t p" "cone_lo L t q"]
    max.cobounded2[of "cone_lo L t p" "cone_lo L t q"] by linarith

text \<open>Where the two upper cones cross, both are the peak; where the two lower cones cross,
  both are the valley. The difference of the two lower cones is proportional to the
  distance from the crossing, so the lower cone of the earlier sample is the greater one
  before the crossing and the lesser one after it.\<close>

lemma peak_time_between:
  assumes "0 < L" "fst p \<le> fst q" "\<bar>snd q - snd p\<bar> \<le> L * (fst q - fst p)"
  shows "fst p \<le> peak_time L p q" "peak_time L p q \<le> fst q"
    and "cone_up L (peak_time L p q) p = peak L p q" "cone_up L (peak_time L p q) q = peak L p q"
proof -
  have ab: "snd q - snd p \<le> L * (fst q - fst p)" "snd p - snd q \<le> L * (fst q - fst p)"
    using assms(3) by (simp_all add: abs_le_iff)
  have d1: "peak_time L p q - fst p = (L * (fst q - fst p) + (snd q - snd p)) / (2 * L)"
    unfolding peak_time_def using assms(1) by (simp add: field_simps)
  have d2: "fst q - peak_time L p q = (L * (fst q - fst p) - (snd q - snd p)) / (2 * L)"
    unfolding peak_time_def using assms(1) by (simp add: field_simps)
  have "0 \<le> L * (fst q - fst p) + (snd q - snd p)" using ab(2) by linarith
  then have "0 \<le> peak_time L p q - fst p" unfolding d1 using assms(1) by (intro divide_nonneg_pos; linarith)
  then show 1: "fst p \<le> peak_time L p q" by linarith
  have "0 \<le> L * (fst q - fst p) - (snd q - snd p)" using ab(1) by linarith
  then have "0 \<le> fst q - peak_time L p q" unfolding d2 using assms(1) by (intro divide_nonneg_pos; linarith)
  then show 2: "peak_time L p q \<le> fst q" by linarith
  have e1: "L * (peak_time L p q - fst p) = (L * (fst q - fst p) + (snd q - snd p)) / 2"
    unfolding d1 using assms(1) by (simp add: field_simps)
  show "cone_up L (peak_time L p q) p = peak L p q"
    unfolding cone_up_def peak_def abs_segment(1)[OF 1 2] e1 by (simp add: field_simps)
  have e2: "L * (fst q - peak_time L p q) = (L * (fst q - fst p) - (snd q - snd p)) / 2"
    unfolding d2 using assms(1) by (simp add: field_simps)
  show "cone_up L (peak_time L p q) q = peak L p q"
    unfolding cone_up_def peak_def abs_segment(2)[OF 1 2] e2 by (simp add: field_simps)
qed

lemma valley_time_between:
  assumes "0 < L" "fst p \<le> fst q" "\<bar>snd q - snd p\<bar> \<le> L * (fst q - fst p)"
  shows "fst p \<le> valley_time L p q" "valley_time L p q \<le> fst q"
    and "cone_lo L (valley_time L p q) p = valley L p q" "cone_lo L (valley_time L p q) q = valley L p q"
proof -
  have ab: "snd q - snd p \<le> L * (fst q - fst p)" "snd p - snd q \<le> L * (fst q - fst p)"
    using assms(3) by (simp_all add: abs_le_iff)
  have d1: "valley_time L p q - fst p = (L * (fst q - fst p) + (snd p - snd q)) / (2 * L)"
    unfolding valley_time_def using assms(1) by (simp add: field_simps)
  have d2: "fst q - valley_time L p q = (L * (fst q - fst p) - (snd p - snd q)) / (2 * L)"
    unfolding valley_time_def using assms(1) by (simp add: field_simps)
  have "0 \<le> L * (fst q - fst p) + (snd p - snd q)" using ab(1) by linarith
  then have "0 \<le> valley_time L p q - fst p" unfolding d1 using assms(1) by (intro divide_nonneg_pos; linarith)
  then show 1: "fst p \<le> valley_time L p q" by linarith
  have "0 \<le> L * (fst q - fst p) - (snd p - snd q)" using ab(2) by linarith
  then have "0 \<le> fst q - valley_time L p q" unfolding d2 using assms(1) by (intro divide_nonneg_pos; linarith)
  then show 2: "valley_time L p q \<le> fst q" by linarith
  have e1: "L * (valley_time L p q - fst p) = (L * (fst q - fst p) + (snd p - snd q)) / 2"
    unfolding d1 using assms(1) by (simp add: field_simps)
  show "cone_lo L (valley_time L p q) p = valley L p q"
    unfolding cone_lo_def valley_def abs_segment(1)[OF 1 2] e1 by (simp add: field_simps)
  have e2: "L * (fst q - valley_time L p q) = (L * (fst q - fst p) - (snd p - snd q)) / 2"
    unfolding d2 using assms(1) by (simp add: field_simps)
  show "cone_lo L (valley_time L p q) q = valley L p q"
    unfolding cone_lo_def valley_def abs_segment(2)[OF 1 2] e2 by (simp add: field_simps)
qed

lemma cone_lo_cross:
  assumes "0 < L" "fst p \<le> u" "u \<le> fst q"
  shows "cone_lo L u p - cone_lo L u q = 2 * L * (valley_time L p q - u)"
  unfolding cone_lo_def valley_time_def abs_segment[OF assms(2,3)] using assms(1) by (simp add: field_simps)

lemma cone_lo_dec: "0 \<le> L \<Longrightarrow> fst p \<le> u \<Longrightarrow> u \<le> v \<Longrightarrow> cone_lo L v p \<le> cone_lo L u p"
  unfolding cone_lo_def by (simp add: mult_left_mono)

lemma cone_lo_inc: "0 \<le> L \<Longrightarrow> u \<le> v \<Longrightarrow> v \<le> fst p \<Longrightarrow> cone_lo L u p \<le> cone_lo L v p"
  unfolding cone_lo_def by (simp add: mult_left_mono)

text \<open>So between two consecutive samples the upper envelope is at most the peak, with
  equality at the crossing of the two cones for a positive bound, and the lower envelope is
  at least the valley, with equality at the crossing. For the bound 0 a consistent set has
  one value, which both envelopes have everywhere.\<close>

theorem upper_le_peak:
  assumes "finite S" "p \<in> S" "q \<in> S" "fst p \<le> t" "t \<le> fst q"
  shows "upper L S t \<le> peak L p q"
proof -
  have "upper L S t \<le> cone_up L t p" "upper L S t \<le> cone_up L t q"
    unfolding upper_def using assms(1-3) by (intro Min_le; simp)+
  with min_cones_le_peak[OF assms(4,5), of L] show ?thesis by (metis min_le_iff_disj order_trans)
qed

theorem valley_le_lower:
  assumes "finite S" "p \<in> S" "q \<in> S" "fst p \<le> t" "t \<le> fst q"
  shows "valley L p q \<le> lower L S t"
proof -
  have "cone_lo L t p \<le> lower L S t" "cone_lo L t q \<le> lower L S t"
    unfolding lower_def using assms(1-3) by (intro Max_ge; simp)+
  with valley_le_max_cones[OF assms(4,5), of L] show ?thesis by (metis le_max_iff_disj order_trans)
qed

theorem upper_peak_attained:
  assumes "finite S" "0 < L" "rcons L S" "neighbours S p q"
  shows "fst p \<le> peak_time L p q" "peak_time L p q \<le> fst q" "upper L S (peak_time L p q) = peak L p q"
proof -
  have pq: "p \<in> S" "q \<in> S" "fst p \<le> fst q" using assms(4) by (simp_all add: neighbours_def)
  have "\<bar>snd q - snd p\<bar> \<le> L * \<bar>fst q - fst p\<bar>" using assms(3) pq(1,2) unfolding rcons_def by blast
  then have c: "\<bar>snd q - snd p\<bar> \<le> L * (fst q - fst p)" using pq(3) by (simp add: abs_of_nonneg)
  note pt = peak_time_between[OF assms(2) pq(3) c]
  show "fst p \<le> peak_time L p q" "peak_time L p q \<le> fst q" by (rule pt(1)) (rule pt(2))
  have "upper L S (peak_time L p q) = min (cone_up L (peak_time L p q) p) (cone_up L (peak_time L p q) q)"
    by (rule upper_neighbours[OF assms(1) _ assms(3,4) pt(1,2)]) (use assms(2) in simp)
  then show "upper L S (peak_time L p q) = peak L p q" by (simp add: pt(3,4))
qed

theorem lower_valley_attained:
  assumes "finite S" "0 < L" "rcons L S" "neighbours S p q"
  shows "fst p \<le> valley_time L p q" "valley_time L p q \<le> fst q" "lower L S (valley_time L p q) = valley L p q"
proof -
  have pq: "p \<in> S" "q \<in> S" "fst p \<le> fst q" using assms(4) by (simp_all add: neighbours_def)
  have "\<bar>snd q - snd p\<bar> \<le> L * \<bar>fst q - fst p\<bar>" using assms(3) pq(1,2) unfolding rcons_def by blast
  then have c: "\<bar>snd q - snd p\<bar> \<le> L * (fst q - fst p)" using pq(3) by (simp add: abs_of_nonneg)
  note vt = valley_time_between[OF assms(2) pq(3) c]
  show "fst p \<le> valley_time L p q" "valley_time L p q \<le> fst q" by (rule vt(1)) (rule vt(2))
  have "lower L S (valley_time L p q) = max (cone_lo L (valley_time L p q) p) (cone_lo L (valley_time L p q) q)"
    by (rule lower_neighbours[OF assms(1) _ assms(3,4) vt(1,2)]) (use assms(2) in simp)
  then show "lower L S (valley_time L p q) = valley L p q" by (simp add: vt(3,4))
qed

lemma lower_zero: "lower 0 S t = lower 0 S u"
  by (simp add: lower_def cone_lo_def)

lemma upper_zero: "upper 0 S t = upper 0 S u"
  by (simp add: upper_def cone_up_def)


subsection \<open>A window above a level\<close>

text \<open>Whether the lower envelope stays at or above a level \<open>c\<close> on a whole window \<open>[a, b]\<close> of
  real time is decided by finitely many rational checks: the lower envelope at \<open>a\<close> and at
  \<open>b\<close>, and the valley of every pair of consecutive samples whose crossing lies in the window.
  The decision is exact: it holds if and only if every admissible signal is at or above
  \<open>c\<close> throughout the window. The proof uses that the lower envelope rises before the first
  sample and falls after the last one, and that between two consecutive samples it is the
  greater of the two lower cones, which falls up to their crossing and rises after it.\<close>

definition above_on :: "real \<Rightarrow> rsamples \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "above_on L S a b c \<longleftrightarrow> (\<forall>t. a \<le> t \<longrightarrow> t \<le> b \<longrightarrow> c \<le> lower L S t)"

definition above_check :: "real \<Rightarrow> rsamples \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "above_check L S a b c \<longleftrightarrow>
     c \<le> lower L S a \<and> c \<le> lower L S b \<and>
     (\<forall>p \<in> S. \<forall>q \<in> S. neighbours S p q \<longrightarrow> fst p < fst q \<longrightarrow> 0 < L \<longrightarrow>
        a \<le> valley_time L p q \<longrightarrow> valley_time L p q \<le> b \<longrightarrow> c \<le> valley L p q)"

lemma lower_rises_before:
  assumes "finite S" "S \<noteq> {}" "0 \<le> L" "u \<le> v" "\<And>r. r \<in> S \<Longrightarrow> v \<le> fst r"
  shows "lower L S u \<le> lower L S v"
proof -
  have "lower L S u \<in> cone_lo L u ` S" unfolding lower_def using assms(1,2) by (intro Max_in) simp_all
  then obtain r where r: "r \<in> S" "lower L S u = cone_lo L u r" by blast
  have "cone_lo L u r \<le> cone_lo L v r" by (rule cone_lo_inc[OF assms(3,4) assms(5)[OF r(1)]])
  also have "\<dots> \<le> lower L S v" unfolding lower_def using assms(1) r(1) by (intro Max_ge) simp_all
  finally show ?thesis using r(2) by simp
qed

lemma lower_falls_after:
  assumes "finite S" "S \<noteq> {}" "0 \<le> L" "u \<le> v" "\<And>r. r \<in> S \<Longrightarrow> fst r \<le> u"
  shows "lower L S v \<le> lower L S u"
proof -
  have "lower L S v \<in> cone_lo L v ` S" unfolding lower_def using assms(1,2) by (intro Max_in) simp_all
  then obtain r where r: "r \<in> S" "lower L S v = cone_lo L v r" by blast
  have "cone_lo L v r \<le> cone_lo L u r" by (rule cone_lo_dec[OF assms(3) assms(5)[OF r(1)] assms(4)])
  also have "\<dots> \<le> lower L S u" unfolding lower_def using assms(1) r(1) by (intro Max_ge) simp_all
  finally show ?thesis using r(2) by simp
qed

text \<open>Every time strictly between the first and the last sample has two neighbouring samples
  at different times.\<close>

lemma neighbours_exist:
  assumes "finite S" "p0 \<in> S" "q0 \<in> S" "fst p0 \<le> t" "t < fst q0"
  shows "\<exists>p q. neighbours S p q \<and> fst p \<le> t \<and> t < fst q"
proof -
  let ?A = "{r \<in> S. fst r \<le> t}" and ?B = "{r \<in> S. t < fst r}"
  have fA: "finite (fst ` ?A)" and fB: "finite (fst ` ?B)" using assms(1) by simp_all
  have "p0 \<in> ?A" using assms(2,4) by simp
  then have neA: "fst ` ?A \<noteq> {}" by blast
  have "q0 \<in> ?B" using assms(3,5) by simp
  then have neB: "fst ` ?B \<noteq> {}" by blast
  from Max_in[OF fA neA] obtain p where p: "p \<in> S" "fst p \<le> t" "fst p = Max (fst ` ?A)" by auto
  from Min_in[OF fB neB] obtain q where q: "q \<in> S" "t < fst q" "fst q = Min (fst ` ?B)" by auto
  have btw: "fst r \<le> fst p \<or> fst q \<le> fst r" if r: "r \<in> S" for r
  proof (cases "fst r \<le> t")
    case True
    with r have "fst r \<in> fst ` ?A" by auto
    then have "fst r \<le> fst p" unfolding p(3) using fA by (rule Max_ge[rotated])
    then show ?thesis ..
  next
    case False
    with r have "fst r \<in> fst ` ?B" by auto
    then have "fst q \<le> fst r" unfolding q(3) using fB by (rule Min_le[rotated])
    then show ?thesis ..
  qed
  have "fst p \<le> fst q" using p(2) q(2) by linarith
  then have "neighbours S p q" unfolding neighbours_def using p(1) q(1) btw by blast
  with p(2) q(2) show ?thesis by blast
qed

theorem above_check_sound:
  assumes "finite S" "S \<noteq> {}" "0 \<le> L" "rcons L S" "above_check L S a b c"
  shows "above_on L S a b c"
  unfolding above_on_def
proof (intro allI impI)
  fix t assume t: "a \<le> t" "t \<le> b"
  have at_a: "c \<le> lower L S a" and at_b: "c \<le> lower L S b" using assms(5) by (simp_all add: above_check_def)
  show "c \<le> lower L S t"
  proof (cases "L = 0")
    case True
    with at_a show ?thesis by (simp add: lower_zero[of S t a])
  next
    case L: False
    with assms(3) have Lpos: "0 < L" by simp
    let ?m = "Min (fst ` S)" and ?M = "Max (fst ` S)"
    have fm: "finite (fst ` S)" and nem: "fst ` S \<noteq> {}" using assms(1,2) by simp_all
    consider "t \<le> ?m" | "?M \<le> t" | "?m < t" "t < ?M" by linarith
    then show ?thesis
    proof cases
      case 1
      have "lower L S a \<le> lower L S t"
      proof (rule lower_rises_before[OF assms(1,2,3) t(1)])
        fix r assume "r \<in> S"
        then have "?m \<le> fst r" by (intro Min_le[OF fm] imageI)
        with 1 show "t \<le> fst r" by linarith
      qed
      with at_a show ?thesis by simp
    next
      case 2
      have "lower L S b \<le> lower L S t"
      proof (rule lower_falls_after[OF assms(1,2,3) t(2)])
        fix r assume "r \<in> S"
        then have "fst r \<le> ?M" by (intro Max_ge[OF fm] imageI)
        with 2 show "fst r \<le> t" by linarith
      qed
      with at_b show ?thesis by simp
    next
      case 3
      from Min_in[OF fm nem] obtain p0 where p0: "p0 \<in> S" "fst p0 = ?m" by auto
      from Max_in[OF fm nem] obtain q0 where q0: "q0 \<in> S" "fst q0 = ?M" by auto
      have "fst p0 \<le> t" "t < fst q0" using 3 p0(2) q0(2) by simp_all
      from neighbours_exist[OF assms(1) p0(1) q0(1) this]
      obtain p q where pq: "neighbours S p q" "fst p \<le> t" "t < fst q" by blast
      then have pqS: "p \<in> S" "q \<in> S" "fst p < fst q" by (auto simp: neighbours_def)
      note vt = lower_valley_attained[OF assms(1) Lpos assms(4) pq(1)]
      let ?T = "valley_time L p q"
      consider "a \<le> ?T" "?T \<le> b" | "?T < a" | "b < ?T" by linarith
      then show ?thesis
      proof cases
        case 1
        from assms(5) have "c \<le> valley L p q"
          unfolding above_check_def using pqS(1,2) pq(1) pqS(3) Lpos 1 by blast
        also have "\<dots> \<le> lower L S t" using valley_le_lower[OF assms(1) pqS(1,2) pq(2)] pq(3) by simp
        finally show ?thesis .
      next
        case 2
        have a: "fst p \<le> a" "a \<le> fst q" using 2 vt(1) t(1) pq(3) by linarith+
        have "2 * L * (valley_time L p q - a) \<le> 0" using 2 Lpos by (intro mult_nonneg_nonpos; linarith)
        with cone_lo_cross[OF Lpos a] have le: "cone_lo L a p \<le> cone_lo L a q" by linarith
        have "lower L S a = max (cone_lo L a p) (cone_lo L a q)"
          by (rule lower_neighbours[OF assms(1,3,4) pq(1) a])
        also have "\<dots> = cone_lo L a q" using le by (simp add: max_def)
        also have "\<dots> \<le> cone_lo L t q" by (rule cone_lo_inc[OF assms(3) t(1)]) (use pq(3) in simp)
        also have "\<dots> \<le> lower L S t" unfolding lower_def using assms(1) pqS(2) by (intro Max_ge) simp_all
        finally show ?thesis using at_a by simp
      next
        case 3
        have b: "fst p \<le> b" "b \<le> fst q" using 3 vt(2) t(2) pq(2) by linarith+
        have "0 \<le> 2 * L * (valley_time L p q - b)" using 3 Lpos by (intro mult_nonneg_nonneg; linarith)
        with cone_lo_cross[OF Lpos b] have le: "cone_lo L b q \<le> cone_lo L b p" by linarith
        have "lower L S b = max (cone_lo L b p) (cone_lo L b q)"
          by (rule lower_neighbours[OF assms(1,3,4) pq(1) b])
        also have "\<dots> = cone_lo L b p" using le by (simp add: max_def)
        also have "\<dots> \<le> cone_lo L t p" by (rule cone_lo_dec[OF assms(3) pq(2) t(2)])
        also have "\<dots> \<le> lower L S t" unfolding lower_def using assms(1) pqS(1) by (intro Max_ge) simp_all
        finally show ?thesis using at_b by simp
      qed
    qed
  qed
qed

theorem above_check_complete:
  assumes "finite S" "0 \<le> L" "rcons L S" "a \<le> b" "above_on L S a b c"
  shows "above_check L S a b c"
  unfolding above_check_def
proof (intro conjI ballI impI)
  show "c \<le> lower L S a" "c \<le> lower L S b" using assms(4,5) by (simp_all add: above_on_def)
  fix p q assume "p \<in> S" "q \<in> S" and n: "neighbours S p q" "fst p < fst q" "0 < L"
    and T: "a \<le> valley_time L p q" "valley_time L p q \<le> b"
  from assms(5) T have "c \<le> lower L S (valley_time L p q)" by (simp add: above_on_def)
  also have "\<dots> = valley L p q" by (rule lower_valley_attained(3)[OF assms(1) n(3) assms(3) n(1)])
  finally show "c \<le> valley L p q" .
qed

corollary above_check_iff:
  assumes "finite S" "S \<noteq> {}" "0 \<le> L" "rcons L S" "a \<le> b"
  shows "above_check L S a b c \<longleftrightarrow> above_on L S a b c"
  using above_check_sound[OF assms(1-4)] above_check_complete[OF assms(1,3,4,5)] by blast

text \<open>The decision is final under more samples: the lower envelope only rises.\<close>

theorem above_on_mono:
  assumes "finite S'" "S \<subseteq> S'" "S \<noteq> {}" "above_on L S a b c"
  shows "above_on L S' a b c"
  using assms envelope_antitone(1)[OF assms(1,2,3)] unfolding above_on_def by (meson order_trans)


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


subsection \<open>Between two samples, in rational arithmetic\<close>

text \<open>The results on neighbouring samples, on the extremes between two consecutive samples
  and on a window above a level, cast to the rational samples and bounds of a trace. The
  decision whether the lower envelope stays at or above a level on a window is then a
  finite rational computation, \<open>above_cert\<close>, proved exact for consistent samples.\<close>

definition real_sample :: "int \<times> rat \<Rightarrow> real \<times> real" where
  "real_sample p = (of_int (fst p), of_rat (snd p))"

lemma real_samples_eq: "real_samples S = real_sample ` S"
  by (simp add: real_samples_def real_sample_def)

lemma real_sample_inj: "real_sample p = real_sample q \<longleftrightarrow> p = q"
  by (simp add: real_sample_def of_rat_eq_iff prod_eq_iff)

definition qneighbours :: "samples \<Rightarrow> int \<times> rat \<Rightarrow> int \<times> rat \<Rightarrow> bool" where
  "qneighbours S p q \<longleftrightarrow> p \<in> S \<and> q \<in> S \<and> fst p \<le> fst q \<and> (\<forall>r \<in> S. fst r \<le> fst p \<or> fst q \<le> fst r)"

lemma qneighbours_cast: "neighbours (real_samples S) (real_sample p) (real_sample q) \<longleftrightarrow> qneighbours S p q"
  by (auto simp: neighbours_def qneighbours_def real_samples_eq real_sample_inj real_sample_def)

lemma of_rat_min: "of_rat (min a b) = min (of_rat a) (of_rat b :: real)"
  by (simp add: min_def of_rat_less_eq)

lemma of_rat_max: "of_rat (max a b) = max (of_rat a) (of_rat b :: real)"
  by (simp add: max_def of_rat_less_eq)

lemma of_rat_pos_iff: "0 < (of_rat q :: real) \<longleftrightarrow> 0 < q"
  using of_rat_less[of 0 q] by simp

lemma of_int_le_of_rat_iff: "(of_int k :: real) \<le> of_rat t \<longleftrightarrow> (of_int k :: rat) \<le> t"
  using of_rat_less_eq[of "of_int k" t] by simp

lemma of_rat_le_of_int_iff: "(of_rat t :: real) \<le> of_int k \<longleftrightarrow> t \<le> (of_int k :: rat)"
  using of_rat_less_eq[of t "of_int k"] by simp

lemma real_sample_fst_less: "fst (real_sample p) < fst (real_sample q) \<longleftrightarrow> fst p < fst q"
  by (simp add: real_sample_def)

lemma qcone_up_cast': "of_rat (qcone_up L t p) = cone_up (of_rat L) (of_rat t) (real_sample p)"
  by (simp add: real_sample_def qcone_up_cast)

lemma qcone_lo_cast': "of_rat (qcone_lo L t p) = cone_lo (of_rat L) (of_rat t) (real_sample p)"
  by (simp add: real_sample_def qcone_lo_cast)

theorem enc_neighbours:
  assumes "finite S" "0 \<le> L" "consistent L S" "qneighbours S p q" "of_int (fst p) \<le> t" "t \<le> of_int (fst q)"
  shows "hi L S t = min (qcone_up L t p) (qcone_up L t q)"
    and "lo L S t = max (qcone_lo L t p) (qcone_lo L t q)"
proof -
  have ne: "S \<noteq> {}" using assms(4) by (auto simp: qneighbours_def)
  have n: "neighbours (real_samples S) (real_sample p) (real_sample q)"
    using assms(4) by (simp add: qneighbours_cast)
  have t: "fst (real_sample p) \<le> of_rat t" "of_rat t \<le> fst (real_sample q)"
    using assms(5,6) by (simp_all add: real_sample_def of_int_le_of_rat_iff of_rat_le_of_int_iff)
  have fin: "finite (real_samples S)" using assms(1) by simp
  have rc: "rcons (of_rat L) (real_samples S)" using assms(3) by (simp add: consistent_rcons)
  have "(of_rat (hi L S t) :: real) = upper (of_rat L) (real_samples S) (of_rat t)" by (rule hi_cast[OF assms(1) ne])
  also have "\<dots> = min (cone_up (of_rat L) (of_rat t) (real_sample p)) (cone_up (of_rat L) (of_rat t) (real_sample q))"
    by (rule upper_neighbours[OF fin of_rat_nonneg[OF assms(2)] rc n t])
  also have "\<dots> = of_rat (min (qcone_up L t p) (qcone_up L t q))" by (simp add: of_rat_min qcone_up_cast')
  finally show "hi L S t = min (qcone_up L t p) (qcone_up L t q)" by (simp add: of_rat_eq_iff)
  have "(of_rat (lo L S t) :: real) = lower (of_rat L) (real_samples S) (of_rat t)" by (rule lo_cast[OF assms(1) ne])
  also have "\<dots> = max (cone_lo (of_rat L) (of_rat t) (real_sample p)) (cone_lo (of_rat L) (of_rat t) (real_sample q))"
    by (rule lower_neighbours[OF fin of_rat_nonneg[OF assms(2)] rc n t])
  also have "\<dots> = of_rat (max (qcone_lo L t p) (qcone_lo L t q))" by (simp add: of_rat_max qcone_lo_cast')
  finally show "lo L S t = max (qcone_lo L t p) (qcone_lo L t q)" by (simp add: of_rat_eq_iff)
qed

definition qpeak :: "rat \<Rightarrow> int \<times> rat \<Rightarrow> int \<times> rat \<Rightarrow> rat" where
  "qpeak L p q = (snd p + snd q) / 2 + L * of_int (fst q - fst p) / 2"

definition qvalley :: "rat \<Rightarrow> int \<times> rat \<Rightarrow> int \<times> rat \<Rightarrow> rat" where
  "qvalley L p q = (snd p + snd q) / 2 - L * of_int (fst q - fst p) / 2"

definition qvalley_time :: "rat \<Rightarrow> int \<times> rat \<Rightarrow> int \<times> rat \<Rightarrow> rat" where
  "qvalley_time L p q = of_int (fst p + fst q) / 2 + (snd p - snd q) / (2 * L)"

lemma qpeak_cast: "of_rat (qpeak L p q) = peak (of_rat L) (real_sample p) (real_sample q)"
  by (simp add: qpeak_def peak_def real_sample_def of_rat_add of_rat_diff of_rat_mult of_rat_divide)

lemma qvalley_cast: "of_rat (qvalley L p q) = valley (of_rat L) (real_sample p) (real_sample q)"
  by (simp add: qvalley_def valley_def real_sample_def of_rat_add of_rat_diff of_rat_mult of_rat_divide)

lemma qvalley_time_cast: "of_rat (qvalley_time L p q) = valley_time (of_rat L) (real_sample p) (real_sample q)"
  by (simp add: qvalley_time_def valley_time_def real_sample_def of_rat_add of_rat_diff of_rat_mult of_rat_divide)

text \<open>Between two samples the upper bound of the enclosure is at most the peak and the lower
  bound at least the valley; between two consecutive samples of a consistent set, under a
  positive bound, the lower bound of the enclosure is the valley at the crossing time.\<close>

theorem hi_le_qpeak:
  assumes "finite S" "p \<in> S" "q \<in> S" "of_int (fst p) \<le> t" "t \<le> of_int (fst q)"
  shows "hi L S t \<le> qpeak L p q"
proof -
  have ne: "S \<noteq> {}" using assms(2) by blast
  have "(of_rat (hi L S t) :: real) = upper (of_rat L) (real_samples S) (of_rat t)" by (rule hi_cast[OF assms(1) ne])
  also have "\<dots> \<le> peak (of_rat L) (real_sample p) (real_sample q)"
    using assms by (intro upper_le_peak)
      (simp_all add: real_samples_eq real_sample_def of_int_le_of_rat_iff of_rat_le_of_int_iff)
  also have "\<dots> = of_rat (qpeak L p q)" by (simp add: qpeak_cast)
  finally show ?thesis by (simp add: of_rat_less_eq)
qed

theorem qvalley_le_lo:
  assumes "finite S" "p \<in> S" "q \<in> S" "of_int (fst p) \<le> t" "t \<le> of_int (fst q)"
  shows "qvalley L p q \<le> lo L S t"
proof -
  have ne: "S \<noteq> {}" using assms(2) by blast
  have "(of_rat (qvalley L p q) :: real) = valley (of_rat L) (real_sample p) (real_sample q)" by (rule qvalley_cast)
  also have "\<dots> \<le> lower (of_rat L) (real_samples S) (of_rat t)"
    using assms by (intro valley_le_lower)
      (simp_all add: real_samples_eq real_sample_def of_int_le_of_rat_iff of_rat_le_of_int_iff)
  also have "\<dots> = of_rat (lo L S t)" by (rule lo_cast[OF assms(1) ne, symmetric])
  finally show ?thesis by (simp add: of_rat_less_eq)
qed

theorem lo_qvalley_attained:
  assumes "finite S" "0 < L" "consistent L S" "qneighbours S p q"
  shows "of_int (fst p) \<le> qvalley_time L p q" "qvalley_time L p q \<le> of_int (fst q)"
    and "lo L S (qvalley_time L p q) = qvalley L p q"
proof -
  have ne: "S \<noteq> {}" using assms(4) by (auto simp: qneighbours_def)
  have fin: "finite (real_samples S)" using assms(1) by simp
  have Lpos: "0 < (of_rat L :: real)" using assms(2) by (simp add: of_rat_pos_iff)
  have rc: "rcons (of_rat L) (real_samples S)" using assms(3) by (simp add: consistent_rcons)
  have n: "neighbours (real_samples S) (real_sample p) (real_sample q)" using assms(4) by (simp add: qneighbours_cast)
  note vt = lower_valley_attained[OF fin Lpos rc n]
  show "of_int (fst p) \<le> qvalley_time L p q"
    using vt(1) unfolding qvalley_time_cast[symmetric] by (simp add: real_sample_def of_int_le_of_rat_iff)
  show "qvalley_time L p q \<le> of_int (fst q)"
    using vt(2) unfolding qvalley_time_cast[symmetric] by (simp add: real_sample_def of_rat_le_of_int_iff)
  have "(of_rat (lo L S (qvalley_time L p q)) :: real) = lower (of_rat L) (real_samples S) (of_rat (qvalley_time L p q))"
    by (rule lo_cast[OF assms(1) ne])
  also have "\<dots> = valley (of_rat L) (real_sample p) (real_sample q)" using vt(3) by (simp add: qvalley_time_cast)
  also have "\<dots> = of_rat (qvalley L p q)" by (simp add: qvalley_cast)
  finally show "lo L S (qvalley_time L p q) = qvalley L p q" by (simp add: of_rat_eq_iff)
qed

definition above_cert :: "rat \<Rightarrow> samples \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> bool" where
  "above_cert L S a b c \<longleftrightarrow>
     c \<le> lo L S a \<and> c \<le> lo L S b \<and>
     (\<forall>p \<in> S. \<forall>q \<in> S. qneighbours S p q \<longrightarrow> fst p < fst q \<longrightarrow> 0 < L \<longrightarrow>
        a \<le> qvalley_time L p q \<longrightarrow> qvalley_time L p q \<le> b \<longrightarrow> c \<le> qvalley L p q)"

lemma above_cert_cast:
  assumes "finite S" "S \<noteq> {}"
  shows "above_check (of_rat L) (real_samples S) (of_rat a) (of_rat b) (of_rat c) \<longleftrightarrow> above_cert L S a b c"
proof -
  have ball: "(\<forall>p \<in> real_samples S. \<forall>q \<in> real_samples S. P p q) \<longleftrightarrow>
              (\<forall>p \<in> S. \<forall>q \<in> S. P (real_sample p) (real_sample q))" for P
    by (simp add: real_samples_eq)
  show ?thesis
    unfolding above_check_def above_cert_def ball
    by (simp add: qneighbours_cast of_rat_pos_iff real_sample_fst_less lo_cast[OF assms, symmetric]
        qvalley_time_cast[symmetric] qvalley_cast[symmetric] of_rat_less_eq)
qed

theorem above_cert_iff:
  assumes "finite S" "S \<noteq> {}" "0 \<le> L" "consistent L S" "a \<le> b"
  shows "above_cert L S a b c \<longleftrightarrow> above_on (of_rat L) (real_samples S) (of_rat a) (of_rat b) (of_rat c)"
  using above_check_iff[of "real_samples S" "of_rat L" "of_rat a" "of_rat b" "of_rat c"] assms
  by (simp add: above_cert_cast of_rat_nonneg consistent_rcons of_rat_less_eq)

lemma adm_nonneg: "adm L S f \<Longrightarrow> 0 \<le> L"
proof -
  assume "adm L S f"
  then have "lip (of_rat L) f" by (simp add: adm_def)
  from lipD[OF this, of 1 0] have "\<bar>f 1 - f 0\<bar> \<le> of_rat L" by simp
  with abs_ge_zero[of "f 1 - f 0"] have "(0 :: real) \<le> of_rat L" by linarith
  then show "0 \<le> L" using of_rat_less_eq[of 0 L] by simp
qed

text \<open>Soundness of the decision for every admissible signal, and finality under more
  consistent samples.\<close>

theorem above_cert_adm:
  assumes "finite S" "S \<noteq> {}" "above_cert L S a b c" "adm L S f" "of_rat a \<le> t" "t \<le> of_rat b"
  shows "of_rat c \<le> f t"
proof -
  have lp: "lip (of_rat L) f" "through (real_samples S) f" using assms(4) by (simp_all add: adm_def)
  have rc: "rcons (of_rat L) (real_samples S)" by (rule lip_through_rcons[OF lp])
  have ck: "above_check (of_rat L) (real_samples S) (of_rat a) (of_rat b) (of_rat c)"
    using assms(3) by (simp add: above_cert_cast[OF assms(1,2)])
  have "above_on (of_rat L) (real_samples S) (of_rat a) (of_rat b) (of_rat c)"
    by (rule above_check_sound[OF _ _ _ rc ck]) (simp_all add: assms(1,2) of_rat_nonneg adm_nonneg[OF assms(4)])
  then have "of_rat c \<le> lower (of_rat L) (real_samples S) t" using assms(5,6) by (simp add: above_on_def)
  also have "\<dots> \<le> f t" using assms(1,2,4) by (intro lower_le_lip) (simp_all add: adm_def)
  finally show ?thesis .
qed

theorem above_cert_mono:
  assumes "finite S'" "S \<subseteq> S'" "S \<noteq> {}" "0 \<le> L" "consistent L S'" "a \<le> b" "above_cert L S a b c"
  shows "above_cert L S' a b c"
proof -
  have fS: "finite S" using assms(2,1) by (rule finite_subset)
  have cS: "consistent L S" using assms(2,5) by (rule consistent_subset)
  have "above_on (of_rat L) (real_samples S) (of_rat a) (of_rat b) (of_rat c)"
    using assms(7) by (simp add: above_cert_iff[OF fS assms(3,4) cS assms(6)])
  then have "above_on (of_rat L) (real_samples S') (of_rat a) (of_rat b) (of_rat c)"
    using assms(1,2,3) by (intro above_on_mono[of "real_samples S'" "real_samples S"]) (simp_all add: real_samples_mono)
  moreover have "S' \<noteq> {}" using assms(2,3) by blast
  ultimately show ?thesis by (simp add: above_cert_iff[OF assms(1) _ assms(4,5,6)])
qed


section \<open>Interval evaluation\<close>

text \<open>An interval state maps a name to an interval value, or to nothing. An interval value
  is a closed interval of rationals, given by its bounds, for a quantity that is a number,
  or an exact value of another kind, a Boolean, a string or a time, which no rate bound
  applies to and which an interval state carries as a state does. The point state of a
  state maps a numeric value to the interval of that value alone and every other value to
  itself; it has the domain of the state.\<close>

datatype ival = IvNum rat rat | IvBool bool | IvStr String.literal | IvTime int

type_synonym 'n istate = "'n \<rightharpoonup> ival"

fun ival_of :: "atom \<Rightarrow> ival" where
  "ival_of (ANum q) = IvNum q q"
| "ival_of (ABool b) = IvBool b"
| "ival_of (AStr s) = IvStr s"
| "ival_of (ATime t) = IvTime t"

definition point :: "('n, atom) state \<Rightarrow> 'n istate" where
  "point \<sigma> x = map_option ival_of (\<sigma> x)"

text \<open>A comparison of two numeric intervals is true when it holds for every pair of values
  in them, false when it fails for every pair, and undefined otherwise. Two exact values
  are equal when they are the same value; a number and a value of another kind are never
  equal; and an ordering comparison with an operand that is not a number is false, as
  \<open>vless\<close> and \<open>vleq\<close> are false on such operands in the core.\<close>

fun ilt :: "ival \<Rightarrow> ival \<Rightarrow> bool option" where
  "ilt (IvNum p q) (IvNum p' q') = (if q < p' then Some True else if q' \<le> p then Some False else None)"
| "ilt _ _ = Some False"

fun ile :: "ival \<Rightarrow> ival \<Rightarrow> bool option" where
  "ile (IvNum p q) (IvNum p' q') = (if q \<le> p' then Some True else if q' < p then Some False else None)"
| "ile _ _ = Some False"

fun ieq :: "ival \<Rightarrow> ival \<Rightarrow> bool option" where
  "ieq (IvNum p q) (IvNum p' q') =
     (if p = q \<and> p' = q' \<and> p = p' then Some True else if q < p' \<or> q' < p then Some False else None)"
| "ieq (IvBool b) (IvBool b') = Some (b = b')"
| "ieq (IvStr s) (IvStr s') = Some (s = s')"
| "ieq (IvTime t) (IvTime t') = Some (t = t')"
| "ieq _ _ = Some False"

primrec evalVI :: "('n, atom) vexp \<Rightarrow> 'n istate \<Rightarrow> ival option" where
  "evalVI (VConst v) I = Some (ival_of v)"
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

text \<open>The interval evaluation of the point state of a state is the evaluation of the state,
  for every state and every condition: the three-valued evaluation of the core is the
  special case of exact readings.\<close>

lemma ieq_ival_of: "ieq (ival_of u) (ival_of w) = Some (u = w)"
  by (cases u; cases w) simp_all

lemma ilt_ival_of: "ilt (ival_of u) (ival_of w) = Some (vless u w)"
  by (cases u; cases w) simp_all

lemma ile_ival_of: "ile (ival_of u) (ival_of w) = Some (vleq u w)"
  by (cases u; cases w) simp_all

lemma point_dom: "dom (point \<sigma>) = dom \<sigma>"
  by (auto simp: point_def dom_def)

lemma evalVI_point: "evalVI a (point \<sigma>) = map_option ival_of (evalV a \<sigma>)"
  by (induction a) (auto simp: point_def split: option.splits)

theorem evalI_point: "evalI e (point \<sigma>) = eval e \<sigma>"
proof (induction e)
  case (EEq a b)
  show ?case by (auto simp: evalVI_point ieq_ival_of split: option.splits)
next
  case (ELt a b)
  show ?case by (auto simp: evalVI_point ilt_ival_of split: option.splits)
next
  case (ELe a b)
  show ?case by (auto simp: evalVI_point ile_ival_of split: option.splits)
qed (simp_all add: point_dom)


subsection \<open>Soundness for real values\<close>

text \<open>A signal has real values, so a condition read on signals is evaluated on a real
  valuation: a partial map from names to real values, a real number or an exact value of
  another kind, with the numeric constants of the condition cast to the reals, the
  comparisons of the reals, and the strong Kleene connectives. On rational values this
  reading is the evaluation of the core (\<open>evalR_eval\<close>).\<close>

datatype rval = RNum real | RBool bool | RStr String.literal | RTime int

type_synonym 'n rstate = "'n \<rightharpoonup> rval"

fun rval_of :: "atom \<Rightarrow> rval" where
  "rval_of (ANum q) = RNum (of_rat q)"
| "rval_of (ABool b) = RBool b"
| "rval_of (AStr s) = RStr s"
| "rval_of (ATime t) = RTime t"

fun rlt :: "rval \<Rightarrow> rval \<Rightarrow> bool" where
  "rlt (RNum u) (RNum w) = (u < w)"
| "rlt _ _ = False"

fun rle :: "rval \<Rightarrow> rval \<Rightarrow> bool" where
  "rle (RNum u) (RNum w) = (u \<le> w)"
| "rle _ _ = False"

primrec evalVR :: "('n, atom) vexp \<Rightarrow> 'n rstate \<Rightarrow> rval option" where
  "evalVR (VConst v) \<rho> = Some (rval_of v)"
| "evalVR (VName x) \<rho> = \<rho> x"
| "evalVR (VDefault x a) \<rho> = (case \<rho> x of Some r \<Rightarrow> Some r | None \<Rightarrow> evalVR a \<rho>)"

primrec evalR :: "('n, atom) expr \<Rightarrow> 'n rstate \<Rightarrow> bool option" where
  "evalR ETrue \<rho> = Some True"
| "evalR EFalse \<rho> = Some False"
| "evalR (EEq a b) \<rho> =
     (case evalVR a \<rho> of None \<Rightarrow> None | Some u \<Rightarrow> (case evalVR b \<rho> of None \<Rightarrow> None | Some w \<Rightarrow> Some (u = w)))"
| "evalR (ELt a b) \<rho> =
     (case evalVR a \<rho> of None \<Rightarrow> None | Some u \<Rightarrow> (case evalVR b \<rho> of None \<Rightarrow> None | Some w \<Rightarrow> Some (rlt u w)))"
| "evalR (ELe a b) \<rho> =
     (case evalVR a \<rho> of None \<Rightarrow> None | Some u \<Rightarrow> (case evalVR b \<rho> of None \<Rightarrow> None | Some w \<Rightarrow> Some (rle u w)))"
| "evalR (ENot e) \<rho> = knot (evalR e \<rho>)"
| "evalR (EAnd e\<^sub>1 e\<^sub>2) \<rho> = kand (evalR e\<^sub>1 \<rho>) (evalR e\<^sub>2 \<rho>)"
| "evalR (EOr e\<^sub>1 e\<^sub>2) \<rho> = kor (evalR e\<^sub>1 \<rho>) (evalR e\<^sub>2 \<rho>)"
| "evalR (EImp e\<^sub>1 e\<^sub>2) \<rho> = kimp (evalR e\<^sub>1 \<rho>) (evalR e\<^sub>2 \<rho>)"
| "evalR (EPresent x) \<rho> = Some (x \<in> dom \<rho>)"

text \<open>The real valuation of a state: each numeric value cast to the reals, every other
  value kept.\<close>

definition real_state :: "('n, atom) state \<Rightarrow> 'n rstate" where
  "real_state \<sigma> x = map_option rval_of (\<sigma> x)"

lemma rval_of_eq: "rval_of u = rval_of w \<longleftrightarrow> u = w"
  by (cases u; cases w) (simp_all add: of_rat_eq_iff)

lemma rlt_rval_of: "rlt (rval_of u) (rval_of w) = vless u w"
  by (cases u; cases w) (simp_all add: of_rat_less)

lemma rle_rval_of: "rle (rval_of u) (rval_of w) = vleq u w"
  by (cases u; cases w) (simp_all add: of_rat_less_eq)

lemma real_state_dom: "dom (real_state \<sigma>) = dom \<sigma>"
  by (auto simp: real_state_def dom_def)

lemma evalVR_real_state: "evalVR a (real_state \<sigma>) = map_option rval_of (evalV a \<sigma>)"
  by (induction a) (auto simp: real_state_def split: option.splits)

theorem evalR_eval: "evalR e (real_state \<sigma>) = eval e \<sigma>"
proof (induction e)
  case (EEq a b)
  show ?case by (auto simp: evalVR_real_state rval_of_eq split: option.splits)
next
  case (ELt a b)
  show ?case by (auto simp: evalVR_real_state rlt_rval_of split: option.splits)
next
  case (ELe a b)
  show ?case by (auto simp: evalVR_real_state rle_rval_of split: option.splits)
qed (simp_all add: real_state_dom)

text \<open>A real value lies in an interval value if it is a real number in the numeric
  interval or the same exact value. A real valuation lies inside an interval state if
  every name with an interval value has a value in it.\<close>

fun inval :: "ival \<Rightarrow> rval \<Rightarrow> bool" where
  "inval (IvNum p q) (RNum r) = (of_rat p \<le> r \<and> r \<le> of_rat q)"
| "inval (IvBool b) (RBool b') = (b = b')"
| "inval (IvStr s) (RStr s') = (s = s')"
| "inval (IvTime t) (RTime t') = (t = t')"
| "inval _ _ = False"

definition inside :: "'n istate \<Rightarrow> 'n rstate \<Rightarrow> bool" where
  "inside I \<rho> \<longleftrightarrow> (\<forall>x i. I x = Some i \<longrightarrow> (\<exists>r. \<rho> x = Some r \<and> inval i r))"

lemma inval_ival_of: "inval (ival_of v) (rval_of v)"
  by (cases v) simp_all

lemma inval_num: "inval (IvNum p q) r \<Longrightarrow> \<exists>u. r = RNum u \<and> of_rat p \<le> u \<and> u \<le> of_rat q"
  by (cases r) simp_all

lemma inval_bool: "inval (IvBool b) r \<Longrightarrow> r = RBool b"
  by (cases r) simp_all

lemma inval_str: "inval (IvStr s) r \<Longrightarrow> r = RStr s"
  by (cases r) simp_all

lemma inval_time: "inval (IvTime t) r \<Longrightarrow> r = RTime t"
  by (cases r) simp_all

lemma evalVI_inside:
  assumes "inside I \<rho>" "default_free a" "evalVI a I = Some i"
  shows "\<exists>r. evalVR a \<rho> = Some r \<and> inval i r"
  using assms by (cases a) (auto simp: inside_def inval_ival_of)

lemma ilt_num_sound:
  fixes r r' :: real
  assumes "ilt (IvNum p q) (IvNum p' q') = Some b" "of_rat p \<le> r" "r \<le> of_rat q" "of_rat p' \<le> r'" "r' \<le> of_rat q'"
  shows "(r < r') = b"
proof (cases b)
  case True
  with assms(1) have "q < p'" by (simp split: if_splits)
  then have "(of_rat q :: real) < of_rat p'" by (simp add: of_rat_less)
  with assms(3,4) have "r < r'" by linarith
  with True show ?thesis by simp
next
  case False
  with assms(1) have "q' \<le> p" by (simp split: if_splits)
  then have "(of_rat q' :: real) \<le> of_rat p" by (simp add: of_rat_less_eq)
  with assms(2,5) have "\<not> r < r'" by linarith
  with False show ?thesis by simp
qed

lemma ile_num_sound:
  fixes r r' :: real
  assumes "ile (IvNum p q) (IvNum p' q') = Some b" "of_rat p \<le> r" "r \<le> of_rat q" "of_rat p' \<le> r'" "r' \<le> of_rat q'"
  shows "(r \<le> r') = b"
proof (cases b)
  case True
  with assms(1) have "q \<le> p'" by (simp split: if_splits)
  then have "(of_rat q :: real) \<le> of_rat p'" by (simp add: of_rat_less_eq)
  with assms(3,4) have "r \<le> r'" by linarith
  with True show ?thesis by simp
next
  case False
  with assms(1) have "q' < p" by (simp split: if_splits)
  then have "(of_rat q' :: real) < of_rat p" by (simp add: of_rat_less)
  with assms(2,5) have "\<not> r \<le> r'" by linarith
  with False show ?thesis by simp
qed

lemma ieq_num_sound:
  fixes r r' :: real
  assumes "ieq (IvNum p q) (IvNum p' q') = Some b" "of_rat p \<le> r" "r \<le> of_rat q" "of_rat p' \<le> r'" "r' \<le> of_rat q'"
  shows "(r = r') = b"
proof (cases b)
  case True
  with assms(1) have eq: "p = q" "p' = q'" "p = p'" by (simp_all split: if_splits)
  then have eq': "p' = q" "q' = q" by simp_all
  have "r = of_rat q" using assms(2,3) eq(1) by (simp add: order_antisym)
  moreover have "r' = of_rat q" using assms(4,5) eq' by (simp add: order_antisym)
  ultimately show ?thesis using True by simp
next
  case False
  with assms(1) have "q < p' \<or> q' < p" by (simp split: if_splits)
  then have "(of_rat q :: real) < of_rat p' \<or> (of_rat q' :: real) < of_rat p" by (simp add: of_rat_less)
  with assms(2-5) have "r \<noteq> r'" by linarith
  with False show ?thesis by simp
qed

lemma ilt_sound:
  assumes "ilt i j = Some b" "inval i r" "inval j r'"
  shows "rlt r r' = b"
proof (cases i)
  case (IvNum p q)
  with assms(2) obtain u where u: "r = RNum u" "of_rat p \<le> u" "u \<le> of_rat q" by (auto dest: inval_num)
  show ?thesis
  proof (cases j)
    case (IvNum p' q')
    with assms(3) obtain w where w: "r' = RNum w" "of_rat p' \<le> w" "w \<le> of_rat q'" by (auto dest: inval_num)
    from assms(1) \<open>i = IvNum p q\<close> IvNum have "ilt (IvNum p q) (IvNum p' q') = Some b" by simp
    from ilt_num_sound[OF this u(2,3) w(2,3)] u(1) w(1) show ?thesis by simp
  qed (use assms(1,3) \<open>i = IvNum p q\<close> u(1) in \<open>auto dest!: inval_bool inval_str inval_time\<close>)
qed (use assms in \<open>auto dest!: inval_bool inval_str inval_time\<close>)

lemma ile_sound:
  assumes "ile i j = Some b" "inval i r" "inval j r'"
  shows "rle r r' = b"
proof (cases i)
  case (IvNum p q)
  with assms(2) obtain u where u: "r = RNum u" "of_rat p \<le> u" "u \<le> of_rat q" by (auto dest: inval_num)
  show ?thesis
  proof (cases j)
    case (IvNum p' q')
    with assms(3) obtain w where w: "r' = RNum w" "of_rat p' \<le> w" "w \<le> of_rat q'" by (auto dest: inval_num)
    from assms(1) \<open>i = IvNum p q\<close> IvNum have "ile (IvNum p q) (IvNum p' q') = Some b" by simp
    from ile_num_sound[OF this u(2,3) w(2,3)] u(1) w(1) show ?thesis by simp
  qed (use assms(1,3) \<open>i = IvNum p q\<close> u(1) in \<open>auto dest!: inval_bool inval_str inval_time\<close>)
qed (use assms in \<open>auto dest!: inval_bool inval_str inval_time\<close>)

lemma ieq_sound:
  assumes "ieq i j = Some b" "inval i r" "inval j r'"
  shows "(r = r') = b"
proof (cases i)
  case (IvNum p q)
  with assms(2) obtain u where u: "r = RNum u" "of_rat p \<le> u" "u \<le> of_rat q" by (auto dest: inval_num)
  show ?thesis
  proof (cases j)
    case (IvNum p' q')
    with assms(3) obtain w where w: "r' = RNum w" "of_rat p' \<le> w" "w \<le> of_rat q'" by (auto dest: inval_num)
    from assms(1) \<open>i = IvNum p q\<close> IvNum have "ieq (IvNum p q) (IvNum p' q') = Some b" by simp
    from ieq_num_sound[OF this u(2,3) w(2,3)] u(1) w(1) show ?thesis by simp
  qed (use assms(1,3) \<open>i = IvNum p q\<close> u(1) in \<open>auto dest!: inval_bool inval_str inval_time\<close>)
next
  case (IvBool b')
  with assms show ?thesis by (cases j) (auto dest!: inval_bool inval_str inval_time inval_num)
next
  case (IvStr s)
  with assms show ?thesis by (cases j) (auto dest!: inval_bool inval_str inval_time inval_num)
next
  case (IvTime t)
  with assms show ?thesis by (cases j) (auto dest!: inval_bool inval_str inval_time inval_num)
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
    then obtain i j where u: "evalVI a I = Some i" and w: "evalVI b I = Some j" and c: "ieq i j = Some b'"
      by (auto split: option.splits)
    from EEq have "default_free a" "default_free b" by simp_all
    with evalVI_inside[OF assms(2) _ u] evalVI_inside[OF assms(2) _ w] obtain r r'
      where rr: "evalVR a \<rho> = Some r" "inval i r" and rr': "evalVR b \<rho> = Some r'" "inval j r'" by blast
    from ieq_sound[OF c rr(2) rr'(2)] rr(1) rr'(1) Some show ?thesis by (simp add: approx_def)
  qed (simp add: approx_def)
next
  case (ELt a b)
  show ?case
  proof (cases "evalI (ELt a b) I")
    case (Some b')
    then obtain i j where u: "evalVI a I = Some i" and w: "evalVI b I = Some j" and c: "ilt i j = Some b'"
      by (auto split: option.splits)
    from ELt have "default_free a" "default_free b" by simp_all
    with evalVI_inside[OF assms(2) _ u] evalVI_inside[OF assms(2) _ w] obtain r r'
      where rr: "evalVR a \<rho> = Some r" "inval i r" and rr': "evalVR b \<rho> = Some r'" "inval j r'" by blast
    from ilt_sound[OF c rr(2) rr'(2)] rr(1) rr'(1) Some show ?thesis by (simp add: approx_def)
  qed (simp add: approx_def)
next
  case (ELe a b)
  show ?case
  proof (cases "evalI (ELe a b) I")
    case (Some b')
    then obtain i j where u: "evalVI a I = Some i" and w: "evalVI b I = Some j" and c: "ile i j = Some b'"
      by (auto split: option.splits)
    from ELe have "default_free a" "default_free b" by simp_all
    with evalVI_inside[OF assms(2) _ u] evalVI_inside[OF assms(2) _ w] obtain r r'
      where rr: "evalVR a \<rho> = Some r" "inval i r" and rr': "evalVR b \<rho> = Some r'" "inval j r'" by blast
    from ile_sound[OF c rr(2) rr'(2)] rr(1) rr'(1) Some show ?thesis by (simp add: approx_def)
  qed (simp add: approx_def)
qed (simp_all add: knot_mono kand_mono kor_mono kimp_mono)

corollary evalI_sound_value:
  assumes "present_free e" "inside I \<rho>" "evalI e I = Some b"
  shows "evalR e \<rho> = Some b"
  using evalI_sound[OF assms(1,2)] assms(3) by (simp add: approx_def)


subsection \<open>Monotonicity under narrowing\<close>

text \<open>An interval value narrows to another if a numeric interval keeps an interval inside
  it and an exact value stays the same; an interval state narrows to another if every name
  with an interval value keeps one that is narrower: the interval form of the information
  order. A definite value of a PRESENT-free condition survives narrowing.\<close>

fun narrower :: "ival \<Rightarrow> ival \<Rightarrow> bool" where
  "narrower (IvNum p q) (IvNum p' q') = (p \<le> p' \<and> q' \<le> q)"
| "narrower (IvBool b) (IvBool b') = (b = b')"
| "narrower (IvStr s) (IvStr s') = (s = s')"
| "narrower (IvTime t) (IvTime t') = (t = t')"
| "narrower _ _ = False"

definition narrows :: "'n istate \<Rightarrow> 'n istate \<Rightarrow> bool" where
  "narrows I I' \<longleftrightarrow> (\<forall>x i. I x = Some i \<longrightarrow> (\<exists>i'. I' x = Some i' \<and> narrower i i'))"

lemma narrower_refl: "narrower i i"
  by (cases i) simp_all

lemma narrower_trans: "narrower i i' \<Longrightarrow> narrower i' i'' \<Longrightarrow> narrower i i''"
  by (cases i; cases i'; cases i'') auto

lemma narrows_refl: "narrows I I"
  by (simp add: narrows_def narrower_refl)

lemma narrows_trans: "narrows I I' \<Longrightarrow> narrows I' I'' \<Longrightarrow> narrows I I''"
  unfolding narrows_def by (meson narrower_trans)

lemma narrower_num: "narrower (IvNum p q) i' \<Longrightarrow> \<exists>p' q'. i' = IvNum p' q' \<and> p \<le> p' \<and> q' \<le> q"
  by (cases i') simp_all

lemma narrower_bool: "narrower (IvBool b) i' \<Longrightarrow> i' = IvBool b"
  by (cases i') simp_all

lemma narrower_str: "narrower (IvStr s) i' \<Longrightarrow> i' = IvStr s"
  by (cases i') simp_all

lemma narrower_time: "narrower (IvTime t) i' \<Longrightarrow> i' = IvTime t"
  by (cases i') simp_all

lemma evalVI_narrows:
  assumes "narrows I I'" "default_free a" "evalVI a I = Some i"
  shows "\<exists>i'. evalVI a I' = Some i' \<and> narrower i i'"
  using assms by (cases a) (auto simp: narrows_def narrower_refl)

text \<open>Narrowing an interval to an empty one could turn a false comparison into a true one
  (with \<open>[5, 6] < [1, 2]\<close> false and \<open>[5, 4] < [6, 2]\<close> true), so monotonicity is stated for
  interval states whose numeric intervals are non-empty.\<close>

fun proper_ival :: "ival \<Rightarrow> bool" where
  "proper_ival (IvNum p q) = (p \<le> q)"
| "proper_ival _ = True"

definition proper :: "'n istate \<Rightarrow> bool" where
  "proper I \<longleftrightarrow> (\<forall>x i. I x = Some i \<longrightarrow> proper_ival i)"

lemma proper_ival_of: "proper_ival (ival_of v)"
  by (cases v) simp_all

lemma evalVI_proper:
  assumes "proper I" "default_free a" "evalVI a I = Some i"
  shows "proper_ival i"
  using assms by (cases a) (auto simp: proper_def proper_ival_of)

lemma ilt_num_narrows:
  assumes "ilt (IvNum p q) (IvNum p' q') = Some b" "p \<le> u" "u \<le> v" "v \<le> q" "p' \<le> u'" "u' \<le> v'" "v' \<le> q'"
  shows "ilt (IvNum u v) (IvNum u' v') = Some b"
proof (cases b)
  case True
  with assms(1) have "q < p'" by (simp split: if_splits)
  with assms(4,5) have "v < u'" by linarith
  with True show ?thesis by simp
next
  case False
  with assms(1) have "\<not> q < p'" "q' \<le> p" by (simp_all split: if_splits)
  with assms(2-7) have "\<not> v < u'" "v' \<le> u" by linarith+
  with False show ?thesis by simp
qed

lemma ile_num_narrows:
  assumes "ile (IvNum p q) (IvNum p' q') = Some b" "p \<le> u" "u \<le> v" "v \<le> q" "p' \<le> u'" "u' \<le> v'" "v' \<le> q'"
  shows "ile (IvNum u v) (IvNum u' v') = Some b"
proof (cases b)
  case True
  with assms(1) have "q \<le> p'" by (simp split: if_splits)
  with assms(4,5) have "v \<le> u'" by linarith
  with True show ?thesis by simp
next
  case False
  with assms(1) have "\<not> q \<le> p'" "q' < p" by (simp_all split: if_splits)
  with assms(2-7) have "\<not> v \<le> u'" "v' < u" by linarith+
  with False show ?thesis by simp
qed

lemma ieq_num_narrows:
  assumes "ieq (IvNum p q) (IvNum p' q') = Some b" "p \<le> u" "u \<le> v" "v \<le> q" "p' \<le> u'" "u' \<le> v'" "v' \<le> q'"
  shows "ieq (IvNum u v) (IvNum u' v') = Some b"
  using assms by (auto split: if_splits)

lemma ilt_narrows:
  assumes "ilt i j = Some b" "narrower i i'" "narrower j j'" "proper_ival i'" "proper_ival j'"
  shows "ilt i' j' = Some b"
proof (cases i)
  case (IvNum p q)
  with assms(2) obtain u v where u: "i' = IvNum u v" "p \<le> u" "v \<le> q" by (auto dest: narrower_num)
  show ?thesis
  proof (cases j)
    case (IvNum p' q')
    with assms(3) obtain u' v' where w: "j' = IvNum u' v'" "p' \<le> u'" "v' \<le> q'" by (auto dest: narrower_num)
    from assms(1) \<open>i = IvNum p q\<close> IvNum have c: "ilt (IvNum p q) (IvNum p' q') = Some b" by simp
    from assms(4,5) u(1) w(1) have "u \<le> v" "u' \<le> v'" by simp_all
    from ilt_num_narrows[OF c u(2) this(1) u(3) w(2) this(2) w(3)] u(1) w(1) show ?thesis by simp
  qed (use assms(1,3) \<open>i = IvNum p q\<close> u(1) in \<open>auto dest!: narrower_bool narrower_str narrower_time\<close>)
qed (use assms in \<open>auto dest!: narrower_bool narrower_str narrower_time\<close>)

lemma ile_narrows:
  assumes "ile i j = Some b" "narrower i i'" "narrower j j'" "proper_ival i'" "proper_ival j'"
  shows "ile i' j' = Some b"
proof (cases i)
  case (IvNum p q)
  with assms(2) obtain u v where u: "i' = IvNum u v" "p \<le> u" "v \<le> q" by (auto dest: narrower_num)
  show ?thesis
  proof (cases j)
    case (IvNum p' q')
    with assms(3) obtain u' v' where w: "j' = IvNum u' v'" "p' \<le> u'" "v' \<le> q'" by (auto dest: narrower_num)
    from assms(1) \<open>i = IvNum p q\<close> IvNum have c: "ile (IvNum p q) (IvNum p' q') = Some b" by simp
    from assms(4,5) u(1) w(1) have "u \<le> v" "u' \<le> v'" by simp_all
    from ile_num_narrows[OF c u(2) this(1) u(3) w(2) this(2) w(3)] u(1) w(1) show ?thesis by simp
  qed (use assms(1,3) \<open>i = IvNum p q\<close> u(1) in \<open>auto dest!: narrower_bool narrower_str narrower_time\<close>)
qed (use assms in \<open>auto dest!: narrower_bool narrower_str narrower_time\<close>)

lemma ieq_narrows:
  assumes "ieq i j = Some b" "narrower i i'" "narrower j j'" "proper_ival i'" "proper_ival j'"
  shows "ieq i' j' = Some b"
proof (cases i)
  case (IvNum p q)
  with assms(2) obtain u v where u: "i' = IvNum u v" "p \<le> u" "v \<le> q" by (auto dest: narrower_num)
  show ?thesis
  proof (cases j)
    case (IvNum p' q')
    with assms(3) obtain u' v' where w: "j' = IvNum u' v'" "p' \<le> u'" "v' \<le> q'" by (auto dest: narrower_num)
    from assms(1) \<open>i = IvNum p q\<close> IvNum have c: "ieq (IvNum p q) (IvNum p' q') = Some b" by simp
    from assms(4,5) u(1) w(1) have "u \<le> v" "u' \<le> v'" by simp_all
    from ieq_num_narrows[OF c u(2) this(1) u(3) w(2) this(2) w(3)] u(1) w(1) show ?thesis by simp
  qed (use assms(1,3) \<open>i = IvNum p q\<close> u(1) in \<open>auto dest!: narrower_bool narrower_str narrower_time\<close>)
next
  case (IvBool b')
  with assms show ?thesis by (cases j) (auto dest!: narrower_bool narrower_str narrower_time narrower_num)
next
  case (IvStr s)
  with assms show ?thesis by (cases j) (auto dest!: narrower_bool narrower_str narrower_time narrower_num)
next
  case (IvTime t)
  with assms show ?thesis by (cases j) (auto dest!: narrower_bool narrower_str narrower_time narrower_num)
qed

theorem evalI_mono:
  assumes "present_free e" "narrows I I'" "proper I'"
  shows "evalI e I \<preceq> evalI e I'"
  using assms(1)
proof (induction e)
  case (EEq a b)
  show ?case
  proof (cases "evalI (EEq a b) I")
    case (Some b')
    then obtain i j where u: "evalVI a I = Some i" and w: "evalVI b I = Some j" and c: "ieq i j = Some b'"
      by (auto split: option.splits)
    from EEq have df: "default_free a" "default_free b" by simp_all
    from evalVI_narrows[OF assms(2) df(1) u] evalVI_narrows[OF assms(2) df(2) w] obtain i' j'
      where n1: "evalVI a I' = Some i'" "narrower i i'" and n2: "evalVI b I' = Some j'" "narrower j j'" by blast
    have "proper_ival i'" "proper_ival j'" using evalVI_proper[OF assms(3) df(1) n1(1)] evalVI_proper[OF assms(3) df(2) n2(1)] .
    with ieq_narrows[OF c n1(2) n2(2)] n1(1) n2(1) Some show ?thesis by (simp add: approx_def)
  qed (simp add: approx_def)
next
  case (ELt a b)
  show ?case
  proof (cases "evalI (ELt a b) I")
    case (Some b')
    then obtain i j where u: "evalVI a I = Some i" and w: "evalVI b I = Some j" and c: "ilt i j = Some b'"
      by (auto split: option.splits)
    from ELt have df: "default_free a" "default_free b" by simp_all
    from evalVI_narrows[OF assms(2) df(1) u] evalVI_narrows[OF assms(2) df(2) w] obtain i' j'
      where n1: "evalVI a I' = Some i'" "narrower i i'" and n2: "evalVI b I' = Some j'" "narrower j j'" by blast
    have "proper_ival i'" "proper_ival j'" using evalVI_proper[OF assms(3) df(1) n1(1)] evalVI_proper[OF assms(3) df(2) n2(1)] .
    with ilt_narrows[OF c n1(2) n2(2)] n1(1) n2(1) Some show ?thesis by (simp add: approx_def)
  qed (simp add: approx_def)
next
  case (ELe a b)
  show ?case
  proof (cases "evalI (ELe a b) I")
    case (Some b')
    then obtain i j where u: "evalVI a I = Some i" and w: "evalVI b I = Some j" and c: "ile i j = Some b'"
      by (auto split: option.splits)
    from ELe have df: "default_free a" "default_free b" by simp_all
    from evalVI_narrows[OF assms(2) df(1) u] evalVI_narrows[OF assms(2) df(2) w] obtain i' j'
      where n1: "evalVI a I' = Some i'" "narrower i i'" and n2: "evalVI b I' = Some j'" "narrower j j'" by blast
    have "proper_ival i'" "proper_ival j'" using evalVI_proper[OF assms(3) df(1) n1(1)] evalVI_proper[OF assms(3) df(2) n2(1)] .
    with ile_narrows[OF c n1(2) n2(2)] n1(1) n2(1) Some show ?thesis by (simp add: approx_def)
  qed (simp add: approx_def)
qed (simp_all add: knot_mono kand_mono kor_mono kimp_mono)

text \<open>The monitor on an interval state blocks unless the condition is known to be false,
  as \<open>blocks\<close> does on a state.\<close>

definition blocksI :: "('n, atom) expr \<Rightarrow> 'n istate \<Rightarrow> bool" where
  "blocksI c I \<longleftrightarrow> evalI c I \<noteq> Some False"

theorem blocksI_point: "blocksI c (point \<sigma>) \<longleftrightarrow> blocks c \<sigma>"
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
      | Some L \<Rightarrow> if samples \<pi> j x = {} then None
                  else Some (IvNum (lo L (samples \<pi> j x) t) (hi L (samples \<pi> j x) t)))"

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
  shows "enclosed R \<pi> j x = Some (IvNum q q)" and "enclosed R \<pi> j x = point (st \<pi> j) x"
proof -
  have p: "(time \<pi> j, q) \<in> samples \<pi> j x" using assms(3,4) by (rule samples_arrival[OF order_refl])
  have c: "consistent L (samples \<pi> j x)" using assms(1,2) by (simp add: consistent_upto_def)
  from enc_sample[OF samples_finite c p]
  have "lo L (samples \<pi> j x) (of_int (time \<pi> j)) = q" "hi L (samples \<pi> j x) (of_int (time \<pi> j)) = q"
    by (simp_all add: enc_def)
  with p assms(1) show "enclosed R \<pi> j x = Some (IvNum q q)"
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
  "signal_state R F \<pi> j t x = (case R x of None \<Rightarrow> real_state (st \<pi> j) x | Some L \<Rightarrow> Some (RNum (F x t)))"

text \<open>The induced valuation at the time of the entry lies inside the interval state of
  the entry: the enclosure part is \<open>adm_in_enc\<close>, the rest is the point state.\<close>

lemma point_inside_real_state: "point \<sigma> x = Some i \<Longrightarrow> \<exists>r. real_state \<sigma> x = Some r \<and> inval i r"
  by (auto simp: point_def real_state_def inval_ival_of)

theorem enclosed_inside:
  assumes "adm_family R F \<pi> j"
  shows "inside (enclosed R \<pi> j) (signal_state R F \<pi> j (of_int (time \<pi> j)))"
  unfolding inside_def
proof (intro allI impI)
  fix x i assume e: "enclosed R \<pi> j x = Some i"
  show "\<exists>r. signal_state R F \<pi> j (of_int (time \<pi> j)) x = Some r \<and> inval i r"
  proof (cases "R x")
    case None
    with e have "point (st \<pi> j) x = Some i" by (simp add: enclosed_def enclosed_at_def)
    with None show ?thesis by (auto simp: signal_state_def dest: point_inside_real_state)
  next
    case (Some L)
    with e have ne: "samples \<pi> j x \<noteq> {}"
      and i: "i = IvNum (lo L (samples \<pi> j x) (of_int (time \<pi> j))) (hi L (samples \<pi> j x) (of_int (time \<pi> j)))"
      by (auto simp: enclosed_def enclosed_at_def split: if_splits)
    have a: "adm L (samples \<pi> j x) (F x)" using assms Some by (simp add: adm_family_def)
    from adm_in_enc[OF samples_finite ne a, of "of_int (time \<pi> j)"] i Some show ?thesis
      by (auto simp: signal_state_def of_rat_of_int_eq)
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

text \<open>Without rate bounds the monitor and the verdict are those of the core, on every
  trace and every condition.\<close>

theorem blocked_actionI_no_bounds:
  "blocked_actionI (\<lambda>_. None) s a c \<pi> j \<longleftrightarrow> blocked_action s a c \<pi> j"
  by (simp add: blocked_actionI_def blocked_action_def enclosed_no_bounds blocksI_point)

theorem forbiddenI_no_bounds:
  "forbiddenI (\<lambda>_. None) s a c \<pi> j \<longleftrightarrow> forbidden s a c \<pi> j"
  by (simp add: forbiddenI_def forbidden_def enclosed_no_bounds evalI_point)

theorem pr_verdictI_no_bounds:
  "pr_verdictI (\<lambda>_. None) s a c \<pi> = pr_verdict s a c \<pi>"
proof -
  have "forbiddenI (\<lambda>_. None) s a c \<pi> = forbidden s a c \<pi>"
    by (rule ext) (rule forbiddenI_no_bounds)
  then show ?thesis by (simp add: pr_verdictI_def pr_verdict_def)
qed

theorem monitor_decisionsI_no_bounds:
  "monitor_decisionsI (\<lambda>_. None) s a c \<pi> = monitor_decisions s a c \<pi>"
  by (simp add: monitor_decisionsI_def monitor_decisions_def enclosed_no_bounds blocksI_point)


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

text \<open>Without rate bounds they are the invariants of the core.\<close>

lemma evalI_point_entry: "evalI \<phi> (enclosed (\<lambda>_. None) \<pi> j) = eval \<phi> (st \<pi> j)"
  unfolding enclosed_no_bounds by (rule evalI_point)

theorem inv_evalI_no_bounds: "inv_evalI (\<lambda>_. None) \<iota> \<pi> = inv_eval \<iota> \<pi>"
  by (cases \<iota>) (simp_all add: evalI_point_entry)

theorem ew_evalI_no_bounds: "ew_evalI (\<lambda>_. None) \<phi> D \<pi> = ew_eval \<phi> D \<pi>"
  unfolding ew_evalI_def ew_eval_def evalI_point_entry by (rule refl)

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


section \<open>The continuous false verdict of EVENTUALLY WITHIN\<close>

text \<open>The false verdict of \<open>EVENTUALLY \<phi> WITHIN d\<close> on enclosures, like that of the core, is a
  statement about the entries of the window (\<open>ew_false_signals\<close>). For the formula \<open>x < c\<close>,
  with \<open>x\<close> under a rate bound and \<open>c\<close> a constant, a verdict about every time of the window
  is decided by \<open>above_cert\<close> on all the samples of \<open>x\<close> in the trace: the quantity is at or
  above \<open>c\<close> throughout the window, for every admissible signal. This reading is not
  causal: it uses every sample of the trace, later ones included, which narrow the
  enclosure at earlier times. It is sound, and it is final under more consistent
  samples.\<close>

definition ew_below_false :: "('n \<Rightarrow> rat option) \<Rightarrow> 'n \<Rightarrow> rat \<Rightarrow> int \<Rightarrow> ('n, atom, 's, 'a) itrace \<Rightarrow> bool" where
  "ew_below_false R x c D \<pi> \<longleftrightarrow>
     passed D \<pi> \<and>
     (case R x of
        None \<Rightarrow> False
      | Some L \<Rightarrow> samples \<pi> (length \<pi> - 1) x \<noteq> {} \<and>
                 above_cert L (samples \<pi> (length \<pi> - 1) x) (of_int (time \<pi> 0)) (of_int D) c)"

theorem ew_evalI_F_sound:
  assumes "ew_below_false R x c D \<pi>" "adm_family R F \<pi> (length \<pi> - 1)"
    and "of_int (time \<pi> 0) \<le> t" "t \<le> of_int D"
  shows "evalR (ELt (VName x) (VConst (ANum c))) (signal_state R F \<pi> (length \<pi> - 1) t) = Some False"
proof -
  from assms(1) obtain L where L: "R x = Some L"
    and ne: "samples \<pi> (length \<pi> - 1) x \<noteq> {}"
    and cert: "above_cert L (samples \<pi> (length \<pi> - 1) x) (of_int (time \<pi> 0)) (of_int D) c"
    by (auto simp: ew_below_false_def split: option.splits)
  have a: "adm L (samples \<pi> (length \<pi> - 1) x) (F x)" using assms(2) L by (simp add: adm_family_def)
  have "of_rat c \<le> F x t"
    by (rule above_cert_adm[OF samples_finite ne cert a]) (use assms(3,4) in \<open>simp_all add: of_rat_of_int_eq\<close>)
  then show ?thesis using L by (simp add: signal_state_def not_less)
qed

theorem ew_below_false_final:
  assumes "ew_below_false R x c D \<pi>" "\<pi> \<noteq> []" "bounds_nonneg R" "consistent_trace R (\<pi> @ \<rho>)" "time \<pi> 0 \<le> D"
  shows "ew_below_false R x c D (\<pi> @ \<rho>)"
proof -
  from assms(1) obtain L where L: "R x = Some L"
    and ne: "samples \<pi> (length \<pi> - 1) x \<noteq> {}"
    and cert: "above_cert L (samples \<pi> (length \<pi> - 1) x) (of_int (time \<pi> 0)) (of_int D) c"
    and p: "passed D \<pi>"
    by (auto simp: ew_below_false_def split: option.splits)
  let ?S = "samples \<pi> (length \<pi> - 1) x" and ?S' = "samples (\<pi> @ \<rho>) (length (\<pi> @ \<rho>) - 1) x"
  have lt: "length \<pi> - 1 < length \<pi>" using assms(2) by simp
  have sub: "?S \<subseteq> ?S'"
    using samples_append[OF lt, of \<rho> x] samples_mono[of "length \<pi> - 1" "length (\<pi> @ \<rho>) - 1" "\<pi> @ \<rho>" x] by simp
  have L0: "0 \<le> L" using assms(3) L by (simp add: bounds_nonneg_def)
  have c': "consistent L ?S'" using assms(4) L by (simp add: consistent_trace_def consistent_upto_def)
  have ab: "(of_int (time \<pi> 0) :: rat) \<le> of_int D" using assms(5) by simp
  have cert': "above_cert L ?S' (of_int (time \<pi> 0)) (of_int D) c"
    by (rule above_cert_mono[OF samples_finite sub ne L0 c' ab cert])
  have t0: "time (\<pi> @ \<rho>) 0 = time \<pi> 0" using assms(2) by simp
  show ?thesis unfolding ew_below_false_def t0 using passed_append[OF p] L cert' sub ne by auto
qed


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
      | Some L \<Rightarrow> (case sample_list \<pi> j x of
                    [] \<Rightarrow> None
                  | p # ps \<Rightarrow> Some (IvNum (lo L (set (p # ps)) t) (hi L (set (p # ps)) t))))"
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
  "enclosed sensor_bounds stale_trace 3 temp = Some (IvNum 84 86)"
  "enclosed sensor_bounds stale_trace 4 temp = Some (IvNum (839 / 10) (861 / 10))"
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
  "enclosed sensor_bounds boundary_trace 3 temp = Some (IvNum (169 / 2) (171 / 2))"
  "enclosed sensor_bounds boundary_trace 4 temp = Some (IvNum (422 / 5) (428 / 5))"
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
  "enclosed sensor_bounds at_limit_trace 2 temp = Some (IvNum 90 90)"
  "enclosed_at sensor_bounds at_limit_trace 2 1794211221 temp = Some (IvNum (899 / 10) (901 / 10))"
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

text \<open>A Boolean factor in the condition of a prohibition: \<open>arm MUST_NOT move WHEN over_limit\<close>,
  whose condition is translated to \<open>over_limit == true\<close> (section 10.6 of CORE.md, rule 2),
  with a string factor beside it. Neither has a rate bound, so the interval state carries
  their values exactly. At the entry before the movement the core knows the condition
  false; so does the reading on interval states, and the monitor on interval states does
  not block the movement.\<close>

definition over :: path where "over = [STR ''over_limit'']"
definition mode :: path where "mode = [STR ''mode'']"

definition over_cond :: "(path, atom) expr" where
  "over_cond = EEq (VName over) (VConst (ABool True))"

definition bool_data :: "(path, atom) state" where
  "bool_data = [over \<mapsto> ABool False, mode \<mapsto> AStr (STR ''manual''), lim \<mapsto> ANum 90]"

definition bool_trace :: ctrace where
  "bool_trace =
     [(bool_data, 1794211200, Tick),
      (bool_data, 1794211205, Arrival over),
      (bool_data, 1794211206, arm_move)]"

value "enclosed sensor_bounds bool_trace 1 over"
value "evalI over_cond (enclosed sensor_bounds bool_trace 1)"
value "monitor_decisionsI sensor_bounds (STR ''arm'') (Act (STR ''move'') []) over_cond bool_trace"

lemma boolean_factor:
  "enclosed sensor_bounds bool_trace 1 over = Some (IvBool False)"
  "enclosed sensor_bounds bool_trace 1 mode = Some (IvStr (STR ''manual''))"
  "eval over_cond (st bool_trace 1) = Some False"
  "evalI over_cond (enclosed sensor_bounds bool_trace 1) = Some False"
  "evalI (EEq (VName mode) (VConst (AStr (STR ''auto'')))) (enclosed sensor_bounds bool_trace 1) = Some False"
  "evalI (EPresent over) (enclosed sensor_bounds bool_trace 1) = Some True"
  "monitor_decisionsI sensor_bounds (STR ''arm'') (Act (STR ''move'') []) over_cond bool_trace = [(2, False)]"
  "monitor_decisions (STR ''arm'') (Act (STR ''move'') []) over_cond bool_trace = [(2, False)]"
  by code_simp+

text \<open>Scenario \<open>sensor_never_false\<close> without its last reading: readings of 97.5 at 08:00:05,
  08:05:00 and 08:10:00, the deadline 08:10:00, and a tick after it. The verdict of the
  core is undefined, since no fresh reading is known at the activation entry, and so is
  the verdict on enclosures at the entries. The continuous reading uses every sample: with
  the bound 0.1 degrees per second the lower envelope falls to 82.75 between the first two
  readings, below the limit, so the verdict is not false; with the bound 0.05 it stays at or
  above 90 throughout the window (the valley between the last two readings is exactly 90),
  and the verdict is false: every signal under that bound through the readings was at or
  above the limit at every time of the ten minutes.\<close>

definition never_false_trace :: ctrace where
  "never_false_trace =
     [(sensor_data (195 / 2), 1794211200, Tick),
      (sensor_data (195 / 2), 1794211205, Arrival temp),
      (sensor_data (195 / 2), 1794211210, stop_drive),
      (sensor_data (195 / 2), 1794211500, Arrival temp),
      (sensor_data (195 / 2), 1794211800, Arrival temp),
      (sensor_data (195 / 2), 1794211801, Tick)]"

definition slow_bounds :: "path \<Rightarrow> rat option" where
  "slow_bounds x = (if x = temp then Some (1 / 20) else None)"

value "ew_evalI sensor_bounds (ELt (VName temp) (VName lim)) 1794211800 never_false_trace"
value "ew_below_false sensor_bounds temp 90 1794211800 never_false_trace"
value "ew_below_false slow_bounds temp 90 1794211800 never_false_trace"
value "lo (1 / 10) (samples never_false_trace 5 temp) (qvalley_time (1 / 10) (1794211205, 195 / 2) (1794211500, 195 / 2))"

lemma never_false_signals:
  "ew_evalI sensor_bounds (ELt (VName temp) (VName lim)) 1794211800 never_false_trace = None"
  "\<not> ew_below_false sensor_bounds temp 90 1794211800 never_false_trace"
  "ew_below_false slow_bounds temp 90 1794211800 never_false_trace"
  "qvalley (1 / 10) (1794211205, 195 / 2) (1794211500, 195 / 2) = 331 / 4"
  "qvalley (1 / 20) (1794211500, 195 / 2) (1794211800, 195 / 2) = 90"
  by code_simp+

end
