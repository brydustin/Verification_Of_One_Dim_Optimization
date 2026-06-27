section \<open>Taylor's Theorem with Peano Remainder\<close>

theory Taylor_Peano
  imports K_Times_Fr_Real
begin

subsection \<open>Real Polynomial Functions: Closure under Differentiation\<close>

lemma deriv_real_polynomial_function:
  assumes "real_polynomial_function p"
  shows   "real_polynomial_function (deriv p)" 
proof -    
  obtain p' where p_def: "real_polynomial_function p' \<and>
             (\<forall>x. (p has_real_derivative (p' x)) (at x))"
    using assms has_real_derivative_polynomial_function by presburger
  have "p' = deriv p"
  proof -
    have "\<forall>r. deriv p r = p' r"
      using DERIV_imp_deriv p_def by blast
    then show ?thesis
      by presburger
  qed
  then show ?thesis
    using p_def by auto
qed

lemma polynomial_function_kth_deriv:
  assumes "real_polynomial_function p"
  shows   "real_polynomial_function ((deriv ^^ k) p)"
  by(induct k, simp add: assms, simp add: deriv_real_polynomial_function)

subsection \<open>Taylor Polynomials and Peano Remainders\<close>

text \<open> As seen below, we can instantiate the result MacLaurin.Taylor 
and prove a version of Taylor's theorem with our definitions. Yet, we are 
interested in the Peano form of Taylor's formula. We, thus, focus on proving
that result. \<close>

theorem Taylor:
  fixes f :: "real \<Rightarrow> real"
  assumes kdiff: "\<forall>t. a \<le> t \<longrightarrow> t \<le> b \<longrightarrow> k_times_Fr_differentiable_at n f t"
    and prems: "0 < n" "a \<le> c" "c \<le> b" "a \<le> x" "x \<le> b" "x \<noteq> c"
  shows "\<exists>\<xi>. (if x < c then x < \<xi> \<and> \<xi> < c else c < \<xi> \<and> \<xi> < x) \<and>
    f x = (\<Sum>m<n. ((deriv^^m) f) c / fact m * (x - c) ^ m)
                + ((deriv^^n) f) \<xi> / fact n * (x - c) ^ n"
proof -
  have dcond: "\<forall>m t. m < n \<and> a \<le> t \<and> t \<le> b \<longrightarrow>
      ((deriv ^^ m) f has_real_derivative (deriv ^^ Suc m) f t) (at t)"
    using kdiff kfr_real_kth_deriv_has_derivative has_field_derivative_def
    by blast
  show ?thesis
    using MacLaurin.Taylor[where diff = "\<lambda>m. (deriv ^^ m) f" and n = n and f = f
            and a = a and b = b and c = c and x = x] dcond prems
    by fastforce
qed

corollary Taylor_as_limit:
  fixes f :: "real \<Rightarrow> real"
  assumes npos: "0 < n"
      and cAB: "c \<in> {a..b}"
      and cont: "isCont ((deriv ^^ n) f) c"
      and diff: "\<And>t. t \<in> {a..b} \<Longrightarrow> k_times_Fr_differentiable_at n f t"
  shows "((\<lambda>x.
           (f x - (\<Sum>m\<le>n. ((deriv ^^ m) f) c / fact m * (x - c) ^ m))
           / (x - c) ^ n) \<longlongrightarrow> 0) (at c within {a..b})"
proof -
  define g where g_def: "g \<equiv> (deriv ^^ n) f"
  define S where S_def :"S x \<equiv> (\<Sum>m<n. ((deriv ^^ m) f) c / fact m * (x - c) ^ m)" for x

  (* Lagrange form gives a point between c and x witnessing the remainder *)
  have ex_t:
    "\<And>x. x \<in> {a..b} \<Longrightarrow> x \<noteq> c \<Longrightarrow>
          \<exists>t. (if x < c then x < t \<and> t < c else c < t \<and> t < x)
            \<and> f x = S x + g t / fact n * (x - c) ^ n"
  proof -
    fix x assume hx: "x \<in> {a..b}" "x \<noteq> c"
    with assms have "\<exists>t. (if x < c then x < t \<and> t < c else c < t \<and> t < x)
                     \<and> f x = (\<Sum>m<n. ((deriv ^^ m) f) c / fact m * (x - c) ^ m)
                              + (g t) / fact n * (x - c) ^ n"
      unfolding g_def S_def by (subst Taylor, simp_all, auto)

    thus "\<exists>t. (if x < c then x < t \<and> t < c else c < t \<and> t < x)
              \<and> f x = S x + g t / fact n * (x - c) ^ n"
      using S_def by presburger
  qed

    (* Choose a concrete selector \<tau>(x) for the Taylor point *)
  then obtain \<tau> :: "real \<Rightarrow> real" where \<tau>_def:
    "\<And>x. x \<in> {a..b} \<and> x \<noteq> c \<Longrightarrow>
         (if x < c then x < \<tau> x \<and> \<tau> x < c else c < \<tau> x \<and> \<tau> x < x)
       \<and> f x = S x + g (\<tau> x) / fact n * (x - c) ^ n"
    by metis

  have evAB: "eventually (\<lambda>x. x \<in> {a..b} - {c}) (at c within {a..b})"
    by (auto simp: eventually_at_filter)

  (* On that event, the centered expression simplifies to a difference in g *)
   have ev_eq:
    "eventually (\<lambda>x. ( f x
                     - S x
                     - g c / fact n * (x - c) ^ n) / (x - c) ^ n
                  = (g (\<tau> x) - g c) / fact n)
                (at c within {a..b})"
  proof (rule eventually_mono[OF evAB])
    fix x :: real
    assume hx: "x \<in> {a..b} - {c}"
    hence xne: "x \<noteq> c" by auto
    have denom_ne: "(x - c) ^ n \<noteq> 0"
      using xne npos by simp

    have fx: "f x - S x = g (\<tau> x) / fact n * (x - c) ^ n"
      using \<tau>_def hx by (simp add: algebra_simps)

    have "( f x - S x - g c / fact n * (x - c) ^ n) / (x - c) ^ n
          = (f x - S x) / (x - c) ^ n - g c / fact n"
      by (metis denom_ne divide_diff_eq_iff)
    also have "... = g (\<tau> x) / fact n - g c / fact n"
      using denom_ne fx by auto
    also have "... = (g (\<tau> x) - g c) / fact n"
      by (simp add: field_simps)
    finally show "( f x - S x - g c / fact n * (x - c) ^ n) / (x - c) ^ n
                  = (g (\<tau> x) - g c) / fact n".
  qed

  (* |\<tau> x - c| \<le> |x - c| whenever \<tau> x lies strictly between x and c *)
  have ev_bound:
    "eventually (\<lambda>x. 0 \<le> \<bar>\<tau> x - c\<bar> \<and> \<bar>\<tau> x - c\<bar> \<le> \<bar>x - c\<bar>) (at c within {a..b})"
    by (rule eventually_mono[OF evAB], auto,
        metis \<tau>_def abs_minus_commute abs_of_pos atLeastAtMost_iff 
        diff_gt_0_iff_gt diff_mono linorder_not_le not_less_iff_gr_or_eq)
  (* Hence \<tau> x \<rightarrow> c as x \<rightarrow> c within {a..b} *)
  have tendsto_tau:
  "((\<lambda>x. \<tau> x) \<longlongrightarrow> c) (at c within {a..b})"
  proof -
    have tend_abs_tau:
  "((\<lambda>x. \<bar>\<tau> x - c\<bar>) \<longlongrightarrow> 0) (at c within {a..b})"
    proof -
      have ev_lower: "eventually (\<lambda>x. 0 \<le> \<bar>\<tau> x - c\<bar>) (at c within {a..b})"
        by simp
    
      have ev_upper:
        "eventually (\<lambda>x. \<bar>\<tau> x - c\<bar> \<le> \<bar>x - c\<bar>) (at c within {a..b})"
      proof (rule eventually_mono[OF evAB])
        fix x assume hx: "x \<in> {a..b} - {c}"
        hence xin: "x \<in> {a..b}" and xne: "x \<noteq> c" by auto
        from \<tau>_def[of x] xin xne have between:
          "(if x < c then x < \<tau> x \<and> \<tau> x < c else c < \<tau> x \<and> \<tau> x < x)" by auto
        thus "\<bar>\<tau> x - c\<bar> \<le> \<bar>x - c\<bar>"
          by (cases "x < c") (auto simp: abs_real_def)
      qed
    
      have L_lower: "((\<lambda>x. 0::real) \<longlongrightarrow> 0) (at c within {a..b})" by simp
      have L_upper: "((\<lambda>x. \<bar>x - c\<bar>) \<longlongrightarrow> 0) (at c within {a..b})"
        by (simp add: LIM_zero tendsto_rabs_zero)
    
      (* sandwich: 0 \<le> |\<tau> x - c| \<le> |x - c|, and |x - c| \<rightarrow> 0 *)
      show ?thesis
        by (rule tendsto_sandwich[OF ev_lower ev_upper L_lower L_upper])
    qed     
      show ?thesis
        by (meson LIM_zero_iff tend_abs_tau tendsto_rabs_zero_cancel)
  qed

  (* Continuity of g at c gives g(\<tau> x) \<rightarrow> g c *)
  have tendsto_g_tau:
    "((\<lambda>x. g (\<tau> x)) \<longlongrightarrow> g c) (at c within {a..b})"
    using assms(3) continuous_within g_def tendsto_compose tendsto_tau by blast

 (* Thus (g(\<tau> x) - g c)/fact n \<rightarrow> 0 *)
  have rhs_to_0: "((\<lambda>x. (g (\<tau> x) - g c) / fact n) \<longlongrightarrow> 0) (at c within {a..b})"
    by (simp add: LIM_zero tendsto_divide_zero tendsto_g_tau)

  have "(((\<lambda>x. ( f x - S x - g c / fact n * (x - c) ^ n) / (x - c) ^ n) \<longlongrightarrow> 0)(at c within {a..b}))
     =  (((\<lambda>x. (g (\<tau> x) - g c) / fact n) \<longlongrightarrow> 0) (at c within {a..b}))"
    by (rule tendsto_cong) (use ev_eq in auto)

  then have base_limit:
    "((\<lambda>x.
        ( f x
        - (\<Sum>m<n. ((deriv ^^ m) f) c / fact m * (x - c) ^ m)
        - ((deriv ^^ n) f) c / fact n * (x - c) ^ n )
       / (x - c) ^ n) \<longlongrightarrow> 0) (at c within {a..b})"
    using rhs_to_0 g_def S_def by simp

  have "\<And>x. (\<Sum>m\<le>n. ((deriv ^^ m) f) c / fact m * (x - c) ^ m)
        = (\<Sum>m<n. ((deriv ^^ m) f) c / fact m * (x - c) ^ m)
          + ((deriv ^^ n) f) c / fact n * (x - c) ^ n"
    using lessThan_Suc_atMost sum.lessThan_Suc by auto

  then show ?thesis
    by (smt (verit, ccfv_SIG) Lim_cong_within base_limit)    
qed

\<comment> \<open>
\textbf{Taylor polynomial of order \(m\) at \(a\).}
We define
\[
  T_m(f;a)(x) \;=\; \sum_{i=0}^{m} \frac{f^{(i)}(a)}{i!}\,(x-a)^{i},
\]
implemented as @{term \<open>taylor_poly m f a x\<close>} using the iterated derivative
@{term \<open>(deriv ^^ i) f\<close>}.
This is a polynomial (in \(x\)) of degree at most \(m\) that matches the first
\(m\) derivatives of \(f\) at the point \(a\).
\<close>

definition taylor_poly :: "nat \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "taylor_poly n f c x \<equiv> (\<Sum> m \<le> n. ((deriv ^^ m) f c / fact m) * (x - c)^m)"

\<comment> \<open>The Peano remainder term: the difference between \(f\) and its degree-\(m\) Taylor polynomial.\<close>

definition peano_remainder ::
  "nat \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real"
  where
  "peano_remainder n f c x = f x - taylor_poly n f c x"

lemma real_poly_diff_pow:
  "real_polynomial_function (\<lambda>t::real. (t - a) ^ i)"
  using real_polynomial_function_power real_polynomial_function_diff
        real_polynomial_function.intros bounded_linear_ident
  by blast

lemma kth_deriv_taylor_term:
  fixes x :: real
  shows "(deriv ^^ k) (\<lambda>t. c * (t - a) ^ i) x =
    (if k \<le> i then c * (of_nat (fact i) / of_nat (fact (i - k))) * (x - a) ^ (i - k) else 0)"
proof -
  have "(deriv ^^ k) (\<lambda>t. c * (t - a) ^ i) x = c * (deriv ^^ k) (\<lambda>t. (t - a) ^ i) x"
    using kth_deriv_cmult_poly[OF real_poly_diff_pow]
    by auto
  also have "\<dots> = c * (if k \<le> i then fact i / fact (i - k) * (x - a) ^ (i - k) else 0)"
    using kth_deriv_diff_pow[where n = k and a = a and k = i and x = x]
    by auto
  also have "\<dots> =
    (if k \<le> i then c * (of_nat (fact i) / of_nat (fact (i - k))) * (x - a) ^ (i - k) else 0)"
    by simp
  finally show ?thesis
    by blast
qed

subsection \<open>Derivatives of the Taylor Polynomial and Peano Remainder\<close>

\<comment> \<open>Derivative rule: For \(k \le m\), the \(k\)-th derivative of the degree-\(m\)
    Taylor polynomial at its centre equals the \(k\)-th derivative of the  original function.\<close>

lemma real_poly_taylor_term:
  "real_polynomial_function (\<lambda>t::real. c * (t - a) ^ i)"
  using real_poly_diff_pow real_polynomial_function.intros
  by blast

lemma real_poly_taylor_poly:
  "real_polynomial_function (taylor_poly m f a)"
  unfolding taylor_poly_def
  using real_polynomial_function_sum[where I = "{..m}"
          and f = "\<lambda>x i. (deriv ^^ i) f a / fact i * (x - a) ^ i"]
        real_poly_taylor_term
  by blast

lemma taylor_poly_diff_at:
  "k_times_Fr_differentiable_at k (taylor_poly m f a) x"
  using real_poly_taylor_poly real_poly_imp_kfr
  by auto

lemma k_diff_at_tay_term:
  fixes f :: "real \<Rightarrow> real"
  shows "k_times_Fr_differentiable_at k (\<lambda>t. (deriv ^^ i) f a / fact i * (t - a) ^ i) x"
  using real_poly_taylor_term real_poly_imp_kfr
  by presburger

lemma kth_deriv_taylor_poly:
  assumes "k \<le> m"
  shows "(deriv ^^ k) (taylor_poly m f a) x =
       (\<Sum> i\<in>{k..m}. ((deriv ^^ i) f a / fact (i - k)) * (x - a) ^ (i - k))"
proof -
  have "(deriv ^^ k) (taylor_poly m f a) x =
          (\<Sum> i\<le>m. (deriv ^^ k)
                     (\<lambda>t. (deriv ^^ i) f a / fact i * (t - a) ^ i) x)"
    unfolding taylor_poly_def
    using kth_deriv_sum_upto_kfr[where F = "\<lambda>i t. (deriv ^^ i) f a / fact i * (t - a) ^ i"
            and n = m and k = k and x = x] k_diff_at_tay_term
    by blast
  also have
    "... = (\<Sum> i\<le>m.
              (if k \<le> i
               then ((deriv ^^ i) f a / fact i) *
                     (of_nat (fact i) / of_nat (fact (i - k))) *
                     (x - a) ^ (i - k)
               else 0))"
    by (subst kth_deriv_taylor_term, simp)
  also have
    "... = (\<Sum> i\<le>m.
              ((deriv ^^ i) f a / fact i) *
              (if k \<le> i
               then of_nat (fact i) / of_nat (fact (i - k)) *
                    (x - a) ^ (i - k)
               else 0))"
  proof -
    have "\<And>i. (if k \<le> i
                then (deriv ^^ i) f a / fact i *
                     (of_nat (fact i) / of_nat (fact (i - k))) * (x - a) ^ (i - k)
                else 0)
            = (deriv ^^ i) f a / fact i *
                (if k \<le> i then of_nat (fact i) / of_nat (fact (i - k)) * (x - a) ^ (i - k) else 0)"
      using mult.assoc mult_zero_right
      by simp
    then show ?thesis
      using sum.cong
      by presburger
  qed
  also have
    "... = (\<Sum> i\<in>{k..m}.((deriv ^^ i) f a / fact (i - k)) * (x - a) ^ (i - k))"
    by (subst sum.mono_neutral_right[where S = "{k..m}"], auto)
  finally show ?thesis.
qed

lemma kth_deriv_peano_remainder_zero:
  assumes "k \<le> m"
      and "k_times_Fr_differentiable_at m f a"
  shows "(deriv ^^ k) (peano_remainder m f a) a = 0"
  unfolding peano_remainder_def
proof -
  have "(deriv ^^ k) (\<lambda>x. f x - taylor_poly m f a x) a =
        (deriv ^^ k) f a - (deriv ^^ k) (taylor_poly m f a) a"
    using assms k_times_Fr_differentiable_at_mono kth_deriv_sub_poly real_poly_taylor_poly
    by blast
  also have "... = (deriv ^^ k) f a - 
  (\<Sum> i\<in>{k..m}. ((deriv ^^ i) f a / fact (i - k)) * (a - a) ^ (i - k))"
    by (simp add: kth_deriv_taylor_poly assms(1))
  also have  
    "... =  0"
   by (simp add: sum.atLeast_Suc_atMost power_0_left assms(1) split: if_splits)
  finally show "(deriv ^^ k) (\<lambda>x. f x - taylor_poly m f a x) a = 0".
qed

lemma peano_kth_deriv_zero_diff:
  assumes "k \<le> m"
      and "k_times_Fr_differentiable_at m f a"
  shows "k_times_Fr_differentiable_at m (peano_remainder m f a) a \<and>
     k_times_Fr_differentiable_at (m - k) ((deriv ^^ k) (peano_remainder m f a)) a"
  unfolding peano_remainder_def
  by (simp add: assms(1,2) k_times_Fr_sub kfr_real_funpow_deriv taylor_poly_diff_at)


subsection \<open>One-sided limits in \<open>\<epsilon>\<close>-\<open>\<delta>\<close> form\<close>

text \<open>Epsilon-delta characterisations of one-sided real limits, derived purely
  from HOL-Analysis (\<open>tendsto_iff\<close>, \<open>eventually_at_left\<close>/\<open>eventually_at_right\<close>).\<close>

lemma tendsto_at_left_x_epsilon_def:
  fixes f :: "real \<Rightarrow> real" and L x :: real
  shows
    "(f \<longlongrightarrow> L) (at_left x) \<longleftrightarrow>
     (\<forall>\<epsilon>>0. \<exists>\<delta>>0. \<forall>y. (y < x \<and> x - y < \<delta>) \<longrightarrow> \<bar>f y - L\<bar> < \<epsilon>)"
proof -
  have "(f \<longlongrightarrow> L) (at_left x) =
        (\<forall>\<epsilon>>0. eventually (\<lambda>y. \<bar>f y - L\<bar> < \<epsilon>) (at_left x))"
    by (simp add: tendsto_iff dist_real_def)
  also have
    "\<dots> = (\<forall>\<epsilon>>0. \<exists>b<x. \<forall>y<x. b < y \<longrightarrow> \<bar>f y - L\<bar> < \<epsilon>)"
    by (subst eventually_at_left[where y = "x - (\<bar>x\<bar> + 1)"], simp, meson)
  also have
    "\<dots> = (\<forall>\<epsilon>>0. \<exists>d>0. \<forall>y. y < x \<and> x - y < d \<longrightarrow> \<bar>f y - L\<bar> < \<epsilon>)"
    by(safe, metis diff_gt_0_iff_gt diff_strict_left_mono not_less_iff_gr_or_eq,
             metis (no_types) add.commute diff_less_eq less_add_same_cancel1)
  finally show ?thesis.
qed

lemma tendsto_at_right_x_epsilon_def:
  fixes f :: "real \<Rightarrow> real" and L x :: real
  shows
    "(f \<longlongrightarrow> L) (at_right x) \<longleftrightarrow>
     (\<forall>\<epsilon>>0. \<exists>\<delta>>0. \<forall>y. (x < y \<and> y - x < \<delta>) \<longrightarrow> \<bar>f y - L\<bar> < \<epsilon>)"
proof -
  have "(f \<longlongrightarrow> L) (at_right x) =
        (\<forall>\<epsilon>>0. eventually (\<lambda>x. \<bar>f x - L\<bar> < \<epsilon>) (at_right x))"
    by (simp add: tendsto_iff dist_real_def)
  also have "... = (\<forall>\<epsilon>>0. \<exists>\<delta>>x. \<forall>y>x. y < \<delta> \<longrightarrow> \<bar>f y - L\<bar> < \<epsilon>)"
    by(subst eventually_at_right[where y = "\<bar>x\<bar> + 1"], simp_all)
  also have "\<dots> =
        (\<forall>\<epsilon>>0. \<exists>\<delta>>0. \<forall>y. (x < y \<and> y - x < \<delta>) \<longrightarrow> \<bar>f y - L\<bar> < \<epsilon>)"
    by (auto, metis diff_add_cancel diff_gt_0_iff_gt diff_less_eq,
        metis add.commute diff_less_eq less_add_same_cancel1)
  finally show ?thesis.
qed


subsection \<open>Taylor's Theorem with Peano Remainder\<close>

lemma ex_remainder_choice:
  fixes f :: "real \<Rightarrow> real" and x0 y :: real and n :: nat
  defines "R \<equiv> peano_remainder (Suc n) f x0"
  defines "A j gj \<equiv> \<bar>(deriv ^^ j) R gj\<bar> / \<bar>(y - x0) ^ (Suc n - j)\<bar>"
  assumes "y \<noteq> x0" and y_small: "\<bar>y - x0\<bar> < \<epsilon>"
    and k_diff: "k_times_Fr_differentiable_at (Suc n) f x0"
    and deriv1: "\<forall>z\<in>closed_segment x0 y. (R has_derivative (\<lambda>h. deriv R z * h)) (at z)"
    and derivi: "\<forall>i < n. \<forall>z. \<bar>z - x0\<bar> < \<epsilon> 
      \<longrightarrow> ((deriv ^^ i) R has_derivative (\<lambda>h. (deriv ^^ Suc i) R z * h)) (at z)"
  shows "\<exists>g. \<forall>j::nat. (g 0 = y) 
    \<and> (j < n \<longrightarrow> (x0 < (y::real) \<longrightarrow> (x0 < g (Suc j) \<and> g (Suc j) < g j)) 
    \<and> (y < (x0::real) \<longrightarrow> (g j < g (Suc j) \<and> g (Suc j) < x0))
    \<and> (A j (g j) \<le> A (Suc j) (g (Suc j))))"
proof-
  have base_case: "\<exists>z. z \<in> open_segment y x0
    \<and> (0 < n \<longrightarrow> (x0 < y \<longrightarrow> x0 < z \<and> z < y)
    \<and> (y < x0 \<longrightarrow> y < z \<and> z < x0)
    \<and> (A 0 y \<le> A (Suc 0) z))" 
    (is "\<exists>z. ?conj1 z \<and> (0 < n \<longrightarrow> ?conj2 y z \<and> ?conj3 y z \<and> ?conj4 0 y z)")
  proof-
    have A0_eq: "A 0 y = \<bar>R y\<bar> / \<bar>(y - x0) ^ (Suc n)\<bar>"
      by (simp add: R_def A_def)
    have "R x0 = 0"
      using kth_deriv_peano_remainder_zero[OF _ k_diff, of 0]
      by (simp add: R_def )
    have "\<exists>z>x0. z < y \<and> R y = (y - x0) * deriv R z" if "x0 < y"
      using closed_segment_eq_real_ivl[of x0 y] \<open>x0 < y\<close> 
        MVT2[OF \<open>x0 < y\<close>, of R "deriv R"] deriv1
      by (clarsimp simp: has_field_derivative_def \<open>R x0 = 0\<close>)
    moreover have "\<exists>z>y. z < x0 \<and> R y = (y - x0) * deriv R z" if "x0 > y"
      using closed_segment_eq_real_ivl[of x0 y] \<open>x0 > y\<close> 
        MVT2[OF \<open>x0 > y\<close>, of R "deriv R"] deriv1
      by (clarsimp simp: has_field_derivative_def \<open>R x0 = 0\<close>)
        (metis left_diff_distrib' minus_diff_eq verit_minus_simplify(4))
    ultimately show "\<exists>z. ?conj1 z \<and> (0 < n \<longrightarrow> ?conj2 y z \<and> ?conj3 y z \<and> ?conj4 0 y z)"
      using A0_eq
      unfolding open_segment_eq_real_ivl
      by (cases \<open>x0 > y\<close>; clarsimp simp add: A_def)
         (metis abs_divide[of "deriv R _" "(y - x0) ^ n"]
                less_eq_real_def[of x0 y]
                abs_divide[of "(y - x0) * deriv R _" "(y - x0) * (y - x0) ^ n"]
                diff_ge_0_iff_ge[of y x0] dual_order.strict_trans[of _ x0 y]
                less_eq_real_def[of "\<bar>deriv R _ / (y - x0) ^ n\<bar>" "\<bar>deriv R _ / (y - x0) ^ n\<bar>"]
                less_eq_real_def[of "0" "0"] order_less_imp_not_less[of x0 y]
                nonzero_mult_divide_mult_cancel_left[of "y - x0" "deriv R _" "(y - x0) ^ n"],
          smt (verit) assms(3) divide_divide_eq_right mult.commute mult_minus_left
              nonzero_mult_div_cancel_left zero_le_mult_iff)
  qed
  have cond2: "\<exists>z. z \<in> open_segment y x0
    \<and> (j < n \<longrightarrow> (x0 < y \<longrightarrow> x0 < z \<and> z < x)
    \<and> (y < x0 \<longrightarrow> x < z \<and> z < x0)
    \<and> (A j x \<le> A (Suc j) z))"
    if x_def: "if j = 0 then x = y else x \<in> open_segment y x0" for x j 
    using x_def
  proof(induct j arbitrary: x)
    case 0
    thus ?case
      using base_case
      by simp
  next
    case (Suc j)
    let ?x = "if j = 0 then y else x"
    obtain z_null where "?conj1 z_null" and "j < n \<longrightarrow> ?conj2 ?x z_null" 
      and "j < n \<longrightarrow> ?conj3 ?x z_null" and "j < n \<longrightarrow> ?conj4 j ?x z_null"
      using base_case Suc(1)[of ?x] Suc(2)
      by (cases "j = 0") auto
    have x_small: "\<bar>x - x0\<bar> < \<epsilon>"
      using Suc(2) y_small \<open>y \<noteq> x0\<close>
      by (cases "x0 > y")
        (auto simp: open_segment_eq_real_ivl)
    have x_rel_x0: "x0 > y \<Longrightarrow> x0 > x" "x0 < y \<Longrightarrow> x0 < x"
      using Suc(2)
      by (auto simp: open_segment_eq_real_ivl)
    hence abs_leq: "\<bar>(x - x0)\<bar> \<le> \<bar>(y - x0)\<bar>"
      using Suc(2) \<open>y \<noteq> x0\<close>
      by (cases "x0 > y")
        (auto simp: open_segment_eq_real_ivl)
    have eq0: "(deriv ^^ (Suc j)) R x0 = 0" if "Suc j < n"
      using kth_deriv_peano_remainder_zero[OF _ k_diff]
      by (metis R_def Suc_lessD linorder_not_less not_less_eq_eq that)
    have "\<exists>z>x0. z < x \<and> (deriv ^^ Suc j) R x - (deriv ^^ Suc j) R x0 
      = (x - x0) * (deriv ^^ Suc (Suc j)) R z" if "x0 < y" and "Suc j < n"
      using x_small eq0[OF \<open>Suc j < n\<close>] Suc(2)
      by (intro MVT2[unfolded has_field_derivative_def, OF x_rel_x0(2)[OF \<open>x0 < y\<close>]]
          derivi[rule_format, OF \<open>Suc j < n\<close>]) clarsimp
    moreover have "\<exists>z>x. z < x0 \<and> (deriv ^^ Suc j) R x0 - (deriv ^^ Suc j) R x 
      = (x0 - x) * (deriv ^^ Suc (Suc j)) R z" if "y < x0" and "Suc j < n"
      using x_small eq0[OF \<open>Suc j < n\<close>] Suc(2)
      by (intro MVT2[unfolded has_field_derivative_def, OF x_rel_x0(1)[OF \<open>y < x0\<close>]]
          derivi[rule_format, OF \<open>Suc j < n\<close>]) clarsimp
    ultimately obtain z where z_in: "z \<in> open_segment x0 x" 
      and dSuc_eq: "Suc j < n \<Longrightarrow> (deriv ^^ Suc j) R x = (x - x0) * (deriv ^^ Suc (Suc j)) R z"
      using \<open>y \<noteq> x0\<close> x_rel_x0 eq0 Rats_dense_in_real
      by (cases "x0 < y"; clarsimp simp: open_segment_eq_real_ivl)
   (blast, metis (mono_tags) dense diff_zero minus_diff_eq mult_minus_left)
    have "A (Suc (Suc j)) w = \<bar>(deriv ^^ (Suc (Suc j))) R w\<bar> / \<bar>(y - x0) ^ (n - Suc j)\<bar>" for w 
      by (simp add: R_def A_def)
    have ASuc_eq: "A (Suc j) x = \<bar>(deriv ^^ (Suc j)) R x\<bar> / \<bar>(y - x0) ^ (n - j)\<bar>"
      by (simp add: R_def A_def)
    also have "... = \<bar>(x - x0) * (deriv ^^ Suc (Suc j)) R z\<bar> / \<bar>(y - x0) ^ (n - j)\<bar>" 
      if "Suc j < n"
      using dSuc_eq[OF \<open>Suc j < n\<close>]
      by simp
    also have "... = \<bar>(x - x0)\<bar> * \<bar>(deriv ^^ Suc (Suc j)) R z\<bar> / \<bar>(y - x0) ^ (n - j)\<bar>" 
      if "Suc j < n"
      by (simp add: abs_mult)
    also have  "... \<le> \<bar>(y - x0)\<bar> * \<bar>(deriv ^^ Suc (Suc j)) R z\<bar> / \<bar>(y - x0) ^ (n - j)\<bar>" 
      if "Suc j < n"
      by (simp add: abs_leq divide_right_mono mult_right_mono)
    also have  "... \<le> \<bar>deriv (deriv ((deriv ^^ j) R)) z\<bar> / \<bar>(y - x0) ^ (n - Suc j)\<bar>" 
      if "Suc j < n"
      using \<open>y \<noteq> x0\<close> \<open>Suc j < n\<close>
      by (cases "x0 < y"; clarsimp)
         (smt (verit, del_insts) Suc_diff_Suc Suc_lessD
              nonzero_mult_divide_mult_cancel_left power_Suc that,
          (simp add: abs_power_minus[symmetric, of "y - x0"]; simp add: power_eq_if))
    finally have "A (Suc j) x \<le> A (Suc (Suc j)) z" if "Suc j < n"
      using \<open>Suc j < n\<close>
      by (simp add: A_def)
    then show ?case
      using z_in x_rel_x0 \<open>y \<noteq> x0\<close> abs_leq
      by (cases "x0 < y"; clarsimp simp: open_segment_eq_real_ivl)
        force+
  qed
  have "\<exists>g. \<forall>j. (if j = 0 then g j = y else g j \<in> open_segment y x0) 
    \<and> (j < n \<longrightarrow> (x0 < y \<longrightarrow> x0 < g (Suc j) \<and> g (Suc j) < g j) 
    \<and> (y < x0 \<longrightarrow> g j < g (Suc j) \<and> g (Suc j) < x0) 
    \<and> (A j (g j) \<le> A (Suc j) (g (Suc j))))"
    using cond2 dependent_nat_choice[where 
        P="\<lambda>m a. if m = 0 then a = y else a \<in> open_segment y x0"
        and Q="\<lambda>j gj gsucj.
          j < n \<longrightarrow> (x0 < y \<longrightarrow> (x0 < gsucj \<and> gsucj < gj)) 
          \<and> (y < x0 \<longrightarrow> (gj < gsucj \<and> gsucj < x0))
          \<and> (A j gj \<le> A (Suc j) gsucj)", simplified]
    by blast
  thus ?thesis
    by metis
qed

lemma ex_remainder_list:
  fixes f :: "real \<Rightarrow> real" and x0 y :: real and n :: nat
  defines "R \<equiv> peano_remainder (Suc n) f x0"
  defines "A j gj \<equiv> \<bar>(deriv ^^ j) R gj\<bar> / \<bar>(y - x0) ^ (Suc n - j)\<bar>"
  assumes "y \<noteq> x0" and y_small: "\<bar>y - x0\<bar> < \<epsilon>"
    and k_diff: "k_times_Fr_differentiable_at (Suc n) f x0"
    and deriv1: "\<forall>z\<in>closed_segment x0 y. (R has_derivative (\<lambda>h. deriv R z * h)) (at z)"
    and derivi: "\<forall>i < n. \<forall>z. \<bar>z - x0\<bar> < \<epsilon> 
      \<longrightarrow> ((deriv ^^ i) R has_derivative (\<lambda>h. (deriv ^^ Suc i) R z * h)) (at z)"
  shows "\<exists>cs. length cs = n \<and>
         (\<forall>j<n. if x0 < y 
            then if j = 0 then x0 < cs ! 0 \<and> cs ! 0 < y else cs ! j < cs ! (j - 1) \<and> x0 < cs ! j 
            else if j = 0 then y < cs ! 0 \<and> cs ! 0 < x0 else cs ! (j - 1) < cs ! j \<and> cs ! j < x0) 
         \<and> (\<forall>j<n. A j (if j = 0 then y else cs ! (j - 1)) 
     \<le> \<bar>(deriv ^^ (j + 1)) (peano_remainder (Suc n) f x0) (cs ! j)\<bar> / \<bar>(y - x0) ^ (n - j)\<bar>)"
proof-
  obtain g where g_props: "\<forall>j::nat. (g 0 = y) 
    \<and> (j < n \<longrightarrow> (x0 < (y::real) \<longrightarrow> (x0 < g (Suc j) \<and> g (Suc j) < g j)) 
    \<and> (y < (x0::real) \<longrightarrow> (g j < g (Suc j) \<and> g (Suc j) < x0))
    \<and> (A j (g j) \<le> A (Suc j) (g (Suc j))))"
    using ex_remainder_choice[OF assms(3-7)[unfolded R_def]]  
    unfolding R_def A_def
    by blast
  then obtain cs where len_cs: "length cs = n"
    and list_assignment: "\<forall>j<n. cs ! j = g (j + 1)"
    by (atomize_elim)
      (auto intro!: exI[where x="map (\<lambda>x. g (Suc x)) [0 ..< n]"])

  from g_props[rule_format] \<open>y \<noteq> x0\<close>
  show ?thesis (is "\<exists>x. ?P x")
    by (intro exI[of _ cs]; cases "y < x0")
       (smt (verit, ccfv_SIG)
            A_def R_def Suc_diff_1 Suc_le_lessD list_assignment len_cs
            add.commute bot_nat_0.not_eq_extremum diff_Suc_1
            diff_Suc_eq_diff_pred linorder_not_le not_less_iff_gr_or_eq
            plus_1_eq_Suc)+
qed

theorem Taylor_Peano_remainder:
  assumes "k_times_Fr_differentiable_at (Suc n) f x0"
  shows   "((\<lambda>x. peano_remainder (n+1) f x0 x / (x-x0) ^ (n+1)) \<longlongrightarrow> 0) (at x0)"
proof(cases "n=0")
  assume "n = 0"
  show "(\<lambda>x. peano_remainder (n+1) f x0 x / (x - x0) ^ (n+1)) \<midarrow>x0\<rightarrow> 0"
  proof - 
    have "k_times_Fr_differentiable_at 1 (peano_remainder 1 f x0) x0"
      by (metis One_nat_def \<open>n = 0\<close> assms peano_kth_deriv_zero_diff zero_less_one_class.zero_le_one)
    then obtain Peano_f' where
      r_has_deriv :
        "(peano_remainder 1 f x0 has_real_derivative Peano_f') (at x0)"
      using one_times_Fr_iff real_differentiable_def by blast
    then have Peanof'_zero : "Peano_f' = 0"
      using r_has_deriv DERIV_imp_deriv kth_deriv_peano_remainder_zero[of 1 1 f x0] assms \<open>n = 0\<close>
      by (metis One_nat_def first_derivative_alt_def le_numeral_extra(4))
    have limit_Peano_Remainder :
      "((\<lambda>x. (peano_remainder 1 f x0 x - peano_remainder 1 f x0 x0)
                 / (x - x0)) \<longlongrightarrow> Peano_f') (at x0)"
      using r_has_deriv by (simp add: has_field_derivativeD) 
    then have "peano_remainder 1 f x0 x0 = 0"
      using kth_deriv_peano_remainder_zero[of 0 1 f x0] assms \<open>n = 0\<close>
      by simp
    then show "(\<lambda>x. peano_remainder (n+1) f x0 x / (x - x0) ^ (n+1)) \<midarrow>x0\<rightarrow> 0"
      using Peanof'_zero \<open>n = 0\<close> limit_Peano_Remainder by force
  qed
next
  assume n_nonzero: "n \<noteq> 0"
  let "?if_prop1 x y j cs" = "if x < y
    then (if j = 0 then x < cs!0 \<and> cs!0 < y else cs!j < cs!(j-1) \<and> cs!j > x)
    else (if j = 0 then y < cs!0 \<and> cs!0 < x else cs!(j-1) <  cs!j \<and> cs!j < x)"
    and "?quotient1 j y cs" = 
      "\<bar>(deriv ^^ j) (\<lambda>x. peano_remainder (Suc n) f x0 x) (if j = 0 then y else cs!(j-1))\<bar>
         / \<bar>(y - x0) ^ ((Suc n) - j)\<bar>"
    and "?quotient2 j y cs" = 
      "\<bar>(deriv ^^ (j+1)) (\<lambda>x. peano_remainder (Suc n) f x0 x) (cs!j)\<bar>
         / \<bar>(y - x0) ^ (n - j)\<bar>"
  have list_exists: "\<exists>\<delta>>0. \<forall>y. y \<noteq> x0 \<longrightarrow> \<bar>y - x0\<bar> < \<delta> 
    \<longrightarrow> (\<exists>cs :: real list.
      length cs = n 
      \<and> (\<forall>j<n. ?if_prop1 x0 y j cs) 
      \<and> (\<forall>j<n. ?quotient1 j y cs \<le> ?quotient2 j y cs))"
  proof -
    have kSucn: "k_times_Fr_differentiable_at (Suc n) (\<lambda>x. peano_remainder (Suc n) f x0 x) x0"
      using peano_kth_deriv_zero_diff[of 0 "Suc n" f x0] assms
      by blast
    obtain A where A: "open A" "x0 \<in> A"
      and Aball: "\<And>y. y \<in> A \<Longrightarrow>
        k_times_Fr_differentiable_at n (\<lambda>x. peano_remainder (Suc n) f x0 x) y"
      using kSucn k_times_Fr_differentiable_at.simps(2)
      by auto
    obtain \<epsilon> where \<epsilon>_pos: "\<epsilon> > 0" and ball_sub: "ball x0 \<epsilon> \<subseteq> A"
      using openE[OF A(1) A(2)]
      by blast
    have diff_ball:
        "\<And>z. \<bar>z - x0\<bar> < \<epsilon> \<Longrightarrow>
             k_times_Fr_differentiable_at n (\<lambda>x. peano_remainder (Suc n) f x0 x) z"
      using Aball ball_sub
      by (metis dist_commute dist_real_def mem_ball subset_iff)

    have field_deriv_ball: "\<forall>z. \<bar>z - x0\<bar> < \<epsilon> \<longrightarrow>
         ((\<lambda>x. peano_remainder (Suc n) f x0 x)
          has_derivative (\<lambda>h. deriv (\<lambda>x. peano_remainder (Suc n) f x0 x) z * h)) (at z)"
      using diff_ball kfr_real_kth_deriv_has_derivative[where k = 0] n_nonzero
      by auto
    then have field_deriv_ball_generalized:
      "\<forall>i < n. \<forall>z. \<bar>z - x0\<bar> < \<epsilon> \<longrightarrow>
    ((deriv ^^ i) (\<lambda>x. peano_remainder (Suc n) f x0 x)
      has_derivative (\<lambda>h. (deriv ^^ Suc i) (\<lambda>x. peano_remainder (Suc n) f x0 x) z * h)) (at z)"
      using diff_ball kfr_real_kth_deriv_has_derivative by blast

    show ?thesis
    proof (intro exI[of _ \<epsilon>] conjI \<epsilon>_pos, clarify)
      fix x 
      assume x_ne: "x \<noteq> x0" 
      assume x_small: "\<bar>x - x0\<bar> < \<epsilon>"
 
      have dir: "x0 < x \<or> x < x0" using x_ne by arith
      have vanishes: "peano_remainder (Suc n) f x0 x0 = 0"
        by (metis assms kth_deriv_peano_remainder_zero kth_deriv_simps(1) less_eq_nat.simps(1))
      show "\<exists>cs. length cs = n 
        \<and> (\<forall>j<n. ?if_prop1 x0 x j cs)
        \<and> (\<forall>j<n. ?quotient1 j x cs \<le> ?quotient2 j x cs)"
        using x_small field_deriv_ball[rule_format] field_deriv_ball_generalized
        by (subst ex_remainder_list[OF x_ne x_small assms],        
            auto simp: closed_segment_eq_real_ivl)
    qed
  qed
  then obtain \<delta> :: real where \<delta>_pos: "\<delta> > 0" and \<delta>_prop: "\<forall>y. y \<noteq> x0 \<longrightarrow> \<bar>y - x0\<bar> < \<delta> 
    \<longrightarrow> (\<exists>cs. length cs = n 
        \<and> (\<forall>j<n. ?if_prop1 x0 y j cs)
        \<and> (\<forall>j<n. ?quotient1 j y cs \<le> ?quotient2 j y cs))"
    by blast
  let "?remainder1 m y" = "(deriv ^^ m) (peano_remainder (Suc n) f x0) y"
  and "?remainder2 m y" = "(deriv ^^ m) (peano_remainder (Suc n) f x0) y"
  have final_term_limit: "(\<lambda>x. (?remainder1 n x - ?remainder1 n x0) / (x - x0)) \<midarrow>x0\<rightarrow> 0"
  proof -
    have "k_times_Fr_differentiable_at (Suc n) (peano_remainder (Suc n) f x0) x0"
      by (meson assms lessI less_le_not_le peano_kth_deriv_zero_diff)
    then have "(\<lambda>r. (?remainder2 n r - ?remainder2 n x0) / (r - x0)) \<midarrow>x0 \<rightarrow> ?remainder2 (Suc n) x0"
      by (metis (lifting) ext DERIV_deriv_iff_real_differentiable has_field_derivative_iff kfr_real_lower_deriv_diff kth_deriv_Suc lessI)
    then have "(\<lambda>r. (?remainder2 n r - ?remainder1 n x0) / (r - x0)) \<midarrow>x0 \<rightarrow> ?remainder1 (Suc n) x0"
      by simp
    then show ?thesis
      by (metis (no_types, lifting) kth_deriv_peano_remainder_zero assms dual_order.refl)
  qed  
  show "(\<lambda>x. peano_remainder (n+1) f x0 x / (x - x0) ^ (n+1)) \<midarrow>x0\<rightarrow> 0" 
  proof(rule filterlim_split_at_real)
    show "((\<lambda>x. peano_remainder (n+1) f x0 x / (x - x0) ^ (n+1)) \<longlongrightarrow> 0) (at_left x0)"     
    proof(subst tendsto_at_left_x_epsilon_def, clarify)
      fix \<epsilon> :: real
      assume \<epsilon>_pos: "0 < \<epsilon>"
      show "\<exists>\<delta>>0. \<forall>y. y < x0 \<and> x0 - y < \<delta> 
      \<longrightarrow> \<bar>peano_remainder (n+1) f x0 y / (y - x0) ^ (n+1) - 0\<bar> < \<epsilon>"
      proof -       
        have "(\<lambda>x. \<bar>((deriv ^^ n) (peano_remainder (Suc n) f x0) x - 
            (deriv ^^ n) (peano_remainder (Suc n) f x0) x0) / (x - x0)\<bar>) \<midarrow>x0\<rightarrow> 0"
          by(rule tendsto_rabs_zero, smt final_term_limit)
        then have "((\<lambda>x. \<bar>(deriv ^^ n) (peano_remainder (Suc n) f x0) x - 
            (deriv ^^ n) (peano_remainder (Suc n) f x0) x0\<bar> / \<bar>x - x0\<bar>) \<longlongrightarrow> 0) (at_left x0)"
          by (meson LIM_cong Lim_at_imp_Lim_at_within abs_divide)     
        with  \<epsilon>_pos
        obtain \<delta>1 where \<delta>1_pos: "\<delta>1 > 0"
                   and \<delta>1_prop: "\<forall>y. y < x0 \<and> x0 - y < \<delta>1 \<longrightarrow>
                        \<bar>(deriv ^^ n) (peano_remainder (Suc n) f x0) y
                        - (deriv ^^ n) (peano_remainder (Suc n) f x0) x0\<bar>
                       /\<bar>y - x0\<bar> < \<epsilon>"
          using tendsto_at_left_x_epsilon_def by auto

        define \<delta>2 where "\<delta>2 = min \<delta> \<delta>1"
        have \<delta>2_pos: "\<delta>2 > 0" 
          by (simp add: \<delta>1_pos \<delta>2_def \<delta>_pos)
      
        have "\<forall>y. y < x0 \<and> x0 - y < \<delta>2 \<longrightarrow>\<bar>peano_remainder (Suc n) f x0 y / (y - x0) ^ Suc n\<bar> < \<epsilon>"
        proof clarify
          fix y :: real
          assume y_cond: "y < x0" "x0 - y < \<delta>2"        
          have y_within_bounds: "y \<noteq> x0 \<and> \<bar>y - x0\<bar> < \<delta>"
            using \<delta>2_def y_cond by fastforce
          then obtain cs
            where cs_len: "length cs = n"
            and cs_order: "(\<forall>j<n. ?if_prop1 x0 y j cs)"
            and cs_ineq:  "\<forall>j<n. ?quotient1 j y cs \<le> ?quotient2 j y cs"
            using \<delta>_prop by blast
          let "?if_term m" = "if m = 0 then y else cs ! (m - 1)"

          have stepwise_chain:
          "\<forall>k \<le> n. \<bar>(\<lambda>t. peano_remainder (Suc n) f x0 t) y\<bar> / \<bar>y - x0\<bar> ^ (Suc n)
                 \<le> \<bar>?remainder1 k (if k = 0 then y else cs ! (k-1))\<bar> 
                  / \<bar>y - x0\<bar> ^ (Suc n - k)"
          proof (intro allI, clarify)
            fix k :: nat
            assume k_bound: "k \<le> n"
            show "\<bar>peano_remainder (Suc n) f x0 y\<bar> / \<bar>y - x0\<bar> ^ Suc n 
              \<le> \<bar>?remainder1 k (if k = 0 then y else cs ! (k - 1))\<bar> / \<bar>y - x0\<bar> ^ (Suc n - k)"
              using k_bound
            proof (induction k rule: nat_induct) 
              show "\<bar>peano_remainder (Suc n) f x0 y\<bar> / \<bar>y - x0\<bar> ^ Suc n 
                \<le> \<bar>?remainder1 0 (?if_term 0)\<bar> / \<bar>y - x0\<bar> ^ (Suc n - 0)"
                by simp
            next
              fix m :: nat
              assume IH: "(m \<le> n \<Longrightarrow> \<bar>peano_remainder (Suc n) f x0 y\<bar> / \<bar>y - x0\<bar> ^ Suc n 
              \<le> \<bar>?remainder1 m (?if_term m)\<bar> / \<bar>y - x0\<bar> ^ (Suc n - m))"
              assume m_bound: "Suc m \<le> n"
              then have IH_antecedent: "m \<le> n"
                by simp
              with IH have IH_consequent: "\<bar>peano_remainder (Suc n) f x0 y\<bar> / \<bar>y - x0\<bar> ^ Suc n 
                \<le> \<bar>?remainder1 m (?if_term m)\<bar> / \<bar>y - x0\<bar> ^ (Suc n - m)"
                by simp
              have "\<bar>?remainder1 m (?if_term m)\<bar> / \<bar>y - x0\<bar> ^ (Suc n - m) 
                \<le> \<bar>?remainder1 (Suc m) (?if_term (Suc m))\<bar> / \<bar>y - x0\<bar> ^ (n -  m)"
              proof -
                have "\<And>m. \<not> m < n \<or> \<bar>?remainder1 m (?if_term m)\<bar> / \<bar>(y - x0) ^ (Suc n - m)\<bar> 
                  \<le> \<bar>?remainder1 (Suc m) (cs ! m)\<bar> / \<bar>(y - x0) ^ (n - m)\<bar>"
                  using Suc_eq_plus1 cs_ineq by presburger
                then show ?thesis
                  by (simp add: Suc_le_lessD m_bound power_abs)
              qed                  
              then show "\<bar>peano_remainder (Suc n) f x0 y\<bar> / \<bar>y - x0\<bar> ^ Suc n 
                \<le> \<bar>?remainder1 (Suc m) (?if_term (Suc m))\<bar> / \<bar>y - x0\<bar> ^ (Suc n - Suc m)"
                by (smt (verit, ccfv_threshold) IH_consequent diff_Suc_Suc)
            qed
          qed
          have cs_tail_bound: "cs ! (n - 1) < x0" 
            by (metis cs_order diff_Suc_1 gr0_conv_Suc lessI n_nonzero 
                not_less_iff_gr_or_eq y_cond(1) zero_less_iff_neq_zero)

          have "\<forall> j < n. \<bar>(cs ! j) - x0\<bar> \<le> \<bar>x0 - y\<bar>"
          proof (intro allI impI)
            fix j :: nat
            assume j_bound: "j < n"
            show "abs (cs ! j - x0) \<le> abs (x0 - y)"
              using j_bound
            proof (induction j rule: nat_induct)
              case 0
              show ?case
                using cs_order n_nonzero y_cond(1) by auto
            next
              case (Suc m)                        
              then show ?case
                using cs_order y_cond(1) by auto
            qed
          qed
          then have final_element_bound: "\<bar>cs ! (n - 1) - x0\<bar> \<le> \<bar>x0 - y\<bar>"
            using n_nonzero by auto                  
          show "\<bar>peano_remainder (Suc n) f x0 y / (y - x0) ^ Suc n\<bar> < \<epsilon>"
          proof - 
            have "\<bar>peano_remainder (Suc n) f x0 y / (y - x0) ^ Suc n\<bar> 
              = \<bar>peano_remainder (Suc n) f x0 y\<bar> / \<bar>y - x0\<bar> ^ Suc n" 
              by (simp, metis power_Suc power_abs)
            also have "... \<le> \<bar>?remainder1 n (?if_term n)\<bar> / \<bar>y - x0\<bar> ^ (Suc n - n)"
              using stepwise_chain[rule_format, of n] by simp
            also have "... \<le> \<bar>?remainder1 n (cs ! (n-1))\<bar>   / \<bar>y - x0\<bar>"
              by (simp add: n_nonzero)
            also have "... \<le> \<bar>?remainder1 n (cs ! (n-1))\<bar>   / \<bar>(cs ! (n-1)) - x0\<bar>"
              by (smt (verit, best) final_element_bound cs_tail_bound frac_le)
            also have "... = \<bar>?remainder1 n (cs ! (n-1)) - ?remainder1 n x0\<bar> / \<bar>(cs!(n-1)) - x0\<bar>"
              using kth_deriv_peano_remainder_zero assms by auto
            also have "... < \<epsilon>"
              using \<delta>1_prop \<delta>2_def cs_tail_bound final_element_bound y_cond by auto
            finally show ?thesis.
          qed
        qed
        then show ?thesis
          using \<delta>2_pos by auto 
      qed
    qed
  next
    show "((\<lambda>x. peano_remainder (n+1) f x0 x / (x - x0) ^ (n+1)) \<longlongrightarrow> 0) (at_right x0)"
    proof(subst tendsto_at_right_x_epsilon_def, clarify)
      fix \<epsilon> :: real
      assume \<epsilon>_pos: "0 < \<epsilon>"
      show "\<exists>\<delta>>0. \<forall>y. x0 < y \<and> y - x0 < \<delta> 
      \<longrightarrow> \<bar>peano_remainder (n+1) f x0 y / (y - x0) ^ (n+1) - 0\<bar> < \<epsilon>"
      proof -       
        have "(\<lambda>x. \<bar>((deriv ^^ n) (peano_remainder (Suc n) f x0) x - 
            (deriv ^^ n) (peano_remainder (Suc n) f x0) x0) / (x - x0)\<bar>) \<midarrow>x0\<rightarrow> 0"
          by(rule tendsto_rabs_zero, smt final_term_limit)
        then have "(\<lambda>x. \<bar>((deriv ^^ n) (peano_remainder (Suc n) f x0) x0 - 
            (deriv ^^ n) (peano_remainder (Suc n) f x0) x) / (x - x0)\<bar>) \<midarrow>x0\<rightarrow> 0"
          by (smt (verit, best) LIM_cong minus_divide_left)
        hence right_limit: 
          "((\<lambda>x. \<bar>?remainder1 n x0 - ?remainder1 n x\<bar> / \<bar>x - x0\<bar>) \<longlongrightarrow> 0) (at_right x0)"
          by (meson LIM_cong Lim_at_imp_Lim_at_within abs_divide)
        have "((\<lambda>x. \<bar>?remainder1 n x0 - ?remainder1 n x\<bar> / \<bar>x - x0\<bar>) \<longlongrightarrow> 0) (at_right x0)
          = (\<forall>\<epsilon>>0. \<exists>\<delta>>0. \<forall>y. x0 < y \<and> y - x0 < \<delta> 
            \<longrightarrow> \<bar>\<bar>?remainder1 n x0 - ?remainder1 n y\<bar> / \<bar>y - x0\<bar> - 0\<bar> < \<epsilon>)"
          by(rule tendsto_at_right_x_epsilon_def)
        with right_limit have "(\<forall>\<epsilon>>0. \<exists>\<delta>>0. \<forall>y. x0 < y \<and> y - x0 < \<delta> 
          \<longrightarrow> \<bar>\<bar>?remainder1 n x0 - ?remainder1 n y\<bar> / \<bar>y - x0\<bar> - 0\<bar> < \<epsilon>)"
          by simp
        
        with \<epsilon>_pos
        obtain \<delta>1 where \<delta>1_pos: "\<delta>1 > 0" and
          \<delta>1_prop: "\<forall>y. x0 < y \<and> y - x0 < \<delta>1 \<longrightarrow> \<bar>?remainder1 n x0 - ?remainder1 n y\<bar> /\<bar>y - x0\<bar> < \<epsilon>"
          by force
         
        define \<delta>2 where "\<delta>2 = min \<delta> \<delta>1"
        have \<delta>2_pos: "\<delta>2 > 0" 
          by (simp add: \<delta>1_pos \<delta>2_def \<delta>_pos)
      
        have "\<forall>y. x0 < y \<and> y - x0 < \<delta>2 \<longrightarrow> \<bar>peano_remainder (Suc n) f x0 y / (y - x0) ^ Suc n\<bar> < \<epsilon>"
        proof clarify
          fix y :: real
          assume y_cond: " x0 < y" " y - x0 < \<delta>2"       
          have y_within_bounds: "y \<noteq> x0 \<and> \<bar>y - x0\<bar> < \<delta>"
            using \<delta>2_def y_cond by fastforce
          then obtain cs
            where cs_len: "length cs = n"
            and cs_order: "(\<forall>j<n. ?if_prop1 x0 y j cs)"
            and cs_ineq:  "\<forall>j<n. ?quotient1 j y cs \<le> ?quotient2 j y cs"
            using \<delta>_prop by blast
          let "?if_term m" = "if m = 0 then y else cs ! (m - 1)"

          have stepwise_chain:
          "\<forall>k \<le> n. \<bar>(\<lambda>t. peano_remainder (Suc n) f x0 t)  y\<bar> / \<bar>y - x0\<bar> ^ (Suc n)
                 \<le> \<bar>?remainder1 k (if k = 0 then y else cs ! (k-1))\<bar> / \<bar>y - x0\<bar> ^ (Suc n - k)"
          proof (intro allI, clarify)
            fix k :: nat
            assume k_bound: "k \<le> n"
            show "\<bar>peano_remainder (Suc n) f x0 y\<bar> / \<bar>y - x0\<bar> ^ Suc n 
              \<le> \<bar>?remainder1 k (if k = 0 then y else cs ! (k - 1))\<bar> / \<bar>y - x0\<bar> ^ (Suc n - k)"
              using k_bound
            proof (induction k rule: nat_induct) 
              show "\<bar>peano_remainder (Suc n) f x0 y\<bar> / \<bar>y - x0\<bar> ^ Suc n 
                \<le> \<bar>?remainder1 0 (if 0 = 0 then y else cs ! (0 - 1))\<bar> / \<bar>y - x0\<bar> ^ (Suc n - 0)"
                by simp
            next
              fix m :: nat
              assume IH: "(m \<le> n \<Longrightarrow> \<bar>peano_remainder (Suc n) f x0 y\<bar> / \<bar>y - x0\<bar> ^ Suc n 
                \<le> \<bar>?remainder1 m (if m = 0 then y else cs ! (m - 1))\<bar> / \<bar>y - x0\<bar> ^ (Suc n - m))"
              assume m_bound: "Suc m \<le> n"
              then have IH_antecedent: "m \<le> n"
                by simp
              with IH have IH_consequent: "\<bar>peano_remainder (Suc n) f x0 y\<bar> / \<bar>y - x0\<bar> ^ Suc n 
                \<le> \<bar>?remainder1 m (?if_term m)\<bar> / \<bar>y - x0\<bar> ^ (Suc n - m)"
                by simp
              have "\<bar>?remainder1 m (?if_term m)\<bar> / \<bar>y - x0\<bar> ^ (Suc n - m) 
                \<le> \<bar>?remainder1 (Suc m) (?if_term (Suc m))\<bar> / \<bar>y - x0\<bar> ^ (n -  m)"
              proof -
                have "\<And>m. \<not> m < n \<or> \<bar>?remainder1 m (?if_term m)\<bar> / \<bar>(y - x0) ^ (Suc n - m)\<bar> 
                  \<le> \<bar>?remainder1 (Suc m) (cs ! m)\<bar> / \<bar>(y - x0) ^ (n - m)\<bar>"
                  using Suc_eq_plus1 cs_ineq by presburger
                then show ?thesis
                  by (simp add: Suc_le_lessD m_bound power_abs)
              qed                  
              then show "\<bar>peano_remainder (Suc n) f x0 y\<bar> / \<bar>y - x0\<bar> ^ Suc n 
                \<le> \<bar>?remainder1 (Suc m) (?if_term (Suc m))\<bar> / \<bar>y - x0\<bar> ^ (Suc n - Suc m)"
                by (smt (verit, ccfv_threshold) IH_consequent diff_Suc_Suc)
            qed
          qed
          have cs_tail_bound: "cs ! (n - 1) > x0" 
            by (metis cs_order diff_Suc_1 gr0_conv_Suc lessI 
                n_nonzero y_cond(1) zero_less_iff_neq_zero)

          have "\<forall> j < n. \<bar>(cs ! j) - x0\<bar> \<le> \<bar>x0 - y\<bar>"
          proof (intro allI impI)
            fix j :: nat
            assume j_bound: "j < n"
            show "abs (cs ! j - x0) \<le> abs (x0 - y)"
              using j_bound
            proof (induction j rule: nat_induct)
              case 0
              show ?case
                using cs_order n_nonzero y_cond(1) by auto
            next
              case (Suc m)                        
              then show ?case
                using cs_order y_cond(1) by auto            
            qed
          qed
          then have final_element_bound: "\<bar>cs ! (n - 1) - x0\<bar> \<le> \<bar>x0 - y\<bar>"
            using n_nonzero by auto
          show "\<bar>peano_remainder (Suc n) f x0 y / (y - x0) ^ Suc n\<bar> < \<epsilon>"
          proof - 
            have "\<bar>peano_remainder (Suc n) f x0 y / (y - x0) ^ Suc n\<bar> 
              = \<bar>peano_remainder (Suc n) f x0 y\<bar> / \<bar>y - x0\<bar> ^ Suc n" 
              by (simp, metis power_Suc power_abs)
            also have "... \<le> \<bar>?remainder1 n (?if_term n)\<bar> / \<bar>y - x0\<bar> ^ (Suc n - n)"
              using stepwise_chain[rule_format, of n] by simp 
            also have "... \<le> \<bar>?remainder1 n (cs ! (n-1))\<bar>   / \<bar>y - x0\<bar>"
              by (simp add: n_nonzero)
            also have "... \<le> \<bar>?remainder1 n (cs ! (n-1))\<bar>   / \<bar>(cs ! (n-1)) - x0\<bar>"
              by (smt (verit, best) final_element_bound cs_tail_bound frac_le)
            also have "... = \<bar>?remainder1 n (cs ! (n-1)) - ?remainder1 n x0\<bar> / \<bar>(cs ! (n-1)) - x0\<bar>"
              using kth_deriv_peano_remainder_zero assms by auto
            also have "... <  \<epsilon>"
              by (smt (verit, del_insts) \<delta>1_prop \<delta>2_def cs_tail_bound final_element_bound y_cond)
            finally show ?thesis.
          qed
        qed
        then show ?thesis
          using \<delta>2_pos by auto
      qed
    qed  
  qed
qed

corollary Taylor_Peano:
  assumes "k_times_Fr_differentiable_at (Suc n) f a"
  obtains h :: "real \<Rightarrow> real"
  where  "((\<lambda>x. h x) \<longlongrightarrow> 0) (at a)"
     and "f x = (\<Sum>i\<le>(n+1). (deriv ^^ i) f a/fact i * (x-a) ^ i) + h x * (x-a)^(n+1)"
proof
  define h where h_def: 
    "h x = (if x=a then 0 else peano_remainder (n+1) f a x / (x - a) ^ (n+1))" for x

  have lim0: "((\<lambda>x. peano_remainder (n+1) f a x / (x - a) ^ (n+1)) \<longlongrightarrow> 0) (at a)"
    using Taylor_Peano_remainder[OF assms].

  have ev_ne: "eventually (\<lambda>x. x \<noteq> a) (at a)"
    by (simp add: eventually_at_filter)

  have eq_ev: "eventually (\<lambda>x. h x = peano_remainder (Suc n) f a x / (x - a) ^ Suc n) (at a)"
    by (simp add: h_def)
    show tend0: "((\<lambda>x. h x) \<longlongrightarrow> 0) (at a)"
      using eq_ev filterlim_cong lim0 by fastforce


      have exp_ne:"\<And>x. x \<noteq> a \<Longrightarrow>
      f x = (\<Sum>i\<le>Suc n. (deriv ^^ i) f a / fact i * (x - a) ^ i) + h x * (x - a) ^ Suc n"
    using h_def peano_remainder_def taylor_poly_def by force

  have exp_a: "f a = (\<Sum>i\<le>Suc n. (deriv ^^ i) f a / fact i * (a - a) ^ i) + h a * (a-a) ^ Suc n"
    by (simp add: h_def)

  show "f x = (\<Sum>i\<le>n + 1. (deriv ^^ i) f a / fact i * (x - a) ^ i) +
    (if x = a then 0 else peano_remainder (n + 1) f a x / (x - a) ^ (n + 1)) * (x - a) ^ (n + 1)"
    using Suc_eq_plus1 h_def exp_a exp_ne
    by presburger
qed

end