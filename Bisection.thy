section \<open>Bisection Method\<close>

theory Bisection
  imports "ITree_Numeric_VCG.ITree_Numeric_VCG" HOL.Transcendental
begin

theorem Bolzanos_theorem:
  fixes f :: "real \<Rightarrow> real"
  assumes a_less_than_b: "\<alpha> < \<beta>"
  assumes opposite_signs: "f(\<alpha>)*f(\<beta>) < 0"  
  assumes continuous_f: "continuous_on {\<alpha>..\<beta>} f"
  shows "\<exists> \<gamma>. (f(\<gamma>) = 0 \<and> \<alpha> < \<gamma> \<and> \<gamma> < \<beta>)"
proof -
  have "f(\<alpha>) \<noteq> 0" and "f(\<beta>) \<noteq> 0"
    using opposite_signs by (auto simp: mult_less_0_iff)
  hence cases: "(f(\<alpha>) < 0 \<and> f(\<beta>) > 0) \<or> (f(\<alpha>) > 0 \<and> f(\<beta>) < 0)"
    using opposite_signs by (auto simp: mult_less_0_iff)
  have  "\<exists> \<gamma>. \<gamma> \<in> {\<alpha>..\<beta>} \<and> f(\<gamma>) = 0"
  proof(cases "f(\<alpha>) < 0 \<and> f(\<beta>) > 0")
    show "f \<alpha> < 0 \<and> 0 < f \<beta> \<Longrightarrow> \<exists>\<gamma>. \<gamma> \<in> {\<alpha>..\<beta>} \<and> f \<gamma> = 0"
      by (metis IVT' a_less_than_b atLeastAtMost_iff continuous_f less_le_not_le) 
  next 
    assume "\<not> (f \<alpha> < 0 \<and> 0 < f \<beta>)"
    then have "(f \<beta> < 0 \<and> 0 < f \<alpha>)"
      using cases by linarith
    from IVT2'[where f = "f", where b="\<beta>", where a = "\<alpha>", where y=0]
    obtain \<gamma> where "\<gamma> \<in> {\<alpha>..\<beta>}" and "f \<gamma> = 0"
      using \<open>f \<beta> < 0 \<and> 0 < f \<alpha>\<close> \<open>f \<beta> < 0 \<and> 0 < f \<alpha>\<close> a_less_than_b continuous_f by auto
    then show ?thesis
      by blast
  qed
  then show ?thesis
    by (smt (verit, best) \<open>f \<alpha> \<noteq> 0\<close> \<open>f \<beta> \<noteq> 0\<close> atLeastAtMost_iff)
qed

subsection \<open>Algorithm\<close>

\<comment> \<open>We formalize a classic bisection root-finder and explicitly emulate the reference
implementation in R’s Computational Methods for Numerical Analysis (cmna) package (source and manual page below).

Links:
\begin{itemize}
\item Source (R):  https://github.com/cran/cmna/blob/master/R/bisection.R
\item Manual page: https://search.r-project.org/CRAN/refmans/cmna/html/bisection.html
\end{itemize}\<close>

zstore state = 
  iter :: "nat"
  fa :: "real"
  fb :: "real"
  lower :: "real"
  upper :: "real"
  xmid :: "real"
  ymid :: "real"
  root :: "real"

program bisection "(f :: real \<Rightarrow> real, a :: real, b :: real, tol :: real)" over state
 = "iter := 0;
    fa:= f(a);
    fb:= f(b);
    lower:= a;
    upper:= b;
    xmid:= lower;
    ymid:= f(xmid);
         
    while upper - lower > tol

    invariant fa * fb \<le> 0 
      \<and> (lower = xmid \<or> upper = xmid)
      \<and> a \<le> lower \<and> upper \<le> b \<and> lower < upper
      \<and> fa = f(lower)
      \<and> fb = f(upper)     
      \<and> upper - lower = (b - a) / 2^iter
      \<and> (iter = 0 \<or> 2 * (upper - lower) > tol)
    variant nat(\<lceil>log 2 ((b - a) / tol)\<rceil>) - iter

    do
      iter:= iter + 1;      
      xmid:= (lower + upper)/2;      
      ymid:= f(xmid);

      if fa*ymid > 0  
      then lower:= xmid; fa:= ymid 
      else upper:= xmid; fb:= ymid 
      fi
    od;
    root:= (lower+upper)/2"

execute "bisection (\<lambda> x. (x*x*x) -2*x*x - 159 , 0, 10, 0.000000000001)"  
\<comment> \<open>This execution terminates with a root estimate of approximately 6.17, as desired.
Moreover, note that log₂((10 − 0) / 10⁻⁹) $\approx$ 43.18; taking the ceiling of this
gives the number of iterations required for the program to terminate.
The next theorem generalizes this observation, thereby proving the total correctness
of the bisection method.\<close>

subsection \<open>Total Correctness Proof\<close>

theorem bisection_error_bound:
  assumes postiv_tolerance: "tol > 0"
  assumes sufficiently_small_tol: "tol < b-a"
  assumes a_less_than_b: "a < b"
  assumes continuous_f: "continuous_on {a..b} f"
  assumes opposite_signs: "f(a)*f(b)<0"
  shows  "H[True] bisection(f,a,b,tol)
       [\<exists> c::real. f(c) = 0 
         \<and> a < c \<and> c < b 
         \<and> upper - lower \<le> tol
         \<and> \<bar>c - xmid\<bar> \<le> (b - a)/2^iter
         \<and> \<bar>c - xmid\<bar> \<le> tol
         \<and> iter = \<lceil>log 2 ((b - a) / tol)\<rceil>]"
proof -
  have ln2_g_0 [simp]: "\<lceil>log 2 ((b - a) / tol)\<rceil> > 0"
    using assms(2) postiv_tolerance by force
  hence [simp]: "0 < log 2 ((b - a) / tol)"
    using zero_less_ceiling by simp
  show ?thesis
  proof (vcg)
    fix xmid upper
    assume a0: "0 < f xmid * f ((xmid + upper) / 2)"
    assume a1: "f xmid * f upper \<le> 0"  
    show "f ((xmid + upper) / 2) * f upper \<le> 0"
      by (smt (verit, del_insts) a0 a1 zero_compare_simps(6))
  next
    fix xmid upper iter
    assume "upper - xmid = (b - a) / 2 ^ iter"
    hence "(upper - xmid) / 2 = (b - a) / (2 * 2 ^ iter)"
      by simp
    thus "upper - (xmid + upper) / 2 = (b - a) / (2 * 2 ^ iter)"
      by (smt (z3) field_sum_of_halves)
  next
    fix xmid upper 
    assume "upper - xmid = b - a"
    thus "upper * 2 - (xmid * 2 + upper * 2) / 2 = b - a"
      by (smt (z3) field_sum_of_halves)
  next
    fix xmid upper 
    assume "upper - xmid = b - a"
    thus "tol < 2 * upper - (2 * xmid + 2 * upper) / 2"
      by (smt (z3)  field_sum_of_halves sufficiently_small_tol)
  next
    show "f a * f b \<le> 0"
      using opposite_signs by auto
  next
    show "a < b"
      by (simp add: a_less_than_b)
  next
    fix xmid upper
    show "upper - xmid = b - a  \<Longrightarrow> upper * 2 - (xmid * 2 + upper * 2) / 2 = b - a"
      by (smt (z3)  field_sum_of_halves)
  next
    fix xmid upper
    show "upper - xmid = b - a \<Longrightarrow> tol < 2 * upper - (2 * xmid + 2 * upper) / 2"
      by (smt (z3) sufficiently_small_tol field_sum_of_halves)
  next
    fix xmid upper iter
    assume a0: "upper - xmid = (b - a) / 2 ^ iter"
    assume a1: "tol < (b - a) / 2 ^ iter"
    show "tol < 2 * upper - (2 * xmid + 2 * upper) / 2"
      by (smt (z3) a0 a1 field_sum_of_halves)
  next
    fix lower upper
    assume a0: "0 < f lower * f ((lower + upper) / 2)"
    assume a1: "f lower * f upper \<le> 0"
    show "f ((lower + upper) / 2) * f upper \<le> 0"
      by (smt (verit, ccfv_SIG) a0 a1 zero_compare_simps(8))
  next
    fix iter lower upper
    assume a0: "0 < f lower * f ((lower + upper) / 2)"
    assume a1: "f lower * f upper \<le> 0"  
    show "f ((lower + upper) / 2) * f upper \<le> 0"
      by (smt (verit, ccfv_SIG) a0 a1 zero_compare_simps(6))
  next
    fix iter lower upper
    assume a0: "upper - lower = (b - a) / 2 ^ iter"
    assume a1: "tol < (b - a) / 2 ^ iter"
    show "tol < 2 * upper - (2 * lower + 2 * upper) / 2"
      by (smt (z3) a0 a1 field_sum_of_halves)
  next
    fix upper xmid
    assume  "\<not> (tol < b - a)"
    thus "\<exists>c. f c = 0 \<and> a < c \<and> c < b \<and> \<bar>c - xmid\<bar> \<le> b - a \<and> \<bar>c - xmid\<bar> \<le> tol \<and> \<lceil>log 2 ((b - a) / tol)\<rceil> = 0"
      using sufficiently_small_tol by blast
  next
    fix iter upper xmid
    assume a0: "\<not> (tol < (b - a) / 2 ^ iter)"
    assume a1: "f xmid * f upper \<le> 0"
    assume a2: "a \<le> xmid"
    assume a3: "upper \<le> b"
    assume a4: "upper - xmid = (b - a) / 2 ^ iter"
    assume a5: "tol < 2 * upper - 2 * xmid"
    show "\<exists>c. f c = 0 \<and> a < c \<and> c < b \<and> \<bar>c - xmid\<bar> \<le> (b - a) / 2 ^ iter \<and> \<bar>c - xmid\<bar> \<le> tol \<and> int iter = \<lceil>log 2 ((b - a) / tol)\<rceil>"
    proof -
      define L where "L = (b - a) / 2 ^ iter"
      have L_pos: "0 < L"
        using L_def a4 a5 assms(1) by linarith

\<comment> \<open>\(f\) is continuous on the sub-interval\<close>
      have cont_sub: "continuous_on {xmid..upper} f"
        by (meson a2 a3 assms(4) atLeastatMost_subset_iff continuous_on_subset)

\<comment> \<open>Bolzano: product \(\le 0\) implies a root in \([x_{\text{mid}},\,\text{upper}]\)\<close>
      obtain c where cI: "c \<in> {xmid..upper}" and fc0: "f c = 0"
        by (metis Bolzanos_theorem L_def L_pos a1 a4 antisym_conv1 atLeastAtMost_iff cont_sub 
            diff_gt_0_iff_gt nle_le no_zero_divisors not_less_iff_gr_or_eq)

      have c_bounds: "a < c \<and> c < b"
        using a2 a3 assms(5) cI fc0 order_less_le by fastforce

\<comment> \<open>distance bound\<close>
      have dist_tol: "\<bar>c - xmid\<bar> \<le> tol"
        using a0 a4 cI by auto

\<comment> \<open>deduce \(\textit{iter} \ge 1 \) from \( \textit{tol} < (b-a) \) and \( L \le \textit{tol}\)\<close>
      from sufficiently_small_tol 
      have iter_pos: "iter \<ge> 1"
        by (metis a0 div_by_1 less_one not_le power_0)

      have ceil_log: "int iter = \<lceil>log 2 ((b - a) / tol)\<rceil>"
      proof -
        have "1/2 < L / tol"
          by (smt (verit, ccfv_SIG) L_def a4 a5 add_divide_distrib assms(1) less_divide_eq_1_pos)
        then have "(2::real) ^ iter * (L / tol) > (2::real) ^ iter * (1/2)"
          by (smt (verit) mult_strict_left_mono zero_less_power)
        then have "(b - a) / tol > (2::real) ^ (iter - 1)"
          by (smt (verit, del_insts) Groups.mult_ac(2) L_def iter_pos mult_cancel_left2
              nonzero_divide_eq_eq power_diff power_one_right times_divide_eq_right)
        moreover have "(b - a) / tol \<le> 2 ^ iter"
          by (metis a0 linorder_not_le mult.commute one_le_power order_less_le_trans pos_divide_le_eq
              postiv_tolerance verit_comp_simplify(28) verit_comp_simplify(5))
        ultimately show ?thesis
          by (smt (verit) Groups.add_ac(2) a0 add_diff_inverse_nat ceiling_log_eq_powr_iff
              int_ops(2) iter_pos linorder_not_le mult.commute of_nat_diff pos_divide_le_eq
              assms(1) powr_realpow zero_less_power)
      qed
      show ?thesis
        using a4 cI c_bounds ceil_log dist_tol fc0 by fastforce
    qed
  next
    fix lower upper
    assume "\<not> tol < b - a"
    thus "\<exists>c. f c = 0 \<and> a < c \<and> c < b \<and> \<bar>c - upper\<bar> \<le> b - a \<and> \<bar>c - upper\<bar> \<le> tol \<and> \<lceil>log 2 ((b - a) / tol)\<rceil> = 0"
      using sufficiently_small_tol by blast
  next
    fix iter lower upper
    assume a0: "\<not> (tol < (b - a) / 2 ^ iter)"
    assume a1: "f lower * f upper \<le> 0"
    assume a2: "a \<le> lower"
    assume a3: "upper \<le> b"
    assume a4: "upper - lower = (b - a) / 2 ^ iter"
    assume a5: "tol < 2 * upper - 2 * lower"
    show "\<exists>c. f c = 0 \<and> a < c \<and> c < b \<and> \<bar>c - upper\<bar> \<le> (b - a) / 2 ^ iter \<and> \<bar>c - upper\<bar> \<le> tol \<and> int iter = \<lceil>log 2 ((b - a) / tol)\<rceil>"
    proof -
      define L where "L = (b - a) / 2 ^ iter"

      have L_pos: "0 < L"
        using L_def a4 a5 assms(1) by linarith

      have cont_sub: "continuous_on {lower..upper} f"
        by (meson a2 a3 assms(4) atLeastatMost_subset_iff continuous_on_subset)

      obtain c where cI: "c \<in> {lower..upper}" and fc0: "f c = 0"
        by (metis Bolzanos_theorem L_def L_pos a1 a4 antisym_conv1 atLeastAtMost_iff cont_sub 
            diff_gt_0_iff_gt nle_le no_zero_divisors not_less_iff_gr_or_eq)

      have c_bounds: "a < c \<and> c < b"
        using a2 a3 assms(5) cI fc0 order_less_le by fastforce
      have dist_tol: "\<bar>c - upper\<bar> \<le> tol"
        using a0 a4 cI by auto
      from sufficiently_small_tol 
      have iter_pos: "iter \<ge> 1"
        by (metis a0 div_by_1 leI less_one power_0)

      have ceil_log: "int iter = \<lceil>log 2 ((b - a) / tol)\<rceil>"
      proof -
        have "1/2 < L / tol"
          by (smt (verit, ccfv_SIG) L_def a4 a5 add_divide_distrib assms(1) less_divide_eq_1_pos)
        then have "(2::real) ^ iter * (L / tol) > (2::real) ^ iter * (1/2)"
          by (smt (verit) mult_strict_left_mono zero_less_power)
        then have "(b - a) / tol > (2::real) ^ (iter - 1)"
          by (smt (verit, del_insts) Groups.mult_ac(2) L_def iter_pos mult_cancel_left2
              nonzero_divide_eq_eq power_diff power_one_right times_divide_eq_right)
        moreover have "(b - a) / tol \<le> 2 ^ iter"
          by (metis a0 linorder_not_le mult.commute one_le_power order_less_le_trans 
              pos_divide_le_eq postiv_tolerance verit_comp_simplify(28) verit_comp_simplify(5))
        ultimately show ?thesis
          by (smt (verit) Groups.add_ac(2) a0 add_diff_inverse_nat ceiling_log_eq_powr_iff
              int_ops(2) iter_pos linorder_not_le mult.commute of_nat_diff pos_divide_le_eq
              assms(1) powr_realpow zero_less_power)
      qed
      show ?thesis
        using a4 cI c_bounds ceil_log dist_tol fc0 by fastforce  
    qed
  next
    fix iter lower upper
    assume a0: "0 < f lower * f ((lower + upper) / 2)"
    assume a1: "f lower * f upper \<le> 0" 
    show "f ((lower + upper) / 2) * f upper \<le> 0"
      by (smt (verit) a0 a1 zero_compare_simps(8))
  next
    fix iter lower upper
    assume "upper - lower = (b - a) / 2 ^ iter"
    thus "upper - (lower + upper) / 2 = (b - a) / (2 * 2 ^ iter)"
      by (simp add: field_simps)
  next
    fix iter :: "\<nat>" 
    assume "tol < (b - a) / 2 ^ iter"
    thus "nat \<lceil>log 2 ((b - a) / tol)\<rceil> - Suc iter < nat \<lceil>log 2 ((b - a) / tol)\<rceil> - iter"
      by (smt (verit, del_insts) Groups.add_ac(2) assms(3) 
          divide_divide_eq_right divide_pos_pos frac_le le_diff_conv less_log_of_power 
          linear linorder_not_le nonzero_mult_div_cancel_left not_less_eq_eq of_nat_Suc 
          of_nat_add of_nat_diff of_nat_le_iff order_le_less postiv_tolerance real_nat_ceiling_ge) 
    thus "nat \<lceil>log 2 ((b - a) / tol)\<rceil> - Suc iter < nat \<lceil>log 2 ((b - a) / tol)\<rceil> - iter".
    thus "nat \<lceil>log 2 ((b - a) / tol)\<rceil> - Suc iter < nat \<lceil>log 2 ((b - a) / tol)\<rceil> - iter".
    thus "nat \<lceil>log 2 ((b - a) / tol)\<rceil> - Suc iter < nat \<lceil>log 2 ((b - a) / tol)\<rceil> - iter".    
  qed
qed
    
end