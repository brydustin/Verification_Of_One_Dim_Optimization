section \<open>Auxiliary Facts\<close>

theory Auxiliary_Facts
  imports
    "Sigmoid_Universal_Approximation.Limits_Higher_Order_Derivatives" 
    "Unconstrained_Optimization.Auxilary_Facts"
begin

subsection \<open> Combinatorics \<close>

lemma binomial_convolution_sum:
  fixes A B :: "nat \<Rightarrow> real"      
  shows
    "(\<Sum> j \<le> k. of_nat (k choose j) *
         (A j * B (Suc (k - j)) + A (Suc j) * B (k - j)))
     =
     (\<Sum> j \<le> Suc k. of_nat (Suc k choose j) * A j * B (Suc k - j))"
proof -
  let ?S1 = "\<Sum>j\<le>k. of_nat (k choose j) * A j       * B (Suc (k - j))"
  let ?S2 = "\<Sum>j\<le>k. of_nat (k choose j) * A (Suc j) * B (k   - j)"

  have split:
    "(\<Sum> j \<le> k. of_nat (k choose j) *
         (A j * B (Suc (k - j)) + A (Suc j) * B (k - j))) = ?S1 + ?S2"
    by (simp add: sum.distrib algebra_simps)
  
  have S1_rewrite:
    "?S1 = (\<Sum>j\<le>Suc k. of_nat (k choose j) * A j * B (Suc k - j))"   
    by (simp add: Suc_diff_le)

  have S1_split :
  "?S1 =
     of_nat (k choose 0) * A 0 * B (Suc k) +
     (\<Sum>j\<in>{1..k}. of_nat (k choose j) * A j * B (Suc k - j))"
  proof -   
    have "?S1 =
            (\<Sum>j\<in>{0..k}. of_nat (k choose j) * A j * B (Suc k - j))"
      using S1_rewrite atMost_atLeast0 by fastforce
    also have "... =
          of_nat (k choose 0) * A 0 * B (Suc k) +
          (\<Sum>j\<in>{1..k}. of_nat (k choose j) * A j * B (Suc k - j))"
      by (simp add: sum.atLeast_Suc_atMost)
      finally show ?thesis.
  qed

  have S2_rewrite:
    "?S2 =
       (\<Sum>j\<in>{1..k}.     of_nat (k choose (j - 1)) * A j       * B (Suc k - j))
     +   of_nat (k choose k)        * A (Suc k) * B 0"
  proof -
    let ?g = "\<lambda>j. of_nat (k choose j) * A (Suc j) * B (k - j)"

    have "?S2 = (\<Sum>j\<in>{0..k}. ?g j)"
      using atMost_atLeast0 by presburger      
    also have "... = (\<Sum>i\<in>{1..Suc k}. ?g (i - 1))"   
      by (rule sum.reindex_bij_witness
            [where i = "\<lambda>n::nat. n - 1"
               and j = Suc 
               and S = "{0..k}"
               and T = "{1..Suc k}" ], simp_all, auto)
    also have "... =
          (\<Sum>j\<in>{1..Suc k}. of_nat (k choose (j - 1)) *
                         A (j) * B (Suc k - j))"
      by auto   
    also have "... =
        (\<Sum>i\<in>{1..k}. of_nat (k choose (i - 1)) *
                     A i * B (Suc k - i))
      +   of_nat (k choose ((Suc k) - 1)) *
          A (Suc ((Suc k) - 1)) *
          B (Suc k - Suc k)"
      by (simp add: sum.insert_remove insert_absorb)
    also have "... =
        (\<Sum>i\<in>{1..k}. of_nat (k choose (i - 1)) *
                     A i * B (Suc k - i))
      +   of_nat (k choose k) * A (Suc k) * B 0"
      by simp
    finally show ?thesis.
  qed

  show "(\<Sum> j \<le> k. of_nat (k choose j) *
         (A j * B (Suc (k - j)) + A (Suc j) * B (k - j)))=
        (\<Sum>j\<le>Suc k.
            of_nat (Suc k choose j)
            * A j * B (Suc k - j))"
  proof -     
    have "(\<Sum> j \<le> k. of_nat (k choose j) *
         (A j * B (Suc (k - j)) + A (Suc j) * B (k - j))) = 
          (\<Sum>j \<in>{0..k}. of_nat (k choose j) *
         (A j * B (Suc (k - j)) + A (Suc j) * B (k - j)))"
      using atLeast0AtMost by presburger
    also have "... =
        (\<Sum> j\<in>{0..k}. of_nat (k choose j) * (A j * B (Suc (k - j))))
      + (\<Sum> j\<in>{0..k}. of_nat (k choose j) * (A (Suc j) * B (k - j)))"
      by (simp add: sum.distrib algebra_simps)
    also have " ... = (\<Sum>j\<in>{0..k}. of_nat (k choose j) * (A j * B (Suc (k - j)))) +  
                      (\<Sum>j\<in>{0..k}. of_nat (k choose j) *  A (Suc j) * B (k - j))"
      by (meson vector_space_over_itself.scale_scale)
    also have " ...  =
            of_nat (k choose 0) * A 0 * B (Suc k) +
         (\<Sum>j\<in>{1..k}. of_nat (k choose j) * A j * B (Suc k - j)) +
         (\<Sum>j\<in>{1..k}.     of_nat (k choose (j - 1)) * A j * B (Suc k - j))
       +   of_nat (k choose k)        * A (Suc k) * B 0"
    proof - 
      have fst_sum: "(\<Sum>j\<in>{0..k}. of_nat (k choose j) * (A j * B (Suc (k - j)))) 
        =  of_nat (k choose 0) * A 0 * B (Suc k) 
        + (\<Sum>j\<in>{1..k}. of_nat (k choose j) * A j * B (Suc k - j))"
        by (simp add: S1_split atLeast0AtMost vector_space_over_itself.scale_scale)
      moreover have snd_sum: "(\<Sum>j\<in>{0..k}. of_nat (k choose j) *  A (Suc j) * B (k - j)) = 
        (\<Sum>j\<in>{1..k}.     of_nat (k choose (j - 1)) * A j * B (Suc k - j))
       +   of_nat (k choose k)        * A (Suc k) * B 0"
        using S2_rewrite atLeast0AtMost by presburger
      ultimately show ?thesis
        by linarith
    qed
    also have "... =
      (of_nat (k choose 0) * A 0 * B (Suc k)
     + (\<Sum> j\<in>{1..k}.
          (of_nat (k choose j)       * A j * B (Suc k - j)
         + of_nat (k choose (j - 1)) * A j * B (Suc k - j))))
   + of_nat (k choose k) * A (Suc k) * B 0"
      by (simp add: sum.distrib)
    also have "... 
      = (of_nat (k choose 0) * A 0 * B (Suc k)
        + (\<Sum> j\<in>{1..k}. ((real (k choose j) + real (k choose (j - 1)))  * A j * B (Suc k - j))))
      + of_nat (k choose k) * A (Suc k) * B 0"
      by (simp add: distrib_left mult.commute)
    also have "... =
      of_nat (k choose 0) * A 0 * B (Suc k)
     + (\<Sum> j\<in>{1..k}. real (Suc k choose j) * A j * B (Suc k - j))
     + of_nat (k choose k) * A (Suc k) * B 0"
    proof - 
      have pascal_pointwise:
      "\<And>j. j \<in> {1..k} \<Longrightarrow>
         (real (k choose j) + real (k choose (j - 1)))
           * A j * B (Suc k - j)
       =  real (Suc k choose j)
           * A j * B (Suc k - j)"
        by (metis One_nat_def Suc_le_eq Suc_pred' 
            add.commute atLeastAtMost_iff binomial_Suc_Suc of_nat_add)
      then show ?thesis
        by (metis (no_types, lifting) sum.cong)
    qed
    also have "... =  (\<Sum>j\<le>Suc k.
            of_nat (Suc k choose j)
            * A j * B (Suc k - j))"
      by (simp add: atMost_atLeast0 sum.atLeast_Suc_atMost)
    finally show ?thesis.
  qed
qed

subsection \<open> Derivative Transferring \<close>

lemma deriv_eq: "(f has_derivative (\<lambda>y. D * y)) (at x) \<Longrightarrow> deriv f x = D"
  unfolding frechet_derivative_def deriv_def 
  using DERIV_unique has_field_derivative_def by blast

lemma has_derivative_transfer_on_open:
  assumes "open X" and "x \<in> X"
  assumes eq_on_X: "\<forall>x\<in>X. f x = g x" 
  assumes f_has_deriv: "(f has_derivative f') (at x)"
  shows "(g has_derivative f') (at x)"
  using at_within_open_subset[OF _ \<open>open X\<close>, of _ X, simplified]
  by (metis \<open>x \<in> X\<close> f_has_deriv eq_on_X has_derivative_transform)

lemma deriv_transfer:
  assumes "open X" and "x \<in> X"
    and eq_on_X: "\<forall>x\<in>X. f x = g x" 
    and f_has_deriv: "(f has_derivative (*) f') (at x within X)"
  shows "deriv f x = deriv g x"
    and "(g has_derivative (*) f') (at x within X)"
  using f_has_deriv has_derivative_transfer_on_open[OF \<open>open X\<close> \<open>x \<in> X\<close> eq_on_X]
  unfolding at_within_open_subset[OF \<open>x \<in> X\<close> \<open>open X\<close>, of X, simplified]
  by (presburger | (metis DERIV_imp_deriv[unfolded has_field_derivative_def]))+

lemma at_within_ball: "\<epsilon> > 0 \<Longrightarrow> at x within ball x \<epsilon> = at x"
  using at_within_open[of x "ball x \<epsilon>", simplified] . 

corollary has_derivative_transfer_on_ball:
  assumes eps_gt0: "0 < \<epsilon>"
  assumes eq_on_ball: "\<forall>y. y \<in> ball x \<epsilon> \<longrightarrow> f y = g y"
  assumes f_has_deriv: "(f has_derivative D) (at x)"
  shows "(g has_derivative D) (at x)"
  using has_derivative_transfer_on_open[OF open_ball _ _ f_has_deriv] 
  by (metis centre_in_ball eq_on_ball eps_gt0)

corollary field_differentiable_transfer_on_ball:
  assumes "0 < \<epsilon>"
  assumes eq_on_ball: "\<forall>y. y \<in> ball x \<epsilon> \<longrightarrow> f y = g y"
  assumes f_diff: "f field_differentiable at x"
  shows "g field_differentiable at x"
  using f_diff has_derivative_transfer_on_ball[OF \<open>0 < \<epsilon>\<close> eq_on_ball]
  by (auto simp: field_differentiable_def has_field_derivative_def)

subsection \<open>\(\varepsilon\)--\(\delta\) Characterizations \<close>


subsubsection \<open> Convergence \<close>

lemma tendsto_at_top_eq:
  fixes f :: "'a::linorder \<Rightarrow> 'b :: metric_space"
  shows "(f \<longlongrightarrow> L) at_top \<longleftrightarrow> (\<forall>e>0. \<exists>N. \<forall>n\<ge>N. dist (f n) L < e)"
  by (simp add: tendsto_iff eventually_at_top_linorder)

corollary tendsto_at_top_epsilon_def:
  "(f \<longlongrightarrow> L) at_top = (\<forall> \<epsilon> > 0. \<exists>N. \<forall>x \<ge> N. \<bar>(f (x::real)::real) - L\<bar> < \<epsilon>)"
  by (simp add: tendsto_at_top_eq dist_norm)

lemma tendsto_at_bot_eq:
  fixes f :: "'a::linorder \<Rightarrow> 'b :: metric_space"
  shows "(f \<longlongrightarrow> L) at_bot \<longleftrightarrow> (\<forall>e>0. \<exists>N. \<forall>n\<le>N. dist (f n) L < e)"
  by (simp add: tendsto_iff eventually_at_bot_linorder)

corollary tendsto_at_bot_epsilon_def:
  "(f \<longlongrightarrow> L) at_bot = (\<forall> \<epsilon> > 0. \<exists>N. \<forall>x \<le> N. \<bar>(f (x::real)::real) - L\<bar> < \<epsilon>)"
  by (simp add: tendsto_at_bot_eq dist_norm)


subsubsection \<open> Divergence \<close>

lemma tendsto_at_top_inf_eq:
  fixes f :: "'a::linorder \<Rightarrow> ereal"
  shows "(f \<longlongrightarrow> \<infinity>) at_top \<longleftrightarrow> (\<forall>r. \<exists>N. \<forall>n\<ge>N. ereal r < f n)"
  by (simp add: tendsto_PInfty eventually_at_top_linorder)

corollary tendsto_inf_at_top_epsilon_def:
  "(g \<longlongrightarrow> \<infinity>) at_top = (\<forall> \<epsilon> > 0. \<exists>N. \<forall>x \<ge> N. (g (x::real)::real) > \<epsilon>)"
  by (auto simp add: tendsto_at_top_inf_eq)
    (metis gt_ex linorder_not_le order.strict_trans order.strict_trans2)

lemma tendsto_at_bot_inf_eq:
  fixes f :: "'a::linorder \<Rightarrow> ereal"
  shows "(f \<longlongrightarrow> \<infinity>) at_bot \<longleftrightarrow> (\<forall>r. \<exists>N. \<forall>n\<le>N. ereal r < f n)"
  by (simp add: tendsto_PInfty eventually_at_bot_linorder)

corollary tendsto_inf_at_bot_epsilon_def:
  "(g \<longlongrightarrow> \<infinity>) at_bot = (\<forall> \<epsilon> > 0. \<exists>N. \<forall>x \<le> N. (g (x::real)::real) > \<epsilon>)"
  by (auto simp add: tendsto_at_bot_inf_eq)
    (metis gt_ex linorder_not_le order.strict_trans order.strict_trans2)

lemma tendsto_at_top_minus_inf_eq:
  fixes f :: "'a::linorder \<Rightarrow> ereal"
  shows "(f \<longlongrightarrow> - \<infinity>) at_top \<longleftrightarrow> (\<forall>r. \<exists>N. \<forall>n\<ge>N. f n < ereal r)"
  by (simp add: tendsto_MInfty eventually_at_top_linorder)

corollary tendsto_minus_inf_at_top_epsilon_def:
  "(g \<longlongrightarrow> -\<infinity>) at_top = (\<forall> \<epsilon> < 0. \<exists>N. \<forall>x \<ge> N. (g (x::real)::real) < \<epsilon>)"
  by (auto simp add: tendsto_at_top_minus_inf_eq)
    (metis linorder_not_less lt_ex order.strict_trans order.strict_trans1)

lemma tendsto_at_bot_minus_inf_eq:
  fixes f :: "'a::linorder \<Rightarrow> ereal"
  shows "(f \<longlongrightarrow> - \<infinity>) at_bot \<longleftrightarrow> (\<forall>r. \<exists>N. \<forall>n\<le>N. f n < ereal r)"
  by (simp add: tendsto_MInfty eventually_at_bot_linorder)

corollary tendsto_minus_inf_at_bot_epsilon_def:
  "(g \<longlongrightarrow> -\<infinity>) at_bot = (\<forall> \<epsilon> < 0. \<exists>N. \<forall>x \<le> N. (g (x::real)::real) < \<epsilon>)"
  by (auto simp add: tendsto_at_bot_minus_inf_eq)
    (metis linorder_not_less lt_ex order.strict_trans order.strict_trans1)


subsubsection \<open> Continuity and Arithmetic \<close>

lemmas tendsto_at_eq = LIM_def

corollary tendsto_at_x_epsilon_def:
  fixes f :: "real \<Rightarrow> real" and L :: real and x :: real
  shows "(f \<longlongrightarrow> L) (at x) = (\<forall>\<epsilon> > 0. \<exists>\<delta> > 0. \<forall>y. (y \<noteq> x \<and> \<bar>y - x\<bar> < \<delta>) \<longrightarrow> \<bar>f y - L\<bar> < \<epsilon>)"
  by (simp add: tendsto_at_eq dist_norm)

corollary continuous_at_eps_delta:
  fixes g :: "real \<Rightarrow> real" and y :: real
  shows "continuous (at y) g = (\<forall>\<epsilon> > 0. \<exists>\<delta> > 0. \<forall>x. \<bar>x - y\<bar> < \<delta> \<longrightarrow> \<bar>g x - g y\<bar> < \<epsilon>)"
  by (clarsimp simp add: continuous_def tendsto_at_eq dist_norm)
    (metis abs_0 diff_self)

corollary tendsto_divide_approaches_const:
  fixes f g :: "real \<Rightarrow> real"
  assumes f_lim:"((\<lambda>x. f (x::real)) \<longlongrightarrow> c) at_top"
      and g_lim: "((\<lambda>x. g (x::real)) \<longlongrightarrow> \<infinity>) at_top"
    shows "((\<lambda>x. f (x::real) / g x) \<longlongrightarrow> 0) at_top"
  using assms real_tendsto_divide_at_top tendsto_PInfty_eq_at_top 
  by blast

corollary tendsto_divide_approaches_const_at_bot:
  fixes f g :: "real \<Rightarrow> real"
  assumes f_lim: "((\<lambda>x. f (x::real)) \<longlongrightarrow> c) at_bot"
      and g_lim: "((\<lambda>x. g (x::real)) \<longlongrightarrow> \<infinity>) at_bot"
    shows "((\<lambda>x. f (x::real) / g x) \<longlongrightarrow> 0) at_bot"
  using assms real_tendsto_divide_at_top tendsto_PInfty_eq_at_top 
  by blast

lemma equal_limits_diff_zero_at_top:
  assumes f_lim: "(f \<longlongrightarrow> (L1::real)) at_top"
  assumes g_lim: "(g \<longlongrightarrow> (L2::real)) at_top"
  shows "((f - g) \<longlongrightarrow> (L1 - L2)) at_top"
  by (simp add: f_lim fun_diff_def g_lim tendsto_diff)

lemma equal_limits_diff_zero_at_bot:
  assumes f_lim: "(f \<longlongrightarrow> (L1::real)) at_bot"
  assumes g_lim: "(g \<longlongrightarrow> (L2::real)) at_bot"
  shows "((f - g) \<longlongrightarrow> (L1 - L2)) at_bot"
  by (simp add: f_lim fun_diff_def g_lim tendsto_diff)


subsubsection \<open> One-Sided Limits\<close>

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

lemma tendsto_within_left_interval_imp_left_limit:
  fixes f  :: "real \<Rightarrow> real"   
    and x0 :: real
    and \<delta>  :: real
    and L  :: real
  assumes \<delta>_pos: "\<delta> > 0"
      and lim_int: "(f \<longlongrightarrow> L) (at x0 within {x0 - \<delta><..<x0})"
    shows  "(f \<longlongrightarrow> L) (at_left x0)"
proof(subst tendsto_at_left_x_epsilon_def, intro allI impI)
  fix \<epsilon> :: real
  assume \<epsilon>_pos: "\<epsilon> > 0"

  from lim_int \<epsilon>_pos
  have ev: "eventually (\<lambda>y. \<bar>f y - L\<bar> < \<epsilon>)
                  (at x0 within {x0 - \<delta><..<x0})"
    by (metis LIM_zero order_tendstoD(2) tendsto_rabs_zero)

  with lim_int \<epsilon>_pos
  obtain d1 where d1_pos: "d1 > 0"
    and d1_prop:
      "\<forall>y. 0 < \<bar>y - x0\<bar> \<and> \<bar>y - x0\<bar> < d1 \<and> y \<in> {x0 - \<delta><..<x0}
           \<longrightarrow> \<bar>f y - L\<bar> < \<epsilon>"
    unfolding eventually_at
    by (metis dist_real_def zero_less_dist_iff)

  define d where "d = min \<delta> d1"
  then have d_pos: "d > 0"
    using \<delta>_pos d1_pos by simp
  thus "\<exists>d>0. \<forall>y. y < x0 \<and> x0 - y < d \<longrightarrow> \<bar>f y - L\<bar> < \<epsilon>"
    using d1_prop d_def by(intro exI[of _d], simp)
qed

lemma tendsto_within_right_interval_imp_right_limit:
  fixes f  :: "real \<Rightarrow> real"
    and x0 \<delta> L :: real
  assumes \<delta>_pos : "\<delta> > 0"
      and lim_int: "(f \<longlongrightarrow> L) (at x0 within {x0<..<x0 + \<delta>})"
  shows  "(f \<longlongrightarrow> L) (at_right x0)"
proof (subst tendsto_at_right_x_epsilon_def, intro allI impI)   
  fix \<epsilon> :: real
  assume \<epsilon>_pos: "\<epsilon> > 0"

  from lim_int \<epsilon>_pos
  have ev: "eventually (\<lambda>y. \<bar>f y - L\<bar> < \<epsilon>)
                   (at x0 within {x0<..<x0 + \<delta>})"
    by (metis LIM_zero order_tendstoD(2) tendsto_rabs_zero)

  from ev obtain d1 where d1_pos: "d1 > 0"
    and d1_prop:
      "\<forall>y. y \<in> {x0<..<x0 + \<delta>} \<and> 0 < \<bar>y - x0\<bar> \<and> \<bar>y - x0\<bar> < d1
           \<longrightarrow> \<bar>f y - L\<bar> < \<epsilon>"
    unfolding eventually_at by (metis dist_real_def zero_less_dist_iff)

  define d where "d = min \<delta> d1"
  have d_pos: "d > 0"
    using \<delta>_pos d1_pos by (simp add: d_def)  
  thus "\<exists>\<delta>>0. \<forall>y. x0 < y \<and> y - x0 < \<delta> \<longrightarrow> \<bar>f y - L\<bar> < \<epsilon>"
    using d1_prop d_def by(intro exI[of _d], simp)
qed

end
