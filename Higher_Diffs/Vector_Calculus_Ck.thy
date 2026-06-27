section \<open>Vector calculus under \<open>C\<^sup>k\<close> hypotheses\<close>

theory Vector_Calculus_Ck
  imports Vector_Calculus Ck_Differentiable
begin

text \<open>
  Differentiability of \<open>f :: real\<^sup>n \<Rightarrow> real\<close> implies the gradient exists.
  This connects @{const k_times_Fr_differentiable_at} at level 1 to the
  gradient.
\<close>


lemma Ck_2_imp_gradient_exists:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes "Ck_on 2 f U" and "x \<in> U"
  shows "\<exists>g. GRAD f x :> g"
proof -
  from assms have "Ck_at 2 f x"
    by (simp add: Ck_on_def)
  then have "f differentiable (at x)"
    by (metis Ck_at.simps(2) Suc_1)
  then show ?thesis
    by (rule Fr_diff_imp_gradient_exists)
qed


lemma Ck_2_imp_hessian_exists:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes "Ck_on 2 f U" and "x \<in> U"
  shows "HESS f x :> \<nabla>\<^sup>2 f x"
proof -
  from assms have C2: "Ck_at 2 f x"
    by (simp add: Ck_on_def)

  then obtain A where
    A: "open A" "x \<in> A" "\<forall>y\<in>A. Ck_at 1 f y"
    and diffx: "f differentiable (at x)"
    and D: "\<forall>v. Ck_at 1 (\<lambda>y. frechet_derivative f (at y) v) x"
    by (metis Ck_at.simps(2) Suc_1)

  let ?H = "(\<chi> i. \<nabla> (\<lambda>y. \<nabla> f y $ i) x)"

  have H_wit: "HESS f x :> ?H"
  proof (unfold has_hessian_def)
    have comp: "\<forall>i\<in>Basis. ((\<lambda>y. \<nabla> f y \<bullet> i) has_derivative (\<lambda>v. ((*v) ?H) v \<bullet> i)) (at x)"
    proof clarify
      fix b :: "real^'n"
      assume b: "b \<in> Basis"
      then obtain i where i: "b = axis i 1"
        by (auto simp: Basis_vec_def)

      let ?Fi = "(\<lambda>y. frechet_derivative f (at y) (axis i 1))"
      let ?Gi = "(\<lambda>y. \<nabla> f y $ i)"

      have Fi_C1: "Ck_at 1 ?Fi x"
        using D by blast
      hence Fi_diff: "?Fi differentiable (at x)"
        by simp

      have eqA: "\<And>y. y \<in> A \<Longrightarrow> ?Fi y = ?Gi y"
        by (metis (lifting) A(3) Ck_at.simps(2) Fr_diff_imp_gradient_exists Suc_eq_plus1 add_0 
            frechet_derivative_at grad_fun_eq has_gradient_def inner_axis' inner_real_def lambda_one)

    
      have ev_eq: "eventually (\<lambda>y. ?Fi y = ?Gi y) (nhds x)"
      proof -
        have "\<exists>S. open S \<and> x \<in> S \<and> (\<forall>y\<in>S. ?Fi y = ?Gi y)"
          using A eqA by blast
        then show ?thesis
          by (simp add: eventually_nhds)
      qed

      have Gi_diff: "?Gi differentiable (at x)"
        by (metis (no_types, lifting) A(1,2) Fi_diff differentiable_eqI eqA)
     

      from Fr_diff_imp_gradient_exists[OF Gi_diff]
      obtain gi where gi: "GRAD ?Gi x :> gi"
        by blast

      have gradGi: "GRAD ?Gi x :> \<nabla> ?Gi x"
        using gi by (rule grad_fun_satisfies_GRAD)

      have dGi: "(?Gi has_derivative (\<lambda>v. v \<bullet> (?H $ i))) (at x)"
        using gradGi unfolding has_gradient_def by simp

      have "((\<lambda>y. \<nabla> f y \<bullet> b) has_derivative (\<lambda>v. ((*v) ?H) v \<bullet> b)) (at x)"
        by (metis (no_types, lifting) ext cart_eq_inner_axis dGi i 
            inner_commute matrix_vector_mul_component)
      then show "((\<lambda>y. \<nabla> f y \<bullet> b) has_derivative (\<lambda>v. ((*v) ?H) v \<bullet> b)) (at x)".
    qed

    then show "(\<nabla> f has_derivative (*v) ?H) (at x)"
      using has_derivative_componentwise_within by blast    
  qed
  show ?thesis
    using H_wit hess_fun_eq by fastforce
qed


lemma Ck_2_imp_hessian_continuous:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes "Ck_on 2 f U"
  shows "continuous_on U (\<nabla>\<^sup>2 f)"
proof -
  have openU: "open U"
    using assms by (simp add: Ck_on_def)

  have comp_cont: "\<And>x i j. x \<in> U \<Longrightarrow> continuous (at x) (\<lambda>y. \<nabla>\<^sup>2 f y $ i $ j)"
  proof -
    fix x i j
    assume xU: "x \<in> U"

    from assms xU have C2x: "Ck_at 2 f x"
      by (simp add: Ck_on_def)

    from C2x obtain A where
      A: "open A" "x \<in> A" "\<forall>y\<in>A. Ck_at 1 f y"
      and diffx: "f differentiable (at x)"
      and Dx: "\<forall>v. Ck_at 1 (\<lambda>y. frechet_derivative f (at y) v) x"
      by (metis Ck_at.simps(2) Suc_1)

    let ?Fi = "(\<lambda>y. frechet_derivative f (at y) (axis i 1))"
    let ?K  = "(\<lambda>y. frechet_derivative ?Fi (at y) (axis j 1))"
    let ?Hc = "(\<lambda>y. \<nabla>\<^sup>2 f y $ i $ j)"

    have Fi_C1: "Ck_at 1 ?Fi x"
      using Dx by simp

    have K_cont: "continuous (at x) ?K"
      using Fi_C1 by simp

    have eq_on_U: "\<And>y. y \<in> U \<Longrightarrow> frechet_derivative ?Fi (at y) (axis j 1) = \<nabla>\<^sup>2 f y $ i $ j"
    proof -
      fix y
      assume yU: "y \<in> U"

      from assms yU have C2y: "Ck_at 2 f y"
        by (simp add: Ck_on_def)

      have dy: "f differentiable (at y)"
        by (metis C2y Ck_at.simps(2) Suc_1)

      have Fi_C1_y: "Ck_at 1 ?Fi y"
        using C2y by (metis Ck_at.simps(2) Suc_1)

      have Fi_diff_y: "?Fi differentiable (at y)"
        using Fi_C1_y by simp

      let ?Gi = "(\<lambda>z. \<nabla> f z $ i)"

      have FG_eq_on_U: "\<And>z. z \<in> U \<Longrightarrow> ?Fi z = ?Gi z"
      proof -
        fix z
        assume zU: "z \<in> U"

        from assms zU have C2z: "Ck_at 2 f z"
          by (simp add: Ck_on_def)

        have dz: "f differentiable (at z)"
          by (metis C2z Ck_at.simps(2) Suc_1)

        from Fr_diff_imp_gradient_exists[OF dz]
        obtain g where g: "GRAD f z :> g"
          by blast
        have g_eq: "\<nabla> f z = g"
          using g by (rule grad_fun_eq)
        have "(f has_derivative (\<lambda>v. v \<bullet> g)) (at z)"
          using g unfolding has_gradient_def by simp
        hence fd_eq: "frechet_derivative f (at z) = (\<lambda>v. v \<bullet> g)"
          by (metis frechet_derivative_at)
        show "?Fi z = ?Gi z"
          by (simp add: fd_eq g_eq inner_axis')
      qed

      have ev_FG: "eventually (\<lambda>z. ?Fi z = ?Gi z) (nhds y)"
        using FG_eq_on_U eventually_nhds openU yU by blast
      

      have Gi_diff_y: "?Gi differentiable (at y)"
        by (metis (no_types, lifting) FG_eq_on_U Fi_diff_y differentiable_eqI openU yU)
     

      then have fd_Fi_Gi: "frechet_derivative ?Fi (at y) = frechet_derivative ?Gi (at y)"
        by (smt (verit, best) FG_eq_on_U frechet_derivative_transform_within_open openU yU)     

      from Fr_diff_imp_gradient_exists[OF Gi_diff_y]
      obtain gi where gi: "GRAD ?Gi y :> gi"
        by blast

      have gi_eq: "\<nabla> ?Gi y = gi"
        using gi by (rule grad_fun_eq)

      have "(?Gi has_derivative (\<lambda>v. v \<bullet> gi)) (at y)"
        using gi unfolding has_gradient_def by simp
      hence fd_Gi: "frechet_derivative ?Gi (at y) = (\<lambda>v. v \<bullet> gi)"
        by (metis frechet_derivative_at)

      have fd_Gi_axis: "frechet_derivative ?Gi (at y) (axis j 1) = \<nabla> ?Gi y $ j"
        by (metis cart_eq_inner_axis fd_Gi gi_eq inner_commute)
      have Hess_y: "HESS f y :> \<nabla>\<^sup>2 f y"
        using assms yU by (rule Ck_2_imp_hessian_exists)

      have hess_eq: "\<nabla>\<^sup>2 f y $ i $ j = \<nabla> ?Gi y $ j"
        using hessian_eq_double_nabla[OF Hess_y] by simp

      show "frechet_derivative ?Fi (at y) (axis j 1) = \<nabla>\<^sup>2 f y $ i $ j"
        using fd_Fi_Gi fd_Gi_axis hess_eq by simp
    qed
    have ev_eq: "eventually (\<lambda>y. ?K y = ?Hc y) (nhds x)"
      using eq_on_U eventually_nhds openU xU by blast   
    show "continuous (at x) ?Hc"
      using K_cont ev_eq isCont_cong by fastforce 
  qed

  show ?thesis
    unfolding continuous_on
  proof
    fix x
    assume xU: "x \<in> U"

    have isCont_H: "isCont (\<lambda>y. \<chi> i. \<chi> j. \<nabla>\<^sup>2 f y $ i $ j) x"
      unfolding isCont_def
    proof (rule tendsto_vec_lambda)
      fix i
      show "((\<lambda>y. \<chi> j. \<nabla>\<^sup>2 f y $ i $ j) \<longlongrightarrow> (\<chi> j. \<nabla>\<^sup>2 f x $ i $ j)) (at x)"
      proof (rule tendsto_vec_lambda)
        fix j
        from comp_cont[OF xU, of i j]
        show "((\<lambda>y. \<nabla>\<^sup>2 f y $ i $ j) \<longlongrightarrow> \<nabla>\<^sup>2 f x $ i $ j) (at x)"
          unfolding isCont_def by simp
      qed
    qed
    then have "continuous (at x) (\<nabla>\<^sup>2 f)"
      by simp
    then show "(\<nabla>\<^sup>2 f \<longlongrightarrow> \<nabla>\<^sup>2 f x) (at x within U)"
      by (metis at_within_open continuous_within openU xU)
  qed
qed


(* ================================================================== *)
subsection \<open>Clairaut's theorem (Symmetry of mixed partials)\<close>
(* ================================================================== *)

text \<open>
  If \<open>f :: real\<^sup>n \<Rightarrow> real\<close> is \<open>C\<^sup>2\<close> on an open set \<open>U\<close>, then its Hessian
  is symmetric at every point of \<open>U\<close>.

  The hypothesis uses the general \<open>Ck_on\<close>, which subsumes both the
  1-d \<open>C_k_on\<close> and the ad-hoc \<open>C2_on_vec\<close>.
\<close>


lemma mixed_coordinate_second_derivative_eq:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes openU: "open U"
      and xU: "x \<in> U"
      and C2: "Ck_on 2 f U"
  shows "(\<nabla> (\<lambda>y. \<nabla> f y $ i)) x $ j = (\<nabla> (\<lambda>y. \<nabla> f y $ j)) x $ i"
proof -
  (* ---------- 0.  Notation ---------- *)
  let ?ei = "axis i 1 :: real^'n"
  let ?ej = "axis j 1 :: real^'n"

  (* ---------- 1.  Work inside a ball ---------- *)
  obtain r where r_pos: "r > 0" and rU: "ball x r \<subseteq> U"
    using openU xU by (meson open_contains_ball)

  define \<delta> where "\<delta> = r / 4"
  have \<delta>_pos: "\<delta> > 0" using r_pos by (simp add: \<delta>_def)

  (* Any point x + s\<sqdot>eᵢ + t\<sqdot>eⱼ with |s|,|t| < \<delta> lies in U. *)
  have inU: "\<lbrakk> \<bar>s\<bar> < \<delta>; \<bar>t\<bar> < \<delta> \<rbrakk> \<Longrightarrow> x + s *\<^sub>R ?ei + t *\<^sub>R ?ej \<in> U" for s t
  proof -
    assume s_bd: "\<bar>s\<bar> < \<delta>" and t_bd: "\<bar>t\<bar> < \<delta>"
    have "norm (s *\<^sub>R ?ei + t *\<^sub>R ?ej) \<le> \<bar>s\<bar> + \<bar>t\<bar>"
      by (simp add: norm_triangle_le)
    also have "\<dots> < \<delta> + \<delta>" using s_bd t_bd by linarith
    also have "\<dots> = r / 2" by (simp add: \<delta>_def)
    also have "\<dots> < r" using r_pos by linarith
    finally show "x + s *\<^sub>R ?ei + t *\<^sub>R ?ej \<in> U"
      by (metis (no_types, lifting) add.assoc basic_trans_rules(31) 
          dist_0_norm dist_add_cancel group_cancel.rule0 mem_ball rU)      
  qed

  (* ---------- 2.  Names for partial derivatives ---------- *)
  (* Ps(s,t) = \<partial>ᵢf at x + s\<sqdot>eᵢ + t\<sqdot>eⱼ *)
  define Ps where "Ps s t = \<nabla> f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej) $ i" for s t
  (* Qt(s,t) = \<partial>ⱼf at x + s\<sqdot>eᵢ + t\<sqdot>eⱼ *)
  define Qt where "Qt s t = \<nabla> f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej) $ j" for s t

  (* ---------- 3.  Basic differentiability facts ---------- *)
  have diff_at: "f differentiable (at z)" if "z \<in> U" for z
    by (metis Ck_at.simps(2) Ck_on_def Suc_1 C2 that)

  have grad_exists: "GRAD f z :> \<nabla> f z" if "z \<in> U" for z
    using Fr_diff_imp_gradient_exists[OF diff_at[OF that]]
      grad_fun_satisfies_GRAD by blast

  have Hess_exists: "HESS f z :> \<nabla>\<^sup>2 f z" if "z \<in> U" for z
    using C2 that by (rule Ck_2_imp_hessian_exists)

  have hcont: "continuous_on U (\<nabla>\<^sup>2 f)"
    using C2 by (rule Ck_2_imp_hessian_continuous)

  (* ---------- 4.  Row-gradient lemma ---------- *)
  (* GRAD (\<lambda>y. \<nabla> f y $ k) z :> (\<nabla>²f z) $ k  for z \<in> U *)
  have row_grad: "GRAD (\<lambda>y. \<nabla> f y $ k) z :> (\<nabla>\<^sup>2 f z) $ k"
    if zU: "z \<in> U" for z k
  proof -
    have H: "(\<nabla> f has_derivative (*v) (\<nabla>\<^sup>2 f z)) (at z)"
      using Hess_exists[OF zU] unfolding has_hessian_def .
    have "((\<lambda>y. \<nabla> f y \<bullet> axis k 1) has_derivative
         (\<lambda>v. ((*v) (\<nabla>\<^sup>2 f z)) v \<bullet> axis k 1)) (at z within UNIV)"
      using H by (subst (asm) has_derivative_componentwise_within[where S = UNIV],
                  auto simp: Basis_vec_def)
    thus ?thesis
      unfolding has_gradient_def 
      by (simp add: inner_axis' inner_commute matrix_vector_mul_component)
  qed

  (* ---------- 5.  Derivatives of the slice maps ---------- *)
  (* \<partial>/\<partial>s [Ps(s,t)] = (\<nabla>²f)$i$i  and  \<partial>/\<partial>t [Ps(s,t)] = (\<nabla>²f)$i$j *)

  have Ps_has_deriv_t:
    "((\<lambda>t'. Ps s t') has_real_derivative (\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ i $ j)
       (at t)"
    if s_bd: "\<bar>s\<bar> < \<delta>" and t_bd: "\<bar>t\<bar> < \<delta>" for s t
  proof -
    let ?z = "x + s *\<^sub>R ?ei + t *\<^sub>R ?ej"
    have zU: "?z \<in> U" using inU[OF s_bd t_bd] .
    have rg: "GRAD (\<lambda>y. \<nabla> f y $ i) ?z :> (\<nabla>\<^sup>2 f ?z) $ i"
      by (rule row_grad[OF zU])
    have fd: "((\<lambda>y. \<nabla> f y $ i) has_derivative (\<lambda>v. v \<bullet> ((\<nabla>\<^sup>2 f ?z) $ i))) (at ?z)"
      using rg unfolding has_gradient_def .
    have lin: "((\<lambda>t'. x + s *\<^sub>R ?ei + t' *\<^sub>R ?ej) has_derivative (\<lambda>dt. dt *\<^sub>R ?ej)) (at t)"
      by (intro derivative_eq_intros) auto
    have chain:
      "((\<lambda>t'. \<nabla> f (x + s *\<^sub>R ?ei + t' *\<^sub>R ?ej) $ i) has_derivative
         (\<lambda>dt. (dt *\<^sub>R ?ej) \<bullet> ((\<nabla>\<^sup>2 f ?z) $ i))) (at t)"
      using has_derivative_compose[OF lin fd] by (simp add: o_def)
    have "(\<lambda>dt. (dt *\<^sub>R ?ej) \<bullet> ((\<nabla>\<^sup>2 f ?z) $ i))
        = (\<lambda>dt. dt * ((\<nabla>\<^sup>2 f ?z) $ i $ j))"
      by (rule ext, simp add: inner_axis' mult.commute)
    thus ?thesis
      using chain unfolding Ps_def has_field_derivative_def
      by (simp add: mult_commute_abs)
  qed

  have Qt_has_deriv_s:
    "((\<lambda>s'. Qt s' t) has_real_derivative (\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ j $ i)
       (at s)"
    if s_bd: "\<bar>s\<bar> < \<delta>" and t_bd: "\<bar>t\<bar> < \<delta>" for s t
  proof -
    let ?z = "x + s *\<^sub>R ?ei + t *\<^sub>R ?ej"
    have zU: "?z \<in> U" using inU[OF s_bd t_bd] .
    have rg: "GRAD (\<lambda>y. \<nabla> f y $ j) ?z :> (\<nabla>\<^sup>2 f ?z) $ j"
      by (rule row_grad[OF zU])
    have fd: "((\<lambda>y. \<nabla> f y $ j) has_derivative (\<lambda>v. v \<bullet> ((\<nabla>\<^sup>2 f ?z) $ j))) (at ?z)"
      using rg unfolding has_gradient_def .
    have lin: "((\<lambda>s'. x + s' *\<^sub>R ?ei + t *\<^sub>R ?ej) has_derivative (\<lambda>ds. ds *\<^sub>R ?ei)) (at s)"
      by (intro derivative_eq_intros) auto
    have chain:
      "((\<lambda>s'. \<nabla> f (x + s' *\<^sub>R ?ei + t *\<^sub>R ?ej) $ j) has_derivative
         (\<lambda>ds. (ds *\<^sub>R ?ei) \<bullet> ((\<nabla>\<^sup>2 f ?z) $ j))) (at s)"
      using has_derivative_compose[OF lin fd] by (simp add: o_def)
    have "(\<lambda>ds. (ds *\<^sub>R ?ei) \<bullet> ((\<nabla>\<^sup>2 f ?z) $ j))
        = (\<lambda>ds. ds * ((\<nabla>\<^sup>2 f ?z) $ j $ i))"
      by (rule ext, simp add: inner_axis' mult.commute)
    thus ?thesis
      using chain unfolding Qt_def has_field_derivative_def
      by (metis (no_types, lifting) ext mult.commute) 
  qed

  (* Similarly for \<partial>/\<partial>s [\<Phi>(s,t)] and \<partial>/\<partial>t [\<Phi>(s,t)] *)
  have Phi_has_deriv_s: "((\<lambda>s'. f (x + s' *\<^sub>R ?ei + t *\<^sub>R ?ej)) has_real_derivative Ps s t) (at s)"
    if s_bd: "\<bar>s\<bar> < \<delta>" and t_bd: "\<bar>t\<bar> < \<delta>" for s t
  proof -
    let ?z = "x + s *\<^sub>R ?ei + t *\<^sub>R ?ej"
    have zU: "?z \<in> U" using inU[OF s_bd t_bd] .
    have fd: "(f has_derivative (\<lambda>v. v \<bullet> \<nabla> f ?z)) (at ?z)"
      using grad_exists[OF zU] unfolding has_gradient_def .
    have lin: "((\<lambda>s'. x + s' *\<^sub>R ?ei + t *\<^sub>R ?ej) has_derivative (\<lambda>ds. ds *\<^sub>R ?ei)) (at s)"
      by (intro derivative_eq_intros) auto
    have chain: "((\<lambda>s'. f (x + s' *\<^sub>R ?ei + t *\<^sub>R ?ej)) has_derivative
         (\<lambda>ds. (ds *\<^sub>R ?ei) \<bullet> \<nabla> f ?z)) (at s)"
      using has_derivative_compose[OF lin fd] by (simp add: o_def)
    have "(\<lambda>ds. (ds *\<^sub>R ?ei) \<bullet> \<nabla> f ?z) = (\<lambda>ds. ds * (\<nabla> f ?z $ i))"
      by (rule ext, simp add: inner_axis' mult.commute)
    thus ?thesis
      using chain unfolding Ps_def has_field_derivative_def
      by (metis (full_types, lifting) ext mult.commute) 
  qed

  have Phi_has_deriv_t: "((\<lambda>t'. f (x + s *\<^sub>R ?ei + t' *\<^sub>R ?ej)) has_real_derivative Qt s t) (at t)"
    if s_bd: "\<bar>s\<bar> < \<delta>" and t_bd: "\<bar>t\<bar> < \<delta>" for s t
  proof -
    let ?z = "x + s *\<^sub>R ?ei + t *\<^sub>R ?ej"
    have zU: "?z \<in> U" using inU[OF s_bd t_bd] .
    have fd: "(f has_derivative (\<lambda>v. v \<bullet> \<nabla> f ?z)) (at ?z)"
      using grad_exists[OF zU] unfolding has_gradient_def .
    have lin: "((\<lambda>t'. x + s *\<^sub>R ?ei + t' *\<^sub>R ?ej) has_derivative (\<lambda>dt. dt *\<^sub>R ?ej)) (at t)"
      by (intro derivative_eq_intros) auto
    have chain: "((\<lambda>t'. f (x + s *\<^sub>R ?ei + t' *\<^sub>R ?ej)) has_derivative
         (\<lambda>dt. (dt *\<^sub>R ?ej) \<bullet> \<nabla> f ?z)) (at t)"
      using has_derivative_compose[OF lin fd] by (simp add: o_def)
    have "(\<lambda>dt. (dt *\<^sub>R ?ej) \<bullet> \<nabla> f ?z) = (\<lambda>dt. dt * (\<nabla> f ?z $ j))"
      by (rule ext, simp add: inner_axis' mult.commute)
    thus ?thesis
      using chain unfolding Qt_def has_field_derivative_def
      by (metis (full_types, lifting) ext mult.commute) 
  qed


  (* ---------- 6.  Continuity of the relevant Hessian entries ---------- *)
  

  (* For the \<epsilon>-\<delta> argument we only need: *)
  have Hij_cont_at_0:
    "\<forall>\<epsilon>>0. \<exists>\<delta>'>0. \<forall>s t. \<bar>s\<bar> < \<delta>' \<and> \<bar>t\<bar> < \<delta>' \<longrightarrow>
       \<bar>(\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ i $ j - (\<nabla>\<^sup>2 f x) $ i $ j\<bar> < \<epsilon>"
  proof -
    have cont_comp: "isCont (\<lambda>p. (\<nabla>\<^sup>2 f (x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej)) $ i $ j) (0,0)"
    proof -
      have cont_hij: "continuous_on U (\<lambda>z. (\<nabla>\<^sup>2 f z) $ i $ j)"
        using hcont by (simp add: continuous_on_component)
      have isCont_hij: "isCont (\<lambda>z. (\<nabla>\<^sup>2 f z) $ i $ j) x"
        using cont_hij openU xU continuous_on_eq_continuous_at by blast
      have isCont_slice: "isCont (\<lambda>p. x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej) (0::real, 0::real)"
        by (intro continuous_intros)
      have at_zero: "(\<lambda>p. x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej) (0::real, 0::real) = x"
        by simp
      have "isCont (\<lambda>z. (\<nabla>\<^sup>2 f z) $ i $ j)
              ((\<lambda>p. x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej) (0, 0))"
        using isCont_hij by (simp add: at_zero)
      thus ?thesis
        by (rule isCont_o2[OF isCont_slice])
    qed
    show ?thesis
    proof (intro allI impI)
      fix \<epsilon> :: real 
      assume eps: "\<epsilon> > 0"

      (* Step 1: unfold isCont to tendsto, then to eventually_at *)
      from cont_comp
      have "((\<lambda>p. (\<nabla>\<^sup>2 f (x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej)) $ i $ j) \<longlongrightarrow>
              (\<nabla>\<^sup>2 f x) $ i $ j) (at (0,0))"
        unfolding isCont_def by simp

      (* Step 2: instantiate tendsto_iff at \<epsilon> *)
      from this[unfolded tendsto_iff] eps
      have "eventually (\<lambda>p. dist ((\<nabla>\<^sup>2 f (x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej)) $ i $ j)
                                  ((\<nabla>\<^sup>2 f x) $ i $ j) < \<epsilon>) (at (0,0))"
        by simp

      (* Step 3: unfold eventually_at to get r'' with the p \<noteq> (0,0) guard *)
      then obtain r'' where r''_pos: "r'' > 0"
        and r''_bd: "\<forall>p. p \<noteq> (0::real, 0::real) \<and> dist p (0,0) < r'' \<longrightarrow>
             dist ((\<nabla>\<^sup>2 f (x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej)) $ i $ j)
                  ((\<nabla>\<^sup>2 f x) $ i $ j) < \<epsilon>"
        unfolding eventually_at by auto

      (* Step 4: extend to ALL p by case-splitting on p = (0,0) *)
      define \<delta>' where "\<delta>' = min \<delta> (r'' / 2)"
      have "\<delta>' > 0" using \<delta>_pos r''_pos by (simp add: \<delta>'_def)
      moreover have "\<forall>s t. \<bar>s\<bar> < \<delta>' \<and> \<bar>t\<bar> < \<delta>' \<longrightarrow>
        \<bar>(\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ i $ j -
         (\<nabla>\<^sup>2 f x) $ i $ j\<bar> < \<epsilon>"
      proof (intro allI impI)
        fix s t assume st: "\<bar>s\<bar> < \<delta>' \<and> \<bar>t\<bar> < \<delta>'"
        show "\<bar>(\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ i $ j -
               (\<nabla>\<^sup>2 f x) $ i $ j\<bar> < \<epsilon>"
        proof (cases "s = 0 \<and> t = 0")
          case True
          then show ?thesis using eps by simp
        next
          case False
          then have "(s, t) \<noteq> (0::real, 0::real)" by auto
          moreover have "dist (s,t) (0::real, 0::real) < r''"
          proof -
            have "dist (s,t) (0::real, 0::real) \<le> \<bar>s\<bar> + \<bar>t\<bar>"
              using sqrt_sum_squares_le_sum_abs by (simp add: dist_Pair_Pair)
            also have "\<dots> < r''" using st by (simp add: \<delta>'_def)
            finally show ?thesis.
          qed
          ultimately have "dist ((\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ i $ j)
                                ((\<nabla>\<^sup>2 f x) $ i $ j) < \<epsilon>"
            using r''_bd by auto
          thus ?thesis by (simp add: dist_real_def)
        qed
      qed
      ultimately show "\<exists>\<delta>'>0. \<forall>s t. \<bar>s\<bar> < \<delta>' \<and> \<bar>t\<bar> < \<delta>' \<longrightarrow>
        \<bar>(\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ i $ j -
         (\<nabla>\<^sup>2 f x) $ i $ j\<bar> < \<epsilon>"
        by blast
    qed
  qed

  have Hji_cont_at_0:
  "\<forall>\<epsilon>>0. \<exists>\<delta>'>0. \<forall>s t. \<bar>s\<bar> < \<delta>' \<and> \<bar>t\<bar> < \<delta>' \<longrightarrow>
     \<bar>(\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ j $ i - (\<nabla>\<^sup>2 f x) $ j $ i\<bar> < \<epsilon>"
  proof -
    have cont_comp: "isCont (\<lambda>p. (\<nabla>\<^sup>2 f (x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej)) $ j $ i) (0,0)"
    proof -
      have cont_hji: "continuous_on U (\<lambda>z. (\<nabla>\<^sup>2 f z) $ j $ i)"
        using hcont by (simp add: continuous_on_component)
      have isCont_hji: "isCont (\<lambda>z. (\<nabla>\<^sup>2 f z) $ j $ i) x"
        using cont_hji openU xU continuous_on_eq_continuous_at by blast
      have isCont_slice: "isCont (\<lambda>p. x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej) (0::real, 0::real)"
        by (intro continuous_intros)
      have at_zero: "(\<lambda>p. x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej) (0::real, 0::real) = x"
        by simp
      have "isCont (\<lambda>z. (\<nabla>\<^sup>2 f z) $ j $ i)
              ((\<lambda>p. x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej) (0, 0))"
        using isCont_hji by (simp add: at_zero)
      thus ?thesis
        by (rule isCont_o2[OF isCont_slice])
    qed
    show ?thesis
    proof (intro allI impI)
      fix \<epsilon> :: real
      assume eps: "\<epsilon> > 0"

      from cont_comp
      have "((\<lambda>p. (\<nabla>\<^sup>2 f (x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej)) $ j $ i) \<longlongrightarrow>
              (\<nabla>\<^sup>2 f x) $ j $ i) (at (0,0))"
        unfolding isCont_def by simp

      from this[unfolded tendsto_iff] eps
      have "eventually (\<lambda>p. dist ((\<nabla>\<^sup>2 f (x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej)) $ j $ i)
                                  ((\<nabla>\<^sup>2 f x) $ j $ i) < \<epsilon>) (at (0,0))"
        by simp

      then obtain r'' where r''_pos: "r'' > 0"
        and r''_bd: "\<forall>p. p \<noteq> (0::real, 0::real) \<and> dist p (0,0) < r'' \<longrightarrow>
             dist ((\<nabla>\<^sup>2 f (x + fst p *\<^sub>R ?ei + snd p *\<^sub>R ?ej)) $ j $ i)
                  ((\<nabla>\<^sup>2 f x) $ j $ i) < \<epsilon>"
        unfolding eventually_at by auto

      define \<delta>' where "\<delta>' = min \<delta> (r'' / 2)"
      have "\<delta>' > 0"
        using \<delta>_pos r''_pos by (simp add: \<delta>'_def)
      moreover have "\<forall>s t. \<bar>s\<bar> < \<delta>' \<and> \<bar>t\<bar> < \<delta>' \<longrightarrow>
        \<bar>(\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ j $ i -
         (\<nabla>\<^sup>2 f x) $ j $ i\<bar> < \<epsilon>"
      proof (intro allI impI)
        fix s t
        assume st: "\<bar>s\<bar> < \<delta>' \<and> \<bar>t\<bar> < \<delta>'"
        show "\<bar>(\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ j $ i -
               (\<nabla>\<^sup>2 f x) $ j $ i\<bar> < \<epsilon>"
        proof (cases "s = 0 \<and> t = 0")
          case True
          then show ?thesis
            using eps by simp
        next
          case False
          then have "(s, t) \<noteq> (0::real, 0::real)"
            by auto
          moreover have "dist (s,t) (0::real, 0::real) < r''"
          proof -
            have "dist (s,t) (0::real, 0::real) \<le> \<bar>s\<bar> + \<bar>t\<bar>"
              using sqrt_sum_squares_le_sum_abs by (simp add: dist_Pair_Pair)
            also have "\<dots> < r''"
              using st by (simp add: \<delta>'_def)
            finally show ?thesis .
          qed
          ultimately have "dist ((\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ j $ i)
                                ((\<nabla>\<^sup>2 f x) $ j $ i) < \<epsilon>"
            using r''_bd by auto
          thus ?thesis
            by (simp add: dist_real_def)
        qed
      qed
      ultimately show "\<exists>\<delta>'>0. \<forall>s t. \<bar>s\<bar> < \<delta>' \<and> \<bar>t\<bar> < \<delta>' \<longrightarrow>
        \<bar>(\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ j $ i -
         (\<nabla>\<^sup>2 f x) $ j $ i\<bar> < \<epsilon>"
        by blast
    qed
  qed


  (* ---------- 7.  The rectangle increment ---------- *)
  define \<Delta> where
    "\<Delta> h k = f (x + h *\<^sub>R ?ei + k *\<^sub>R ?ej)
           - f (x + h *\<^sub>R ?ei)
           - f (x + k *\<^sub>R ?ej)
           + f x" for h k

  (* ---------- 8.  MVT, direction 1: differentiate in s first, then t ---------- *)
  (*
     g(s) = f(x + s\<sqdot>eᵢ + k\<sqdot>eⱼ) - f(x + s\<sqdot>eᵢ)
     g(h) - g(0) = \<Delta>(h,k)
     By MVT: \<exists> \<xi> between 0 and h.  \<Delta>(h,k) = h \<sqdot> g'(\<xi>)
     g'(s) = Ps(s,k) - Ps(s,0)
     Then p(t) = Ps(\<xi>,t), and p(k) - p(0) = g'(\<xi>) = Ps(\<xi>,k) - Ps(\<xi>,0)
     By MVT on p: \<exists> \<eta> between 0 and k.
       Ps(\<xi>,k) - Ps(\<xi>,0) = k \<sqdot> (\<nabla>²f(x + \<xi>\<sqdot>eᵢ + \<eta>\<sqdot>eⱼ))$i$j
     So \<Delta>(h,k) = h \<sqdot> k \<sqdot> (\<nabla>²f(x + \<xi>\<sqdot>eᵢ + \<eta>\<sqdot>eⱼ))$i$j
  *)
  have dir1:
    "\<exists>\<xi> \<eta>. \<bar>\<xi>\<bar> \<le> \<bar>h\<bar> \<and> \<bar>\<eta>\<bar> \<le> \<bar>k\<bar> \<and>
            \<Delta> h k = h * k * (\<nabla>\<^sup>2 f (x + \<xi> *\<^sub>R ?ei + \<eta> *\<^sub>R ?ej)) $ i $ j"
    if h_pos: "h > 0" and k_pos: "k > 0"
       and h_bd: "h < \<delta>" and k_bd: "k < \<delta>"
    for h k
  proof -
    (* g(s) = f(x + s\<sqdot>eᵢ + k\<sqdot>eⱼ) - f(x + s\<sqdot>eᵢ) *)
    define g where "g s = f (x + s *\<^sub>R ?ei + k *\<^sub>R ?ej) - f (x + s *\<^sub>R ?ei)" for s

    have g_deriv: "(g has_real_derivative (Ps s k - Ps s 0)) (at s)"
      if "\<bar>s\<bar> < \<delta>" for s
    proof -
      have "((\<lambda>s'. f (x + s' *\<^sub>R ?ei + k *\<^sub>R ?ej)) has_real_derivative Ps s k) (at s)"
        using Phi_has_deriv_s[of s k] that k_bd k_pos by linarith 
      moreover have "((\<lambda>s'. f (x + s' *\<^sub>R ?ei + 0 *\<^sub>R ?ej)) has_real_derivative Ps s 0) (at s)"
        using Phi_has_deriv_s[of s 0] that \<delta>_pos by auto
      ultimately show ?thesis
        unfolding g_def
        by (subst derivative_eq_intros, simp_all)
    qed

    (* Apply MVT to g on [0,h] *)
    have g_deriv_on_seg: "\<And>x. 0 \<le> x \<Longrightarrow> x \<le> h \<Longrightarrow> (g has_real_derivative (Ps x k - Ps x 0)) (at x)"
    proof -
      fix x :: real
      assume x0: "0 \<le> x"
      assume xh: "x \<le> h"
      have "\<bar>x\<bar> = x"
        using x0 by simp
      also have "... \<le> h"
        using xh by simp
      also have "... < \<delta>"
        using h_bd by simp
      finally have "\<bar>x\<bar> < \<delta>" .
      thus "(g has_real_derivative (Ps x k - Ps x 0)) (at x)"
        by (rule g_deriv)
    qed
    
    have g_diff: "\<exists>\<xi>. 0 < \<xi> \<and> \<xi> < h \<and> \<Delta> h k = h * (Ps \<xi> k - Ps \<xi> 0)"
    proof -
      obtain \<xi> where \<xi>:
        "0 < \<xi>" "\<xi> < h"
        "g h - g 0 = (h - 0) * (Ps \<xi> k - Ps \<xi> 0)"
        using MVT2[of 0 h g "\<lambda>x. Ps x k - Ps x 0"]
          h_pos g_deriv_on_seg
        by blast
      have "g h - g 0 = \<Delta> h k"
        by (simp add: g_def \<Delta>_def)
      with \<xi> show ?thesis
        by auto
    qed
    then obtain \<xi> where \<xi>_pos: "0 < \<xi>" and \<xi>_lt: "\<xi> < h"
      and eq1: "\<Delta> h k = h * (Ps \<xi> k - Ps \<xi> 0)" by blast

    (* Now apply MVT to p(t) = Ps(\<xi>,t) on [0,k] *)
    define p where "p t = Ps \<xi> t" for t

    have p_deriv: "(p has_real_derivative (\<nabla>\<^sup>2 f (x + \<xi> *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ i $ j) (at t)"
      if "\<bar>t\<bar> < \<delta>" for t
      using Ps_has_deriv_t[of \<xi> t] \<xi>_lt h_bd that
      unfolding p_def
      using \<xi>_pos by argo 

    
    (* MVT application to p on [0,k] *)
    have p_deriv_on_seg: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> k \<Longrightarrow>
       (p has_real_derivative (\<nabla>\<^sup>2 f (x + \<xi> *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ i $ j) (at t)"
    proof -
      fix t :: real
      assume t0: "0 \<le> t"
      assume tk: "t \<le> k"
      have "\<bar>t\<bar> = t"
        using t0 by simp
      also have "... \<le> k"
        using tk by simp
      also have "... < \<delta>"
        using k_bd by simp
      finally have "\<bar>t\<bar> < \<delta>".
      thus "(p has_real_derivative (\<nabla>\<^sup>2 f (x + \<xi> *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ i $ j) (at t)"
        by (rule p_deriv)
    qed

    have p_diff: "\<exists>\<eta>. 0 < \<eta> \<and> \<eta> < k \<and>
        Ps \<xi> k - Ps \<xi> 0 = k * (\<nabla>\<^sup>2 f (x + \<xi> *\<^sub>R ?ei + \<eta> *\<^sub>R ?ej)) $ i $ j"
    proof -
      obtain \<eta> where \<eta>:
        "0 < \<eta>"
        "\<eta> < k"
        "p k - p 0 = (k - 0) * ((\<nabla>\<^sup>2 f (x + \<xi> *\<^sub>R ?ei + \<eta> *\<^sub>R ?ej)) $ i $ j)"
        using MVT2[of 0 k p "\<lambda>t. (\<nabla>\<^sup>2 f (x + \<xi> *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ i $ j"] k_pos p_deriv_on_seg
        by blast
      have "p k - p 0 = Ps \<xi> k - Ps \<xi> 0"
        unfolding p_def by simp
      with \<eta> show ?thesis
        by auto
    qed
    then obtain \<eta> where \<eta>_pos: "0 < \<eta>" and \<eta>_lt: "\<eta> < k"
      and eq2: "Ps \<xi> k - Ps \<xi> 0 = k * (\<nabla>\<^sup>2 f (x + \<xi> *\<^sub>R ?ei + \<eta> *\<^sub>R ?ej)) $ i $ j"
      by blast

    have "\<Delta> h k = h * (k * (\<nabla>\<^sup>2 f (x + \<xi> *\<^sub>R ?ei + \<eta> *\<^sub>R ?ej)) $ i $ j)"
      using eq1 eq2 by simp
    hence "\<Delta> h k = h * k * (\<nabla>\<^sup>2 f (x + \<xi> *\<^sub>R ?ei + \<eta> *\<^sub>R ?ej)) $ i $ j"
      by (simp add: mult.assoc)
    moreover have "\<bar>\<xi>\<bar> \<le> \<bar>h\<bar>" using \<xi>_pos \<xi>_lt h_pos by linarith
    moreover have "\<bar>\<eta>\<bar> \<le> \<bar>k\<bar>" using \<eta>_pos \<eta>_lt k_pos by linarith
    ultimately show ?thesis by blast
  qed

  (* ---------- 9.  MVT, direction 2: differentiate in t first, then s ---------- *)
  have dir2:
    "\<exists>\<xi>' \<eta>'. \<bar>\<xi>'\<bar> \<le> \<bar>h\<bar> \<and> \<bar>\<eta>'\<bar> \<le> \<bar>k\<bar> \<and>
              \<Delta> h k = h * k * (\<nabla>\<^sup>2 f (x + \<xi>' *\<^sub>R ?ei + \<eta>' *\<^sub>R ?ej)) $ j $ i"
    if h_pos: "h > 0" and k_pos: "k > 0"
       and h_bd: "h < \<delta>" and k_bd: "k < \<delta>"
    for h k
  proof -
    (* g̃(t) = f(x + h\<sqdot>eᵢ + t\<sqdot>eⱼ) - f(x + t\<sqdot>eⱼ) *)
    define g' where "g' t = f (x + h *\<^sub>R ?ei + t *\<^sub>R ?ej) - f (x + t *\<^sub>R ?ej)" for t

    have g'_deriv: "(g' has_real_derivative (Qt h t - Qt 0 t)) (at t)"
      if "\<bar>t\<bar> < \<delta>" for t
    proof -
      have "((\<lambda>t'. f (x + h *\<^sub>R ?ei + t' *\<^sub>R ?ej)) has_real_derivative Qt h t) (at t)"
        using Phi_has_deriv_t[of h t] h_bd that
        using h_pos by linarith 
      moreover have "((\<lambda>t'. f (x + 0 *\<^sub>R ?ei + t' *\<^sub>R ?ej)) has_real_derivative Qt 0 t) (at t)"
        using Phi_has_deriv_t[of 0 t] \<delta>_pos that by auto
      ultimately show ?thesis
        unfolding g'_def by (subst derivative_eq_intros, simp_all)
    qed

    (* MVT on g̃ over [0,k] *)
    have g'_diff: "\<exists>\<eta>'. 0 < \<eta>' \<and> \<eta>' < k \<and> \<Delta> h k = k * (Qt h \<eta>' - Qt 0 \<eta>')"
    proof -
      have "g' k - g' 0 = \<Delta> h k"
        by (simp add: g'_def \<Delta>_def)
      moreover have g'_deriv_on_seg:
        "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> k \<Longrightarrow> (g' has_real_derivative (Qt h t - Qt 0 t)) (at t)"
      proof -
        fix t :: real
        assume t0: "0 \<le> t"
        assume tk: "t \<le> k"
        have "\<bar>t\<bar> = t"
          using t0 by simp
        also have "... \<le> k"
          using tk by simp
        also have "... < \<delta>"
          using k_bd by simp
        finally have "\<bar>t\<bar> < \<delta>".
        thus "(g' has_real_derivative (Qt h t - Qt 0 t)) (at t)"
          by (rule g'_deriv)
      qed
      moreover obtain \<eta>' where "0 < \<eta>'" "\<eta>' < k"
        and "g' k - g' 0 = k * (Qt h \<eta>' - Qt 0 \<eta>')"
        using MVT2[of 0 k g' "\<lambda>t. Qt h t - Qt 0 t"] k_pos g'_deriv_on_seg
        by auto
      ultimately show ?thesis
        by auto
    qed

    then obtain \<eta>' where \<eta>'_pos: "0 < \<eta>'" and \<eta>'_lt: "\<eta>' < k"
      and eq1': "\<Delta> h k = k * (Qt h \<eta>' - Qt 0 \<eta>')" by blast

    (* MVT on q(s) = Qt(s, \<eta>') over [0,h] *)
    define q where "q s = Qt s \<eta>'" for s

    have q_deriv_on_seg:
      "\<And>s. 0 \<le> s \<Longrightarrow> s \<le> h \<Longrightarrow>
        (q has_real_derivative (\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + \<eta>' *\<^sub>R ?ej)) $ j $ i) (at s)"
    proof -
      fix s :: real
      assume s0: "0 \<le> s"
      assume sh: "s \<le> h"
      have "\<bar>s\<bar> = s"
        using s0 by simp
      also have "... \<le> h"
        using sh by simp
      also have "... < \<delta>"
        using h_bd by simp
      finally have "\<bar>s\<bar> < \<delta>" .
      thus "(q has_real_derivative (\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + \<eta>' *\<^sub>R ?ej)) $ j $ i) (at s)"
        using Qt_has_deriv_s \<eta>'_lt \<eta>'_pos \<open>q \<equiv> \<lambda>s. Qt s \<eta>'\<close> k_bd by fastforce
    qed

    have q_diff: "\<exists>\<xi>'. 0 < \<xi>' \<and> \<xi>' < h \<and>
        Qt h \<eta>' - Qt 0 \<eta>' = h * (\<nabla>\<^sup>2 f (x + \<xi>' *\<^sub>R ?ei + \<eta>' *\<^sub>R ?ej)) $ j $ i"
    proof -
      obtain \<xi>' where \<xi>':
        "0 < \<xi>'"
        "\<xi>' < h"
        "q h - q 0 = (h - 0) * ((\<nabla>\<^sup>2 f (x + \<xi>' *\<^sub>R ?ei + \<eta>' *\<^sub>R ?ej)) $ j $ i)"
        using MVT2[of 0 h q "\<lambda>s. (\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + \<eta>' *\<^sub>R ?ej)) $ j $ i"] h_pos q_deriv_on_seg
        by blast
      have "q h - q 0 = Qt h \<eta>' - Qt 0 \<eta>'"
        unfolding q_def by simp
      with \<xi>' show ?thesis
        by auto
    qed
    then obtain \<xi>' where \<xi>'_pos: "0 < \<xi>'" and \<xi>'_lt: "\<xi>' < h"
      and eq2': "Qt h \<eta>' - Qt 0 \<eta>' = h * (\<nabla>\<^sup>2 f (x + \<xi>' *\<^sub>R ?ei + \<eta>' *\<^sub>R ?ej)) $ j $ i"
      by blast

    have "\<Delta> h k = k * (h * (\<nabla>\<^sup>2 f (x + \<xi>' *\<^sub>R ?ei + \<eta>' *\<^sub>R ?ej)) $ j $ i)"
      using eq1' eq2' by simp
    hence "\<Delta> h k = h * k * (\<nabla>\<^sup>2 f (x + \<xi>' *\<^sub>R ?ei + \<eta>' *\<^sub>R ?ej)) $ j $ i"
      by (simp add: mult.commute mult.assoc)
    moreover have "\<bar>\<xi>'\<bar> \<le> \<bar>h\<bar>" using \<xi>'_pos \<xi>'_lt h_pos by linarith
    moreover have "\<bar>\<eta>'\<bar> \<le> \<bar>k\<bar>" using \<eta>'_pos \<eta>'_lt k_pos by linarith
    ultimately show ?thesis by blast
  qed

  (* ---------- 10.  Combine: equality of Hessian entries ---------- *)
  have "(\<nabla>\<^sup>2 f x) $ i $ j = (\<nabla>\<^sup>2 f x) $ j $ i"
  proof (rule ccontr)
    assume neq: "(\<nabla>\<^sup>2 f x) $ i $ j \<noteq> (\<nabla>\<^sup>2 f x) $ j $ i"

    define \<epsilon> where "\<epsilon> = \<bar>(\<nabla>\<^sup>2 f x) $ i $ j - (\<nabla>\<^sup>2 f x) $ j $ i\<bar> / 3"
    then have \<epsilon>_pos: "\<epsilon> > 0" using neq by simp

    (* By continuity, get \<delta>\<^sub>1 for the (i,j) entry and \<delta>\<^sub>2 for the (j,i) entry *)
    obtain \<delta>\<^sub>1 where \<delta>\<^sub>1_pos: "\<delta>\<^sub>1 > 0"
      and \<delta>\<^sub>1_bd: "\<forall>s t. \<bar>s\<bar> < \<delta>\<^sub>1 \<and> \<bar>t\<bar> < \<delta>\<^sub>1 \<longrightarrow>
        \<bar>(\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ i $ j - (\<nabla>\<^sup>2 f x) $ i $ j\<bar> < \<epsilon>"
      using Hij_cont_at_0 \<epsilon>_pos by blast

    obtain \<delta>\<^sub>2 where \<delta>\<^sub>2_pos: "\<delta>\<^sub>2 > 0"
      and \<delta>\<^sub>2_bd: "\<forall>s t. \<bar>s\<bar> < \<delta>\<^sub>2 \<and> \<bar>t\<bar> < \<delta>\<^sub>2 \<longrightarrow>
        \<bar>(\<nabla>\<^sup>2 f (x + s *\<^sub>R ?ei + t *\<^sub>R ?ej)) $ j $ i - (\<nabla>\<^sup>2 f x) $ j $ i\<bar> < \<epsilon>"
      using Hji_cont_at_0 \<epsilon>_pos by blast

    define \<delta>\<^sub>3 where "\<delta>\<^sub>3 = min \<delta> (min \<delta>\<^sub>1 \<delta>\<^sub>2)"
    have \<delta>\<^sub>3_pos: "\<delta>\<^sub>3 > 0" using \<delta>_pos \<delta>\<^sub>1_pos \<delta>\<^sub>2_pos by (simp add: \<delta>\<^sub>3_def)

    (* Pick concrete h, k *)
    define h where "h = \<delta>\<^sub>3 / 2"
    define k where "k = \<delta>\<^sub>3 / 2"
    have h_pos: "h > 0" and k_pos: "k > 0"
      using \<delta>\<^sub>3_pos by (simp_all add: h_def k_def)
    have h_bd: "h < \<delta>" and k_bd: "k < \<delta>"
      using \<delta>\<^sub>3_pos by (simp_all add: h_def k_def \<delta>\<^sub>3_def, auto)

    (* Apply dir1 and dir2 *)
    obtain \<xi> \<eta> where \<xi>_bd: "\<bar>\<xi>\<bar> \<le> h" and \<eta>_bd: "\<bar>\<eta>\<bar> \<le> k"
      and eq_ij: "\<Delta> h k = h * k * (\<nabla>\<^sup>2 f (x + \<xi> *\<^sub>R ?ei + \<eta> *\<^sub>R ?ej)) $ i $ j"
      using dir1[OF h_pos k_pos h_bd k_bd] h_pos k_pos by auto

    obtain \<xi>' \<eta>' where \<xi>'_bd: "\<bar>\<xi>'\<bar> \<le> h" and \<eta>'_bd: "\<bar>\<eta>'\<bar> \<le> k"
      and eq_ji: "\<Delta> h k = h * k * (\<nabla>\<^sup>2 f (x + \<xi>' *\<^sub>R ?ei + \<eta>' *\<^sub>R ?ej)) $ j $ i"
      using dir2[OF h_pos k_pos h_bd k_bd] h_pos k_pos by auto

    (* Both \<xi>,\<eta> and \<xi>',\<eta>' are within \<delta>\<^sub>1 and \<delta>\<^sub>2 bounds *)
    have "\<bar>\<xi>\<bar> < \<delta>\<^sub>1" and "\<bar>\<eta>\<bar> < \<delta>\<^sub>1"
      using \<xi>_bd \<eta>_bd \<delta>\<^sub>3_pos by (simp_all add: h_def k_def \<delta>\<^sub>3_def)
    hence close_ij:
      "\<bar>(\<nabla>\<^sup>2 f (x + \<xi> *\<^sub>R ?ei + \<eta> *\<^sub>R ?ej)) $ i $ j - (\<nabla>\<^sup>2 f x) $ i $ j\<bar> < \<epsilon>"
      using \<delta>\<^sub>1_bd by blast

    have "\<bar>\<xi>'\<bar> < \<delta>\<^sub>2" and "\<bar>\<eta>'\<bar> < \<delta>\<^sub>2"
      using \<xi>'_bd \<eta>'_bd \<delta>\<^sub>3_pos by (simp_all add: h_def k_def \<delta>\<^sub>3_def)
    hence close_ji:
      "\<bar>(\<nabla>\<^sup>2 f (x + \<xi>' *\<^sub>R ?ei + \<eta>' *\<^sub>R ?ej)) $ j $ i - (\<nabla>\<^sup>2 f x) $ j $ i\<bar> < \<epsilon>"
      using \<delta>\<^sub>2_bd by blast

    (* From eq_ij and eq_ji, since h*k > 0 we can cancel: *)
    have "(\<nabla>\<^sup>2 f (x + \<xi> *\<^sub>R ?ei + \<eta> *\<^sub>R ?ej)) $ i $ j =
          (\<nabla>\<^sup>2 f (x + \<xi>' *\<^sub>R ?ei + \<eta>' *\<^sub>R ?ej)) $ j $ i"
      using eq_ij eq_ji h_pos k_pos by simp

    (* Triangle inequality gives contradiction *)
    hence "\<bar>(\<nabla>\<^sup>2 f x) $ i $ j - (\<nabla>\<^sup>2 f x) $ j $ i\<bar> < 2 * \<epsilon>"
      using close_ij close_ji by linarith    
    hence "\<bar>(\<nabla>\<^sup>2 f x) $ i $ j - (\<nabla>\<^sup>2 f x) $ j $ i\<bar>
            < 2 * \<bar>(\<nabla>\<^sup>2 f x) $ i $ j - (\<nabla>\<^sup>2 f x) $ j $ i\<bar> / 3"
      by (simp add: \<epsilon>_def)
    moreover have "\<bar>(\<nabla>\<^sup>2 f x) $ i $ j - (\<nabla>\<^sup>2 f x) $ j $ i\<bar> > 0"
      using neq by simp
    ultimately show False
      by (simp add: field_simps)
  qed

  (* ---------- 11.  Translate to gradient notation ---------- *)
  have Hx: "HESS f x :> \<nabla>\<^sup>2 f x"
    using Hess_exists xU by blast

  have rowi: "(\<nabla>\<^sup>2 f x) $ i $ j = (\<nabla> (\<lambda>y. \<nabla> f y $ i)) x $ j"
    using hessian_eq_double_nabla[OF Hx] by simp
  have rowj: "(\<nabla>\<^sup>2 f x) $ j $ i = (\<nabla> (\<lambda>y. \<nabla> f y $ j)) x $ i"
    using hessian_eq_double_nabla[OF Hx] by simp

  show ?thesis
    using \<open>(\<nabla>\<^sup>2 f x) $ i $ j = (\<nabla>\<^sup>2 f x) $ j $ i\<close> rowi rowj by simp
qed




theorem clairaut_hessian_symmetric:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes "open U"
      and "x \<in> U"
      and "Ck_on 2 f U"
  shows "transpose (\<nabla>\<^sup>2 f x) = \<nabla>\<^sup>2 f x"
proof -
  have H: "HESS f x :> \<nabla>\<^sup>2 f x"
    using assms(2,3) by (subst Ck_2_imp_hessian_exists, simp_all)

  have sym_entries: "\<forall>i j. \<nabla>\<^sup>2 f x $ i $ j = \<nabla>\<^sup>2 f x $ j $ i"
  proof (intro allI)
    fix i j
    have ij: "\<nabla>\<^sup>2 f x $ i $ j = (\<nabla> (\<lambda>y. \<nabla> f y $ i)) x $ j"
      using hessian_eq_double_nabla[OF H] by simp
    have ji: "\<nabla>\<^sup>2 f x $ j $ i = (\<nabla> (\<lambda>y. \<nabla> f y $ j)) x $ i"
      using hessian_eq_double_nabla[OF H] by simp
    have mix: "(\<nabla> (\<lambda>y. \<nabla> f y $ i)) x $ j = (\<nabla> (\<lambda>y. \<nabla> f y $ j)) x $ i"
      by (rule mixed_coordinate_second_derivative_eq[OF assms])
    show "\<nabla>\<^sup>2 f x $ i $ j = \<nabla>\<^sup>2 f x $ j $ i"
      using ij ji mix by simp
  qed
  then show ?thesis
    by (simp add: Finite_Cartesian_Product.transpose_def)
qed

text \<open>Equivalently, all mixed partials commute.\<close>


corollary mixed_partials_commute:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes "open U" and "x \<in> U" and "Ck_on 2 f U"
  shows "\<nabla>\<^sup>2 f x $ i $ j = \<nabla>\<^sup>2 f x $ j $ i"
  using clairaut_hessian_symmetric[OF assms]
  by (metis (no_types, lifting) Finite_Cartesian_Product.transpose_def vec_lambda_beta)

(* ================================================================== *)
subsection \<open>Basic algebra of gradients\<close>
(* ================================================================== *)


lemma hessian_add_on_C2:
  fixes f g :: "real^'n::finite \<Rightarrow> real"
  assumes Cf: "Ck_on 2 f U"
      and Cg: "Ck_on 2 g U"
      and xU: "x \<in> U"
  shows "\<nabla>\<^sup>2 (\<lambda>y. f y + g y) x = \<nabla>\<^sup>2 f x + \<nabla>\<^sup>2 g x"
proof (rule vec_eq_iff[THEN iffD2], intro allI)
  fix i
  have openU: "open U"
    using Cf by (simp add: Ck_on_def)
  have Hf: "HESS f x :> \<nabla>\<^sup>2 f x"
    using Cf xU by (rule Ck_2_imp_hessian_exists)
  have Hg: "HESS g x :> \<nabla>\<^sup>2 g x"
    using Cg xU by (rule Ck_2_imp_hessian_exists)
  have Hfg: "HESS (\<lambda>y. f y + g y) x :> \<nabla>\<^sup>2 (\<lambda>y. f y + g y) x"
    using Ck_on_add[OF Cf Cg] xU by (rule Ck_2_imp_hessian_exists)
  let ?\<phi> = "\<lambda>y. \<nabla> (\<lambda>z. f z + g z) y $ i"
  let ?\<psi> = "\<lambda>y. \<nabla> f y $ i + \<nabla> g y $ i"
  have eqU: "\<And>y. y \<in> U \<Longrightarrow> ?\<phi> y = ?\<psi> y"
  proof -
    fix y assume yU: "y \<in> U"
    have Gf: "GRAD f y :> \<nabla> f y"
      using Ck_2_imp_gradient_exists[OF Cf yU]
      by (blast intro: grad_fun_satisfies_GRAD)
    have Gg: "GRAD g y :> \<nabla> g y"
      using Ck_2_imp_gradient_exists[OF Cg yU]
      by (blast intro: grad_fun_satisfies_GRAD)
    have "GRAD (\<lambda>z. f z + g z) y :> \<nabla> f y + \<nabla> g y"
      by (rule GRAD_add[OF Gf Gg])
    hence "\<nabla> (\<lambda>z. f z + g z) y = \<nabla> f y + \<nabla> g y"
      by (rule grad_fun_eq)
    thus "?\<phi> y = ?\<psi> y" by simp
  qed
  have Grow_f: "GRAD (\<lambda>y. \<nabla> f y $ i) x :> (\<nabla>\<^sup>2 f x) $ i"
    by (rule HESS_row_gradient[OF Hf])
  have Grow_g: "GRAD (\<lambda>y. \<nabla> g y $ i) x :> (\<nabla>\<^sup>2 g x) $ i"
    by (rule HESS_row_gradient[OF Hg])
  have G\<psi>: "GRAD ?\<psi> x :> ((\<nabla>\<^sup>2 f x + \<nabla>\<^sup>2 g x) $ i)"
    using GRAD_add[OF Grow_f Grow_g] by simp
  have D\<psi>: "(?\<psi> has_derivative (\<lambda>v. v \<bullet> ((\<nabla>\<^sup>2 f x + \<nabla>\<^sup>2 g x) $ i))) (at x)"
    using G\<psi> unfolding has_gradient_def by simp
  have D\<phi>: "(?\<phi> has_derivative (\<lambda>v. v \<bullet> ((\<nabla>\<^sup>2 f x + \<nabla>\<^sup>2 g x) $ i))) (at x)"
    by (smt (verit, best) D\<psi> eqU has_derivative_transform_within_open openU xU)
  have G\<phi>: "GRAD ?\<phi> x :> ((\<nabla>\<^sup>2 f x + \<nabla>\<^sup>2 g x) $ i)"
    using D\<phi> unfolding has_gradient_def by simp
  show "\<nabla>\<^sup>2 (\<lambda>y. f y + g y) x $ i = (\<nabla>\<^sup>2 f x + \<nabla>\<^sup>2 g x) $ i"
    using G\<phi> HESS_row_eq Hfg grad_fun_eq by fastforce
qed


lemma hessian_scaleR_on_C2:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes Cf: "Ck_on 2 f U"
      and xU: "x \<in> U"
  shows "\<nabla>\<^sup>2 (\<lambda>y. c * f y) x = c *\<^sub>R \<nabla>\<^sup>2 f x"
proof (rule vec_eq_iff[THEN iffD2], intro allI)
  fix i
  have openU: "open U"
    using Cf by (simp add: Ck_on_def)
  have Hf: "HESS f x :> \<nabla>\<^sup>2 f x"
    using Cf xU by (rule Ck_2_imp_hessian_exists)
  have Hcf: "HESS (\<lambda>y. c * f y) x :> \<nabla>\<^sup>2 (\<lambda>y. c * f y) x"
    using Ck_on_scaleR[OF Cf] xU by (subst Ck_2_imp_hessian_exists, auto)
  let ?\<phi> = "\<lambda>y. \<nabla> (\<lambda>z. c * f z) y $ i"
  let ?\<psi> = "\<lambda>y. c * (\<nabla> f y $ i)"
  have eqU: "\<And>y. y \<in> U \<Longrightarrow> ?\<phi> y = ?\<psi> y"
  proof -
    fix y assume yU: "y \<in> U"
    have Gf: "GRAD f y :> \<nabla> f y"
      using Ck_2_imp_gradient_exists[OF Cf yU]
      by (blast intro: grad_fun_satisfies_GRAD)
    have "GRAD (\<lambda>z. c * f z) y :> c *\<^sub>R \<nabla> f y"
      by (rule GRAD_scaleR[OF Gf])
    hence "\<nabla> (\<lambda>z. c * f z) y = c *\<^sub>R \<nabla> f y"
      by (rule grad_fun_eq)
    thus "?\<phi> y = ?\<psi> y" by simp
  qed
  have Grow_f: "GRAD (\<lambda>y. \<nabla> f y $ i) x :> (\<nabla>\<^sup>2 f x) $ i"
    by (rule HESS_row_gradient[OF Hf])
  have G\<psi>: "GRAD ?\<psi> x :> c *\<^sub>R ((\<nabla>\<^sup>2 f x) $ i)"
    using GRAD_scaleR[OF Grow_f] by simp
  have D\<psi>: "(?\<psi> has_derivative (\<lambda>v. v \<bullet> (c *\<^sub>R ((\<nabla>\<^sup>2 f x) $ i)))) (at x)"
    using G\<psi> unfolding has_gradient_def by simp
  have D\<phi>: "(?\<phi> has_derivative (\<lambda>v. v \<bullet> (c *\<^sub>R ((\<nabla>\<^sup>2 f x) $ i)))) (at x)"
    using D\<psi> eqU has_derivative_transform_within_open openU xU by fastforce
  have G\<phi>: "GRAD ?\<phi> x :> c *\<^sub>R ((\<nabla>\<^sup>2 f x) $ i)"
    using D\<phi> unfolding has_gradient_def by simp
  show "\<nabla>\<^sup>2 (\<lambda>y. c * f y) x $ i = (c *\<^sub>R \<nabla>\<^sup>2 f x) $ i"
    using G\<phi> HESS_row_eq Hcf grad_fun_eq by fastforce
qed


lemma hessian_sub_on_C2:
  fixes f g :: "real^'n::finite \<Rightarrow> real"
  assumes Cf: "Ck_on 2 f U"
      and Cg: "Ck_on 2 g U"
      and xU: "x \<in> U"
  shows "\<nabla>\<^sup>2 (\<lambda>y. f y - g y) x = \<nabla>\<^sup>2 f x - \<nabla>\<^sup>2 g x"
proof -
  have "\<nabla>\<^sup>2 (\<lambda>y. f y + (-1) * g y) x = \<nabla>\<^sup>2 f x + (-1) *\<^sub>R \<nabla>\<^sup>2 g x"
  proof (subst hessian_add_on_C2)
    show "Ck_on 2 f U" 
      by (rule Cf)
    show "Ck_on 2 (\<lambda>y. (-1) * g y) U" 
      using Ck_on_scaleR[OF Cg] by (metis ext real_scaleR_def) 
    show "x \<in> U" 
      by (rule xU)
    show "\<nabla>\<^sup>2 f x + \<nabla>\<^sup>2 (\<lambda>y. - 1 * g y) x = \<nabla>\<^sup>2 f x + - 1 *\<^sub>R \<nabla>\<^sup>2 g x"
      by (metis Cg hessian_scaleR_on_C2 xU)
  qed
  thus ?thesis by simp
qed


lemma hessian_sum_on_C2:
  fixes F :: "'i \<Rightarrow> real^'n::finite \<Rightarrow> real"
  assumes fin: "finite I"
      and C2: "\<And>i. i \<in> I \<Longrightarrow> Ck_on 2 (F i) U"
      and xU: "x \<in> U"
  shows "\<nabla>\<^sup>2 (\<lambda>y. \<Sum>i\<in>I. F i y) x = (\<Sum>i\<in>I. \<nabla>\<^sup>2 (F i) x)"
  using fin C2
proof (induction rule: finite_induct)
  case empty
  show ?case by (simp add: hessian_const_zero)
next
  case (insert i I)
  have Ci: "Ck_on 2 (F i) U"
    using insert.prems by simp
  have openU: "open U"
    using Ci by (simp add: Ck_on_def)
  have C2_I: "\<And>j. j \<in> I \<Longrightarrow> Ck_on 2 (F j) U"
    using insert.prems by simp
  have CI: "Ck_on 2 (\<lambda>y. \<Sum>j\<in>I. F j y) U"
  proof (cases "I = {}")
    case True
    then show ?thesis
      using Ck_on_const[OF openU] by simp
  next
    case False
    then show ?thesis
      using Ck_on_sum[OF insert.hyps(1) False C2_I]
      by presburger 
  qed
  have IH: "\<nabla>\<^sup>2 (\<lambda>y. \<Sum>j\<in>I. F j y) x = (\<Sum>j\<in>I. \<nabla>\<^sup>2 (F j) x)"
    using insert.IH C2_I by blast
  have "\<nabla>\<^sup>2 (\<lambda>y. \<Sum>j\<in>insert i I. F j y) x
        = \<nabla>\<^sup>2 (\<lambda>y. F i y + (\<Sum>j\<in>I. F j y)) x"
    by (simp add: insert.hyps(1,2))
  also have "\<dots> = \<nabla>\<^sup>2 (F i) x + \<nabla>\<^sup>2 (\<lambda>y. \<Sum>j\<in>I. F j y) x"
    by (rule hessian_add_on_C2[OF Ci CI xU])
  also have "\<dots> = \<nabla>\<^sup>2 (F i) x + (\<Sum>j\<in>I. \<nabla>\<^sup>2 (F j) x)"
    by (simp add: IH)
  also have "\<dots> = (\<Sum>j\<in>insert i I. \<nabla>\<^sup>2 (F j) x)"
    using insert.hyps by simp
  finally show ?case.
qed


lemma second_directional_derivative_eq_hessian_quadratic_form:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes C2: "Ck_on 2 f U"
      and xU: "x \<in> U"
  shows "frechet_derivative (\<lambda>y. frechet_derivative f (at y) v) (at x) v
       = v \<bullet> ((\<nabla>\<^sup>2 f x) *v v)"
proof -
  have openU: "open U"
    using C2 by (simp add: Ck_on_def)

  have H: "HESS f x :> \<nabla>\<^sup>2 f x"
    using C2 xU by (rule Ck_2_imp_hessian_exists)

  have eqU: "\<And>y. y \<in> U \<Longrightarrow> frechet_derivative f (at y) v = v \<bullet> \<nabla> f y"
  proof -
    fix y
    assume yU: "y \<in> U"

    from Ck_2_imp_gradient_exists[OF C2 yU]
    obtain g where g: "GRAD f y :> g"
      by blast

    have Gy: "GRAD f y :> \<nabla> f y"
      using g by (rule grad_fun_satisfies_GRAD)

    have "(f has_derivative (\<lambda>w. w \<bullet> \<nabla> f y)) (at y)"
      using Gy unfolding has_gradient_def by simp
    hence "frechet_derivative f (at y) = (\<lambda>w. w \<bullet> \<nabla> f y)"
      by (subst frechet_derivative_at, auto)

    thus "frechet_derivative f (at y) v = v \<bullet> \<nabla> f y"
      by simp
  qed
  have "\<exists>A. open A \<and> x \<in> A \<and> (\<forall>y\<in>A. frechet_derivative f (at y) v = v \<bullet> \<nabla> f y)"
    using openU xU eqU by blast
  then have ev_eq: "eventually (\<lambda>y. frechet_derivative f (at y) v = v \<bullet> \<nabla> f y) (nhds x)"        
    by (simp add: eventually_nhds)
  have Dgrad: "(\<nabla> f has_derivative (*v) (\<nabla>\<^sup>2 f x)) (at x)"
    using H unfolding has_hessian_def by simp
  have Dcomp: "((\<lambda>y. v \<bullet> \<nabla> f y) has_derivative (\<lambda>h. v \<bullet> (((*v) (\<nabla>\<^sup>2 f x)) h))) (at x)"
    using Dgrad by (auto intro!: derivative_eq_intros)
  have Dfd: "((\<lambda>y. frechet_derivative f (at y) v) has_derivative
       (\<lambda>h. v \<bullet> (((*v) (\<nabla>\<^sup>2 f x)) h))) (at x)"
    by (metis (no_types, lifting) Dcomp eqU has_derivative_transform_within_open openU xU)
  have FD: "frechet_derivative (\<lambda>y. frechet_derivative f (at y) v) (at x)
    = (\<lambda>h. v \<bullet> (((*v) (\<nabla>\<^sup>2 f x)) h))"
    by (metis Dfd frechet_derivative_at)
  show ?thesis
    by (simp add: FD)
qed

(* ================================================================== *)
subsection \<open>Outer product of vectors\<close>
(* ================================================================== *)


lemma hessian_mult_on_C2:
  fixes f g :: "real^'n::finite \<Rightarrow> real"
  assumes Cf: "Ck_on 2 f U"
      and Cg: "Ck_on 2 g U"
      and xU: "x \<in> U"
  shows "\<nabla>\<^sup>2 (\<lambda>y. f y * g y) x =
           f x *\<^sub>R \<nabla>\<^sup>2 g x + g x *\<^sub>R \<nabla>\<^sup>2 f x
         + (\<nabla> f x) \<otimes> (\<nabla> g x)
         + (\<nabla> g x) \<otimes> (\<nabla> f x)"
proof (rule vec_eq_iff[THEN iffD2], intro allI)
  fix i

  have openU: "open U"
    using Cf by (simp add: Ck_on_def)

  (* ---- Hessians exist ---- *)
  have Hf: "HESS f x :> \<nabla>\<^sup>2 f x"
    using Cf xU by (rule Ck_2_imp_hessian_exists)
  have Hg: "HESS g x :> \<nabla>\<^sup>2 g x"
    using Cg xU by (rule Ck_2_imp_hessian_exists)

  have Cfh: "Ck_on 2 (\<lambda>y. f y * g y) U"
    by (simp add: Cf Cg Ck_on_mult)

  have Hfg: "HESS (\<lambda>y. f y * g y) x :> \<nabla>\<^sup>2 (\<lambda>y. f y * g y) x"
    using Cfh xU by (rule Ck_2_imp_hessian_exists)

  (* ---- Gradient existence on U ---- *)
  have Gf_at: "\<And>y. y \<in> U \<Longrightarrow> GRAD f y :> \<nabla> f y"
    using Ck_2_imp_gradient_exists[OF Cf]
    by (blast intro: grad_fun_satisfies_GRAD)
  have Gg_at: "\<And>y. y \<in> U \<Longrightarrow> GRAD g y :> \<nabla> g y"
    using Ck_2_imp_gradient_exists[OF Cg]
    by (blast intro: grad_fun_satisfies_GRAD)

  (* ---- Row gradients of Hessians ---- *)
  have Hf_row: "GRAD (\<lambda>y. \<nabla> f y $ i) x :> (\<nabla>\<^sup>2 f x) $ i"
    by (rule HESS_row_gradient[OF Hf])
  have Hg_row: "GRAD (\<lambda>y. \<nabla> g y $ i) x :> (\<nabla>\<^sup>2 g x) $ i"
    by (rule HESS_row_gradient[OF Hg])

  (* ---- The i-th component of \<nabla>(fg) ---- *)
  (* On U: \<nabla>(fg)(y) $ i = f(y) * \<nabla>g(y) $ i + g(y) * \<nabla>f(y) $ i *)
  let ?\<phi> = "\<lambda>y. \<nabla> (\<lambda>z. f z * g z) y $ i"
  let ?\<psi> = "\<lambda>y. f y * (\<nabla> g y $ i) + g y * (\<nabla> f y $ i)"

  have eqU: "\<And>y. y \<in> U \<Longrightarrow> ?\<phi> y = ?\<psi> y"
  proof -
    fix y assume yU: "y \<in> U"
    have "GRAD (\<lambda>z. f z * g z) y :> f y *\<^sub>R \<nabla> g y + g y *\<^sub>R \<nabla> f y"
      by (rule GRAD_mult[OF Gf_at[OF yU] Gg_at[OF yU]])
    hence "\<nabla> (\<lambda>z. f z * g z) y = f y *\<^sub>R \<nabla> g y + g y *\<^sub>R \<nabla> f y"
      by (rule grad_fun_eq)
    thus "?\<phi> y = ?\<psi> y" by simp
  qed

  (* ---- Gradient of y \<mapsto> f(y) * \<nabla>g(y)$i ---- *)
  have Gf_x: "GRAD f x :> \<nabla> f x"
    using Gf_at[OF xU] .
  have Gg_x: "GRAD g x :> \<nabla> g x"
    using Gg_at[OF xU] .

  have G_term1: "GRAD (\<lambda>y. f y * (\<nabla> g y $ i)) x :>
                   f x *\<^sub>R (\<nabla>\<^sup>2 g x) $ i + (\<nabla> g x $ i) *\<^sub>R \<nabla> f x"
    by (rule GRAD_mult[OF Gf_x Hg_row])

  (* ---- Gradient of y \<mapsto> g(y) * \<nabla>f(y)$i ---- *)
  have G_term2: "GRAD (\<lambda>y. g y * (\<nabla> f y $ i)) x :>
                   g x *\<^sub>R (\<nabla>\<^sup>2 f x) $ i + (\<nabla> f x $ i) *\<^sub>R \<nabla> g x"
    by (rule GRAD_mult[OF Gg_x Hf_row])

  (* ---- Gradient of \<psi> by addition ---- *)
  have G\<psi>: "GRAD ?\<psi> x :>
               (f x *\<^sub>R (\<nabla>\<^sup>2 g x) $ i + (\<nabla> g x $ i) *\<^sub>R \<nabla> f x)
             + (g x *\<^sub>R (\<nabla>\<^sup>2 f x) $ i + (\<nabla> f x $ i) *\<^sub>R \<nabla> g x)"
    by (rule GRAD_add[OF G_term1 G_term2])

  (* ---- Transfer from \<psi> to \<phi> using agreement on U ---- *)
  have D\<psi>: "(?\<psi> has_derivative
      (\<lambda>v. v \<bullet> ((f x *\<^sub>R (\<nabla>\<^sup>2 g x) $ i + (\<nabla> g x $ i) *\<^sub>R \<nabla> f x)
              + (g x *\<^sub>R (\<nabla>\<^sup>2 f x) $ i + (\<nabla> f x $ i) *\<^sub>R \<nabla> g x)))) (at x)"
    using G\<psi> unfolding has_gradient_def by simp

  have D\<phi>: "(?\<phi> has_derivative
      (\<lambda>v. v \<bullet> ((f x *\<^sub>R (\<nabla>\<^sup>2 g x) $ i + (\<nabla> g x $ i) *\<^sub>R \<nabla> f x)
              + (g x *\<^sub>R (\<nabla>\<^sup>2 f x) $ i + (\<nabla> f x $ i) *\<^sub>R \<nabla> g x)))) (at x)"
    using D\<psi> eqU has_derivative_transform_within_open openU xU by fastforce

  have G\<phi>: "GRAD ?\<phi> x :>
               (f x *\<^sub>R (\<nabla>\<^sup>2 g x) $ i + (\<nabla> g x $ i) *\<^sub>R \<nabla> f x)
             + (g x *\<^sub>R (\<nabla>\<^sup>2 f x) $ i + (\<nabla> f x $ i) *\<^sub>R \<nabla> g x)"
    using D\<phi> unfolding has_gradient_def by simp

  (* ---- Assemble the row ---- *)
  have row_eq: "\<nabla> ?\<phi> x =
      (f x *\<^sub>R (\<nabla>\<^sup>2 g x) $ i + (\<nabla> g x $ i) *\<^sub>R \<nabla> f x)
    + (g x *\<^sub>R (\<nabla>\<^sup>2 f x) $ i + (\<nabla> f x $ i) *\<^sub>R \<nabla> g x)"
    by (rule grad_fun_eq[OF G\<phi>])

  have lhs: "\<nabla>\<^sup>2 (\<lambda>y. f y * g y) x $ i = \<nabla> ?\<phi> x"
    using HESS_row_eq[OF Hfg] by simp

  (* ---- Express the RHS in terms of the target matrix ---- *)
  let ?M = "f x *\<^sub>R \<nabla>\<^sup>2 g x + g x *\<^sub>R \<nabla>\<^sup>2 f x
          + (\<nabla> f x) \<otimes> (\<nabla> g x)
          + (\<nabla> g x) \<otimes> (\<nabla> f x)"

  have rhs: "?M $ i =
      (f x *\<^sub>R (\<nabla>\<^sup>2 g x) $ i + (\<nabla> g x $ i) *\<^sub>R \<nabla> f x)
    + (g x *\<^sub>R (\<nabla>\<^sup>2 f x) $ i + (\<nabla> f x $ i) *\<^sub>R \<nabla> g x)"
    by (simp add: vec_eq_iff outer_prod_row algebra_simps)

  show "\<nabla>\<^sup>2 (\<lambda>y. f y * g y) x $ i = ?M $ i"
    using lhs row_eq rhs by simp
qed

(* ================================================================== *)
subsection \<open>Matrix–inner product identity\<close>
(* ================================================================== *)


lemma Ck_on_component:
  fixes F :: "real^'n::finite \<Rightarrow> real^'m::finite"
  assumes "Ck_on k F U"
  shows "Ck_on k (\<lambda>x. F x $ r) U"
proof -
  have oU: "open U"
    using assms by (simp add: Ck_on_def)
  then have hF: "higher_differentiable_on U F k"
    using assms by (simp add: Ck_on_iff_higher_differentiable_on)

  have hcomp: "higher_differentiable_on U (\<lambda>x. F x $ r) k"
    using hF
  proof (induction k arbitrary: F)
    case 0
    then show ?case
      by (metis continuous_on_component higher_differentiable_on.simps(1))
  next
    case (Suc k)
    then have hdiff:
      "higher_differentiable_on U F (Suc k)"
      by simp
    have diffF: "\<forall>x\<in>U. F differentiable (at x)"
      using hdiff higher_differentiable_on.simps(2) by blast
    have diff_comp: "\<forall>x\<in>U. (\<lambda>x. F x $ r) differentiable (at x)"
    proof
      fix x
      assume xU: "x \<in> U"
      have FD: "(F has_derivative frechet_derivative F (at x)) (at x)"
        using diffF xU frechet_derivative_worksI by blast 
      have Hcomp:"((\<lambda>y. F y \<bullet> axis r 1) has_derivative
            (\<lambda>h. frechet_derivative F (at x) h \<bullet> axis r 1)) (at x within UNIV)"
        using FD
        by (subst (asm) has_derivative_componentwise_within[where S=UNIV], auto simp: Basis_vec_def)
      have comp_fun: "(\<lambda>y. F y \<bullet> axis r 1) = (\<lambda>y. F y $ r)"
        by (rule ext) (simp add: cart_eq_inner_axis)
      have "((\<lambda>y. F y $ r) has_derivative (\<lambda>h. frechet_derivative F (at x) h $ r)) (at x)"
        using Hcomp by (simp add: inner_axis)
      then show "(\<lambda>x. F x $ r) differentiable (at x)"
        unfolding differentiable_def by blast
    qed
    have der_comp: "\<forall>v. higher_differentiable_on U
                   (\<lambda>x. frechet_derivative (\<lambda>x. F x $ r) (at x) v) k"
    proof
      fix v
      have eqU: "\<And>x. x \<in> U \<Longrightarrow> frechet_derivative (\<lambda>x. F x $ r) (at x) v =
                               frechet_derivative F (at x) v $ r"
      proof -
        fix x
        assume xU: "x \<in> U"
        have FD: "(F has_derivative frechet_derivative F (at x)) (at x)"
          using diffF xU frechet_derivative_worksI by blast
        have Hcomp:"((\<lambda>y. F y \<bullet> axis r 1) has_derivative
                     (\<lambda>h. frechet_derivative F (at x) h \<bullet> axis r 1)) (at x within UNIV)"
          using FD
          by (subst (asm) has_derivative_componentwise_within[where S=UNIV], auto simp: Basis_vec_def)
        have comp_fun: "(\<lambda>y. F y \<bullet> axis r 1) = (\<lambda>y. F y $ r)"
          by (rule ext) (simp add: cart_eq_inner_axis)
        have coord_D: "((\<lambda>y. F y $ r) has_derivative
                        (\<lambda>h. frechet_derivative F (at x) h $ r)) (at x)"
          using Hcomp by (simp add: cart_eq_inner_axis)
        have coord_FD: "frechet_derivative (\<lambda>y. F y $ r) (at x) =
                   (\<lambda>h. frechet_derivative F (at x) h $ r)"
          by (subst frechet_derivative_at[OF coord_D], simp)
        show "frechet_derivative (\<lambda>x. F x $ r) (at x) v = frechet_derivative F (at x) v $ r"
          by (simp add: coord_FD)
      qed
      have hderF:  "higher_differentiable_on U (\<lambda>x. frechet_derivative F (at x) v) k"
        using hdiff higher_differentiable_on.simps(2) by blast
      have "higher_differentiable_on U  (\<lambda>x. (frechet_derivative F (at x) v :: real^'m) $ r) k"
        using Suc.IH[OF hderF].
      then show "higher_differentiable_on U (\<lambda>x. frechet_derivative (\<lambda>x. F x $ r) (at x) v) k"
        using oU eqU by (subst higher_differentiable_on_cong, simp_all)
    qed
    then show ?case
      using diff_comp higher_differentiable_on.simps(2) by blast 
  qed
  with oU show ?thesis
    by (simp add: Ck_on_iff_higher_differentiable_on)
qed


(* ================================================================== *)
subsection \<open>Hessian chain rule\<close>
(* ================================================================== *)


text \<open>
  Row extraction for a quadratic matrix product:
    \<open>(A\<^sup>T B A)\<^sub>i = \<Sigma>\<^sub>r A\<^sub>r\<^sub>i \<sqdot> (A\<^sup>T \<sqdot> B\<^sub>r)\<close>
  where \<open>B\<^sub>r\<close> is the \<open>r\<close>-th row of \<open>B\<close> viewed as a column vector.
\<close>


lemma hessian_compose_on_C2:
  fixes g :: "real^'m::finite \<Rightarrow> real"
    and F :: "real^'n::finite \<Rightarrow> real^'m"
  assumes Cg: "Ck_on 2 g V"
      and CF: "Ck_on 2 F U"
      and FUV: "\<And>y. y \<in> U \<Longrightarrow> F y \<in> V"
      and xU: "x \<in> U"
  shows "\<nabla>\<^sup>2 (\<lambda>y. g (F y)) x =
           transpose (jacobian F x) ** \<nabla>\<^sup>2 g (F x) ** jacobian F x
         + (\<Sum>r\<in>UNIV. (\<nabla> g (F x) $ r) *\<^sub>R \<nabla>\<^sup>2 (\<lambda>y. F y $ r) x)"
         (is "?LHS = ?RHS")
proof (rule vec_eq_iff[THEN iffD2], intro allI)
  fix i :: 'n

  have openU: "open U" using CF by (simp add: Ck_on_def)
  have openV: "open V" using Cg by (simp add: Ck_on_def)

  (* ---- C² closure: g \<circ> F is C² on U ---- *)
  have CgF: "Ck_on 2 (\<lambda>y. g (F y)) U"
    using Ck_on_compose[OF Cg CF FUV] .

  (* ---- Component C² ---- *)
  have CF_r: "\<And>r. Ck_on 2 (\<lambda>y. F y $ r) U"
    using CF by (rule Ck_on_component)

  (* ---- Hessians exist ---- *)
  have HgF: "HESS (\<lambda>y. g (F y)) x :> \<nabla>\<^sup>2 (\<lambda>y. g (F y)) x"
    using CgF xU by (rule Ck_2_imp_hessian_exists)
  have Hg: "HESS g (F x) :> \<nabla>\<^sup>2 g (F x)"
    using Cg FUV[OF xU] by (rule Ck_2_imp_hessian_exists)
  have HF_r: "\<And>r. HESS (\<lambda>y. F y $ r) x :> \<nabla>\<^sup>2 (\<lambda>y. F y $ r) x"
    using CF_r xU by (rule Ck_2_imp_hessian_exists)

  (* ---- Differentiability of F on U ---- *)
  have F_diff: "\<And>y. y \<in> U \<Longrightarrow> F differentiable (at y)"
  proof -
    fix y assume "y \<in> U"
    then have "Ck_at 2 F y"
      using CF by (simp add: Ck_on_def)
    thus "F differentiable (at y)"
      by (metis Ck_at.simps(2) Suc_1)
  qed

  (* ---- Gradient existence ---- *)
  have Gg_at: "\<And>z. z \<in> V \<Longrightarrow> GRAD g z :> \<nabla> g z"
    using Ck_2_imp_gradient_exists[OF Cg]
    by (blast intro: grad_fun_satisfies_GRAD)

  have GF_r_at: "\<And>r y. y \<in> U \<Longrightarrow> GRAD (\<lambda>y. F y $ r) y :> \<nabla> (\<lambda>y. F y $ r) y"
    using Ck_2_imp_gradient_exists[OF CF_r]
    by (blast intro: grad_fun_satisfies_GRAD)

  (* ---- Row gradients of component Hessians ---- *)
  have HF_r_row: "\<And>r. GRAD (\<lambda>y. \<nabla> (\<lambda>z. F z $ r) y $ i) x :> (\<nabla>\<^sup>2 (\<lambda>y. F y $ r) x) $ i"
    by (rule HESS_row_gradient[OF HF_r])

  (* ---- Row gradient of the Hessian of g ---- *)
  have Hg_row: "\<And>r. GRAD (\<lambda>z. \<nabla> g z $ r) (F x) :> (\<nabla>\<^sup>2 g (F x)) $ r"
    by (rule HESS_row_gradient[OF Hg])

  (* ---- On U, \<nabla>(g \<circ> F)(y) $ i = \<Sigma>_r (\<nabla>(F_r)(y) $ i) * (\<nabla>g(F(y)) $ r) ---- *)
  let ?\<phi> = "\<lambda>y. \<nabla> (\<lambda>z. g (F z)) y $ i"
  let ?\<psi> = "\<lambda>y. \<Sum>r\<in>UNIV. \<nabla> (\<lambda>z. F z $ r) y $ i * \<nabla> g (F y) $ r"

  have eqU: "\<And>y. y \<in> U \<Longrightarrow> ?\<phi> y = ?\<psi> y"
  proof -
    fix y :: "real^'n"
    assume yU: "y \<in> U"

    have Fy_V: "F y \<in> V" using FUV[OF yU] .
    have Gy: "GRAD g (F y) :> \<nabla> g (F y)"
      using Gg_at[OF Fy_V] .
    have Fy_diff: "F differentiable (at y)"
      using F_diff[OF yU] .

    have grad_comp: "\<nabla> (\<lambda>z. g (F z)) y = transpose (jacobian F y) *v \<nabla> g (F y)"
      by (rule grad_fun_compose[where g=g and F=F], blast intro: Gy, rule Fy_diff)

    have "?\<phi> y = (transpose (jacobian F y) *v \<nabla> g (F y)) $ i"
      using grad_comp by simp
    also have "\<dots> = (\<Sum>r\<in>UNIV. transpose (jacobian F y) $ i $ r * \<nabla> g (F y) $ r)"
      by (simp add: matrix_vector_mult_def)
    also have "\<dots> = (\<Sum>r\<in>UNIV. jacobian F y $ r $ i * \<nabla> g (F y) $ r)"
      by (simp add: transpose_def)
    also have "\<dots> = ?\<psi> y"
    proof (rule sum.cong[OF refl])
      fix r :: 'm
      assume "r \<in> UNIV"

      have Fr_diff: "(\<lambda>z. F z $ r) differentiable (at y)"
      proof -
        have FD: "(F has_derivative frechet_derivative F (at y)) (at y)"
          using Fy_diff frechet_derivative_worksI by blast 

        have Hcomp:"((\<lambda>z. F z \<bullet> axis r 1) has_derivative
                     (\<lambda>h. frechet_derivative F (at y) h \<bullet> axis r 1)) (at y within UNIV)"
          using FD
          by (subst (asm) has_derivative_componentwise_within[where S = UNIV],
              auto simp: Basis_vec_def)

        have comp_fun: "(\<lambda>z. F z \<bullet> axis r 1) = (\<lambda>z. F z $ r)"
          by (rule ext) (simp add: cart_eq_inner_axis)
        have coord_D: "((\<lambda>z. F z $ r) has_derivative
                        (\<lambda>h. frechet_derivative F (at y) h $ r)) (at y)"
          using Hcomp by (simp add: inner_axis)
        then show ?thesis
          unfolding differentiable_def by blast
      qed

      show "jacobian F y $ r $ i * \<nabla> g (F y) $ r =  \<nabla> (\<lambda>z. F z $ r) y $ i * \<nabla> g (F y) $ r"
      proof -
        have Jcomp: "jacobian F y $ r $ i = frechet_derivative (\<lambda>z. F z $ r) (at y) (axis i 1)"
          using jacobian_component[OF Fy_diff, of r i] by simp

        have GFr: "GRAD (\<lambda>z. F z $ r) y :> \<nabla> (\<lambda>z. F z $ r) y"
          using Fr_diff_imp_gradient_exists[OF Fr_diff]
          by (blast intro: grad_fun_satisfies_GRAD)

        have DFr: "((\<lambda>z. F z $ r) has_derivative (\<lambda>h. h \<bullet> \<nabla> (\<lambda>z. F z $ r) y)) (at y)"
          using GFr unfolding has_gradient_def by simp

        have FD_eq:  "frechet_derivative (\<lambda>z. F z $ r) (at y) = (\<lambda>h. h \<bullet> \<nabla> (\<lambda>z. F z $ r) y)"
          by (subst frechet_derivative_at[OF DFr], simp)

        have "frechet_derivative (\<lambda>z. F z $ r) (at y) (axis i 1)
              = axis i 1 \<bullet> \<nabla> (\<lambda>z. F z $ r) y"
          by (simp add: FD_eq)
        also have "... = \<nabla> (\<lambda>z. F z $ r) y $ i"
          using inner_commute by (simp add: cart_eq_inner_axis, auto)
        finally show ?thesis
          using Jcomp by simp
      qed
      then have "jacobian F y $ r $ i = \<nabla> (\<lambda>z. F z $ r) y $ i"
        using jacobian_component[OF Fy_diff]
        by (metis (mono_tags, lifting) Fr_diff Fr_diff_imp_gradient_exists cart_eq_inner_axis 
            frechet_derivative_at grad_fun_eq has_gradient_def inner_commute) 
      qed
      thus "\<nabla> (\<lambda>z. g (F z)) y $ i = (\<Sum>r\<in>UNIV. \<nabla> (\<lambda>z. F z $ r) y $ i * \<nabla> g (F y) $ r)"
        using calculation by presburger
  qed

  (* ---- Differentiate \<psi> at x using GRAD_sum, GRAD_mult ---- *)
  (*
     \<psi>(y) = \<Sigma>_r  a_r(y) * b_r(y)
     where a_r(y) = \<nabla>(F_r)(y) $ i  and  b_r(y) = \<nabla>g(F(y)) $ r.

     GRAD a_r(x) = (\<nabla>²(F_r)(x)) $ i       [by HESS_row_gradient]
     GRAD b_r(x) = transpose(J_F(x)) *v (\<nabla>²g(F(x)) $ r)  [by GRAD_compose']

     By GRAD_mult:
     GRAD (a_r \<sqdot> b_r)(x) = a_r(x) *\<^sub>R GRAD b_r(x) + b_r(x) *\<^sub>R GRAD a_r(x)

     By GRAD_sum:
     GRAD \<psi>(x) = \<Sigma>_r [a_r(x) *\<^sub>R GRAD b_r(x) + b_r(x) *\<^sub>R GRAD a_r(x)]
  *)

  have Ga_r: "\<And>r. GRAD (\<lambda>y. \<nabla> (\<lambda>z. F z $ r) y $ i) x :> (\<nabla>\<^sup>2 (\<lambda>y. F y $ r) x) $ i"
    using HF_r_row .

  have Gb_r: "\<And>r. GRAD (\<lambda>y. \<nabla> g (F y) $ r) x :> transpose (jacobian F x) *v ((\<nabla>\<^sup>2 g (F x)) $ r)"
  proof -
    fix r :: 'm
    have "GRAD (\<lambda>z. \<nabla> g z $ r) (F x) :> (\<nabla>\<^sup>2 g (F x)) $ r"
      using Hg_row .
    thus "GRAD (\<lambda>y. \<nabla> g (F y) $ r) x :> transpose (jacobian F x) *v ((\<nabla>\<^sup>2 g (F x)) $ r)"
      by (rule GRAD_compose'[OF _ F_diff[OF xU]])
  qed

  have G_term_r: "\<And>r. GRAD (\<lambda>y. \<nabla> (\<lambda>z. F z $ r) y $ i * \<nabla> g (F y) $ r) x :>
      \<nabla> (\<lambda>z. F z $ r) x $ i *\<^sub>R (transpose (jacobian F x) *v ((\<nabla>\<^sup>2 g (F x)) $ r))
    + \<nabla> g (F x) $ r *\<^sub>R ((\<nabla>\<^sup>2 (\<lambda>y. F y $ r) x) $ i)"
    by (rule GRAD_mult[OF Ga_r Gb_r])

  define G_r where "G_r r =
      \<nabla> (\<lambda>z. F z $ r) x $ i *\<^sub>R (transpose (jacobian F x) *v ((\<nabla>\<^sup>2 g (F x)) $ r))
    + \<nabla> g (F x) $ r *\<^sub>R ((\<nabla>\<^sup>2 (\<lambda>y. F y $ r) x) $ i)" for r

  have G\<psi>: "GRAD ?\<psi> x :> (\<Sum>r\<in>UNIV. G_r r)"
  proof -
    have "\<And>r. r \<in> (UNIV :: 'm set) \<Longrightarrow>
      GRAD (\<lambda>y. \<nabla> (\<lambda>z. F z $ r) y $ i * \<nabla> g (F y) $ r) x :> G_r r"
      using G_term_r by (simp add: G_r_def)
    thus ?thesis
      by (rule GRAD_sum[OF finite_class.finite_UNIV])
  qed

  (* ---- Transfer from \<psi> to \<phi> ---- *)
  have D\<psi>: "(?\<psi> has_derivative (\<lambda>v. v \<bullet> (\<Sum>r\<in>UNIV. G_r r))) (at x)"
    using G\<psi> unfolding has_gradient_def .

  have D\<phi>: "(?\<phi> has_derivative (\<lambda>v. v \<bullet> (\<Sum>r\<in>UNIV. G_r r))) (at x)"
    using D\<psi> eqU has_derivative_transform_within_open openU xU by fastforce

  have G\<phi>: "GRAD ?\<phi> x :> (\<Sum>r\<in>UNIV. G_r r)"
    using D\<phi> unfolding has_gradient_def by simp

  have row_eq: "\<nabla> ?\<phi> x = (\<Sum>r\<in>UNIV. G_r r)"
    by (rule grad_fun_eq[OF G\<phi>])

  have lhs: "?LHS $ i = \<nabla> ?\<phi> x"
    using HESS_row_eq[OF HgF] by simp

  (* ---- Match the RHS row ---- *)
  (*
     ?RHS $ i = [J^T ** \<nabla>²g(F x) ** J] $ i + [\<Sigma>_r (\<nabla>g(F x)$r) *\<^sub>R \<nabla>²(F_r)(x)] $ i

     We need: \<Sigma>_r G_r(r) = ?RHS $ i

     Expand G_r(r):
       G_r r = a_r(x) *\<^sub>R [J^T *v (\<nabla>²g(F x) $ r)]  +  b_r(x) *\<^sub>R [(\<nabla>²(F_r) x) $ i]

     \<Sigma>_r b_r(x) *\<^sub>R [(\<nabla>²(F_r) x) $ i]  =  [\<Sigma>_r \<nabla>g(F x)$r *\<^sub>R \<nabla>²(F_r)(x)] $ i   \<checkmark>

     \<Sigma>_r a_r(x) *\<^sub>R [J^T *v (\<nabla>²g(F x) $ r)]  =  [J^T ** \<nabla>²g(F x) ** J] $ i
     This is the key matrix algebra step.
  *)

  have sum_second: "(\<Sum>r\<in>UNIV. \<nabla> g (F x) $ r *\<^sub>R ((\<nabla>\<^sup>2 (\<lambda>y. F y $ r) x) $ i))
                  = (\<Sum>r\<in>UNIV. (\<nabla> g (F x) $ r) *\<^sub>R \<nabla>\<^sup>2 (\<lambda>y. F y $ r) x) $ i"
    by simp

  (* matrix algebra: the key identity relating the sum to J^T H J *)
  have sum_first: "(\<Sum>r\<in>UNIV. \<nabla> (\<lambda>z. F z $ r) x $ i *\<^sub>R
                      (transpose (jacobian F x) *v ((\<nabla>\<^sup>2 g (F x)) $ r)))
                 = (transpose (jacobian F x) ** \<nabla>\<^sup>2 g (F x) ** jacobian F x) $ i"
  proof -
    have grad_jac: "\<nabla> (\<lambda>z. F z $ r) x $ i = jacobian F x $ r $ i" for r
    proof -
      have Fr_diff: "(\<lambda>z. F z $ r) differentiable (at x)"
        using F_diff[OF xU] by (metis CF_r Ck_at.simps(2) Ck_on_def Suc_1 xU)     
      have GFr: "GRAD (\<lambda>z. F z $ r) x :> \<nabla> (\<lambda>z. F z $ r) x"
        using Fr_diff_imp_gradient_exists[OF Fr_diff]
        by (blast intro: grad_fun_satisfies_GRAD)
      have FD_eq: "frechet_derivative (\<lambda>z. F z $ r) (at x) = (\<lambda>h. h \<bullet> \<nabla> (\<lambda>z. F z $ r) x)"
        using GFr unfolding has_gradient_def  by (metis frechet_derivative_at)
      have "jacobian F x $ r $ i = frechet_derivative (\<lambda>z. F z $ r) (at x) (axis i 1)"
        using jacobian_component[OF F_diff[OF xU]].
      also have "\<dots> = \<nabla> (\<lambda>z. F z $ r) x $ i"
        by (simp add: FD_eq cart_eq_inner_axis inner_commute,
            metis (no_types, lifting) ext FD_eq cart_eq_inner_axis)
      finally show ?thesis by simp
    qed
    then have "(\<Sum>r\<in>UNIV. \<nabla> (\<lambda>z. F z $ r) x $ i *\<^sub>R  (transpose (jacobian F x) *v ((\<nabla>\<^sup>2 g (F x)) $ r)))
        = (\<Sum>r\<in>UNIV. jacobian F x $ r $ i *\<^sub>R   (transpose (jacobian F x) *v ((\<nabla>\<^sup>2 g (F x)) $ r)))"
      by simp
    also have "\<dots> = (transpose (jacobian F x) ** \<nabla>\<^sup>2 g (F x) ** jacobian F x) $ i"
      by (rule row_transpose_mult_both[symmetric])
    finally show ?thesis.
  qed
  then have "(\<Sum>r\<in>UNIV. G_r r) = ?RHS $ i"
    unfolding G_r_def by (metis (no_types) sum.distrib sum_second vector_add_component)
  then show "?LHS $ i = ?RHS $ i"
    using lhs row_eq by simp
qed


(* ================================================================== *)
subsection \<open>Affine composition (special case)\<close>
(* ================================================================== *)

text \<open>
  If \<open>F(y) = A *v y + b\<close> is affine, then \<open>Jᶠ = A\<close> is constant and each
  \<open>\<nabla>²Fᵣ = 0\<close>, so the chain rule simplifies to:

    \<open>\<nabla>²(g \<circ> F)(x) = Aᵀ \<^emph>\<^emph> \<nabla>²g(A *v x + b) \<^emph>\<^emph> A\<close>
\<close>


lemma hessian_affine_compose_on_C2:
  fixes g :: "real^'m::finite \<Rightarrow> real"
    and A :: "real^'n^'m"
    and b :: "real^'m"
  assumes Cg: "Ck_on 2 g V"
      and sub: "\<And>y. y \<in> U \<Longrightarrow> A *v y + b \<in> V"
      and oU: "open U"
      and xU: "x \<in> U"
  shows "\<nabla>\<^sup>2 (\<lambda>y. g (A *v y + b)) x = transpose A ** \<nabla>\<^sup>2 g (A *v x + b) ** A"
proof -
  define F where "F y = A *v y + b" for y
  have bl: "bounded_linear ((*v) A)"
    by simp
  then have f1: "higher_differentiable_on U ((*v) A) 2"
    using bounded_linear.higher_differentiable_on by blast
  have "higher_differentiable_on U (\<lambda>y. A *v y + b) 2"
      using oU f1 by (subst higher_differentiable_on_add, auto, 
                      simp add: higher_differentiable_on_const)      
  then have CF: "Ck_on 2 F U"
    unfolding F_def using oU by (simp add: Ck_on_iff_higher_differentiable_on)  
  have F_diff: "\<And>y. F differentiable (at y)"
    unfolding F_def by (simp add: bounded_linear_imp_differentiable)
  have jac_eq: "jacobian F y = A" for y
    unfolding jacobian_def F_def by (metis bl bounded_linear_imp_has_derivative 
              frechet_derivative_at has_derivative_add_const matrix_of_matrix_vector_mul)
  have comp_hess_zero: "\<nabla>\<^sup>2 (\<lambda>y. F y $ r) x = 0" for r
  proof -
    have fn_eq: "(\<lambda>y. F y $ r) = (\<lambda>y. b $ r + y \<bullet> (A $ r))"
    proof (rule ext)
      fix y :: "real^'n"
      have "F y $ r = (A *v y + b) $ r"
        by (simp add: F_def)
      also have "\<dots> = (\<Sum>j\<in>UNIV. A $ r $ j * y $ j) + b $ r"
        by (simp add: matrix_vector_mult_def)
      also have "\<dots> = b $ r + y \<bullet> (A $ r)"
        by (simp add: inner_vec_def, meson mult.commute)
      finally show "F y $ r = b $ r + y \<bullet> (A $ r)".
    qed
    have "HESS (\<lambda>y. b $ r + y \<bullet> (A $ r)) x :> 0"
      by (rule HESS_affine_zero)
    hence "HESS (\<lambda>y. F y $ r) x :> 0"
      by (simp add: fn_eq)
    thus ?thesis
      by (metis hess_fun_eq)
  qed
  then have grad_zero_sum: "(\<Sum>r\<in>UNIV. \<nabla> g (F x) $ r *\<^sub>R \<nabla>\<^sup>2 (\<lambda>y. F y $ r) x) = 0"
    by simp
  have "\<nabla>\<^sup>2 (\<lambda>y. g (F y)) x =
         transpose (jacobian F x) ** \<nabla>\<^sup>2 g (F x) ** jacobian F x
       + (\<Sum>r\<in>UNIV. \<nabla> g (F x) $ r *\<^sub>R \<nabla>\<^sup>2 (\<lambda>y. F y $ r) x)"
    by (rule hessian_compose_on_C2[OF Cg CF _ xU], simp add: F_def sub)
  also have "\<dots> = transpose A ** \<nabla>\<^sup>2 g (F x) ** A + 0"
    by (simp add: jac_eq grad_zero_sum)
  also have "\<dots> = transpose A ** \<nabla>\<^sup>2 g (A *v x + b) ** A"
    by (simp add: F_def)
  ultimately show ?thesis by (simp add: F_def)
qed


end
