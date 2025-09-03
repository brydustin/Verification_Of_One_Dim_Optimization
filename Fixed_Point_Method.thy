section \<open>Fixed Point Method\<close>

theory Fixed_Point_Method
  imports 
    "ITree_Numeric_VCG.ITree_Numeric_VCG"  
    "Higher_Diff_Taylor_Peano.Taylor_Peano"
begin

subsection \<open>Contractive Map Facts\<close>

lemma contractive_deriv_bound:
  fixes B :: real
  assumes "C_k_on 1 f U"
  assumes "z \<in> U"
  assumes "\<bar>deriv f z\<bar> < B"
  shows "\<exists> \<epsilon> > 0. \<exists>\<delta> > 0. ({z - \<delta> <..< z + \<delta>} \<subseteq> U) \<and> (\<forall> x \<in> {z - \<delta> <..< z + \<delta>}. \<bar>deriv f x\<bar> < B - \<epsilon>)"
proof -
  have "(\<exists> \<nu>. 0 < \<nu> \<and> {z - \<nu> .. z + \<nu>} \<subseteq> U)"
    by (metis C_k_on_def assms(1,2) cball_eq_atLeastAtMost open_contains_cball_eq)
  then obtain \<nu> where \<nu>_pos: "\<nu> > 0" and \<nu>_def: "{z - \<nu> .. z + \<nu>} \<subseteq> U"
    by blast

  obtain \<epsilon> where \<epsilon>_def: "\<epsilon> = (B - \<bar>deriv f z\<bar>) / 2" and \<epsilon>_pos: "\<epsilon> > 0"
    using assms(3) by fastforce
  have "continuous_on U (deriv f)"
    using C1_cont_diff assms(1) by blast
  then have "continuous (at z) (deriv f)"
    by (metis C_k_on_def assms(1,2) continuous_on_eq_continuous_at)
  then have "\<forall> \<epsilon> > 0. \<exists> \<delta> > 0.  \<forall>x. \<bar>x - z\<bar> < \<delta> \<longrightarrow> \<bar>deriv f x - deriv f z\<bar> < \<epsilon>"
    using continuous_at_eps_delta by blast
  then obtain \<delta> where \<delta>_pos: "\<delta> > 0" and \<delta>_prop:
    "\<forall>x. \<bar>x - z\<bar> < \<delta> \<longrightarrow> \<bar>deriv f x - deriv f z\<bar> < \<epsilon>"
    by (meson \<epsilon>_pos)
  obtain \<gamma> where \<gamma>_def: "\<gamma> = min \<delta> \<nu>" and \<gamma>_pos: "0 < \<gamma>"
    by (simp add: \<delta>_pos \<nu>_pos)
  
  have bound: "\<forall>x \<in> {z - \<gamma> <..< z + \<gamma>}. \<bar>deriv f x\<bar> < \<bar>deriv f z\<bar> + (B - \<bar>deriv f z\<bar>)/2"
  proof clarify
    fix x :: real
    assume x_def: "x \<in> {z - \<gamma> <..< z + \<gamma>}"
    have "\<bar>deriv f x\<bar> \<le> \<bar>deriv f z\<bar> + \<bar>deriv f x - deriv f z\<bar>"
      by (simp add: abs_triangle_ineq)
    also have "... < \<bar>deriv f z\<bar> + (B - \<bar>deriv f z\<bar>)/2"
      using \<delta>_prop \<epsilon>_def \<gamma>_def dist_real_def x_def by force
    finally show "\<bar>deriv f x\<bar> < \<bar>deriv f z\<bar> + (B - \<bar>deriv f z\<bar>)/2".
  qed
  have "\<bar>deriv f z\<bar> + (B - \<bar>deriv f z\<bar>)/2 = B - \<epsilon>"
    by (smt (z3) \<epsilon>_def field_sum_of_halves)
  hence desired_bnd: "\<forall>x \<in> {z - \<gamma> <..< z + \<gamma>}. \<bar>deriv f x\<bar> < B - \<epsilon>"
    using bound by presburger

  have "{z - \<gamma> <..< z + \<gamma>} \<subseteq> U"
    using \<gamma>_def \<nu>_def atLeastAtMost_eq_cball greaterThanLessThan_eq_ball by auto  
  then show ?thesis
    using \<epsilon>_pos \<gamma>_pos desired_bnd by blast
qed

corollary contractive_deriv_imp_contra:
  fixes B :: real
  assumes "C_k_on 1 f U"
  assumes "z \<in> U"
  assumes "\<bar>deriv f z\<bar> < B"
  shows "\<exists>\<epsilon> > 0. \<exists>\<delta> > 0.
           ((\<epsilon> < B) \<and> {z - \<delta> <..< z + \<delta>} \<subseteq> U) \<and>
           (\<forall>x y. (x \<in> {z - \<delta> <..< z + \<delta>} \<and> y \<in> {x <..< z + \<delta>})
                \<longrightarrow> \<bar>f x - f y\<bar> < (B - \<epsilon>) * \<bar>x - y\<bar>)"
proof -
  from contractive_deriv_bound[OF assms] obtain \<epsilon> \<delta>
    where \<epsilon>_pos: "\<epsilon> > 0" and \<delta>_pos: "\<delta> > 0"
      and bound:   "\<forall>x \<in> {z - \<delta> <..< z + \<delta>}. \<bar>deriv f x\<bar> < B - \<epsilon>"
      and subset': "{z - \<delta> <..< z + \<delta>} \<subseteq> U"
    by auto
  then have \<epsilon>_lt_B: "\<epsilon> < B"
    by (smt (verit) dist_real_def field_sum_of_halves greaterThanLessThan_eq_ball mem_ball)

  have mvt:
    "\<forall>x y. (x \<in> {z - \<delta> <..< z + \<delta>} \<and> y \<in> {x <..< z + \<delta>})
           \<longrightarrow> \<bar>f x - f y\<bar> < (B - \<epsilon>) * \<bar>x - y\<bar>"
  proof clarify
    fix x y :: real
    assume x_in: "x \<in> {z - \<delta> <..< z + \<delta>}" and y_in: "y \<in> {x <..< z + \<delta>}"
    then have x_lt_y: "x < y"
      by (meson greaterThanLessThan_iff)
    then have "\<exists>t>x. t < y \<and> f y - f x = (y - x) * deriv f t"
    proof (rule MVT2[where a = x and b = y and f = f and f' = "deriv f"])
      fix t
      assume "x \<le> t" and "t \<le> y"
      hence "t \<in> {z - \<delta> <..< z + \<delta>}"
        using x_in y_in by auto
      then have "t \<in> U"
        using subset' by blast
      then show "(f has_real_derivative deriv f t) (at t)"
        using C1_cont_diff assms(1) by fast
    qed    
    then obtain \<theta> where \<theta>_in: "\<theta> \<in> {x <..< y}"
                     and \<theta>_eq: "f x - f y = (deriv f \<theta>) * (x - y)"
      by (metis (no_types, opaque_lifting) cross3_simps(11,25) diff_diff_add
          greaterThanLessThan_iff right_minus_eq)

    have "\<theta> \<in> {z - \<delta> <..< z + \<delta>}"
      using x_in y_in \<theta>_in by auto
    then have "\<bar>deriv f \<theta>\<bar> < B - \<epsilon>"
      using bound by blast
    then show "\<bar>f x - f y\<bar> < (B - \<epsilon>) * \<bar>x - y\<bar>"
      using \<theta>_eq x_lt_y by (simp add: abs_mult)
  qed
  then show ?thesis
    using \<epsilon>_pos \<delta>_pos \<epsilon>_lt_B subset' by blast
qed

lemma contraction_ball_closure:
  fixes f :: "real \<Rightarrow> real" and r c \<delta> :: real
  assumes fr:      "f r = r"
    and contr:    "\<forall>s t. \<bar>s - r\<bar> < \<delta> \<longrightarrow> \<bar>t - r\<bar> < \<delta> \<longrightarrow> \<bar>f s - f t\<bar> \<le> c * \<bar>s - t\<bar>"
    and c_bound: "0 \<le> c \<and> c < 1"
  shows "\<forall>n x. \<bar>x - r\<bar> < \<delta> \<longrightarrow> \<bar>(f ^^ n) x - r\<bar> < \<delta>"
proof (clarify)
  fix n :: nat and x :: real
  assume H: "\<bar>x - r\<bar> < \<delta>"
  show "\<bar>(f ^^ n) x - r\<bar> < \<delta>"
  proof (induct n)
    show "\<bar>(f ^^ 0) x - r\<bar> < \<delta>"
      by (simp add: H) 
  next
    case (Suc k)
    then have IH: "\<bar>(f ^^ k) x - r\<bar> < \<delta>"
     by auto 
    have "\<bar>(f ^^ Suc k) x - r\<bar> = \<bar>f ((f ^^ k) x) - r\<bar>"
      by simp
    also have "\<dots> = \<bar>f ((f ^^ k) x) - f r\<bar>"
      using fr by simp
    also have "\<dots> \<le> c * \<bar>(f ^^ k) x - r\<bar>"
      using IH assms(2) by auto
    also have "\<dots> < \<delta>"
      by (smt (verit, best) Suc.hyps c_bound mult_left_le_one_le)
    finally show ?case.
  qed
qed

corollary contraction_ball_closure':
  fixes f :: "real \<Rightarrow> real" and r \<delta> \<delta>0 \<epsilon> :: real
  assumes order_bound:
      "\<forall>x y. x \<in> {r - \<delta>0<..<r + \<delta>0} \<longrightarrow> y \<in> {x<..<r + \<delta>0}
             \<longrightarrow> \<bar>f x - f y\<bar> < (1 - \<epsilon>) * \<bar>x - y\<bar>"
    and \<epsilon>_pos : "0 < \<epsilon>"
    and \<delta>_pos : "0 < \<delta>" and \<delta>_le: "\<delta> \<le> \<delta>0"
  shows "\<forall>s t. s \<noteq> t \<longrightarrow> \<bar>s - r\<bar> < \<delta> \<longrightarrow> \<bar>t - r\<bar> < \<delta>
               \<longrightarrow> \<bar>f s - f t\<bar> < (1 - \<epsilon>) * \<bar>s - t\<bar>"
proof (clarify)
  fix s t :: real
  assume s_neq: "s \<noteq> t"
     and sb:    "\<bar>s - r\<bar> < \<delta>"
     and tb:    "\<bar>t - r\<bar> < \<delta>"
  have s_in: "s \<in> {r - \<delta>0<..<r + \<delta>0}"
    using \<delta>_le dist_real_def sb by auto
  have t_in: "t \<in> {r - \<delta>0<..<r + \<delta>0}"
    using \<delta>_le dist_real_def tb by force
  show "\<bar>f s - f t\<bar> < (1 - \<epsilon>) * \<bar>s - t\<bar>"
  proof (cases "s < t")
    case True
    hence "t \<in> {s<..<r + \<delta>0}"
      using t_in by simp
    thus "\<bar>f s - f t\<bar> < (1 - \<epsilon>) * \<bar>s - t\<bar>"
      using order_bound s_in by blast
  next
    case False
    hence "t < s" 
      using s_neq by auto
    hence "s \<in> {t<..<r + \<delta>0}"
      using s_in by simp
    thus "\<bar>f s - f t\<bar> < (1 - \<epsilon>) * \<bar>s - t\<bar>"
      by (metis abs_minus_commute assms(1) t_in)     
  qed
qed

subsection \<open>Algorithm\<close>

zstore state = lvstore +
  x :: "real"
  fx :: "real"
  f'x :: "real"
  gx :: "real"
  x_new :: "real"
  itr :: "nat"
  Break :: "nat"

program fixed_point_iter "(f :: real \<Rightarrow> real, x\<^sub>0 :: real, tol :: real, max_iter :: nat)" over state
  = "x := x\<^sub>0; x_new := f x; itr := 0; Break :=0;
  while (itr < max_iter \<and> Break = 0)
    invariant itr \<le> max_iter
 \<and> x            = (f ^^ itr) x\<^sub>0
 \<and> x_new        = f x
 \<and> (Break \<noteq> 0 \<longrightarrow> \<bar>x_new - x\<bar> < tol)           
  variant max_iter - itr
  do
    if \<bar>x_new - x\<bar> < tol then Break := 1
    fi;
    x := x_new; x_new := f x; itr := itr + 1
  od"

execute "fixed_point_iter(\<lambda> x. x*x, 0.5, 0.1, 100)"
\<comment> \<open>This program terminates after 3 iterations with an estimate of the fixed point \(0\),
     namely \(0.0000152587890625\), when starting from \(0.5\), within an error tolerance
     of \(0.1\).\<close>

subsection \<open>Total Correctness Proofs\<close>

\<comment> \<open>This next lemma captures the standard local contraction argument behind fixed-point
   iteration. Under the assumptions (a fixed point \(f\,r = r\), a local
   contraction with constant \(0 \le c < 1\) on the ball \(\{x \mid |x-r| < \delta\}\),
   and an initial point \(x_0\) inside that ball), the Hoare triple asserts the
   quantitative error bound
   \[
     |x - r| \;\le\; c^{\mathit{itr}}\,|x_0 - r|
   \]
   at the end of the program. Intuitively, setting \(t = r\) in the contractive
   hypothesis yields \(|f(s) - r| \le c\,|s - r|\), so each iteration shrinks the
   distance to \(r\) by a factor \(c\); an \(itr\)-step induction gives the stated
   geometric rate.

   The result is *local*: no global properties of \(f\) are required—only
   contractivity in a neighborhood of \(r\). In particular, the bound also
   implies that all iterates remain inside the \(\delta\)-ball around \(r\),
   since \( |x_k - r| \le c^k |x_0 - r| < |x_0 - r| < \delta\).\<close>

lemma fixed_point_iter_error_bound_local:
  fixes f       :: "real \<Rightarrow> real"
    and r x\<^sub>0  c \<delta> :: real
    and max_iter :: nat
  assumes c_nonneg:    "0 \<le> c"
    and c_strict:      "c < 1"
    and \<delta>_pos:         "\<delta> > 0"
    and r_is_fixed:    "f r = r"
    and x0_in_ball:    "\<bar>r - x\<^sub>0\<bar> < \<delta>"
    and contractive:   "\<forall>s t. \<bar>s - r\<bar> < \<delta> \<and> \<bar>t - r\<bar> < \<delta> \<longrightarrow> \<bar>f s - f t\<bar> \<le> c * \<bar>s - t\<bar>"
  shows 
    "H[True] fixed_point_iter (f, x\<^sub>0, tol, max_iter)[\<bar>x - r\<bar> \<le> c^itr *\<bar>x\<^sub>0 - r\<bar> \<and> (itr \<le> max_iter)]"
proof(vcg)
  fix itr :: nat
  assume step_small: "\<bar>f ((f ^^ itr) x\<^sub>0) - (f ^^ itr) x\<^sub>0\<bar> < tol"
     and below_max:  "itr < max_iter"
 
  from assms have t_in_ball: "\<bar>(f ^^ itr) x\<^sub>0 - r\<bar> < \<delta>"
    by (subst contraction_ball_closure, simp_all)
  then have s_in_ball: "\<bar>f ((f ^^ itr) x\<^sub>0) - r\<bar> < \<delta>"
    by (smt (verit) assms(4,6) c_strict mult_less_cancel_right2)
  
  have step_bound:
    "\<bar>f (f ((f ^^ itr) x\<^sub>0)) - f ((f ^^ itr) x\<^sub>0)\<bar> \<le> c * \<bar>f ((f ^^ itr) x\<^sub>0) - (f ^^ itr) x\<^sub>0\<bar>"
    using contractive s_in_ball t_in_ball by presburger
  also have "... < tol"
    using c_strict
    by (smt (verit) mult_le_cancel_right2 step_small) 
  finally show "\<bar>f (f ((f ^^ itr) x\<^sub>0)) - f ((f ^^ itr) x\<^sub>0)\<bar> < tol".
  then show "\<bar>f (f ((f ^^ itr) x\<^sub>0)) - f ((f ^^ itr) x\<^sub>0)\<bar> < tol".  (*Get one goal for free*)
next     
  show "\<bar>(f ^^ max_iter) x\<^sub>0 - r\<bar> \<le> c ^ max_iter * \<bar>x\<^sub>0 - r\<bar>"
  proof (induction max_iter)
    show "\<bar>(f ^^ 0) x\<^sub>0 - r\<bar> \<le> c ^ 0 * \<bar>x\<^sub>0 - r\<bar>"
      by simp
  next
    case (Suc n)    
    have step: "\<bar>(f ^^ Suc n) x\<^sub>0 - r\<bar> = \<bar>f ((f ^^ n) x\<^sub>0) - r\<bar>"
      by simp
    also have "\<dots> = \<bar>f ((f ^^ n) x\<^sub>0) - f r\<bar>"
      using r_is_fixed by force
    also have "\<dots> \<le> c * \<bar>(f ^^ n) x\<^sub>0 - r\<bar>"
      by (smt (verit) Suc.IH assms(1,5,6) c_strict mult_left_le_one_le power_le_one zero_le_power)
    also have "\<dots> \<le> c * (c ^ n * \<bar>x\<^sub>0 - r\<bar>)"
      by (meson Suc.IH assms(1) mult_left_mono)
    also have "\<dots> = c ^ Suc n * \<bar>x\<^sub>0 - r\<bar>"
      by simp
    finally show ?case.
  qed
  then show "\<bar>(f ^^ max_iter) x\<^sub>0 - r\<bar> \<le> c ^ max_iter * \<bar>x\<^sub>0 - r\<bar>"
    by simp
next
  fix itr Break :: nat    
  show "\<bar>(f ^^ itr) x\<^sub>0 - r\<bar> \<le> c ^ itr * \<bar>x\<^sub>0 - r\<bar>"
  proof (induction itr)
    show "\<bar>(f ^^ 0) x\<^sub>0 - r\<bar> \<le> c ^ 0 * \<bar>x\<^sub>0 - r\<bar>"
      by simp
  next
    fix itr 
    assume IH: "\<bar>(f ^^ itr) x\<^sub>0 - r\<bar> \<le> c ^ itr * \<bar>x\<^sub>0 - r\<bar>"   
    have "\<bar>(f ^^ Suc itr) x\<^sub>0 - r\<bar> = \<bar>f ((f ^^ itr) x\<^sub>0) - r\<bar>"
      by simp
    also have "... = \<bar>f ((f ^^ itr) x\<^sub>0) - f r\<bar>"
      using assms(4) by auto
    also have "... \<le> c * \<bar>(f ^^ itr) x\<^sub>0 - r\<bar>"
      by (smt (verit, best) IH assms(1,5,6) c_strict mult_left_le_one_le power_le_one zero_le_power)
    also have "... \<le> c * \<bar>(c ^ itr * \<bar>x\<^sub>0 - r\<bar>)\<bar>"
      using IH c_nonneg by (simp add: mult_mono)
    also have "... \<le> c ^ Suc itr * \<bar>x\<^sub>0 - r\<bar>"
      by (simp add: assms(1))
    finally show "\<bar>(f ^^ Suc itr) x\<^sub>0 - r\<bar> \<le> c ^ Suc itr * \<bar>x\<^sub>0 - r\<bar>".
  qed
qed

\<comment> \<open>This is a local Banach–type contraction statement. Since \(f \in C^{1}(U)\) and
\(|\mathrm{deriv}\,f\,r|<1\), continuity of \(\mathrm{deriv}\,f\) yields \(\varepsilon>0\) and
\(\delta>0\) with \(|\mathrm{deriv}\,f\,x|\le 1-\varepsilon\) whenever \(|x-r|<\delta\).
By the mean-value theorem, this uniform bound implies the local Lipschitz estimate
\(|f(s)-f(t)|\le(1-\varepsilon)\,|s-t|\) for all \(s,t\) with \(|s-r|,|t-r|<\delta\).

Instantiating the generic contraction error lemma with \(c=1-\varepsilon\) yields the geometric decay
\[
  |x-r|\;\le\;(1-\varepsilon)^{\mathit{itr}}\;|x_{0}-r|
\]
at loop exit, uniformly for every start \(x_{0}\) in the \(\delta\)-ball around \(r\).\<close>

lemma fixed_point_iter_error_bound_C1:
  fixes f    :: "real \<Rightarrow> real"
    and r tol :: real
    and max_iter :: nat
  assumes r_fixed   : "f r = r"
      and r_in_U    : "r \<in> U"
      and cont_deriv: "C_k_on 1 f U"    
      and f_strict  : "\<bar>deriv f r\<bar> < 1"
  shows
    "\<exists>(\<delta> :: real)>0. \<exists>(\<epsilon> :: real)>0.       
        (\<forall>(x\<^sub>0 :: real). \<bar>r - x\<^sub>0\<bar> < \<delta> \<longrightarrow>
           H[True] fixed_point_iter (f, x\<^sub>0, tol, max_iter)
             [\<bar>x - r\<bar> \<le> (1 - \<epsilon>) ^ itr * \<bar>x\<^sub>0 - r\<bar> \<and> (itr \<le> max_iter)])"
proof -
  \<comment> \<open>Obtain \(\varepsilon>0\) and \(\delta>0\) from the derivative bound to get a local contraction.\<close>
  obtain \<epsilon> \<delta> where
      \<epsilon>_pos: "0 < \<epsilon>"
    and \<epsilon>_lt  :  "\<epsilon> < 1"
    and \<delta>_pos  : "\<delta> > 0"
    and subset : "{r - \<delta><..<r + \<delta>} \<subseteq> U"
    and lip    : "\<forall>x y. x \<in> {r-\<delta><..<r+\<delta>} \<longrightarrow> y \<in> {x<..<r+\<delta>}
                       \<longrightarrow> \<bar>f x - f y\<bar> < (1 - \<epsilon>) * \<bar>x - y\<bar>"
    by (meson assms(2,4) cont_deriv contractive_deriv_imp_contra)


  \<comment> \<open>Instantiate \(\delta\) for the outer existential.\<close>
  show "\<exists>\<delta>>0. (\<exists>\<epsilon>>0. (\<forall>x\<^sub>0. \<bar>r - x\<^sub>0\<bar> < \<delta> \<longrightarrow>
                      H[True] fixed_point_iter (f, x\<^sub>0, tol, max_iter)
                        [\<bar>x - r\<bar> \<le> (1 - \<epsilon>) ^ itr * \<bar>x\<^sub>0 - r\<bar> \<and> (itr \<le> max_iter)]))"
  proof (intro exI[where x=\<delta>], intro conjI insert \<delta>_pos)
    show "\<exists>\<epsilon>>0. \<forall>x\<^sub>0. \<bar>r - x\<^sub>0\<bar> < \<delta> \<longrightarrow> H[True] fixed_point_iter (f, x\<^sub>0, tol, max_iter) [\<bar>x - r\<bar> \<le> (1 - \<epsilon>) ^ itr * \<bar>x\<^sub>0 - r\<bar> \<and> (itr \<le> max_iter)]"
    proof (intro exI[where x=\<epsilon>], intro conjI insert \<epsilon>_pos, clarify)
      fix x\<^sub>0 :: real
      assume sufficiently_close: "\<bar>r - x\<^sub>0\<bar> < \<delta>"      
      with assms(1-3) \<delta>_pos show
        "H[True] fixed_point_iter (f, x\<^sub>0, tol, max_iter)
           [\<bar>x - r\<bar> \<le> (1 - \<epsilon>) ^ itr * \<bar>x\<^sub>0 - r\<bar> \<and> (itr \<le> max_iter)]"
      proof (subst fixed_point_iter_error_bound_local[where \<delta> = \<delta>], safe)
        show "0 \<le> 1 - \<epsilon>"
          using \<epsilon>_lt by auto
        show "1 - \<epsilon> < 1"
          using \<epsilon>_pos by auto        
      next
        \<comment>\<open>Prove the Lipschitz bound for arbitrary \(s, t\) in the \(\delta\)-ball.\<close>

        fix s t
        assume  a1: "\<bar>s - r\<bar> < \<delta>" and a2: "\<bar>t - r\<bar> < \<delta>"
         
        have s_dist: "s \<in> {r - \<delta><..<r + \<delta>}"
          using a1 dist_real_def by auto
        have t_dist: "t \<in> {r - \<delta><..<r + \<delta>}"
          using a2 dist_real_def by auto
  
        show "\<bar>f s - f t\<bar> \<le> (1 - \<epsilon>) * \<bar>s - t\<bar>"
        proof (cases "t < s")
          show "\<lbrakk>t < s\<rbrakk> \<Longrightarrow> \<bar>f s - f t\<bar> \<le> (1 - \<epsilon>) * \<bar>s - t\<bar>"
            by (metis abs_minus_commute greaterThanLessThan_iff less_eq_real_def lip s_dist t_dist)
          show "\<lbrakk>\<not> t < s\<rbrakk> \<Longrightarrow> \<bar>f s - f t\<bar> \<le> (1 - \<epsilon>) * \<bar>s - t\<bar>"
            by (metis abs_0 cancel_comm_monoid_add_class.diff_cancel greaterThanLessThan_iff 
                lip mult.commute mult_zero_left not_less_iff_gr_or_eq s_dist t_dist verit_comp_simplify1(3))
        qed
      qed
    qed
  qed
qed

\<comment> \<open>Quadratic error decay near a fixed point.
Assume \(f(r)=r\), \(f \in C^{1}(U)\), \(f'(r)=0\), and \(f\) is twice differentiable at \(r\).
Then there exist \(\delta>0\) and \(\varepsilon>0\) such that, for all starts \(x_{0}\) with
\(|x_{0}-r|<\delta\), the iteration satisfies the bound
\[
  |x-r|\;\le\;\Bigl(\tfrac{|f''(r)|+\varepsilon}{2}\Bigr)^{\,2^{\mathit{itr}}-1}\,|x_{0}-r|^{\,2^{\mathit{itr}}}.
\]
This is the hallmark of quadratic convergence: each step (locally) squares the error up to a
uniform constant depending on \(f''(r)\). The parameter \(\varepsilon>0\) accounts for the
local nature of the estimate and can be made arbitrarily small by shrinking the neighborhood.
Our proof invokes the Peano form of Taylor’s theorem near \(r\), yielding
\(f(x)-r=\tfrac12 f''(r)(x-r)^2+o\!\left((x-r)^2\right)\), from which the stated bound follows.\<close>

lemma fixed_point_iter_quadratic_convergence_case:
  fixes f        :: "real \<Rightarrow> real"
    and r        :: real
    and max_iter  :: nat
  assumes r_fixed   : "f r = r"
      and r_in_U    : "r \<in> U"
      and cont_deriv: "C_k_on 1 f U"      
      and der0     : "deriv f r = 0"     
      and twice_dff: "f twice_differentiable_at r"
  shows
    "\<exists>(\<delta> :: real)>0. \<exists>(\<epsilon> :: real)>0.           
      (\<forall>x\<^sub>0. \<bar>r - x\<^sub>0\<bar> < \<delta> \<longrightarrow>
       H[True] fixed_point_iter (f,x\<^sub>0, tol, max_iter)
       [\<bar>x - r\<bar> \<le> (((\<bar>deriv (deriv f) r\<bar> + \<epsilon>)/2)^(2^itr-1))* \<bar>x\<^sub>0 - r\<bar>^(2^itr) \<and> (itr \<le> max_iter)])"
proof - 
  obtain \<epsilon> \<delta>0 where
      \<epsilon>_pos: "0 < \<epsilon>" 
    and \<epsilon>_lt: "\<epsilon> < 1"
    and \<delta>0_pos  : "\<delta>0 > 0"
    and subset : "{r - \<delta>0<..<r + \<delta>0} \<subseteq> U"
    and lip    : "\<forall>x y. x \<in> {r-\<delta>0<..<r+\<delta>0} \<longrightarrow> y \<in> {x<..<r+\<delta>0}
                       \<longrightarrow> \<bar>f x - f y\<bar> < (1 - \<epsilon>) * \<bar>x - y\<bar>"
    by (metis abs_0 assms(2,4) cont_deriv contractive_deriv_imp_contra zero_less_one)

  \<comment> \<open>Here we apply Taylor’s theorem with Peano remainder at \(r\): \<close>
  have "(\<lambda>x. peano_remainder (Suc 1) f r x / (x - r) ^ Suc 1) \<midarrow>r\<rightarrow> 0"
    by(rule Taylor_Peano, smt Suc_1 assms(5))
  then have "(\<lambda>x. (f x - (\<Sum>i\<le>2. Nth_derivative i f r / fact i * (x - r) ^ i)) / (x - r) ^ 2) \<midarrow>r\<rightarrow> 0"
    unfolding peano_remainder_def taylor_poly_def
    by (metis Suc_1) 
  then have "(\<forall>\<epsilon>>0. \<exists>\<delta>>0. \<forall>y. y \<noteq> r \<and> \<bar>y - r\<bar> < \<delta> \<longrightarrow> 
  \<bar>(\<lambda>x. (f x - (\<Sum>m\<le>2. Nth_derivative m f r / fact m * (x - r) ^ m)) / (x - r) ^ 2) y - 0\<bar> < \<epsilon>)"
    using tendsto_at_x_epsilon_def by simp
  then obtain \<delta>1 where \<delta>1_pos: "\<delta>1 > 0"
  and r0_prop:
    "\<And>x. x \<noteq> r \<Longrightarrow> \<bar>x - r\<bar> < \<delta>1 \<longrightarrow>
         \<bar>(f x - (\<Sum>m\<le>2. Nth_derivative m f r / fact m * (x - r)^m)) / (x - r)^2\<bar> < \<epsilon> / 2"
    using \<epsilon>_pos by (smt (verit, del_insts) half_gt_zero)

  then obtain h :: "real \<Rightarrow> real" where h_def: "h = (\<lambda> x. (f x - (\<Sum>m\<le>2. Nth_derivative m f r / fact m * (x - r)^m)) / (x - r)^2)"
      and h_bound: "\<And>x. x \<noteq> r \<Longrightarrow> \<bar>x - r\<bar> < \<delta>1 \<longrightarrow> \<bar>h x\<bar> < \<epsilon> / 2"
    by presburger

  obtain \<delta> where \<delta>_def: "\<delta> = min \<delta>0 \<delta>1"
    by blast
  then have \<delta>_pos: "0 < \<delta>" and \<delta>_leq_\<delta>0: "\<delta> \<le> \<delta>0" and \<delta>_leq_\<delta>1: "\<delta> \<le> \<delta>1"
    using \<delta>0_pos \<delta>1_pos by linarith+

  from lip have contraction: "\<forall>s t. s \<noteq> t \<longrightarrow> \<bar>s - r\<bar> < \<delta> \<longrightarrow> \<bar>t - r\<bar> < \<delta> \<longrightarrow> \<bar>f s - f t\<bar> < (1 - \<epsilon>) * \<bar>s - t\<bar>"
    by(rule contraction_ball_closure', (simp add: \<epsilon>_pos \<delta>_pos \<delta>_leq_\<delta>0)+)

  show "\<exists>\<delta>>0. \<exists>\<epsilon>>0. \<forall>x\<^sub>0. \<bar>r - x\<^sub>0\<bar> < \<delta> \<longrightarrow> H[True] fixed_point_iter (f, x\<^sub>0, tol, max_iter) 
                      [\<bar>x - r\<bar> \<le> ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) ^ (2 ^ itr - 1) * \<bar>x\<^sub>0 - r\<bar> ^ 2 ^ itr \<and> itr \<le> max_iter]"
  proof(intro exI[where x=\<delta>], intro conjI insert \<delta>_pos)
    show "\<exists>\<epsilon>>0. \<forall>x\<^sub>0. \<bar>r - x\<^sub>0\<bar> < \<delta> \<longrightarrow> H[True] fixed_point_iter (f, x\<^sub>0, tol, max_iter) 
                [\<bar>x - r\<bar> \<le> ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) ^ (2 ^ itr - 1) * \<bar>x\<^sub>0 - r\<bar> ^ 2 ^ itr \<and> itr \<le> max_iter]"
    proof(intro exI[where x=\<epsilon>], intro conjI insert \<epsilon>_pos, clarify)
      fix x\<^sub>0 :: real
      assume sufficiently_close: "\<bar>r - x\<^sub>0\<bar> < \<delta>"

      have contractive_iterates: "\<forall> (Itr :: nat). \<bar>(f ^^ Itr) x\<^sub>0 - r\<bar> < \<delta>"
      proof clarify
        fix Itr
        show "\<bar>(f ^^ Itr) x\<^sub>0 - r\<bar> < \<delta>"
        proof(subst contraction_ball_closure[where c = "(1 - \<epsilon>)"])
          show "f r = r"
            by (simp add: assms(1))
          show "0 \<le> 1 - \<epsilon> \<and> 1 - \<epsilon> < 1"
            using \<epsilon>_lt \<epsilon>_pos by auto
          show "\<bar>x\<^sub>0 - r\<bar> < \<delta>" and True
            using sufficiently_close by auto
          show "\<forall>s t. \<bar>s - r\<bar> < \<delta> \<longrightarrow> \<bar>t - r\<bar> < \<delta> \<longrightarrow> \<bar>f s - f t\<bar> \<le> (1 - \<epsilon>) * \<bar>s - t\<bar>"
            by (metis abs_0 cancel_comm_monoid_add_class.diff_cancel contraction less_eq_real_def mult.commute mult_zero_left)
        qed
      qed
         
      show " H[True] fixed_point_iter (f, x\<^sub>0, tol, max_iter) 
               [\<bar>x - r\<bar> \<le> ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) ^ (2 ^ itr - 1) * \<bar>x\<^sub>0 - r\<bar> ^ 2 ^ itr \<and> itr \<le> max_iter]"
      proof(vcg)
        fix itr :: nat
        assume step_small: "\<bar>f ((f ^^ itr) x\<^sub>0) - (f ^^ itr) x\<^sub>0\<bar> < tol"
           and below_max:  "itr < max_iter"
        then have "\<bar>f ((f ^^ itr) x\<^sub>0) - r\<bar> < \<delta>"
          by (metis contractive_iterates funpow.simps(2) o_apply)
        then have step_bound:
          "\<bar>f (f ((f ^^ itr) x\<^sub>0)) - f ((f ^^ itr) x\<^sub>0)\<bar> \<le> (1 - \<epsilon>) * \<bar>f ((f ^^ itr) x\<^sub>0) - (f ^^ itr) x\<^sub>0\<bar>"
          by (metis abs_0 arith_simps(63) contraction diff_self less_eq_real_def contractive_iterates)
        also have "... < tol"
          by (smt (verit, best) \<epsilon>_lt \<epsilon>_pos mult_left_le_one_le step_small)
        finally show "\<bar>f (f ((f ^^ itr) x\<^sub>0)) - f ((f ^^ itr) x\<^sub>0)\<bar> < tol".
        then show "\<bar>f (f ((f ^^ itr) x\<^sub>0)) - f ((f ^^ itr) x\<^sub>0)\<bar> < tol".  (*Get one goal for free*)
      next  
        have one_step:
          "\<forall>(x::real). \<bar>x - r\<bar> < \<delta> \<longrightarrow>  \<bar>f x - r\<bar> \<le> ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) * \<bar>x - r\<bar>^2"
        proof(clarify)
          fix x :: real
          assume delta_close: "\<bar>x - r\<bar> < \<delta>"
          then have h_bnd:"\<bar>h x\<bar> < \<epsilon> / 2"
            by (smt (verit, del_insts) h_bound \<delta>_leq_\<delta>1 \<epsilon>_pos division_ring_divide_zero  h_def half_gt_zero mult_cancel_left2 power2_eq_square)

          show "\<bar>f x - r\<bar> \<le> (\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2 * \<bar>x - r\<bar>\<^sup>2"
          proof(cases "x = r")
            show " \<lbrakk>x = r\<rbrakk> \<Longrightarrow> \<bar>f x - r\<bar> \<le> (\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2 * \<bar>x - r\<bar>\<^sup>2"
              by (simp add: assms(1))
          next
            assume x_neq_r: "x \<noteq> r"
            then have pos_dist: "0 < \<bar>x - r\<bar>"
              by auto

            have taylor_snd_order:
              "f = (\<lambda>x.
                    f r
                  + ((deriv (deriv f) r) / 2) * (x - r)^2
                  + (x - r)^2 * h x)"            
            proof -   
              have f_eq: "f = (\<lambda>x. (\<Sum> m \<le> 2. Nth_derivative m f r / fact m * (x - r)^m) + (x - r)^2 * h x)"
                by (auto simp: h_def fun_eq_iff)   
              then have "f  = 
                     (\<lambda> x.(\<Sum> m \<le> 1. Nth_derivative m f r / fact m * (x - r)^m)
                                  + (Nth_derivative 2 f r / fact 2 * (x - r)^2)
                                  + (x - r)^2 * h x)"
                by (metis (no_types, lifting) Suc_1 sum.atMost_Suc)
              also have "... =
                    (\<lambda> x.            (Nth_derivative 0 f r / fact 0 * (x - r)^0)
                                   + (Nth_derivative 1 f r / fact 1 * (x - r)^1)
                                   + (Nth_derivative 2 f r / fact 2 * (x - r)^2)
                                   + (x - r)^2 * h x)"
                by simp
              also have "... =
                    (\<lambda> x.            (f r)
                                   + (deriv f r  * (x - r))
                                   + ((deriv (deriv f) r) /  2 * (x - r)^2)
                                   + (x - r)^2 * h x)"
                using second_derivative_alt_def by auto
              also have "... =
                    (\<lambda> x.            (f r)                                
                                   + ((deriv (deriv f) r) /  2 * (x - r)^2)
                                   + (x - r)^2 * h x)"
                by (simp add: assms(4))
              finally show ?thesis.
            qed
            then have "f x - r = ((deriv (deriv f) r) / 2 + h x) * (x - r)^2"
              by (smt (verit, best) Groups.mult_ac(2) assms(1) right_diff_distrib')            
            then have abs_fx: "\<bar>f x - r\<bar> = \<bar>(deriv (deriv f) r) / 2 + h x\<bar> * \<bar>x - r\<bar>^2"
              by (simp add: abs_mult)
            also have "... \<le> (\<bar>deriv (deriv f) r\<bar> / 2 + \<bar>h x\<bar>)  * \<bar>x - r\<bar>^2"
              by (simp add: mult_right_mono)
            also have "... \<le> (\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2 * \<bar>x - r\<bar>\<^sup>2"
              using h_bnd pos_dist by auto
            finally show ?thesis.
          qed              
        qed
  
        have Inductive_Step: "\<forall> (Itr :: nat). \<bar>(f ^^ Itr) x\<^sub>0 - r\<bar> \<le> ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) ^ (2 ^ Itr - Suc 0) * \<bar>x\<^sub>0 - r\<bar> ^ 2 ^ Itr"
        proof(clarify)
          fix Itr :: nat
          show "\<bar>(f ^^ Itr) x\<^sub>0 - r\<bar> \<le> ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) ^ (2 ^ Itr - Suc 0) * \<bar>x\<^sub>0 - r\<bar> ^ 2 ^ Itr"
          proof(induct Itr)
            show "\<bar>(f ^^ 0) x\<^sub>0 - r\<bar> \<le> ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) ^ (2 ^ 0 - Suc 0) * \<bar>x\<^sub>0 - r\<bar> ^ 2 ^ 0"
              by simp
          next
            fix Itr
            assume IH:  "\<bar>(f ^^ Itr) x\<^sub>0 - r\<bar> \<le> ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) ^ (2 ^ Itr - Suc 0) * \<bar>x\<^sub>0 - r\<bar> ^ 2 ^ Itr"  
            have step_eq: "\<bar>(f ^^ Suc Itr) x\<^sub>0 - r\<bar> = \<bar>f ((f ^^ Itr) x\<^sub>0) - r\<bar>"
              by simp
            also have "\<dots> \<le> ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) * \<bar>(f ^^ Itr) x\<^sub>0 - r\<bar>^2"
              using one_step contractive_iterates
              by blast  
            also have "\<dots> \<le> ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2)
                       * ( ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) ^ (2 ^ Itr - Suc 0)
                       * \<bar>x\<^sub>0 - r\<bar> ^ (2 ^ Itr) ) ^ 2"
              by (smt (z3) IH \<epsilon>_pos field_sum_of_halves mult_left_mono power_less_imp_less_base)
            also have "\<dots> = ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) ^ (1 + 2 * (2 ^ Itr - Suc 0))
                       * \<bar>x\<^sub>0 - r\<bar> ^ (2 * (2 ^ Itr))"
              by (simp add: power_even_eq power_mult_distrib)
            ultimately show "\<bar>(f ^^ Suc Itr) x\<^sub>0 - r\<bar> \<le> ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) ^ (2 ^ Suc Itr - Suc 0) * \<bar>x\<^sub>0 - r\<bar> ^ 2 ^ Suc Itr"
              by (smt (verit, ccfv_SIG) Suc_1 Suc_pred bot_nat_0.not_eq_extremum diff_diff_left
                  nat.discI nat.simps(1) nat_power_eq_Suc_0_iff plus_1_eq_Suc power_Suc0_right 
                  power_add power_eq_0_iff power_eq_if right_diff_distrib')
          qed
        qed
        then show "\<bar>(f ^^ max_iter) x\<^sub>0 - r\<bar> \<le> ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) ^ (2 ^ max_iter - Suc 0) * \<bar>x\<^sub>0 - r\<bar> ^ 2 ^ max_iter"
          by blast
        then show "\<bar>(f ^^ max_iter) x\<^sub>0 - r\<bar> \<le> ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) ^ (2 ^ max_iter - Suc 0) * \<bar>x\<^sub>0 - r\<bar> ^ 2 ^ max_iter"
          by blast
        show "\<And>itr Break. \<lbrakk>itr \<le> max_iter; 0 < Break; \<bar>f ((f ^^ itr) x\<^sub>0) - (f ^^ itr) x\<^sub>0\<bar> < tol\<rbrakk>  \<Longrightarrow> \<bar>(f ^^ itr) x\<^sub>0 - r\<bar> \<le> ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) ^ (2 ^ itr - Suc 0) * \<bar>x\<^sub>0 - r\<bar> ^ 2 ^ itr"
          using Inductive_Step by blast
      qed
    qed
  qed
qed

end