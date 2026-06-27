section \<open>Vector calculus: gradient, Hessian, Jacobian\<close>

theory Vector_Calculus
  imports Smooth_Manifolds.Smooth
begin

text \<open>Transfer a Fréchet derivative across functions agreeing on an open set
  (a 2-line wrapper around HOL-Analysis @{thm has_derivative_transform}).\<close>

lemma has_derivative_transfer_on_open:
  assumes "open X" and "x \<in> X"
  assumes eq_on_X: "\<forall>x\<in>X. f x = g x"
  assumes f_has_deriv: "(f has_derivative f') (at x)"
  shows "(g has_derivative f') (at x)"
  using at_within_open_subset[OF _ \<open>open X\<close>, of _ X, simplified]
  by (metis \<open>x \<in> X\<close> f_has_deriv eq_on_X has_derivative_transform)

(* ================================================================== *)
subsection \<open>Gradient for \<open>real\<^sup>n \<Rightarrow> real\<close>\<close>
(* ================================================================== *)

definition has_gradient ::
    "(real^'n::finite \<Rightarrow> real) \<Rightarrow> real^'n \<Rightarrow> real^'n \<Rightarrow> bool"
    ("(GRAD (_)/ (_)/ :> (_))" [1000,1000,60] 60)
  where "GRAD f x :> g \<longleftrightarrow> (f has_derivative (\<lambda>v. v \<bullet> g)) (at x)"


lemma gradient_unique:
  "GRAD f x :> g \<Longrightarrow> GRAD f x :> g' \<Longrightarrow> g = g'"
  unfolding has_gradient_def
  by (metis has_derivative_unique vector_eq_ldot)


definition grad_fun :: "(real^'n::finite \<Rightarrow> real) \<Rightarrow> real^'n \<Rightarrow> real^'n"
  ("\<nabla>")
  where "\<nabla> f x = (THE g :: real^'n. GRAD f x :> g)"


lemma grad_fun_eq:
  assumes "GRAD f x :> g"
  shows "\<nabla> f x = g"
  unfolding grad_fun_def using assms gradient_unique
  by (metis the_equality)


lemma grad_fun_satisfies_GRAD:
  assumes "GRAD f x :> g"
  shows "GRAD f x :> \<nabla> f x"
  using assms grad_fun_eq by blast


lemma has_derivative_to_gradient:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes "(f has_derivative L) (at x)"
  shows "GRAD f x :> (\<Sum>i\<in>UNIV. L (axis i 1) *\<^sub>R axis i 1)"
proof -
  let ?g = "(\<Sum>i\<in>UNIV. L (axis i 1) *\<^sub>R axis i 1)"

  have bl: "bounded_linear L"
    using assms by (rule has_derivative_bounded_linear)

  have L_eq: "L = (\<lambda>v. v \<bullet> ?g)"
  proof
    fix v :: "real^'n"
    have v_exp: "v = (\<Sum>i\<in>UNIV. (v $ i) *\<^sub>R axis i 1)"
      by (metis (no_types) basis_expansion scalar_mult_eq_scaleR)
    then have "L v = L (\<Sum>i\<in>UNIV. (v $ i) *\<^sub>R axis i 1)"
      by simp
    also have "... = (\<Sum>i\<in>UNIV. L ((v $ i) *\<^sub>R axis i 1))"
      using bl bounded_linear.linear linear_sum by blast
    also have "... = (\<Sum>i\<in>UNIV. (v $ i) * L (axis i 1))"
      by (simp add: bl linear_simps(5))
    also have "... = v \<bullet> ?g"
      by (smt (verit, ccfv_SIG) Finite_Cartesian_Product.sum_cong_aux inner_axis 
          inner_commute inner_real_def inner_scaleR_right inner_sum_right real_inner_1_right)
    finally show "L v = v \<bullet> ?g".
  qed
  have "(f has_derivative (\<lambda>v. v \<bullet> ?g)) (at x)"
    using assms L_eq by simp
  then show ?thesis
    unfolding has_gradient_def.
qed


lemma Fr_diff_imp_gradient_exists:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes "f differentiable (at x)"
  shows "\<exists>g. GRAD f x :> g"
  using assms unfolding differentiable_def by (blast intro: has_derivative_to_gradient)


(* ================================================================== *)
subsection \<open>Hessian for \<open>real\<^sup>n \<Rightarrow> real\<close>\<close>
(* ================================================================== *)

text \<open>
  The (1-d) second derivative predicate, retained for backward compatibility
  with the 1-d theory.
\<close>


definition has_hessian_at :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool"
    ("(HDERIV (_)/ (_)/ :> (_))" [1000, 1000, 60] 60)
  where "HDERIV f x :> H \<longleftrightarrow> (deriv f has_derivative (\<lambda>h. h * H)) (at x)"

text \<open>
  The multi-dimensional Hessian: the Fréchet derivative of the gradient,
  represented as a matrix.
\<close>


definition has_hessian ::
    "(real^'n::finite \<Rightarrow> real) \<Rightarrow> real^'n \<Rightarrow> real^'n^'n \<Rightarrow> bool"
    ("(HESS (_)/ (_)/ :> (_))" [1000, 1000, 60] 60)
  where "HESS f x :> H \<longleftrightarrow> (\<nabla> f has_derivative (\<lambda>v. H *v v)) (at x)"


lemma hessian_unique:
  "HESS f x :> H \<Longrightarrow> HESS f x :> H' \<Longrightarrow> H = H'"
  unfolding has_hessian_def
  by (metis has_derivative_unique matrix_eq)


definition hess_fun :: "(real^'n::finite \<Rightarrow> real) \<Rightarrow> real^'n \<Rightarrow> real^'n^'n"
  ("\<nabla>\<^sup>2")
  where "\<nabla>\<^sup>2 f x = (THE H :: real^'n^'n. HESS f x :> H)"


lemma hess_fun_eq:
  assumes "HESS f x :> H"
  shows "\<nabla>\<^sup>2 f x = H"
  unfolding hess_fun_def using assms hessian_unique
  by (metis the_equality)


lemma hessian_eq_jacobian_of_gradient:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes "HESS f x :> H"
  shows "H = matrix (frechet_derivative (\<nabla> f) (at x))"
  by (metis assms frechet_derivative_at' has_hessian_def matrix_of_matrix_vector_mul)

text \<open>
  The Hessian entries are iterated partial derivatives:
  \<open>(\<nabla>\<^sup>2 f x) $ i $ j = \<partial>\<^sub>j (\<partial>\<^sub>i f) (x)\<close>.
\<close>


lemma hessian_eq_double_nabla:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes "HESS f x :> \<nabla>\<^sup>2 f x"
  shows "\<forall>i j. \<nabla>\<^sup>2 f x $ i $ j = (\<nabla> (\<lambda>y. \<nabla> f y $ i)) x $ j"
proof (intro allI)
  fix i j
  have row_grad: "GRAD (\<lambda>y. \<nabla> f y $ i) x :> (\<nabla>\<^sup>2 f x) $ i"
  proof -
    have H: "(\<nabla> f has_derivative (*v) (\<nabla>\<^sup>2 f x)) (at x)"
      using assms unfolding has_hessian_def by simp
    have Hcomp: "((\<lambda>y. \<nabla> f y \<bullet> axis i 1) has_derivative
         (\<lambda>v. ((*v) (\<nabla>\<^sup>2 f x)) v \<bullet> axis i 1)) (at x within UNIV)"
      using H by (subst (asm) has_derivative_componentwise_within[where S = UNIV],
                  auto simp: Basis_vec_def)
    have comp_fun:  "(\<lambda>y. \<nabla> f y \<bullet> axis i 1) = (\<lambda>y. \<nabla> f y $ i)"
      by (rule ext, simp add: cart_eq_inner_axis)
    have comp_deriv: "(\<lambda>v. ((*v) (\<nabla>\<^sup>2 f x)) v \<bullet> axis i 1) = (\<lambda>v. v \<bullet> ((\<nabla>\<^sup>2 f x) $ i))"
      by (rule ext, simp add: inner_axis' inner_commute matrix_vector_mul_component) 
    from Hcomp show ?thesis
      unfolding has_gradient_def by (simp add: comp_fun comp_deriv)
  qed
  hence "\<nabla> (\<lambda>y. \<nabla> f y $ i) x = (\<nabla>\<^sup>2 f x) $ i"
    by (rule grad_fun_eq)
  then show "\<nabla>\<^sup>2 f x $ i $ j = (\<nabla> (\<lambda>y. \<nabla> f y $ i)) x $ j"
    by simp
qed


(* ================================================================== *)
subsection \<open>Connecting \<open>C\<^sup>k\<close> to the Hessian\<close>
(* ================================================================== *)

text \<open>
  These bridge lemmas connect the abstract \<open>C\<^sup>k\<close> notion to the concrete
  gradient/Hessian machinery.  They are the missing link in the existing
  development.
\<close>

lemma clairaut_scalar_R2:
  fixes \<Phi>  :: "real \<Rightarrow> real \<Rightarrow> real"
  fixes fx :: "real \<Rightarrow> real"
    and fy :: "real \<Rightarrow> real \<Rightarrow> (real \<Rightarrow>\<^sub>L real)"
  assumes fx:
    "((\<lambda>u. \<Phi> u y) has_derivative fx) (at x within X)"
  assumes fy:
    "\<And>u v. u \<in> X \<Longrightarrow> v \<in> Y \<Longrightarrow>
      ((\<lambda>v'. \<Phi> u v') has_derivative (blinfun_apply (fy u v))) (at v within Y)"
  assumes fy_cont:
    "continuous (at (x,y) within X \<times> Y) (\<lambda>(u,v). fy u v)"
  assumes yY: "y \<in> Y"
  assumes convY: "convex Y"
  shows
    "((\<lambda>p. \<Phi> (fst p) (snd p)) has_derivative
        (\<lambda>(tx,ty). fx tx + blinfun_apply (fy x y) ty))
      (at (x,y) within X \<times> Y)"
proof -
  have "((\<lambda>(x,y). \<Phi> x y) has_derivative
          (\<lambda>(tx,ty). fx tx + blinfun_apply (fy x y) ty))
        (at (x,y) within X \<times> Y)"
    by (rule has_derivative_partialsI[OF fx fy fy_cont yY convY])
  then show ?thesis
    by (simp add: case_prod_unfold)
qed


lemma clairaut_scalar_R2_mixed_eq:
  fixes \<Phi>  :: "real \<Rightarrow> real \<Rightarrow> real"
  fixes fx :: "real \<Rightarrow> real"
    and fy :: "real \<Rightarrow> real \<Rightarrow> (real \<Rightarrow>\<^sub>L real)"
    and gy :: "real \<Rightarrow> real"
    and gx :: "real \<Rightarrow> real \<Rightarrow> (real \<Rightarrow>\<^sub>L real)"
  assumes fx:
    "((\<lambda>u. \<Phi> u y) has_derivative fx) (at x within X)"
  assumes fy:
    "\<And>u v. u \<in> X \<Longrightarrow> v \<in> Y \<Longrightarrow>
      ((\<lambda>v'. \<Phi> u v') has_derivative (blinfun_apply (fy u v))) (at v within Y)"
  assumes fy_cont:
    "continuous (at (x,y) within X \<times> Y) (\<lambda>(u,v). fy u v)"
  assumes gy:
    "((\<lambda>v. \<Phi> x v) has_derivative gy) (at y within Y)"
  assumes gx:
    "\<And>v u. v \<in> Y \<Longrightarrow> u \<in> X \<Longrightarrow>
      ((\<lambda>u'. \<Phi> u' v) has_derivative (blinfun_apply (gx v u))) (at u within X)"
  assumes gx_cont:
    "continuous (at (y,x) within Y \<times> X) (\<lambda>(v,u). gx v u)"
  assumes xX: "x \<in> X" and yY: "y \<in> Y"
  assumes openX: "open X" and openY: "open Y"
  assumes convX: "convex X" and convY: "convex Y"
  shows
    "(\<lambda>(tx,ty). fx tx + blinfun_apply (fy x y) ty) =
     (\<lambda>(tx,ty). blinfun_apply (gx y x) tx + gy ty)"
proof -
  have D1:
    "((\<lambda>p. \<Phi> (fst p) (snd p)) has_derivative
        (\<lambda>(tx,ty). fx tx + blinfun_apply (fy x y) ty))
      (at (x,y) within X \<times> Y)"
    by (rule clairaut_scalar_R2[OF fx fy fy_cont yY convY])

  have Dswap:
    "((\<lambda>p. \<Phi> (snd p) (fst p)) has_derivative
        (\<lambda>(tv,tu). gy tv + blinfun_apply (gx y x) tu))
      (at (y,x) within Y \<times> X)"
  proof -
    have "((\<lambda>p. (\<lambda>v u. \<Phi> u v) (fst p) (snd p)) has_derivative
            (\<lambda>(tv,tu). gy tv + blinfun_apply (gx y x) tu))
          (at (y,x) within Y \<times> X)"
      by (rule clairaut_scalar_R2[
            where \<Phi> = "\<lambda>v u. \<Phi> u v"
              and fx = gy and fy = gx
              and x = y and X = Y and y = x and Y = X])
         (use gy gx gx_cont xX convX in auto)
    then show ?thesis
      by (simp add: case_prod_unfold)
  qed

  have bl_swap: "bounded_linear (\<lambda>(tx::real,ty::real). (ty,tx))"
    by (simp add: bounded_linear_Pair bounded_linear_fst bounded_linear_snd case_prod_unfold)

  have Dswap_map: "((\<lambda>(u::real,v::real). (v,u)) has_derivative (\<lambda>(tx,ty). (ty,tx)))
      (at (x,y) within X \<times> Y)"
    by (simp add: bl_swap bounded_linear_imp_has_derivative)
  have swap_image:
    "(\<lambda>(u::real,v::real). (v,u)) ` (X \<times> Y) = Y \<times> X"
    by auto

  have Dswap': "((\<lambda>p. \<Phi> (snd p) (fst p)) has_derivative
        (\<lambda>(tv,tu). gy tv + blinfun_apply (gx y x) tu))
      (at ((\<lambda>(u::real,v::real). (v,u)) (x,y))
          within ((\<lambda>(u::real,v::real). (v,u)) ` (X \<times> Y)))"
    using Dswap by (simp add: swap_image)

  have D2: "((\<lambda>p. \<Phi> (fst p) (snd p)) has_derivative
        (\<lambda>(tx,ty). blinfun_apply (gx y x) tx + gy ty))
      (at (x,y) within X \<times> Y)"
  proof -
    have "(((\<lambda>p. \<Phi> (snd p) (fst p)) \<circ> (\<lambda>(u::real,v::real). (v,u)))
            has_derivative
            ((\<lambda>(tv,tu). gy tv + blinfun_apply (gx y x) tu)
              \<circ> (\<lambda>(tx,ty). (ty,tx))))
          (at (x,y) within X \<times> Y)"
      by (rule diff_chain_within[OF Dswap_map Dswap'])
    then show ?thesis
      by (simp add: o_def case_prod_unfold ac_simps)
  qed

  have D1_at: "((\<lambda>p. \<Phi> (fst p) (snd p)) has_derivative
        (\<lambda>(tx,ty). fx tx + blinfun_apply (fy x y) ty)) (at (x,y))"
    by (metis (mono_tags, lifting) D1 SigmaI at_within_open openX openY open_Times xX yY)

  have D2_at: "((\<lambda>p. \<Phi> (fst p) (snd p)) has_derivative
        (\<lambda>(tx,ty). blinfun_apply (gx y x) tx + gy ty))  (at (x,y))"
    by (metis (lifting) D2 Sigma_cong at_within_open mem_Sigma_iff openX openY open_Times xX yY)    
  show ?thesis
    by (rule has_derivative_unique[OF D1_at D2_at])
qed


(* The rectangle argument:                                             *)
(*   \<Delta>(h,k) = f(x+h\<sqdot>eᵢ+k\<sqdot>eⱼ) - f(x+h\<sqdot>eᵢ) - f(x+k\<sqdot>eⱼ) + f(x)     *)
(*                                                                     *)
(*   By MVT in s then t:  \<Delta> = h\<sqdot>k\<sqdot>(\<nabla>²f z₁)$i$j                       *)
(*   By MVT in t then s:  \<Delta> = h\<sqdot>k\<sqdot>(\<nabla>²f z₂)$j$i                       *)
(*   where z₁,z₂ \<rightarrow> x as h,k \<rightarrow> 0.                                     *)
(*   By continuity of \<nabla>²f, both Hessian entries equal at x.           *)
(* ================================================================== *)


lemma GRAD_add:
  fixes f g :: "real^'n::finite \<Rightarrow> real"
  assumes Gf: "GRAD f x :> gf"
      and Gg: "GRAD g x :> gg"
  shows "GRAD (\<lambda>y. f y + g y) x :> gf + gg"
  using Gf Gg
  unfolding has_gradient_def
  by (auto intro!: derivative_eq_intros simp: inner_add_right)


lemma grad_fun_add:
  fixes f g :: "real^'n::finite \<Rightarrow> real"
  assumes "\<exists>gf. GRAD f x :> gf"
      and "\<exists>gg. GRAD g x :> gg"
  shows "\<nabla> (\<lambda>y. f y + g y) x = \<nabla> f x + \<nabla> g x"
proof -
  have Gf: "GRAD f x :> \<nabla> f x"
    using assms(1) by (blast intro: grad_fun_satisfies_GRAD)
  have Gg: "GRAD g x :> \<nabla> g x"
    using assms(2) by (blast intro: grad_fun_satisfies_GRAD)
  have "GRAD (\<lambda>y. f y + g y) x :> \<nabla> f x + \<nabla> g x"
    by (rule GRAD_add[OF Gf Gg])
  thus ?thesis
    by (rule grad_fun_eq)
qed


lemma GRAD_scaleR:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes Gf: "GRAD f x :> gf"
  shows "GRAD (\<lambda>y. c * f y) x :> c *\<^sub>R gf"
  using Gf
  unfolding has_gradient_def
  by (auto intro!: derivative_eq_intros simp: inner_commute)


lemma grad_fun_scaleR:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes "\<exists>gf. GRAD f x :> gf"
  shows "\<nabla> (\<lambda>y. c * f y) x = c *\<^sub>R \<nabla> f x"
proof -
  have Gf: "GRAD f x :> \<nabla> f x"
    using assms by (blast intro: grad_fun_satisfies_GRAD)
  have "GRAD (\<lambda>y. c * f y) x :> c *\<^sub>R \<nabla> f x"
    by (rule GRAD_scaleR[OF Gf])
  thus ?thesis
    by (rule grad_fun_eq)
qed


lemma GRAD_neg:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes Gf: "GRAD f x :> gf"
  shows "GRAD (\<lambda>y. - f y) x :> - gf"
proof -
  have "GRAD (\<lambda>y. (-1) * f y) x :> (-1) *\<^sub>R gf"
    by (rule GRAD_scaleR[OF Gf])
  thus ?thesis by simp
qed


lemma grad_fun_neg:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes "\<exists>gf. GRAD f x :> gf"
  shows "\<nabla> (\<lambda>y. - f y) x = - \<nabla> f x"
proof -
  have "\<nabla> (\<lambda>y. (-1) * f y) x = (-1) *\<^sub>R \<nabla> f x"
    by (rule grad_fun_scaleR[OF assms])
  thus ?thesis by simp
qed


lemma GRAD_sub:
  fixes f g :: "real^'n::finite \<Rightarrow> real"
  assumes Gf: "GRAD f x :> gf"
      and Gg: "GRAD g x :> gg"
  shows "GRAD (\<lambda>y. f y - g y) x :> gf - gg"
proof -
  have "GRAD (\<lambda>y. f y + (- g y)) x :> gf + (- gg)"
    by (rule GRAD_add[OF Gf GRAD_neg[OF Gg]])
  thus ?thesis by simp
qed


lemma grad_fun_sub:
  fixes f g :: "real^'n::finite \<Rightarrow> real"
  assumes "\<exists>gf. GRAD f x :> gf"
      and "\<exists>gg. GRAD g x :> gg"
  shows "\<nabla> (\<lambda>y. f y - g y) x = \<nabla> f x - \<nabla> g x"
proof -
  have "\<nabla> (\<lambda>y. f y + (- g y)) x = \<nabla> f x + \<nabla> (\<lambda>y. - g y) x"
    using assms grad_fun_add GRAD_neg by blast
  also have "\<nabla> (\<lambda>y. - g y) x = - \<nabla> g x"
    by (rule grad_fun_neg[OF assms(2)])
  finally show ?thesis by simp
qed


(* ================================================================== *)
subsection \<open>Constants and affine maps\<close>
(* ================================================================== *)


lemma GRAD_const:
  fixes c :: real
  shows "GRAD (\<lambda>_. c) x :> 0"
  unfolding has_gradient_def
  by simp


lemma grad_fun_const:
  fixes c :: real
  shows "\<nabla> (\<lambda>_. c) x = 0"
  by (rule grad_fun_eq[OF GRAD_const])


lemma GRAD_affine:
  fixes a :: real and b :: "real^'n::finite"
  shows "GRAD (\<lambda>x. a + x \<bullet> b) x :> b"
  unfolding has_gradient_def
  by (auto intro!: derivative_eq_intros simp: inner_commute)


lemma grad_fun_affine:
  fixes a :: real and b :: "real^'n::finite"
  shows "\<nabla> (\<lambda>x. a + x \<bullet> b) x = b"
  by (rule grad_fun_eq[OF GRAD_affine])


lemma GRAD_sum:
  fixes F :: "'i \<Rightarrow> real^'n::finite \<Rightarrow> real"
  fixes G :: "'i \<Rightarrow> real^'n"
  assumes fin: "finite I"
      and G: "\<And>i. i \<in> I \<Longrightarrow> GRAD (F i) x :> G i"
  shows "GRAD (\<lambda>y. \<Sum>i\<in>I. F i y) x :> (\<Sum>i\<in>I. G i)"
  using fin G
proof (induction rule: finite_induct)
  case empty
  show ?case
    unfolding has_gradient_def
    by simp
next
  case (insert i I)
  have Gi: "GRAD (F i) x :> G i"
    using insert.prems by simp
  have GI: "GRAD (\<lambda>y. \<Sum>j\<in>I. F j y) x :> (\<Sum>j\<in>I. G j)"
    using insert.IH insert.prems by blast
  have "GRAD (\<lambda>y. F i y + (\<Sum>j\<in>I. F j y)) x :> G i + (\<Sum>j\<in>I. G j)"
    by (rule GRAD_add[OF Gi GI])
  then show ?case
    using insert.hyps
    by simp
qed


lemma grad_fun_sum:
  fixes F :: "'i \<Rightarrow> real^'n::finite \<Rightarrow> real"
  assumes fin: "finite I"
      and exG: "\<And>i. i \<in> I \<Longrightarrow> \<exists>g. GRAD (F i) x :> g"
  shows "\<nabla> (\<lambda>y. \<Sum>i\<in>I. F i y) x = (\<Sum>i\<in>I. \<nabla> (F i) x)"
proof -
  have G: "\<And>i. i \<in> I \<Longrightarrow> GRAD (F i) x :> \<nabla> (F i) x"
    using exG by (blast intro: grad_fun_satisfies_GRAD)
  have "GRAD (\<lambda>y. \<Sum>i\<in>I. F i y) x :> (\<Sum>i\<in>I. \<nabla> (F i) x)"
    by (rule GRAD_sum[OF fin G])
  thus ?thesis
    by (rule grad_fun_eq)
qed


(* ================================================================== *)
subsection \<open>Hessian: constants and affine maps\<close>
(* ================================================================== *)


lemma HESS_const_zero:
  fixes c :: real
  shows "HESS (\<lambda>_. c) x :> 0"
  unfolding has_hessian_def
  by (metis (no_types, lifting) ext grad_fun_const has_derivative_const matrix_vector_mult_0)


lemma HESS_affine_zero:
  fixes a :: real and b :: "real^'n::finite"
  shows "HESS (\<lambda>x. a + x \<bullet> b) x :> 0"
  unfolding has_hessian_def
  by (metis (no_types, lifting) ext grad_fun_affine has_derivative_const matrix_vector_mult_0)


lemma hessian_const_zero:
  fixes c :: real
  shows "\<nabla>\<^sup>2 (\<lambda>_. c) x = 0"
  using HESS_const_zero by (metis hess_fun_eq)


lemma hessian_affine_zero:
  fixes a :: real and b :: "real^'n::finite"
  shows "\<nabla>\<^sup>2 (\<lambda>x. a + x \<bullet> b) x = 0"
  using HESS_affine_zero by (metis hess_fun_eq)


(* ================================================================== *)
subsection \<open>Coordinate formulas\<close>
(* ================================================================== *)


lemma HESS_row_gradient:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes H: "HESS f x :> Hx"
  shows "GRAD (\<lambda>y. \<nabla> f y $ i) x :> Hx $ i"
proof -
  have Hd: "(\<nabla> f has_derivative (*v) Hx) (at x)"
    using H unfolding has_hessian_def by simp
  have Hcomp:
    "((\<lambda>y. \<nabla> f y \<bullet> axis i 1) has_derivative
       (\<lambda>v. ((*v) Hx) v \<bullet> axis i 1)) (at x within UNIV)"
    using Hd
    by (subst (asm) has_derivative_componentwise_within[where S = UNIV])
       (auto simp: Basis_vec_def)
  have comp_fun:
    "(\<lambda>y. \<nabla> f y \<bullet> axis i 1) = (\<lambda>y. \<nabla> f y $ i)"
    by (rule ext) (simp add: cart_eq_inner_axis)
  have comp_deriv:
    "(\<lambda>v. ((*v) Hx) v \<bullet> axis i 1) = (\<lambda>v. v \<bullet> (Hx $ i))"
    by (metis (no_types) cart_eq_inner_axis inner_commute matrix_vector_mul_component)
  show ?thesis
    using Hcomp
    unfolding has_gradient_def
    by (simp add: comp_fun comp_deriv)
qed


lemma HESS_row_eq:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes H: "HESS f x :> Hx"
  shows "\<nabla> (\<lambda>y. \<nabla> f y $ i) x = Hx $ i"
  by (rule grad_fun_eq[OF HESS_row_gradient[OF H]])


lemma HESS_component_eq:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes H: "HESS f x :> Hx"
  shows "Hx $ i $ j = (\<nabla> (\<lambda>y. \<nabla> f y $ i)) x $ j"
  using HESS_row_eq[OF H, of i] by simp


(* ================================================================== *)
subsection \<open>Hessian algebra at the predicate level\<close>
(* ================================================================== *)


lemma HESS_add:
  fixes f g :: "real^'n::finite \<Rightarrow> real"
  assumes Hf: "HESS f x :> Hf'" and Hg: "HESS g x :> Hg'"
      and eq: "\<And>y. y \<in> A \<Longrightarrow> \<nabla> (\<lambda>z. f z + g z) y = \<nabla> f y + \<nabla> g y"
      and Aop: "open A" and xA: "x \<in> A"
  shows "HESS (\<lambda>y. f y + g y) x :> Hf' + Hg'"
proof -
  have dsum: "((\<lambda>y. \<nabla> f y + \<nabla> g y) has_derivative
               (\<lambda>v. Hf' *v v + Hg' *v v)) (at x)"
    using has_derivative_add
      Hf[unfolded has_hessian_def] Hg[unfolded has_hessian_def] by blast
  have dtrans: "((\<lambda>y. \<nabla> (\<lambda>z. f z + g z) y) has_derivative
                 (\<lambda>v. Hf' *v v + Hg' *v v)) (at x)"
    by (smt (verit, best) Aop dsum eq has_derivative_transfer_on_open xA)

  have "\<And>v. (Hf' + Hg') *v v = Hf' *v v + Hg' *v v"
    by (simp add: matrix_vector_mult_def vec_eq_iff sum.distrib distrib_right)
  thus ?thesis
    unfolding has_hessian_def using dtrans by presburger 
qed


lemma HESS_scaleR:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes Hf: "HESS f x :> Hf'"
      and eq: "\<And>y. y \<in> A \<Longrightarrow> \<nabla> (\<lambda>z. c * f z) y = c *\<^sub>R \<nabla> f y"
      and Aop: "open A" and xA: "x \<in> A"
  shows "HESS (\<lambda>y. c * f y) x :> c *\<^sub>R Hf'"
proof -
  have dscale: "((\<lambda>y. c *\<^sub>R \<nabla> f y) has_derivative
                 (\<lambda>v. c *\<^sub>R (Hf' *v v))) (at x)"
    using Hf[unfolded has_hessian_def]
    by (intro has_derivative_scaleR_right)
  have dtrans: "((\<lambda>y. \<nabla> (\<lambda>z. c * f z) y) has_derivative
                 (\<lambda>v. c *\<^sub>R (Hf' *v v))) (at x)"
    using Aop dscale eq has_derivative_transform_within_open xA by force
  have "\<And>v. (c *\<^sub>R Hf') *v v = c *\<^sub>R (Hf' *v v)"
    by (simp add: matrix_vector_mult_def vec_eq_iff scaleR_sum_right,
        simp add: sum_distrib_left vector_space_over_itself.scale_scale)
  thus ?thesis
    unfolding has_hessian_def using dtrans by presburger 
qed


(* ================================================================== *)
subsection \<open>Linearity of the Hessian on C² maps\<close>
(* ================================================================== *)


definition outer_prod :: "real^'n \<Rightarrow> real^'n \<Rightarrow> real^'n^'n" (infixl "\<otimes>" 70)
  where "a \<otimes> b = (\<chi> i j. a $ i * b $ j)"


lemma outer_prod_component [simp]:
  "(a \<otimes> b) $ i $ j = a $ i * b $ j"
  by (simp add: outer_prod_def)


lemma outer_prod_row:
  "(a \<otimes> b) $ i = (a $ i) *\<^sub>R b"
  by (simp add: vec_eq_iff outer_prod_def)


lemma outer_prod_commute:
  "transpose (a \<otimes> b) = b \<otimes> a"
  by (simp add: vec_eq_iff transpose_def outer_prod_def mult.commute)


lemma outer_prod_add_left:
  "(a + b) \<otimes> c = a \<otimes> c + b \<otimes> c"
  by (simp add: vec_eq_iff outer_prod_def distrib_right)


lemma outer_prod_add_right:
  "a \<otimes> (b + c) = a \<otimes> b + a \<otimes> c"
  by (simp add: vec_eq_iff outer_prod_def distrib_left)


lemma outer_prod_scaleR_left:
  "(c *\<^sub>R a) \<otimes> b = c *\<^sub>R (a \<otimes> b)"
  by (simp add: vec_eq_iff outer_prod_def)


lemma outer_prod_scaleR_right:
  "a \<otimes> (c *\<^sub>R b) = c *\<^sub>R (a \<otimes> b)"
  by (simp add: vec_eq_iff outer_prod_def)


lemma outer_prod_zero_left [simp]:
  "0 \<otimes> b = 0"
  by (simp add: vec_eq_iff outer_prod_def)


lemma outer_prod_zero_right [simp]:
  "a \<otimes> 0 = 0"
  by (simp add: vec_eq_iff outer_prod_def)


lemma outer_prod_mult_vec:
  "(a \<otimes> b) *v v = (b \<bullet> v) *\<^sub>R a"
  by (simp add: matrix_vector_mul_component outer_prod_row vec_eq_iff)

 
(* ================================================================== *)
subsection \<open>Gradient product rule\<close>
(* ================================================================== *)


lemma GRAD_mult:
  fixes f g :: "real^'n::finite \<Rightarrow> real"
  assumes Gf: "GRAD f x :> df"
      and Gg: "GRAD g x :> dg"
  shows "GRAD (\<lambda>y. f y * g y) x :> f x *\<^sub>R dg + g x *\<^sub>R df"
proof -
  have Df: "(f has_derivative (\<lambda>v. v \<bullet> df)) (at x)"
    using Gf unfolding has_gradient_def.
  have Dg: "(g has_derivative (\<lambda>v. v \<bullet> dg)) (at x)"
    using Gg unfolding has_gradient_def.
  have "((\<lambda>y. f y * g y) has_derivative
         (\<lambda>v. f x * (v \<bullet> dg) + (v \<bullet> df) * g x)) (at x)"
    using Df Dg by (auto intro!: derivative_eq_intros)
  moreover have "\<And>v. f x * (v \<bullet> dg) + (v \<bullet> df) * g x
                    = v \<bullet> (f x *\<^sub>R dg + g x *\<^sub>R df)"
    by (simp add: inner_add_right mult.commute)
  ultimately show ?thesis
    unfolding has_gradient_def by simp
qed


lemma grad_fun_mult:
  fixes f g :: "real^'n::finite \<Rightarrow> real"
  assumes "\<exists>gf. GRAD f x :> gf"
      and "\<exists>gg. GRAD g x :> gg"
  shows "\<nabla> (\<lambda>y. f y * g y) x = f x *\<^sub>R \<nabla> g x + g x *\<^sub>R \<nabla> f x"
proof -
  have Gf: "GRAD f x :> \<nabla> f x"
    using assms(1) by (blast intro: grad_fun_satisfies_GRAD)
  have Gg: "GRAD g x :> \<nabla> g x"
    using assms(2) by (blast intro: grad_fun_satisfies_GRAD)
  have "GRAD (\<lambda>y. f y * g y) x :> f x *\<^sub>R \<nabla> g x + g x *\<^sub>R \<nabla> f x"
    by (rule GRAD_mult[OF Gf Gg])
  thus ?thesis
    by (rule grad_fun_eq)
qed


(* ================================================================== *)
subsection \<open>Hessian product rule\<close>
(* ================================================================== *)

text \<open>
  For scalar \<open>C²\<close> functions \<open>f, g : \<real>ⁿ \<rightarrow> \<real>\<close> on an open set \<open>U\<close>:

    \<open>\<nabla>²(fg)(x) = f(x) \<nabla>²g(x) + g(x) \<nabla>²f(x) + (\<nabla>f(x)) \<otimes> (\<nabla>g(x)) + (\<nabla>g(x)) \<otimes> (\<nabla>f(x))\<close>

  where \<open>a \<otimes> b\<close> denotes the outer product \<open>(\<chi> i j. a$i * b$j)\<close>.
\<close>


lemma transpose_mv_inner:
  fixes A :: "real^'n^'m" and v :: "real^'n" and w :: "real^'m"
  shows "(A *v v) \<bullet> w = v \<bullet> (transpose A *v w)"
proof -
  have "(A *v v) \<bullet> w = (\<Sum>i\<in>UNIV. (\<Sum>j\<in>UNIV. A $ i $ j * v $ j) * w $ i)"
    by (simp add: matrix_vector_mult_def inner_vec_def)
  also have "\<dots> = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. (A $ i $ j * v $ j) * w $ i)"
    by (simp add: sum_distrib_left algebra_simps)
  also have "\<dots> = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. w $ i * A $ i $ j * v $ j)"
    by (simp add: algebra_simps)
  also have "\<dots> = (\<Sum>j\<in>UNIV. \<Sum>i\<in>UNIV. w $ i * A $ i $ j * v $ j)"
    using sum.swap by fastforce
  also have "\<dots> = (\<Sum>j\<in>UNIV. v $ j * (\<Sum>i\<in>UNIV. A $ i $ j * w $ i))"
    by (simp add: sum_distrib_left sum_distrib_right algebra_simps)
  also have "\<dots> = v \<bullet> (transpose A *v w)"
    by (simp add: matrix_vector_mult_def inner_vec_def transpose_def)
  finally show ?thesis.
qed


(* ================================================================== *)
subsection \<open>Jacobian\<close>
(* ================================================================== *)


definition jacobian :: "(real^'n::finite \<Rightarrow> real^'m::finite) \<Rightarrow> real^'n \<Rightarrow> real^'n^'m"
  where "jacobian F x = matrix (frechet_derivative F (at x))"


lemma jacobian_works:
  assumes "F differentiable (at x)"
  shows "frechet_derivative F (at x) v = jacobian F x *v v"
  unfolding jacobian_def
  by (simp add: assms linear_frechet_derivative)


lemma jacobian_component:
  assumes "F differentiable (at x)"
  shows "jacobian F x $ r $ i = frechet_derivative (\<lambda>y. F y $ r) (at x) (axis i 1)"
proof -
  have FD: "(F has_derivative frechet_derivative F (at x)) (at x)"
    using assms frechet_derivative_works by blast 

  have coord_D:  "((\<lambda>y. F y $ r) has_derivative (\<lambda>h. frechet_derivative F (at x) h $ r)) (at x)"
  proof -
    have Hcomp: "((\<lambda>y. F y \<bullet> axis r 1) has_derivative
          (\<lambda>h. frechet_derivative F (at x) h \<bullet> axis r 1)) (at x within UNIV)"
      using FD by (subst (asm) has_derivative_componentwise_within[where S = UNIV], 
                   auto simp: Basis_vec_def)
    have comp_fun: "(\<lambda>y. F y \<bullet> axis r 1) = (\<lambda>y. F y $ r)"
      by (rule ext, simp add: cart_eq_inner_axis)
    have comp_deriv: "(\<lambda>h. frechet_derivative F (at x) h \<bullet> axis r 1)
                    = (\<lambda>h. frechet_derivative F (at x) h $ r)"
      by (rule ext, simp add: cart_eq_inner_axis)
    show ?thesis
      using Hcomp by (simp add: comp_fun comp_deriv)
  qed
  have coord_FD: "frechet_derivative (\<lambda>y. F y $ r) (at x) = (\<lambda>h. frechet_derivative F (at x) h $ r)"
    by (subst frechet_derivative_at[OF coord_D], simp)
  have "(jacobian F x *v axis i 1) $ r = jacobian F x $ r $ i"
    by (simp add: matrix_vector_mult_def,
        metis (full_types) cart_eq_inner_axis inner_real_def inner_vec_def)
  moreover have "jacobian F x *v axis i 1 = frechet_derivative F (at x) (axis i 1)"
    using assms by (subst jacobian_works, auto)
  ultimately have "jacobian F x $ r $ i = frechet_derivative F (at x) (axis i 1) $ r"
    by simp
  also have "... = frechet_derivative (\<lambda>y. F y $ r) (at x) (axis i 1)"
    by (simp add: coord_FD)
  finally show ?thesis.
qed

(* ================================================================== *)
subsection \<open>Gradient chain rule\<close>
(* ================================================================== *)

text \<open>
  If \<open>g : \<real>ᵐ \<rightarrow> \<real>\<close> has gradient \<open>\<nabla>g(F(x))\<close> at \<open>F(x)\<close> and \<open>F : \<real>ⁿ \<rightarrow> \<real>ᵐ\<close>
  is Fréchet differentiable at \<open>x\<close>, then:

    \<open>\<nabla>(g \<circ> F)(x) = Jᶠ(x)ᵀ *v \<nabla>g(F(x))\<close>

  where \<open>Jᶠ(x)\<close> is the Jacobian of \<open>F\<close> at \<open>x\<close>.
\<close>


lemma GRAD_compose:
  fixes g :: "real^'m::finite \<Rightarrow> real"
    and F :: "real^'n::finite \<Rightarrow> real^'m"
  assumes Gg: "GRAD g (F x) :> dg"
      and DF: "(F has_derivative J) (at x)"
  shows "GRAD (\<lambda>y. g (F y)) x :> transpose (matrix J) *v dg"
proof -
  have Dg: "(g has_derivative (\<lambda>w. w \<bullet> dg)) (at (F x))"
    using Gg unfolding has_gradient_def .

  have Dcomp: "((\<lambda>y. g (F y)) has_derivative (\<lambda>v. J v \<bullet> dg)) (at x)"
    using has_derivative_compose[OF DF Dg] by (simp add: o_def)

  have "\<And>v. J v \<bullet> dg = v \<bullet> (transpose (matrix J) *v dg)"
  proof -
    fix v
    have bl: "bounded_linear J"
      using DF by (rule has_derivative_bounded_linear)
    have "J v = matrix J *v v"
      using bl by (simp add: matrix_works)
    hence "J v \<bullet> dg = (matrix J *v v) \<bullet> dg"
      by simp
    also have "\<dots> = v \<bullet> (transpose (matrix J) *v dg)"
      by (rule transpose_mv_inner)
    finally show "J v \<bullet> dg = v \<bullet> (transpose (matrix J) *v dg)" .
  qed

  hence "((\<lambda>y. g (F y)) has_derivative (\<lambda>v. v \<bullet> (transpose (matrix J) *v dg))) (at x)"
    using Dcomp by simp

  thus ?thesis
    unfolding has_gradient_def .
qed


corollary GRAD_compose':
  fixes g :: "real^'m::finite \<Rightarrow> real"
    and F :: "real^'n::finite \<Rightarrow> real^'m"
  assumes Gg: "GRAD g (F x) :> dg"
      and DF: "F differentiable (at x)"
  shows "GRAD (\<lambda>y. g (F y)) x :> transpose (jacobian F x) *v dg"
proof -
  have "(F has_derivative frechet_derivative F (at x)) (at x)"
    using DF by (simp add: frechet_derivative_worksI)
  thus ?thesis
    by (simp add: jacobian_def, metis GRAD_compose Gg transpose_matrix_vector)
qed


lemma grad_fun_compose:
  fixes g :: "real^'m::finite \<Rightarrow> real"
    and F :: "real^'n::finite \<Rightarrow> real^'m"
  assumes "\<exists>gg. GRAD g (F x) :> gg"
      and "F differentiable (at x)"
  shows "\<nabla> (\<lambda>y. g (F y)) x = transpose (jacobian F x) *v \<nabla> g (F x)"
proof -
  have Gg: "GRAD g (F x) :> \<nabla> g (F x)"
    using assms(1) by (blast intro: grad_fun_satisfies_GRAD)
  have "GRAD (\<lambda>y. g (F y)) x :> transpose (jacobian F x) *v \<nabla> g (F x)"
    by (rule GRAD_compose'[OF Gg assms(2)])
  thus ?thesis
    by (rule grad_fun_eq)
qed


(* ================================================================== *)
subsection \<open>Component closure\<close>
(* ================================================================== *)


lemma row_transpose_mult_both:
  fixes A :: "real^'n^'m" and B :: "real^'m^'m"
  shows "(transpose A ** B ** A) $ i = (\<Sum>r\<in>UNIV. A $ r $ i *\<^sub>R (transpose A *v (B $ r)))"
proof (rule vec_eq_iff[THEN iffD2], intro allI)
  fix j :: 'n
  have "(transpose A ** B ** A) $ i $ j
      = (\<Sum>s\<in>UNIV. (transpose A ** B) $ i $ s * A $ s $ j)"
    by (simp add: matrix_matrix_mult_def)
  also have "\<dots> = (\<Sum>s\<in>UNIV. (\<Sum>r\<in>UNIV. A $ r $ i * B $ r $ s) * A $ s $ j)"
    by (simp add: matrix_matrix_mult_def transpose_def)
  also have "\<dots> = (\<Sum>s\<in>UNIV. \<Sum>r\<in>UNIV. A $ r $ i * B $ r $ s * A $ s $ j)"
    by (simp add: sum_distrib_right mult.assoc)
  also have "\<dots> = (\<Sum>r\<in>UNIV. \<Sum>s\<in>UNIV. A $ r $ i * B $ r $ s * A $ s $ j)"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>r\<in>UNIV. A $ r $ i * (\<Sum>s\<in>UNIV. B $ r $ s * A $ s $ j))"
    by (simp add: sum_distrib_left mult.assoc)
  also have "\<dots> = (\<Sum>r\<in>UNIV. A $ r $ i * (\<Sum>s\<in>UNIV. A $ s $ j * B $ r $ s))"
    by (simp add: mult.commute)
  also have "\<dots> = (\<Sum>r\<in>UNIV. A $ r $ i * (transpose A *v (B $ r)) $ j)"
    by (simp add: matrix_vector_mult_def transpose_def)
  also have "\<dots> = (\<Sum>r\<in>UNIV. A $ r $ i *\<^sub>R (transpose A *v (B $ r))) $ j"
    by simp
  finally show "(Finite_Cartesian_Product.transpose A ** B ** A) $ i $ j =
          (\<Sum>r\<in>UNIV. A $ r $ i *\<^sub>R (Finite_Cartesian_Product.transpose A *v B $ r)) $ j"
    by simp
qed


text \<open>
  For \<open>g : \<real>ᵐ \<rightarrow> \<real>\<close> that is \<open>C²\<close> on \<open>V\<close> and \<open>F : \<real>ⁿ \<rightarrow> \<real>ᵐ\<close> that is
  \<open>C²\<close> on \<open>U\<close> with \<open>F(U) \<subseteq> V\<close>:

    \<open>\<nabla>²(g \<circ> F)(x) = Jᶠ(x)ᵀ \<^emph>\<^emph> \<nabla>²g(F(x)) \<^emph>\<^emph> Jᶠ(x) + \<Sigma>ᵣ (\<nabla>g(F(x)) $ r) *\<^sub>R \<nabla>²Fᵣ(x)\<close>

  where \<open>Jᶠ(x) = jacobian F x\<close> and \<open>Fᵣ(y) = F(y) $ r\<close>.
\<close>


(* ================================================================== *)
subsection \<open>Further derivative–predicate relations\<close>
(* ================================================================== *)

text \<open>The first-order Fréchet derivative of a scalar field is the inner product
  with its gradient.\<close>

lemma frechet_eq_inner_gradient:
  fixes f :: "real^'n::finite \<Rightarrow> real"
  assumes "(f has_derivative L) (at x)" and "GRAD f x :> \<nabla> f x"
  shows "L v = v \<bullet> \<nabla> f x"
  using assms has_derivative_unique has_gradient_def by blast

end
