section \<open>Gradient Descent: VCG, Lammich, and Floating-Point Verification\<close>

theory Gradient_Descent
  imports
    "ITree_Numeric_VCG.ITree_Numeric_VCG"
    "Refine_Monadic.Refine_Monadic"
    Float_Vector
begin

text \<open>
  Two verifications of the SAME gradient-descent algorithm (linear convergence
  under a Lipschitz gradient and the Polyak--Lojasiewicz inequality, with the
  fixed step \<open>1/L\<close>). Paradigm A is the imperative ITree program discharged by
  the VCG-based Hoare logic, together with the standalone convergence
  mathematics it uses. Paradigm B replays it in
  Lammich's Refinement Framework: a single \<open>WHILET\<close> over \<open>(x, iter)\<close> whose
  termination is the iteration bound \<open>\<lceil>ln(2L(f x0 - f x_min)/\<epsilon>\<^sup>2)/ln(1/(1-\<mu>/L))\<rceil>\<close>.
  Both sides share the per-step lemmas \<open>step_choice\<close> and
  \<open>grad_sq_le_gap_from_smoothness\<close>.
\<close>

section \<open>Kantorovich inequality (shared math, used by the quadratic form)\<close>

section \<open>Definitions\<close>

definition diagonal_mat :: "('a::zero) ^ 'n ^ 'n \<Rightarrow> bool" where
  "diagonal_mat A \<longleftrightarrow> (\<forall>i j. i \<noteq> j \<longrightarrow> A $ i $ j = 0)"

definition quad_form_fc :: "real^'n^'n \<Rightarrow> real^'n \<Rightarrow> real" where
  "quad_form_fc Q x = x \<bullet> (Q *v x)"

section \<open>Diagonal matrix helpers\<close>

lemma mat_vec_mult_entry_diagonal:
  fixes D :: "real^'n^'n" and y :: "real^'n"
  assumes "diagonal_mat D"
  shows "(D *v y) $ i = (D $ i $ i) * (y $ i)"
proof -
  have "(D *v y) $ i = (\<Sum>j\<in>UNIV. (D $ i $ j) * (y $ j))"
    by (simp add: matrix_vector_mult_def)
  also have "... = (\<Sum>j\<in>UNIV. if j = i then (D $ i $ i) * (y $ i) else 0)"
  proof (rule sum.cong[OF refl])
    fix j
    show "(D $ i $ j) * (y $ j) = (if j = i then (D $ i $ i) * (y $ i) else 0)"
    proof (cases "j = i")
      case True then show ?thesis by simp
    next
      case False
      then have "D $ i $ j = 0"
        by (metis assms diagonal_mat_def)
      then show ?thesis using False by simp
    qed
  qed
  also have "... = (D $ i $ i) * (y $ i)"
    by simp
  finally show ?thesis.
qed

lemma quad_form_fc_diagonal_sum:
  fixes D :: "real^'n^'n" and y :: "real^'n"
  assumes "diagonal_mat D"
  shows "quad_form_fc D y = (\<Sum>i\<in>UNIV. (D $ i $ i) * (y $ i)^2)"
  by (smt (verit) assms inner_commute inner_real_def inner_vec_def
      mat_vec_mult_entry_diagonal more_arith_simps(11) power2_eq_square
      quad_form_fc_def sum_mono)

lemma diagonal_inverse_entries:
  fixes D Dinv :: "real^'n^'n"
  assumes diagD: "diagonal_mat D"
      and invL:  "D ** Dinv = Finite_Cartesian_Product.mat 1"
  shows "\<forall>i. Dinv $ i $ i = inverse (D $ i $ i)"
proof
  fix i
  \<comment> \<open>The (i,i) entry of D ** Dinv equals 1\<close>
  have entry_one: "(D ** Dinv) $ i $ i = 1"
    by (metis assms(2) axis_nth cart_eq_inner_axis matrix_vector_mul_component matrix_vector_mul_lid)
  \<comment> \<open>Expand the (i,i) entry of the product\<close>
  have expand: "(D ** Dinv) $ i $ i = (\<Sum>j\<in>UNIV. D $ i $ j * Dinv $ j $ i)"
    by (simp add: matrix_matrix_mult_def)
  \<comment> \<open>Off-diagonal entries of D are zero, so the sum collapses to D$i$i * Dinv$i$i\<close>
  have collapse: "(\<Sum>j\<in>UNIV. D $ i $ j * Dinv $ j $ i) = D $ i $ i * Dinv $ i $ i"
  proof -
    have "(\<Sum>j\<in>UNIV. D $ i $ j * Dinv $ j $ i)
        = (\<Sum>j\<in>UNIV. if j = i then D $ i $ i * Dinv $ i $ i else 0)"
    proof (rule sum.cong[OF refl])
      fix j
      show "D $ i $ j * Dinv $ j $ i = (if j = i then D $ i $ i * Dinv $ i $ i else 0)"
      proof (cases "j = i")
        case True then show ?thesis by simp
      next
        case False
        then have "D $ i $ j = 0"
          by (metis assms(1) diagonal_mat_def)
        then show ?thesis using False by simp
      qed
    qed
    also have "... = D $ i $ i * Dinv $ i $ i"
      by simp
    finally show ?thesis.
  qed
  \<comment> \<open>So D$i$i * Dinv$i$i = 1, giving Dinv$i$i = inverse(D$i$i)\<close>
  have prod_one: "D $ i $ i * Dinv $ i $ i = 1"
    using entry_one expand collapse by simp
  thus "Dinv $ i $ i = inverse (D $ i $ i)"
    by (metis inverse_unique)
qed

lemma diagonal_inverse_offdiag_zero:
  fixes D Dinv :: "real^'n^'n"
  assumes "diagonal_mat D" and "D ** Dinv = Finite_Cartesian_Product.mat 1"
  shows "i \<noteq> j \<Longrightarrow> Dinv $ i $ j = 0"
  by (smt (z3) Groups.mult_ac(2) assms axis_nth cart_eq_inner_axis column_def 
      matrix_vector_mul_assoc matrix_vector_mul_component matrix_vector_mul_lid 
      diagonal_inverse_entries diagonal_mat_def inner_commute mat_vec_mult_entry_diagonal 
      matrix_vector_mult_basis matrix_vector_mult_def more_arith_simps(11) mult_cancel_right1) 

section \<open>Symmetry helpers\<close>

lemma diagonal_mat_symmetric:
  fixes D :: "real^'n^'n"
  assumes "diagonal_mat D"
  shows "\<forall>i j. D $ i $ j = D $ j $ i"
proof (intro allI)
  fix i j
  show "D $ i $ j = D $ j $ i"
  proof (cases "i = j")
    case True then show ?thesis by simp
  next
    case False
    then have "D $ i $ j = 0" using assms unfolding diagonal_mat_def by blast
    moreover have "D $ j $ i = 0" using False assms unfolding diagonal_mat_def
      by presburger 
    ultimately show ?thesis by simp
  qed
qed

lemma orthogonal_diag_orthogonal_symmetric:
  fixes U D :: "real^'n^'n"
  assumes orthU: "orthogonal_matrix U"
      and diagD: "diagonal_mat D"
  shows "\<forall>i j. (Finite_Cartesian_Product.transpose U ** D ** U) $ i $ j
             = (Finite_Cartesian_Product.transpose U ** D ** U) $ j $ i"
proof (intro allI)
  fix i j
  have symD: "Finite_Cartesian_Product.transpose D = D"
    by (simp add: Finite_Cartesian_Product.transpose_def diagonal_mat_symmetric[OF diagD] matrix_eq)
  have "Finite_Cartesian_Product.transpose (Finite_Cartesian_Product.transpose U ** D ** U)
      = Finite_Cartesian_Product.transpose U ** D ** U"
    by (metis (no_types) transpose_transpose local.symD matrix_mul_assoc matrix_transpose_mul)
  thus "(Finite_Cartesian_Product.transpose U ** D ** U) $ i $ j
      = (Finite_Cartesian_Product.transpose U ** D ** U) $ j $ i"
    by (metis (lifting) transpose_def vec_lambda_beta)
qed

section \<open>Positive definiteness from eigenvalue bounds\<close>

lemma eig_lower_imp_pos_def:
  fixes Q :: "real^'n^'n"
  assumes a_pos:   "0 < a"
      and eig_lower: "\<And>x. a * (x \<bullet> x) \<le> x \<bullet> (Q *v x)"
      and x_nz:    "x \<noteq> 0"
  shows "0 < x \<bullet> (Q *v x)"
proof -
  have inner_pos: "0 < x \<bullet> x"
    using x_nz inner_gt_zero_iff by blast
  have "0 < a * (x \<bullet> x)"
    using a_pos inner_pos by (intro mult_pos_pos)
  thus ?thesis
    using eig_lower[of x] by linarith
qed

lemma eig_lower_imp_quad_form_pos:
  fixes Q :: "real^'n^'n"
  assumes a_pos:     "0 < a"
      and eig_lower: "\<And>x. a * (x \<bullet> x) \<le> x \<bullet> (Q *v x)"
      and x_nz:      "x \<noteq> 0"
  shows "0 < quad_form_fc Q x"
  unfolding quad_form_fc_def
  using eig_lower_imp_pos_def[OF a_pos eig_lower x_nz].

section \<open>Scalar Kantorovich\<close>

lemma scalar_kantorovich:
  fixes a A lam :: real
  assumes "0 < a" and "a \<le> A" and "a \<le> lam" and "lam \<le> A"
  shows "lam + (a * A) / lam \<le> a + A"
proof -
  have lam_pos: "0 < lam" using assms by linarith
  have "(lam - a) * (lam - A) \<le> 0"
    by (simp add: assms(3,4) mult_le_0_iff)
  hence "lam^2 - (a + A)*lam + a*A \<le> 0"
    by (simp add: algebra_simps power2_eq_square)
  with lam_pos show ?thesis
    by (simp add: field_simps power2_eq_square)
qed

lemma four_mult_le_square_sum:
  fixes u v :: real
  shows "4 * u * v \<le> (u + v) * (u + v)"
proof -
  have ge0: "0 \<le> (u - v) * (u - v)"
    by (rule zero_le_square)
  hence "(u - v) * (u - v) + 4 * u * v = (u + v) * (u + v)"
    by (simp add: algebra_simps)
  with ge0 show ?thesis
     by linarith     
qed

section \<open>Kantorovich for diagonal Q\<close>

lemma kantorovich_diagonal_case:
  fixes D Dinv :: "real ^ 'n ^ 'n" and y :: "real ^ 'n"
  assumes diagD: "diagonal_mat D"
      and invL:  "D ** Dinv = Finite_Cartesian_Product.mat 1"
      and a_pos: "0 < a"
      and a_le_A: "a \<le> A"
      and bd:    "\<And>i. a \<le> D $ i $ i \<and> D $ i $ i \<le> A"
      and y_nz:  "y \<noteq> 0"
  shows "((y \<bullet> y)^2) / (quad_form_fc D y * quad_form_fc Dinv y) \<ge> (4*a*A) / (a + A)^2"
proof -
  let ?w = "\<lambda>i. (y $ i)^2"
  let ?S = "\<Sum>i\<in>UNIV. ?w i"
  let ?T = "\<Sum>i\<in>UNIV. (D $ i $ i) * ?w i"
  let ?U = "\<Sum>i\<in>UNIV. (Dinv $ i $ i) * ?w i"

  have w_nonneg: "\<And>i. 0 \<le> ?w i" by simp
  have S_eq: "?S = y \<bullet> y" by (simp add: inner_vec_def power2_eq_square)
  have T_eq: "?T = quad_form_fc D y"
    using quad_form_fc_diagonal_sum[OF diagD] by simp

  have diagDinv: "diagonal_mat Dinv"
    by (meson diagD diagonal_inverse_offdiag_zero diagonal_mat_def invL)
  have Dinv_diag: "\<And>i. Dinv $ i $ i = inverse (D $ i $ i)"
    using diagonal_inverse_entries[OF diagD invL] by blast
  have U_eq: "?U = quad_form_fc Dinv y"
    using quad_form_fc_diagonal_sum[OF diagDinv]
    by (simp add: Dinv_diag)

  have A_pos: "0 < A" using a_pos a_le_A by linarith
  have S_pos: "0 < ?S" by (simp add: S_eq assms(6))

  have T_ge: "a * ?S \<le> ?T"
    by (simp add: bd mult_right_mono sum_distrib_left sum_mono)

  have U_ge: "(inverse A) * ?S \<le> ?U"
  proof -
    have "(\<Sum>i\<in>UNIV. (inverse A) * ?w i) \<le> (\<Sum>i\<in>UNIV. inverse (D $ i $ i) * ?w i)"
    proof (intro sum_mono)
      fix i
      have Di_pos: "0 < D $ i $ i"
        by (smt (verit, best) assms(3) bd) 
      show "(inverse A) * ?w i \<le> inverse (D $ i $ i) * ?w i"
        using Di_pos A_pos bd by (intro mult_right_mono, simp_all)
    qed
    thus ?thesis by (simp add: Dinv_diag sum_distrib_left)
  qed

  have T_pos: "0 < ?T" 
    by (smt (verit) S_pos T_ge a_pos mult_sign_intros(5))
  have U_pos: "0 < ?U" 
    by (smt (verit) A_pos S_pos U_ge inverse_positive_iff_positive mult_sign_intros(5))

  \<comment> \<open>Weighted scalar Kantorovich\<close>
  have sum_step: "?T + (a*A) * ?U \<le> (a + A) * ?S"
  proof -
    have per_i: "\<And>i. ?w i * ((D $ i $ i) + (a*A) / (D $ i $ i)) \<le> ?w i * (a + A)"
      using scalar_kantorovich[OF a_pos a_le_A] bd
      by (simp add: mult_left_mono)
    have lhs: "(\<Sum>i\<in>UNIV. ?w i * ((D $ i $ i) + (a*A) / (D $ i $ i))) = ?T + (a*A) * ?U"
      by (simp add: Dinv_diag field_simps sum.distrib sum_distrib_left)
    have rhs: "(\<Sum>i\<in>UNIV. ?w i * (a + A)) = (a + A) * ?S"
      by (simp add: sum_distrib_left algebra_simps)
    have "(\<Sum>i\<in>UNIV. ?w i * ((D $ i $ i) + (a*A) / (D $ i $ i))) \<le> (\<Sum>i\<in>UNIV. ?w i * (a + A))"
      using per_i by (intro sum_mono) simp
    thus ?thesis using lhs rhs by simp
  qed

  \<comment> \<open>4uv \<le> (u+v)²\<close>
  have prod_step: "4 * ?T * ((a*A) * ?U) \<le> ((a + A) * ?S)^2"
  proof -
    have "4 * ?T * ((a*A) * ?U) \<le> (?T + (a*A) * ?U)^2"
      by (simp add: four_mult_le_square_sum power2_eq_square)
    also have "... \<le> ((a + A) * ?S)^2"
      using sum_step T_pos U_pos a_pos a_le_A by (intro power_mono, linarith, simp)
    finally show ?thesis.
  qed

  have denom_pos: "0 < ?T * ?U" using T_pos U_pos by simp
  show ?thesis
  proof -
    have a_plus_A_pos: "0 < a + A" 
      using a_pos a_le_A by linarith
    then have a_plus_A_sq_pos: "0 < (a + A)^2" 
      using zero_less_power by blast
    \<comment> \<open>Rearrange prod_step into the form 4*a*A * (?T * ?U) \<le> (a+A)^2 * ?S^2\<close>
    have key: "4 * a * A * (?T * ?U) \<le> (a + A)^2 * ?S^2"
      using prod_step by (simp add: power2_eq_square algebra_simps)
    \<comment> \<open>Divide both sides by (a+A)^2 * (?T * ?U)\<close>
    have ratio: "(4 * a * A) / (a + A)^2 \<le> ?S^2 / (?T * ?U)"
    proof -
      have "(4 * a * A) / (a + A)^2   = (4 * a * A * (?T * ?U)) / ((a + A)^2 * (?T * ?U))"
        using denom_pos by auto
      also have "... \<le> ((a + A)^2 * ?S^2) / ((a + A)^2 * (?T * ?U))"
        using key denom_pos a_plus_A_sq_pos
        by (meson divide_right_mono less_imp_le mult_nonneg_nonneg)
      also have "... = ?S^2 / (?T * ?U)"
        using a_plus_A_sq_pos by simp
      finally show ?thesis.
    qed
    show "((y \<bullet> y)^2) / (quad_form_fc D y * quad_form_fc Dinv y) \<ge> (4*a*A) / (a + A)^2"
      using S_eq T_eq U_eq ratio by presburger
  qed
qed

section \<open>Orthogonal helpers\<close>

lemma orthogonal_mat_inj_vmult:
  fixes U :: "real ^ 'n ^ 'n"
  assumes "orthogonal_matrix U"
  shows "U *v x = 0 \<Longrightarrow> x = 0"
  using assms matrix_left_invertible_ker orthogonal_matrix_def by blast

lemma orthogonal_mat_inner_self:
  fixes U :: "real ^ 'n ^ 'n"
  assumes "orthogonal_matrix U"
  shows "(U *v x) \<bullet> (U *v x) = x \<bullet> x"
  by (metis assms dot_lmul_matrix matrix_vector_mul_assoc
      matrix_vector_mul_lid orthogonal_matrix_def transpose_matrix_vector)

lemma quad_form_fc_orth_cong:
  fixes U D :: "real ^ 'n ^ 'n"
  assumes "orthogonal_matrix U"
  shows "quad_form_fc (Finite_Cartesian_Product.transpose U ** D ** U) x  = quad_form_fc D (U *v x)"
  by (metis dot_lmul_matrix matrix_vector_mul_assoc quad_form_fc_def vector_transpose_matrix)

section \<open>Kantorovich inequality\<close>

theorem kantorovich:
  fixes U D Dinv :: "real ^ 'n ^ 'n" and x :: "real ^ 'n"
  assumes orthU:  "orthogonal_matrix U"
      and diagD:  "diagonal_mat D"
      and invL:   "D ** Dinv = Finite_Cartesian_Product.mat 1"
      and a_pos:  "0 < a"
      and a_le_A: "a \<le> A"
      and bd:     "\<And>i. a \<le> D $ i $ i \<and> D $ i $ i \<le> A"
      and x_nz:   "x \<noteq> 0"
  defines Q:    "Q    \<equiv> Finite_Cartesian_Product.transpose U ** D    ** U"
      and Qinv: "Qinv \<equiv> Finite_Cartesian_Product.transpose U ** Dinv ** U"
  shows "((x \<bullet> x)^2) / (quad_form_fc Q x * quad_form_fc Qinv x) \<ge> (4*a*A) / (a + A)^2"
proof - 
  have "U *v x \<noteq> 0"
    using assms(1,7) orthogonal_mat_inj_vmult by blast    
  then show ?thesis
    by (smt (verit) Q Qinv assms(1,4) bd diagD invL  kantorovich_diagonal_case 
        orthogonal_mat_inner_self quad_form_fc_orth_cong)    
qed

section \<open>Shared foundations (smoothness/descent lemmas, state, programs)\<close>

section \<open>Auxiliary Facts\<close>

lemma interval_integral_id:
  fixes a b :: real
  shows "(LBINT t=a..b. t) = (b\<^sup>2 - a\<^sup>2) / 2"
proof -
  have "\<And>x. ((\<lambda>u::real. u^2 / 2)  has_real_derivative x) (at x within {min a b .. max a b})"
    by (auto intro!: derivative_eq_intros)
  then have "\<And>x. ((\<lambda>u::real. u^2 / 2) has_vector_derivative x) (at x within {min a b .. max a b})"    
    by (simp add: has_real_derivative_iff_has_vector_derivative)  
  then have "(LBINT t=a..b. t) = (\<lambda>u::real. u^2 / 2) b - (\<lambda>u::real. u^2 / 2) a"
    using continuous_on_id interval_integral_FTC_finite by blast
  then show ?thesis
    by (simp add: power2_eq_square algebra_simps)
qed

lemma interval_integral_mono_on:
  fixes f g :: "real \<Rightarrow> real"
  assumes ab: "a \<le> b"
  assumes contf: "continuous_on {a..b} f"
  assumes contg: "continuous_on {a..b} g"
  assumes fg: "\<And>x. x \<in> {a..b} \<Longrightarrow> f x \<le> g x"
  shows "(LBINT x=a..b. f x) \<le> (LBINT x=a..b. g x)"
  by (metis assms borel_integrable_atLeastAtMost' integral_le 
      interval_integral_eq_integral set_borel_integral_eq_integral(1))

lemma segment_has_vector_derivative:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
    and x d :: 'a
  defines "h \<equiv> (\<lambda>t::real. x + t *\<^sub>R d)"
  defines "g \<equiv> (\<lambda>t::real. f (h t))"
  defines "phi \<equiv> (\<lambda>t::real. G (h t) \<bullet> d)"
  assumes deriv_G: "\<And>z. (f has_derivative (\<lambda>u. G z \<bullet> u)) (at z)"
  shows "\<And>t. (g has_vector_derivative phi t) (at t within {0..1})"
proof -
  fix t 
  have "(h has_vector_derivative d) (at t within {0..1})"
    unfolding h_def by (auto intro!: derivative_eq_intros)
  then have "(h has_derivative (\<lambda>s. s *\<^sub>R d)) (at t within {0..1})"
    by (simp add: has_vector_derivative_def)
  then have "(g has_derivative (\<lambda>s. (\<lambda>u. G (h t) \<bullet> u) ((\<lambda>r. r *\<^sub>R d) s))) (at t within {0..1})"
    using assms(2,4) has_derivative_compose by blast
  then have  "(g has_derivative (\<lambda>s. s * (phi t))) (at t within {0..1})"
    by (simp add: assms(3))
  then show "(g has_vector_derivative phi t) (at t within {0..1})"
    by (simp add: has_vector_derivative_def)
qed

lemma segment_FTC_01_real:
  fixes g   :: "real \<Rightarrow> real"
    and phi :: "real \<Rightarrow> real"
  assumes cont_phi: "continuous_on {0..1} phi"
  assumes g_vderiv: "\<And>t. t \<in> {0..1} \<Longrightarrow> (g has_vector_derivative phi t) (at t within {0..1})"
  shows "(LBINT t=0..1. phi t) = g 1 - g 0"
  using interval_integral_FTC_finite
  by (metis assms(2) atLeastAtMost_iff cont_phi min_0_1(1) max_0_1(1) one_ereal_def zero_ereal_def)

section \<open>Descent and Contraction under Lipschitz Gradients\<close>

lemma descent_lemma_from_Lipschitz_gradient:
  fixes f :: "'a::euclidean_space \<Rightarrow> real"
  assumes L0: "0 \<le> L"
  assumes deriv_grad: "\<And>z. (f has_derivative (\<lambda>h. grad z \<bullet> h)) (at z)"
  assumes lip: "\<And>u v. \<parallel>grad u - grad v\<parallel> \<le> L * \<parallel>u - v\<parallel>"
  shows "\<And> x y. f y \<le> f x + (grad x \<bullet> (y - x)) + (L/2) * \<parallel>y - x\<parallel>\<^sup>2"
proof -
  fix x y :: 'a
  let ?d   = "y - x"
  let ?h   = "\<lambda>t::real. x + t *\<^sub>R ?d"
  let ?g   = "\<lambda>t::real. f (?h t)"
  let ?phi = "\<lambda>t::real. (grad (?h t) \<bullet> ?d)"
  let ?psi = "\<lambda>t::real. ((grad (?h t) - grad x) \<bullet> ?d)"
  have phi_lip: "lipschitz_on (L * (norm ?d)^2) {0..1} ?phi"
    unfolding lipschitz_on_def
  proof (intro conjI ballI)
    show "0 \<le> L * (norm ?d)^2" 
      using L0 by simp
  next  
    fix s t :: real
    assume s01: "s \<in> {0..1}"
    assume t01: "t \<in> {0..1}"
    have hsht: "?h s - ?h t = (s - t) *\<^sub>R ?d"
      by (simp add: algebra_simps)
    have "dist (?phi s) (?phi t) = abs (?phi s - ?phi t)"
      using dist_real_def by blast
    also have "... = abs ((grad (?h s) - grad (?h t)) \<bullet> ?d)"
      by (simp add: inner_diff_left)
    also have "... \<le> norm (grad (?h s) - grad (?h t)) * norm ?d"
      by (meson Cauchy_Schwarz_ineq2)
    also have "... \<le> (L * norm (?h s - ?h t)) * norm ?d"
      by (meson assms(3) mult_right_mono norm_ge_zero)
    also have "... = (L * (abs (s - t) * norm ?d)) * norm ?d"
      using hsht by auto
    also have "... = (L * (norm ?d)^2) * abs (s - t)"
      by (simp add: algebra_simps power2_eq_square)
    also have "... = (L * (norm ?d)^2) * dist s t"
      using dist_real_def by presburger
    finally show "dist (?phi s) (?phi t) \<le> (L * (norm ?d)^2) * dist s t".
  qed
  then have cont_phi: "continuous_on {0..1} ?phi"
    using lipschitz_on_continuous_on by blast
  have g_vderiv: "\<And>t. t \<in> {0..1} \<Longrightarrow> (?g has_vector_derivative ?phi t) (at t within {0..1})"
    using assms(2) segment_has_vector_derivative by blast  
  have FTC: "(LBINT t=0..1. ?phi t) = ?g 1 - ?g 0"
    using cont_phi g_vderiv segment_FTC_01_real by presburger
  have line_int: "f y - f x = (LBINT t=0..1. ?phi t)"
    using FTC by (simp add: algebra_simps)
  have phi_split: "(LBINT t=0..1. ?phi t) = (LBINT t=0..1. (grad x \<bullet> ?d) + ?psi t)"
    by (simp add: algebra_simps)
  have const_int: "(LBINT t=0..1. (grad x \<bullet> ?d)) = (grad x \<bullet> ?d)"
    by (simp add: one_ereal_def zero_ereal_def)
  have psi_pointwise: "\<And>t. t \<in> {0..1} \<Longrightarrow> ?psi t \<le> L * t * (norm ?d)^2"
  proof -
    fix t :: real
    assume t01: "t \<in> {0..1}"
    have tnonneg: "0 \<le> t" using t01 by auto
    have cs: "?psi t \<le> norm (grad (?h t) - grad x) * norm ?d"
      using norm_cauchy_schwarz by blast
    have gx: "norm (grad (?h t) - grad x) \<le> L * norm (?h t - x)"
      using lip[of "?h t" x] by (simp add: norm_minus_commute)
    have hx: "?h t - x = t *\<^sub>R ?d"
      by (simp add: algebra_simps)
    have nhx: "norm (?h t - x) = t * norm ?d"
      using tnonneg by simp
    have "norm (grad (?h t) - grad x) * norm ?d  \<le> (L * (t * norm ?d)) * norm ?d"
      by (metis gx mult_right_mono nhx norm_ge_zero)
    hence "norm (grad (?h t) - grad x) * norm ?d \<le> L * t * (norm ?d)^2"
      by (simp add: algebra_simps power2_eq_square)
    thus "?psi t \<le> L * t * (norm ?d)^2"
      using cs by linarith
  qed
  have psi_lip: "lipschitz_on (L * (norm ?d)^2) {0..1} ?psi"
    using phi_lip unfolding lipschitz_on_def 
    by (simp add: dist_real_def inner_commute inner_diff_right)
  then have cont_psi: "continuous_on {0..1} ?psi"
    using lipschitz_on_continuous_on by blast
  have cont_rhs: "continuous_on {0..1} (\<lambda>t. L * t * (norm ?d)^2)"
    by (intro continuous_intros) 
  have psi_int_bound: "(LBINT t=0..1. ?psi t) \<le> (LBINT t=0..1. L * t * (norm ?d)^2)"
    using interval_integral_eq_integral by (smt (verit, ccfv_SIG) cont_psi cont_rhs 
          interval_integral_mono_on one_ereal_def psi_pointwise zero_ereal_def)
  have "(LBINT t=0..1. t) = (1/2::real)"      
    by (metis ereal_eq_0(1) interval_integral_id one_ereal_def
         power_one power_zero_numeral verit_minus_simplify(2))
  then have rhs_eval: "(LBINT t=0..1. L * t * (norm ?d)^2) = (L/2) * (norm ?d)^2"
    by simp
  have "(LBINT t=0..1. ?phi t) \<le> (grad x \<bullet> ?d) + (L/2) * (norm ?d)^2"
  proof -
   have "(LBINT t=0..1. ?phi t) = (LBINT t=0..1. (grad x \<bullet> ?d)) + (LBINT t=0..1. ?psi t)"
    proof -
      have "(LBINT t=0..1. ?phi t) = (LBINT t=0..1. (grad x \<bullet> ?d) + ?psi t)"
        using phi_split by simp
      also have "... = (LBINT t=0..1. (grad x \<bullet> ?d)) + (LBINT t=0..1. ?psi t)"
      proof -
        have int_const: "interval_lebesgue_integrable lborel 0 1 (\<lambda>t. (grad x \<bullet> ?d))"
        proof -
          have "continuous_on {0..1} (\<lambda>t. (grad x \<bullet> ?d))"
            by (intro continuous_intros)
          thus ?thesis
            by (simp add: one_ereal_def zero_ereal_def)
        qed
        have int_psi: "interval_lebesgue_integrable lborel 0 1 ?psi"
          by (simp add: cont_psi interval_integrable_continuous_on one_ereal_def zero_ereal_def)
        show ?thesis
          using int_const int_psi by simp
      qed
      finally show ?thesis.
    qed
    also have "... \<le> (grad x \<bullet> ?d) + (LBINT t=0..1. L * t * (norm ?d)^2)"
      using const_int psi_int_bound by simp
    also have "... = (grad x \<bullet> ?d) + (L/2) * (norm ?d)^2"
      using rhs_eval by presburger
    finally show ?thesis.
  qed
  then show "f y \<le> f x + grad x \<bullet> (y - x) + L / 2 * \<parallel>y - x\<parallel>\<^sup>2"
    using line_int by simp
qed

lemma step_choice:
  assumes L_pos:      "0 < L"
      and step_size:  "\<And>x. \<alpha> x = 1 / L"
      and fst_deriv_L_smooth: "\<And>x y. f y \<le> f x + grad x \<bullet> (y - x) + (L/2)*\<parallel>y - x\<parallel>\<^sup>2"
      and PL: "\<And>x. 2 * \<mu> * (f x - f x_min) \<le> grad x \<bullet> grad x"
  shows "\<And>x. f (x - \<alpha> x *\<^sub>R grad x) - f x_min \<le> (1 - (\<alpha> x) * \<mu>) * (f x - f x_min)"
proof -
  fix x
  have L_ne0: "L \<noteq> 0"
    using L_pos by auto
  have \<alpha>_pos: "0 < \<alpha> x"
    using L_pos step_size by simp
  have descent: "f (x - \<alpha> x *\<^sub>R grad x) \<le> f x - (1/(2*L)) * (grad x \<bullet> grad x)"    
  proof -
    let ?g = "grad x \<bullet> grad x"
    have h1:  "f (x - \<alpha> x *\<^sub>R grad x) 
        \<le> f x + (- (\<alpha> x) * (grad x \<bullet> grad x)) + (L / 2) * ((\<alpha> x)^2 * (grad x \<bullet> grad x))"
      by (smt (verit, best) \<alpha>_pos add_diff_cancel_left' add_uminus_conv_diff assms(3) 
          inner_scaleR_right norm_scaleR power2_norm_eq_inner
          power_mult_distrib scaleR_minus_left)
    have h2: "f x + (- (\<alpha> x) * ?g) + (L / 2) * ((\<alpha> x)^2 * ?g)  = f x - (1/(2*L)) * ?g"
      using L_ne0 by (simp add: step_size field_simps power2_eq_square)
    show ?thesis
      by (metis h1 h2)
  qed
  have "(\<mu> / L) * (f x - f x_min) \<le> (1/(2*L)) * (grad x \<bullet> grad x)"
  proof -
    have c_nonneg: "0 \<le> (1/(2*L))"
      using L_pos by simp
    have PLx: "2 * \<mu> * (f x - f x_min) \<le> grad x \<bullet> grad x"
      using PL by simp
    have "(1/(2*L)) * (2 * \<mu> * (f x - f x_min)) \<le> (1/(2*L)) * (grad x \<bullet> grad x)"
      using mult_left_mono[OF PLx c_nonneg].
    with L_ne0 show ?thesis
      by simp
  qed
  with descent show  "f (x - \<alpha> x *\<^sub>R grad x) - f x_min \<le> (1 - \<alpha> x * \<mu>) * (f x - f x_min)"
    by (simp add: step_size field_simps, argo)
qed

lemma grad_sq_le_gap_from_smoothness:
  fixes f     :: "'a::euclidean_space \<Rightarrow> real"
    and \<alpha>     :: "'a \<Rightarrow> real"
  assumes L_pos:     "0 < L"
      and step_size: "\<And>x. \<alpha> x = 1 / L"
      and f_min:     "\<And>x. f x_min \<le> f x"
      and smooth_upper: "\<And>x y. f y \<le> f x + grad x \<bullet> (y - x) + (L/2)*\<parallel>y - x\<parallel>^2"
  shows "\<And>x. grad x \<bullet> grad x \<le> 2 *L*(f x - f x_min)"
proof -
  fix x
  have L_ne0: "L \<noteq> 0" using L_pos by auto
  have "(norm ((x - \<alpha> x *\<^sub>R grad x) - x))^2 = (\<alpha> x)^2 * (grad x \<bullet> grad x)"
    by (simp add: power2_norm_eq_inner power_mult_distrib)
  then have "f (x - \<alpha> x *\<^sub>R grad x)
     \<le> f x + (- (\<alpha> x) * (grad x \<bullet> grad x))  + (L / 2) * ((\<alpha> x)^2 * (grad x \<bullet> grad x))"
    by (smt (verit, best) assms(4) cancel_ab_semigroup_add_class.diff_right_commute 
        diff_0 diff_self inner_scaleR_right scaleR_minus_left)
  with L_ne0 have "f (x - \<alpha> x *\<^sub>R grad x) \<le> f x - (1/(2*L)) * (grad x \<bullet> grad x)"
    by (simp add: step_size field_simps power2_eq_square)
  then  have "(1/(2*L)) * (grad x \<bullet> grad x) \<le> f x - f x_min"
    by (smt (verit, best) assms(3))
  thus "grad x \<bullet> grad x \<le> 2 * L * (f x - f x_min)"
    using L_pos by (simp add: field_simps)
qed

subsection \<open>Algorithm\<close>

alphabet 'i st = lvstore +
  iter :: nat
  x    :: "real vec['i]"
instantiation st_ext :: (finite, default) default
begin
definition default_st_ext :: "('a,'b) st_ext" where
  "default_st_ext = \<lparr> iter\<^sub>v = 0, x\<^sub>v = 0, \<dots> = default\<rparr>"
instance ..
end

program gradient_descent
 "(grad :: \<real> vec['i] \<Rightarrow> \<real> vec['i], x0 :: \<real> vec['i], \<alpha> :: \<real> vec['i] \<Rightarrow> \<real>, \<epsilon> :: \<real>)"
 over "'i::finite st" =
"x:= x0; iter:= 0; while (grad(x) \<bullet> grad(x) > \<epsilon>\<^sup>2) do x:= x-(\<alpha> x) *\<^sub>R grad(x); iter:= iter+1 od"

execute "gradient_descent (\<lambda>x. (2 *\<^sub>R x) - Vector[2,-4], Vector[10,0], (\<lambda>x. 0.25),  0.01)"
(*Terminates: \<lparr>local_store\<^sub>v = pfun_of_alist [], iter\<^sub>v = 11, x\<^sub>v = \<^bold>[1.00439453125, - 1.9990234375\<^bold>]\<rparr> *)

definition R_gradient_descent ::
  "(real vec['i] \<Rightarrow> real vec['i]) \<Rightarrow> real vec['i] \<Rightarrow> (real vec['i] \<Rightarrow> real) \<Rightarrow> real
     \<Rightarrow> (real vec['i] \<times> nat) nres" where
  "R_gradient_descent grad x0 \<alpha> \<epsilon> \<equiv>
     WHILET (\<lambda>(x, iter). grad x \<bullet> grad x > \<epsilon>\<^sup>2)
            (\<lambda>(x, iter). RETURN (x - (\<alpha> x) *\<^sub>R grad x, iter + 1))
            (x0, 0)"

section \<open>General case: nonconvex L-smooth (epsilon-stationary in O(L (f x0 - f x_min) / eps^2) steps)\<close>

section \<open>Paradigm B (general): Lammich's Refinement Framework (\<open>nres\<close>)\<close>

text \<open>Most general gradient-descent result: only \<open>L\<close>-smoothness (Lipschitz
  gradient) and \<open>f\<close> bounded below.  No convexity, no PL inequality.  Plain GD
  with fixed step \<open>1/L\<close> reaches an \<open>\<epsilon>\<close>-stationary point (\<open>\<parallel>grad x\<parallel> \<le> \<epsilon>\<close>) in
  \<open>O(L (f x0 - f x_min) / \<epsilon>\<^sup>2)\<close> steps.  Proof: the descent lemma plus telescoping
  (each looping step lowers \<open>f\<close> by at least \<open>\<epsilon>\<^sup>2/(2L)\<close>).\<close>

definition gd_bound_gen ::
  "(real vec['i] \<Rightarrow> real) \<Rightarrow> real vec['i] \<Rightarrow> real vec['i] \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat" where
  "gd_bound_gen f x0 x_min L \<epsilon> = nat \<lceil>2 * L * (f x0 - f x_min) / \<epsilon>\<^sup>2\<rceil>"

definition gd_invar_gen ::
  "(real vec['i] \<Rightarrow> real vec['i]) \<Rightarrow> (real vec['i] \<Rightarrow> real) \<Rightarrow> real vec['i] \<Rightarrow> real vec['i]
     \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real vec['i] \<times> nat) \<Rightarrow> bool" where
  "gd_invar_gen grad f x0 x_min L \<epsilon> \<equiv> \<lambda>(x, iter).
       real iter * (\<epsilon>\<^sup>2 / (2 * L)) \<le> f x0 - f x
     \<and> iter \<le> gd_bound_gen f x0 x_min L \<epsilon>
     \<and> (\<epsilon>\<^sup>2 < grad x \<bullet> grad x \<longrightarrow> iter < gd_bound_gen f x0 x_min L \<epsilon>)"

context
  fixes grad :: "real vec['i] \<Rightarrow> real vec['i]" and f :: "real vec['i] \<Rightarrow> real"
    and x0 x_min :: "real vec['i]" and \<alpha> :: "real vec['i] \<Rightarrow> real" and L \<epsilon> :: real
  assumes \<epsilon>_pos: "0 < \<epsilon>" and L_pos: "0 < L"
    and step_size: "\<And>x. \<alpha> x = 1 / L"
    and f_min: "\<And>x. f x_min \<le> f x"
    and grad_correct: "\<And>x. (f has_derivative (\<lambda>h. grad x \<bullet> h)) (at x)"
    and grad_Lipschitz: "\<And>x y. \<parallel>grad x - grad y\<parallel> \<le> L * \<parallel>x - y\<parallel>"
begin

lemma gen_smooth: "f v \<le> f u + grad u \<bullet> (v - u) + (L/2) * \<parallel>v - u\<parallel>\<^sup>2"
  by (meson L_pos grad_Lipschitz descent_lemma_from_Lipschitz_gradient grad_correct le_less)

lemma gen_descent:
  fixes x :: "real vec['i]"
  shows "f (x - \<alpha> x *\<^sub>R grad x) \<le> f x - (1/(2*L)) * (grad x \<bullet> grad x)"
proof -
  have L_ne0: "L \<noteq> 0" using L_pos by simp
  have a_pos: "0 < \<alpha> x" using L_pos step_size by simp
  let ?g = "grad x \<bullet> grad x"
  have h1: "f (x - \<alpha> x *\<^sub>R grad x)
      \<le> f x + (- (\<alpha> x) * (grad x \<bullet> grad x)) + (L / 2) * ((\<alpha> x)^2 * (grad x \<bullet> grad x))"
    by (smt (verit, best) a_pos add_diff_cancel_left' add_uminus_conv_diff gen_smooth
        inner_scaleR_right norm_scaleR power2_norm_eq_inner power_mult_distrib scaleR_minus_left)
  have h2: "f x + (- (\<alpha> x) * ?g) + (L / 2) * ((\<alpha> x)^2 * ?g) = f x - (1/(2*L)) * ?g"
    using L_ne0 by (simp add: step_size field_simps power2_eq_square)
  show ?thesis by (metis h1 h2)
qed

lemma gd_iter_lt_bound_gen:
  fixes x :: "real vec['i]" and iter :: nat
  assumes energy: "real iter * (\<epsilon>\<^sup>2 / (2*L)) \<le> f x0 - f x"
    and looping: "\<epsilon>\<^sup>2 < grad x \<bullet> grad x"
  shows "iter < gd_bound_gen f x0 x_min L \<epsilon>"
proof -
  have eps2_pos: "0 < \<epsilon>\<^sup>2" using \<epsilon>_pos by simp
  let ?c = "\<epsilon>\<^sup>2 / (2*L)"
  have c_pos: "0 < ?c" using eps2_pos L_pos by simp
  have half_pos: "0 < 1/(2*L)" using L_pos by simp
  have c_lt: "?c < (1/(2*L)) * (grad x \<bullet> grad x)"
    using mult_strict_left_mono[OF looping half_pos] by simp
  have "f (x - \<alpha> x *\<^sub>R grad x) < f x - ?c" using gen_descent[of x] c_lt by linarith
  hence fx_gt: "f x_min < f x - ?c" using f_min[of "x - \<alpha> x *\<^sub>R grad x"] by linarith
  have dd: "(real iter + 1) * ?c = real iter * ?c + ?c" by (simp add: distrib_right add_divide_distrib)
  have step1: "(real iter + 1) * ?c < f x0 - f x_min" using dd energy fx_gt by linarith
  have iter_c: "real iter * ?c < f x0 - f x_min" using dd step1 c_pos by linarith
  have "real iter < 2 * L * (f x0 - f x_min) / \<epsilon>\<^sup>2"
    using iter_c L_pos eps2_pos by (simp add: field_simps)
  hence "int iter < \<lceil>2 * L * (f x0 - f x_min) / \<epsilon>\<^sup>2\<rceil>" by (simp add: less_ceiling_iff)
  thus "iter < gd_bound_gen f x0 x_min L \<epsilon>"
    by (simp add: gd_bound_gen_def zless_nat_eq_int_zless)
qed

lemma gd_invar_step_gen:
  fixes x :: "real vec['i]" and iter :: nat
  assumes inv: "gd_invar_gen grad f x0 x_min L \<epsilon> (x, iter)"
    and guard: "\<epsilon>\<^sup>2 < grad x \<bullet> grad x"
  shows "gd_invar_gen grad f x0 x_min L \<epsilon> (x - \<alpha> x *\<^sub>R grad x, iter + 1)
       \<and> ((x - \<alpha> x *\<^sub>R grad x, iter + 1), (x, iter))
           \<in> Wellfounded.measure (\<lambda>(x, iter). gd_bound_gen f x0 x_min L \<epsilon> - iter)"
proof -
  let ?N = "gd_bound_gen f x0 x_min L \<epsilon>"
  let ?x' = "x - \<alpha> x *\<^sub>R grad x"
  let ?c = "\<epsilon>\<^sup>2 / (2*L)"
  from inv have energy: "real iter * ?c \<le> f x0 - f x" by (auto simp: gd_invar_gen_def)
  have iter_lt: "iter < ?N" using gd_iter_lt_bound_gen[OF energy guard] .
  have half_pos: "0 < 1/(2*L)" using L_pos by simp
  have c_lt: "?c < (1/(2*L)) * (grad x \<bullet> grad x)"
    using mult_strict_left_mono[OF guard half_pos] by simp
  have fle: "f ?x' \<le> f x - ?c" using gen_descent[of x] c_lt by linarith
  have energy': "real (iter + 1) * ?c \<le> f x0 - f ?x'"
  proof -
    have "real (iter + 1) * ?c = real iter * ?c + ?c" by (simp add: distrib_right add_divide_distrib)
    thus ?thesis using energy fle by linarith
  qed
  have iterN': "iter + 1 \<le> ?N" using iter_lt by simp
  have inv': "gd_invar_gen grad f x0 x_min L \<epsilon> (?x', iter + 1)"
    unfolding gd_invar_gen_def using energy' iterN' gd_iter_lt_bound_gen[OF energy'] by auto
  have "?N - (iter + 1) < ?N - iter" using iter_lt by linarith
  hence var: "((?x', iter + 1), (x, iter)) \<in> Wellfounded.measure (\<lambda>(x, iter). ?N - iter)"
    by simp 
  show ?thesis using inv' var by simp
qed

lemma gd_exit_gen:
  fixes x :: "real vec['i]" and iter :: nat
  assumes inv: "gd_invar_gen grad f x0 x_min L \<epsilon> (x, iter)"
    and nguard: "\<not> \<epsilon>\<^sup>2 < grad x \<bullet> grad x"
  shows "\<parallel>grad x\<parallel> \<le> \<epsilon> \<and> iter \<le> gd_bound_gen f x0 x_min L \<epsilon>"
proof -
  from inv have iterN: "iter \<le> gd_bound_gen f x0 x_min L \<epsilon>" by (auto simp: gd_invar_gen_def)
  have "\<parallel>grad x\<parallel>\<^sup>2 \<le> \<epsilon>\<^sup>2" using nguard by (simp add: power2_norm_eq_inner)
  hence "\<parallel>grad x\<parallel> \<le> \<epsilon>" using \<epsilon>_pos by (smt (verit) norm_ge_zero power2_le_imp_le)
  thus ?thesis using iterN by simp
qed

theorem R_gradient_descent_general_correct:
  "R_gradient_descent grad x0 \<alpha> \<epsilon>
     \<le> SPEC (\<lambda>(x, iter). \<parallel>grad x\<parallel> \<le> \<epsilon> \<and> iter \<le> gd_bound_gen f x0 x_min L \<epsilon>)"
  unfolding R_gradient_descent_def
  apply (refine_vcg WHILET_rule[where I = "gd_invar_gen grad f x0 x_min L \<epsilon>"
            and R = "Wellfounded.measure (\<lambda>(x, iter). gd_bound_gen f x0 x_min L \<epsilon> - iter)"])
  subgoal by simp
  subgoal using gd_iter_lt_bound_gen[where x = x0 and iter = 0] by (auto simp: gd_invar_gen_def)
  subgoal for s using gd_invar_step_gen by (cases s) (auto simp: in_measure)
  subgoal for s using gd_invar_step_gen by (cases s) (auto simp: in_measure)
  subgoal for s using gd_exit_gen by (cases s) auto
  subgoal for s using gd_exit_gen by (cases s) auto
  done

end

section \<open>Paradigm A (general): Imperative ITree Program, VCG-based Hoare Logic\<close>

program gradient_descent_gen_aux
 "(grad :: real vec['i] \<Rightarrow> real vec['i], x0 :: real vec['i],
   \<alpha> :: real vec['i] \<Rightarrow> real, \<epsilon> :: real,
   f :: real vec['i] \<Rightarrow> real, L :: real, x_min :: real vec['i])"
 over "'i::finite st" =
"x := x0; iter := 0;
 while (grad(x) \<bullet> grad(x) > \<epsilon>\<^sup>2)
  invariant real iter * (\<epsilon>\<^sup>2 / (2*L)) \<le> f x0 - f x
    \<and> iter \<le> nat \<lceil>2*L*(f x0 - f x_min)/\<epsilon>\<^sup>2\<rceil>
    \<and> (\<parallel>grad(x)\<parallel> > \<epsilon> \<longrightarrow> iter + 1 \<le> nat \<lceil>2*L*(f x0 - f x_min)/\<epsilon>\<^sup>2\<rceil>)
  variant nat \<lceil>2*L*(f x0 - f x_min)/\<epsilon>\<^sup>2\<rceil> - iter
  do x := x - (\<alpha> x) *\<^sub>R grad(x); iter := iter + 1 od"

lemma gradient_descent_gen_aux_is_gradient_descent:
  "gradient_descent_gen_aux (grad, x0, \<alpha>, \<epsilon>, f, L, x_min) = gradient_descent (grad, x0, \<alpha>, \<epsilon>)"
  by (simp add: gradient_descent_gen_aux_def gradient_descent_def while_inv_def while_inv_var_def)

theorem gradient_descent_gen_aux_convergence:
  assumes \<epsilon>_pos: "0 < \<epsilon>" and L_pos: "0 < L"
    and step_size: "\<And>x. \<alpha> x = 1 / L"
    and f_min: "\<And>x. f x_min \<le> f x"
    and grad_correct: "\<And>x. (f has_derivative (\<lambda>h. grad x \<bullet> h)) (at x)"
    and grad_Lipschitz: "\<And>x y. \<parallel>grad x - grad y\<parallel> \<le> L * \<parallel>x - y\<parallel>"
  shows "H[True] gradient_descent_gen_aux (grad, x0, \<alpha>, \<epsilon>, f, L, x_min)
     [\<parallel>grad x\<parallel> \<le> \<epsilon> \<and> iter \<le> nat \<lceil>2*L*(f x0 - f x_min)/\<epsilon>\<^sup>2\<rceil>]"
proof -
  \<comment> \<open>Per-step energy decrease (the descent lemma at the line-search step); used by VCs 5 and 6.\<close>
  have step_gain: "\<And>x. \<epsilon>\<^sup>2 < grad x \<bullet> grad x \<Longrightarrow> \<epsilon>\<^sup>2 / (2 * L) \<le> f x - f (x - \<alpha> x *\<^sub>R grad x)"
  proof -
    fix x assume g: "\<epsilon>\<^sup>2 < grad x \<bullet> grad x"
    have "f (x - \<alpha> x *\<^sub>R grad x) \<le> f x - (grad x \<bullet> grad x) / (2 * L)"
      by (metis (no_types, lifting) assms(2,3,5,6) f_min gen_descent inner_scaleR_right
          scaleR_one times_divide_eq_left)
    moreover have "\<epsilon>\<^sup>2 / (2 * L) \<le> (grad x \<bullet> grad x) / (2 * L)"
      using g L_pos by (simp add: divide_right_mono)
    ultimately show "\<epsilon>\<^sup>2 / (2 * L) \<le> f x - f (x - \<alpha> x *\<^sub>R grad x)" by linarith
  qed
  \<comment> \<open>One iteration preserves the accumulated-energy invariant.\<close>
  have energy_next: "\<And>iter x. \<lbrakk>real iter * \<epsilon>\<^sup>2 / (2 * L) \<le> f x0 - f x; \<epsilon>\<^sup>2 < grad x \<bullet> grad x\<rbrakk>
      \<Longrightarrow> (1 + real iter) * \<epsilon>\<^sup>2 / (2 * L) \<le> f x0 - f (x - \<alpha> x *\<^sub>R grad x)"
  proof -
    fix iter x
    assume IH: "real iter * \<epsilon>\<^sup>2 / (2 * L) \<le> f x0 - f x" and g: "\<epsilon>\<^sup>2 < grad x \<bullet> grad x"
    have "(1 + real iter) * \<epsilon>\<^sup>2 / (2 * L) = real iter * \<epsilon>\<^sup>2 / (2 * L) + \<epsilon>\<^sup>2 / (2 * L)"
      by (simp add: algebra_simps add_divide_distrib)
    thus "(1 + real iter) * \<epsilon>\<^sup>2 / (2 * L) \<le> f x0 - f (x - \<alpha> x *\<^sub>R grad x)"
      using IH step_gain[OF g] by linarith
  qed
  show ?thesis
  proof (vcg)
    \<comment> \<open>VCs 1--4: the guard \<open>\<epsilon>\<^sup>2 < grad x \<bullet> grad x\<close> contradicts \<open>\<not> \<epsilon> < \<parallel>grad x\<parallel>\<close>.\<close>
    show "\<And>iter x. \<lbrakk>\<epsilon>\<^sup>2 < grad x \<bullet> grad x; \<not> \<epsilon> < \<parallel>grad x\<parallel>\<rbrakk>
         \<Longrightarrow> (1 + real iter) * \<epsilon>\<^sup>2 / (2 * L) \<le> f x0 - f (x - \<alpha> x *\<^sub>R grad x)"
      using norm_gt_square by blast
    show "\<And>iter x. \<lbrakk>\<epsilon>\<^sup>2 < grad x \<bullet> grad x; \<not> \<epsilon> < \<parallel>grad x\<parallel>\<rbrakk>
         \<Longrightarrow> Suc iter \<le> nat \<lceil>2 * L * (f x0 - f x_min) / \<epsilon>\<^sup>2\<rceil>"
      using norm_gt_square by blast
    show "\<And>iter x. \<lbrakk>\<epsilon>\<^sup>2 < grad x \<bullet> grad x; \<not> \<epsilon> < \<parallel>grad x\<parallel>\<rbrakk>
         \<Longrightarrow> Suc (Suc iter) \<le> nat \<lceil>2 * L * (f x0 - f x_min) / \<epsilon>\<^sup>2\<rceil>"
      using norm_gt_square by blast
    show "\<And>iter x. \<lbrakk>\<epsilon>\<^sup>2 < grad x \<bullet> grad x; \<not> \<epsilon> < \<parallel>grad x\<parallel>\<rbrakk>
         \<Longrightarrow> nat \<lceil>2 * L * (f x0 - f x_min) / \<epsilon>\<^sup>2\<rceil> - Suc iter < nat \<lceil>2 * L * (f x0 - f x_min) / \<epsilon>\<^sup>2\<rceil> - iter"
      using norm_gt_square by blast
    \<comment> \<open>VC 5: one step preserves the energy invariant.\<close>
    show "\<And>iter x. \<lbrakk>real iter * \<epsilon>\<^sup>2 / (2 * L) \<le> f x0 - f x; \<epsilon>\<^sup>2 < grad x \<bullet> grad x;
          Suc iter \<le> nat \<lceil>2 * L * (f x0 - f x_min) / \<epsilon>\<^sup>2\<rceil>\<rbrakk>
         \<Longrightarrow> (1 + real iter) * \<epsilon>\<^sup>2 / (2 * L) \<le> f x0 - f (x - \<alpha> x *\<^sub>R grad x)"
      using energy_next by blast
    \<comment> \<open>VC 6: while still looping, the iteration bound advances by one.\<close>
    show "\<And>iter x. \<lbrakk>real iter * \<epsilon>\<^sup>2 / (2 * L) \<le> f x0 - f x; \<epsilon>\<^sup>2 < grad x \<bullet> grad x;
          Suc iter \<le> nat \<lceil>2 * L * (f x0 - f x_min) / \<epsilon>\<^sup>2\<rceil>;
          \<epsilon> < \<parallel>grad (x - \<alpha> x *\<^sub>R grad x)\<parallel>\<rbrakk>
         \<Longrightarrow> Suc (Suc iter) \<le> nat \<lceil>2 * L * (f x0 - f x_min) / \<epsilon>\<^sup>2\<rceil>"
    proof -
      fix iter x
      assume IH: "real iter * \<epsilon>\<^sup>2 / (2 * L) \<le> f x0 - f x"
        and grad_gt: "\<epsilon>\<^sup>2 < grad x \<bullet> grad x"
        and grad_gt': "\<epsilon> < \<parallel>grad (x - \<alpha> x *\<^sub>R grad x)\<parallel>"
      have e': "real (iter + 1) * (\<epsilon>\<^sup>2 / (2 * L)) \<le> f x0 - f (x - \<alpha> x *\<^sub>R grad x)"
        using energy_next[OF IH grad_gt] by simp
      have g': "\<epsilon>\<^sup>2 < grad (x - \<alpha> x *\<^sub>R grad x) \<bullet> grad (x - \<alpha> x *\<^sub>R grad x)"
        using grad_gt' \<epsilon>_pos norm_gt_square by (metis basic_trans_rules(20))
      have "iter + 1 < gd_bound_gen f x0 x_min L \<epsilon>"
        by (metis assms(1,2,3,4,5,6) e' g' gd_iter_lt_bound_gen)
      thus "Suc (Suc iter) \<le> nat \<lceil>2 * L * (f x0 - f x_min) / \<epsilon>\<^sup>2\<rceil>"
        by (simp add: gd_bound_gen_def)
    qed
    \<comment> \<open>VC 7: the bound is positive at the start.\<close>
    show "\<lbrakk>\<epsilon> < \<parallel>grad x0\<parallel>\<rbrakk> \<Longrightarrow> Suc 0 \<le> nat \<lceil>2 * L * (f x0 - f x_min) / \<epsilon>\<^sup>2\<rceil>"
    proof -
      assume grad_gt0: "\<epsilon> < \<parallel>grad x0\<parallel>"
      have g0: "\<epsilon>\<^sup>2 < grad x0 \<bullet> grad x0"
        using grad_gt0 \<epsilon>_pos norm_gt_square by (metis basic_trans_rules(20))
      have e0: "real 0 * (\<epsilon>\<^sup>2 / (2 * L)) \<le> f x0 - f x0" by simp
      have "0 < gd_bound_gen f x0 x_min L \<epsilon>"
        by (metis assms(1,2,3,4,5,6) e0 g0 gd_iter_lt_bound_gen)
      thus "Suc 0 \<le> nat \<lceil>2 * L * (f x0 - f x_min) / \<epsilon>\<^sup>2\<rceil>"
        by (simp add: gd_bound_gen_def, linarith)
    qed
    \<comment> \<open>VC 8: on loop exit the gradient is small.\<close>
    show "\<And>iter x. \<lbrakk>\<not> \<epsilon>\<^sup>2 < grad x \<bullet> grad x; real iter * \<epsilon>\<^sup>2 / (2 * L) \<le> f x0 - f x;
          Suc iter \<le> nat \<lceil>2 * L * (f x0 - f x_min) / \<epsilon>\<^sup>2\<rceil>\<rbrakk> \<Longrightarrow> \<parallel>grad x\<parallel> \<le> \<epsilon>"
      by (smt (verit, ccfv_threshold) \<epsilon>_pos norm_gt_square)
  qed
qed




section \<open>Linear case: Polyak--Lojasiewicz, fixed step 1/L (linear rate)\<close>
section \<open>Paradigm B: Lammich's Refinement Framework (\<open>nres\<close>)\<close>


definition gd_bound :: "(real vec['i] \<Rightarrow> real) \<Rightarrow> real vec['i] \<Rightarrow> real vec['i] \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat"
  where
  "gd_bound f x0 x_min L \<mu> \<epsilon> = nat \<lceil>ln (2 * L * (f x0 - f x_min) / \<epsilon>\<^sup>2) / ln (1 / (1 - \<mu>/L))\<rceil>"

definition gd_invar ::
  "(real vec['i] \<Rightarrow> real vec['i]) \<Rightarrow> (real vec['i] \<Rightarrow> real) \<Rightarrow> real vec['i] \<Rightarrow> real vec['i]
     \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real vec['i] \<times> nat) \<Rightarrow> bool" where
  "gd_invar grad f x0 x_min L \<mu> \<epsilon> \<equiv> \<lambda>(x, iter).
       f x - f x_min \<le> (f x0 - f x_min) * (1 - \<mu>/L) ^ iter
     \<and> iter \<le> gd_bound f x0 x_min L \<mu> \<epsilon>
     \<and> (\<epsilon>\<^sup>2 < grad x \<bullet> grad x \<longrightarrow> iter < gd_bound f x0 x_min L \<mu> \<epsilon>)"

context
  fixes grad :: "real vec['i] \<Rightarrow> real vec['i]"
    and f :: "real vec['i] \<Rightarrow> real"
    and x0 x_min :: "real vec['i]"
    and \<alpha> :: "real vec['i] \<Rightarrow> real"
    and L \<mu> \<epsilon> :: real
  assumes \<epsilon>_pos: "0 < \<epsilon>" and L_pos: "0 < L" and \<mu>_pos: "0 < \<mu>" and \<mu>_lt_L: "\<mu> < L"
    and step_size: "\<And>x. \<alpha> x = 1 / L"
    and f_min: "\<And>x. f x_min \<le> f x"
    and grad_correct: "\<And>x. (f has_derivative (\<lambda>h. grad x \<bullet> h)) (at x)"
    and grad_Lipschitz: "\<And>x y. \<parallel>grad x - grad y\<parallel> \<le> L * \<parallel>x - y\<parallel>"
    and PL: "\<And>x. 2 * \<mu> * (f x - f x_min) \<le> grad x \<bullet> grad x"
begin

lemma gd_smooth: "f v \<le> f u + grad u \<bullet> (v - u) + (L/2) * \<parallel>v - u\<parallel>\<^sup>2"
  by (meson L_pos grad_Lipschitz descent_lemma_from_Lipschitz_gradient grad_correct le_less)

lemma gd_grad_le_gap:
  fixes x :: "real vec['i]"
  shows "grad x \<bullet> grad x \<le> 2 * L * (f x - f x_min)"
  using grad_sq_le_gap_from_smoothness[OF L_pos step_size f_min gd_smooth, of x] .

text \<open>While the loop runs, the iteration count is strictly below the bound.\<close>

lemma gd_iter_lt_bound:
  fixes x :: "real vec['i]" and iter :: nat
  assumes energy: "f x - f x_min \<le> (f x0 - f x_min) * (1 - \<mu>/L) ^ iter"
    and looping: "\<epsilon>\<^sup>2 < grad x \<bullet> grad x"
  shows "iter < gd_bound f x0 x_min L \<mu> \<epsilon>"
proof -
  define q where "q = \<mu>/L"
  define A where "A = 2 * L * (f x0 - f x_min)"
  have q_pos: "0 < q" using \<mu>_pos L_pos by (simp add: q_def)
  have q_lt1: "q < 1" using \<mu>_lt_L L_pos by (simp add: q_def field_simps)
  have omq_pos: "0 < 1 - q" using q_lt1 by simp
  have eps2_pos: "0 < \<epsilon>\<^sup>2" using \<epsilon>_pos by simp
  have pow_pos: "0 < (1 - q) ^ iter" using omq_pos by simp
  have e1: "\<epsilon>\<^sup>2 < A * (1 - q) ^ iter"
  proof -
    have "\<epsilon>\<^sup>2 < 2 * L * (f x - f x_min)" using looping gd_grad_le_gap[of x] by linarith
    also have "... \<le> 2 * L * ((f x0 - f x_min) * (1 - q) ^ iter)"
      using energy L_pos by (simp add: q_def mult_left_mono)
    finally show ?thesis by (simp add: A_def algebra_simps)
  qed
  have A_pos: "0 < A"
  proof -
    have "0 < A * (1 - q) ^ iter" using e1 eps2_pos by linarith
    thus ?thesis using pow_pos q_lt1 by (simp add: zero_less_mult_iff)
  qed
  have inv_ge1: "1 \<le> (1 / (1 - q)) ^ iter"
    using omq_pos q_pos by (simp add: one_le_power)
  have key: "(1 / (1 - q)) ^ iter < A / \<epsilon>\<^sup>2"
  proof -
    have "\<epsilon>\<^sup>2 / A < (1 - q) ^ iter" using e1 A_pos by (simp add: divide_less_eq mult.commute)
    hence "1 / (1 - q) ^ iter < A / \<epsilon>\<^sup>2"
      using pow_pos A_pos eps2_pos by (simp add: field_simps)
    thus ?thesis by (simp add: power_one_over)
  qed
  have AoverEps_gt1: "1 < A / \<epsilon>\<^sup>2" using key inv_ge1 by linarith
  have lnq_pos: "0 < ln (1 / (1 - q))" using omq_pos q_pos by simp
  have invq_pos: "0 < 1 / (1 - q)" using omq_pos by simp
  have "ln ((1 / (1 - q)) ^ iter) < ln (A / \<epsilon>\<^sup>2)"
    using key invq_pos AoverEps_gt1 by (simp add: zero_less_power)
  hence "real iter * ln (1 / (1 - q)) < ln (A / \<epsilon>\<^sup>2)"
    using invq_pos by (simp add: ln_realpow)
  hence "real iter < ln (A / \<epsilon>\<^sup>2) / ln (1 / (1 - q))"
    using lnq_pos by (simp add: pos_less_divide_eq)
  hence "int iter < \<lceil>ln (2 * L * (f x0 - f x_min) / \<epsilon>\<^sup>2) / ln (1 / (1 - \<mu>/L))\<rceil>"
    by (simp add: A_def q_def less_ceiling_iff)
  thus "iter < gd_bound f x0 x_min L \<mu> \<epsilon>"
    by (simp add: gd_bound_def zless_nat_eq_int_zless)
qed

text \<open>One step preserves the invariant and strictly decreases the variant.\<close>

lemma gd_invar_step:
  fixes x :: "real vec['i]" and iter :: nat
  assumes inv: "gd_invar grad f x0 x_min L \<mu> \<epsilon> (x, iter)"
    and guard: "\<epsilon>\<^sup>2 < grad x \<bullet> grad x"
  shows "gd_invar grad f x0 x_min L \<mu> \<epsilon> (x - \<alpha> x *\<^sub>R grad x, iter + 1)
       \<and> ((x - \<alpha> x *\<^sub>R grad x, iter + 1), (x, iter))
           \<in> Wellfounded.measure (\<lambda>(x, iter). gd_bound f x0 x_min L \<mu> \<epsilon> - iter)"
proof -
  let ?N = "gd_bound f x0 x_min L \<mu> \<epsilon>"
  let ?x' = "x - \<alpha> x *\<^sub>R grad x"
  from inv have energy: "f x - f x_min \<le> (f x0 - f x_min) * (1 - \<mu>/L) ^ iter"
    by (auto simp: gd_invar_def)
  have q_lt1: "\<mu>/L < 1" using \<mu>_lt_L L_pos by (simp add: field_simps)
  have omq_nonneg: "0 \<le> 1 - \<mu>/L" using q_lt1 by simp
  have iter_lt: "iter < ?N" using gd_iter_lt_bound[OF energy guard] .
  have contract: "f ?x' - f x_min \<le> (1 - \<mu>/L) * (f x - f x_min)"
  proof -
    have "f ?x' - f x_min \<le> (1 - \<alpha> x * \<mu>) * (f x - f x_min)"
      using step_choice[OF L_pos step_size gd_smooth PL, of x] .
    thus ?thesis by (simp add: step_size)
  qed
  have energy': "f ?x' - f x_min \<le> (f x0 - f x_min) * (1 - \<mu>/L) ^ (iter + 1)"
  proof -
    have "f ?x' - f x_min \<le> (1 - \<mu>/L) * (f x - f x_min)" using contract .
    also have "... \<le> (1 - \<mu>/L) * ((f x0 - f x_min) * (1 - \<mu>/L) ^ iter)"
      by (rule mult_left_mono[OF energy omq_nonneg])
    also have "... = (f x0 - f x_min) * (1 - \<mu>/L) ^ (iter + 1)"
      by (simp add: mult_ac)
    finally show ?thesis .
  qed
  have iterN': "iter + 1 \<le> ?N" using iter_lt by simp
  have inv': "gd_invar grad f x0 x_min L \<mu> \<epsilon> (?x', iter + 1)"
    unfolding gd_invar_def using energy' iterN' gd_iter_lt_bound[OF energy'] by auto
  have "?N - (iter + 1) < ?N - iter" using iter_lt by linarith
  hence var: "((?x', iter + 1), (x, iter))
                \<in> Wellfounded.measure (\<lambda>(x, iter). ?N - iter)" by (simp add: in_measure)
  show ?thesis using inv' var by simp
qed

text \<open>On exit the gradient is small and the iteration count is within the bound.\<close>

lemma gd_exit_prop:
  fixes x :: "real vec['i]" and iter :: nat
  assumes inv: "gd_invar grad f x0 x_min L \<mu> \<epsilon> (x, iter)"
    and nguard: "\<not> \<epsilon>\<^sup>2 < grad x \<bullet> grad x"
  shows "\<parallel>grad x\<parallel> \<le> \<epsilon> \<and> iter \<le> gd_bound f x0 x_min L \<mu> \<epsilon>"
proof -
  from inv have iterN: "iter \<le> gd_bound f x0 x_min L \<mu> \<epsilon>" by (auto simp: gd_invar_def)
  have "\<parallel>grad x\<parallel>\<^sup>2 \<le> \<epsilon>\<^sup>2" using nguard by (simp add: power2_norm_eq_inner)
  hence "\<parallel>grad x\<parallel> \<le> \<epsilon>" using \<epsilon>_pos by (smt (verit) norm_ge_zero power2_le_imp_le)
  thus ?thesis using iterN by simp
qed

theorem R_gradient_descent_correct:
  "R_gradient_descent grad x0 \<alpha> \<epsilon>
     \<le> SPEC (\<lambda>(x, iter). \<parallel>grad x\<parallel> \<le> \<epsilon> \<and> iter \<le> gd_bound f x0 x_min L \<mu> \<epsilon>)"
  unfolding R_gradient_descent_def
  apply (refine_vcg WHILET_rule[where I = "gd_invar grad f x0 x_min L \<mu> \<epsilon>"
            and R = "Wellfounded.measure (\<lambda>(x, iter). gd_bound f x0 x_min L \<mu> \<epsilon> - iter)"])
  subgoal by simp
  subgoal using gd_iter_lt_bound[of x0 0] by (auto simp: gd_invar_def)
  subgoal for s using gd_invar_step by (cases s) (auto simp: in_measure)
  subgoal for s using gd_invar_step by (cases s) (auto simp: in_measure)
  subgoal for s using gd_exit_prop by (cases s) auto
  subgoal for s using gd_exit_prop by (cases s) auto
  done

end

section \<open>Paradigm A (linear): Imperative ITree Program, VCG-based Hoare Logic\<close>

program gradient_descent_aux
 "(grad :: real vec['i] \<Rightarrow> real vec['i], x0 :: real vec['i],
   \<alpha> :: real vec['i] \<Rightarrow> real, \<epsilon> :: real,
   f :: real vec['i] \<Rightarrow> real, L :: real, \<mu> :: real, x_min :: real vec['i])"
 over "'i::finite st" =
"x := x0; iter := 0;
 while (grad(x) \<bullet> grad(x) > \<epsilon>\<^sup>2)
  invariant f(x) - f(x_min) \<le> (f(x0) - f(x_min)) * (1 - (\<alpha> x0) * \<mu>) ^ iter
   \<and>                       iter \<le> nat\<lceil>ln((2*L*(f x0 - f x_min)) / \<epsilon>\<^sup>2) / ln (1 / (1 - \<alpha>(x) * \<mu>))\<rceil> 
   \<and>  (\<parallel>grad(x)\<parallel> > \<epsilon> \<longrightarrow> iter+1 \<le> nat\<lceil>ln ((2*L*(f x0 - f x_min)) / \<epsilon>\<^sup>2) / ln (1 / (1 - \<alpha>(x) * \<mu>))\<rceil>)
  variant nat\<lceil>ln ((2*L*(f x0 - f x_min)) / \<epsilon>\<^sup>2) / ln (1 / (1 - \<alpha>(x) * \<mu>))\<rceil> - iter
  do x := x - (\<alpha> x) *\<^sub>R grad(x); iter := iter + 1 od"

lemma gradient_descent_aux_is_gradient_descent:
  "gradient_descent_aux (grad, x0, \<alpha>, \<epsilon>, f, L, \<mu>, x_min) = gradient_descent (grad, x0, \<alpha>, \<epsilon>)"
  by (simp add: gradient_descent_aux_def gradient_descent_def while_inv_def while_inv_var_def)

theorem gradient_descent_aux_linear_convergence:
  assumes \<epsilon>_pos:  "0 < \<epsilon>"
    and L_pos:  "0 < L"
    and \<mu>_pos:  "0 < \<mu>"
    and \<mu>_lt_L: "\<mu> < L"
    and step_size: "\<And>x. \<alpha> x = 1 / L"
    and f_min:  "\<And>x. f x_min \<le> f x"
    and grad_correct:"\<And>x. (f has_derivative (\<lambda>h. grad x \<bullet> h)) (at x)"
    and grad_Lipschitz: "\<And>x y. \<parallel>grad x - grad y\<parallel> \<le> L * \<parallel>x - y\<parallel>"
    and Polyak_Lojasiewicz: "\<And>x. 2 * \<mu> * (f x - f x_min) \<le> grad x \<bullet> grad x"
  shows "H[True] gradient_descent_aux (grad, x0, \<alpha>, \<epsilon>, f, L, \<mu>, x_min)
    [\<parallel>grad x\<parallel> \<le> \<epsilon> \<and> iter \<le> nat \<lceil>ln ((2 * L * (f x0 - f x_min)) / \<epsilon>\<^sup>2) / ln (1 / (1 - \<mu> / L))\<rceil>]"
proof -
  have fst_deriv_L_Lipshitz: "\<And>x y. f y \<le> f x + grad x \<bullet> (y - x) + (L / 2) * (norm (y - x))^2"
    by (meson L_pos assms(8) descent_lemma_from_Lipschitz_gradient grad_correct le_less)
  have grad_sq_le_gap: "\<And>z. grad z \<bullet> grad z \<le> 2 * L * (f z - f x_min)"
    using grad_sq_le_gap_from_smoothness[OF L_pos step_size f_min fst_deriv_L_Lipshitz] .
  have aqL: "\<And>z. \<alpha> z * \<mu> = \<mu> / L"
    using step_size L_pos by (simp add: field_simps)
  show ?thesis
    proof(vcg)
    show "\<And>iter x.\<lbrakk> \<epsilon>\<^sup>2 < grad x \<bullet> grad x; \<not> \<epsilon> < \<parallel>grad x\<parallel>\<rbrakk> \<Longrightarrow> 
      f (x - \<alpha> x *\<^sub>R grad x) - f x_min  \<le> (f x0 - f x_min) * ((1 - \<alpha> x0 * \<mu>) * (1 - \<alpha> x0 * \<mu>) ^ iter)" 
      using norm_gt_square by blast  
    show "\<And>iter x. \<lbrakk>\<epsilon>\<^sup>2 < grad x \<bullet> grad x; \<not> \<epsilon> < \<parallel>grad x\<parallel>\<rbrakk> \<Longrightarrow> 
      Suc iter      \<le> nat \<lceil>ln (2 * L * (f x0 - f x_min) / \<epsilon>\<^sup>2) /
                       ln (1 / (1 - \<alpha> (x - \<alpha> x *\<^sub>R grad x) * \<mu>))\<rceil>"
      using norm_gt_square by blast
    show "\<And>iter x.\<lbrakk> \<epsilon>\<^sup>2 < grad x \<bullet> grad x; \<not> \<epsilon> < \<parallel>grad x\<parallel>\<rbrakk> \<Longrightarrow> 
      Suc (Suc iter) \<le> nat \<lceil>ln (2 * L * (f x0 - f x_min) / \<epsilon>\<^sup>2) / 
                      ln (1 / (1 - \<alpha> (x - \<alpha> x *\<^sub>R grad x) * \<mu>))\<rceil>" 
      using norm_gt_square by blast
    show "\<And>iter x.\<lbrakk> \<epsilon>\<^sup>2 < grad x \<bullet> grad x; \<not> \<epsilon> < \<parallel>grad x\<parallel>\<rbrakk> \<Longrightarrow> 
      nat \<lceil>ln (2 * L * (f x0 - f x_min) / \<epsilon>\<^sup>2) /ln (1 / (1 - \<alpha> (x - \<alpha> x *\<^sub>R grad x) * \<mu>))\<rceil> - Suc iter  
    < nat \<lceil>ln (2 * L * (f x0 - f x_min) / \<epsilon>\<^sup>2) / ln (1 / (1 - \<alpha> x * \<mu>))\<rceil> - iter" 
      using norm_gt_square by blast
    show "\<And>iter x.\<lbrakk>Suc iter \<le> nat \<lceil>ln (2 * L * (f x0 - f x_min) / \<epsilon>\<^sup>2) / ln (1 / (1 - \<alpha> x * \<mu>))\<rceil>\<rbrakk> \<Longrightarrow> 
       Suc iter \<le> nat \<lceil>ln (2 * L * (f x0 - f x_min) / \<epsilon>\<^sup>2) / ln (1 / (1 - \<alpha> (x - \<alpha> x *\<^sub>R grad x) * \<mu>))\<rceil>"
      by (metis assms(5))
    show "\<And>iter x. \<lbrakk>\<not> \<epsilon>\<^sup>2 < grad x \<bullet> grad x\<rbrakk> \<Longrightarrow> \<parallel>grad x\<parallel> \<le> \<epsilon>" 
        by (smt (verit, ccfv_threshold) \<epsilon>_pos norm_gt_square)
    show "\<And>iter x. Suc iter \<le> nat \<lceil>ln (2 * L * (f x0 - f x_min) / \<epsilon>\<^sup>2) / ln (1 / (1 - \<alpha> x * \<mu>))\<rceil>
      \<Longrightarrow> nat \<lceil>ln (2 * L * (f x0 - f x_min) / \<epsilon>\<^sup>2) /ln (1 / (1 - \<alpha> (x - \<alpha> x *\<^sub>R grad x)*\<mu>))\<rceil> - Suc iter
        < nat \<lceil>ln (2 * L * (f x0 - f x_min) / \<epsilon>\<^sup>2) /ln (1 / (1 - \<alpha> x * \<mu>))\<rceil> - iter"
      by (metis assms(5) diff_less_mono2 le_simps(3) lessI) 
    show "\<And> iter x. iter \<le> nat \<lceil> ln (2 * L * (f x0 - f x_min) / \<epsilon>\<^sup>2)  / ln (1 / (1 - \<alpha> x * \<mu>)) \<rceil>  \<Longrightarrow>
                     iter \<le> nat \<lceil> ln (2 * L * (f x0 - f x_min) / \<epsilon>\<^sup>2)  / ln (1 / (1 - \<mu> / L)) \<rceil>"
      using assms(1,5) by auto
    thus "\<And>iter x. Suc iter \<le> nat \<lceil>ln (2 * L * (f x0 - f x_min) / \<epsilon>\<^sup>2) / ln (1 / (1 - \<alpha> x * \<mu>))\<rceil>
                    \<Longrightarrow> iter \<le> nat \<lceil>ln (2 * L * (f x0 - f x_min) / \<epsilon>\<^sup>2) / ln (1 / (1 - \<mu> / L))\<rceil>"
      by force   
  next
    assume eps_lt: "\<epsilon> < \<parallel>grad x0\<parallel>"
    have g0: "\<epsilon>\<^sup>2 < grad x0 \<bullet> grad x0"
      by (meson assms(1) basic_trans_rules(20) eps_lt norm_gt_square)
    have e0: "f x0 - f x_min \<le> (f x0 - f x_min) * (1 - \<mu>/L) ^ 0" by simp
    have "0 < gd_bound f x0 x_min L \<mu> \<epsilon>"
      by (metis assms(1,2,3,4,5,6,7,8,9) e0 g0 gd_iter_lt_bound)
    moreover have "gd_bound f x0 x_min L \<mu> \<epsilon>
                   = nat \<lceil>ln (2 * L * (f x0 - f x_min) / \<epsilon>\<^sup>2) / ln (1 / (1 - \<alpha> x0 * \<mu>))\<rceil>"
      using aqL by (simp add: gd_bound_def)
    ultimately show "Suc 0 \<le> nat \<lceil>ln (2 * L * (f x0 - f x_min) / \<epsilon>\<^sup>2) / ln (1 / (1 - \<alpha> x0 * \<mu>))\<rceil>"
      by linarith
  next
    fix iter x
    assume a1: "f x - f x_min \<le> (f x0 - f x_min) * (1 - \<alpha> x0 * \<mu>) ^ iter"
    assume a2: "\<epsilon>\<^sup>2 < grad x \<bullet> grad x"
    assume a3: "\<epsilon> < \<parallel>grad (x - \<alpha> x *\<^sub>R grad x)\<parallel>"
    have \<alpha>x_eq: "\<alpha> x = \<alpha> x0" by (simp add: step_size)
    have one_minus_q_pos: "0 < 1 - \<alpha> x0 * \<mu>"
      using \<mu>_lt_L L_pos by (simp add: step_size field_simps)
    \<comment> \<open>Energy at the next iterate: one step of @{thm step_choice}, lifted along the invariant.\<close>
    have gap_step: "f (x - \<alpha> x *\<^sub>R grad x) - f x_min \<le> (1 - \<alpha> x0 * \<mu>) * (f x - f x_min)"
      using step_choice[OF L_pos step_size fst_deriv_L_Lipshitz Polyak_Lojasiewicz, of x]
      by (simp add: \<alpha>x_eq)
    have gap_step2: "f (x - \<alpha> x *\<^sub>R grad x) - f x_min \<le> (f x0 - f x_min) * (1 - \<alpha> x0 * \<mu>) ^ (Suc iter)"
      by (smt (verit, best) a1 gap_step mult_le_cancel_left_pos one_minus_q_pos power.simps(2)
          real_scaleR_def scaleR_left_commute)
    have e': "f (x - \<alpha> x *\<^sub>R grad x) - f x_min \<le> (f x0 - f x_min) * (1 - \<mu>/L) ^ (Suc iter)"
      using gap_step2 aqL by simp
    have g': "\<epsilon>\<^sup>2 < grad (x - \<alpha> x *\<^sub>R grad x) \<bullet> grad (x - \<alpha> x *\<^sub>R grad x)"
      by (meson assms(1) basic_trans_rules(20) a3 norm_gt_square)
    \<comment> \<open>Iteration bound is shared with the Lammich side: @{thm gd_iter_lt_bound}.\<close>
    have "iter + 1 < gd_bound f x0 x_min L \<mu> \<epsilon>"
      by (metis L_pos Polyak_Lojasiewicz Suc_eq_plus1 \<epsilon>_pos \<mu>_pos assms(4,5,6) e' g' 
          gd_iter_lt_bound grad_Lipschitz grad_correct)
    moreover have "gd_bound f x0 x_min L \<mu> \<epsilon>
                   = nat \<lceil>ln (2 * L * (f x0 - f x_min) / \<epsilon>\<^sup>2) /
                            ln (1 / (1 - \<alpha> (x - \<alpha> x *\<^sub>R grad x) * \<mu>))\<rceil>"
      using aqL by (simp add: gd_bound_def)
    ultimately show "Suc (Suc iter) \<le> nat \<lceil>ln (2 * L * (f x0 - f x_min) / \<epsilon>\<^sup>2) /
                                     ln (1 / (1 - \<alpha> (x - \<alpha> x *\<^sub>R grad x) * \<mu>))\<rceil>"
      by linarith
  next
    fix iter x
    assume gap_iter: "f x - f x_min \<le> (f x0 - f x_min) * (1 - \<alpha> x0 * \<mu>) ^ iter"
    assume not_done: "\<epsilon>\<^sup>2 < grad x \<bullet> grad x"
    assume iter_bound: "Suc iter \<le> nat \<lceil>ln (2 * L * (f x0 - f x_min) / \<epsilon>\<^sup>2) / ln (1 / (1 - \<alpha> x * \<mu>))\<rceil>"
    have L_ne0: "L \<noteq> 0"
     using L_pos by simp
    have \<alpha>_const: "\<alpha> x = \<alpha> x0"
      using step_size by simp
    have \<alpha>x0_def: "\<alpha> x0 * \<mu> = \<mu> / L"
      using step_size L_pos by (simp add: field_simps)
    have \<mu>_div_L_lt1: "\<mu> / L < 1"
      using \<mu>_lt_L L_pos by (simp add: field_simps)
    have one_minus_nonneg: "0 \<le> 1 - \<alpha> x0 * \<mu>"
      using \<mu>_div_L_lt1 \<alpha>x0_def by simp
    \<comment> \<open>One step's gap decrease is exactly @{thm step_choice}.\<close>
    have "f (x - \<alpha> x *\<^sub>R grad x) - f x_min \<le> (1 - \<alpha> x * \<mu>) * (f x - f x_min)"
      using step_choice[OF L_pos step_size fst_deriv_L_Lipshitz Polyak_Lojasiewicz, of x] .
    also have "... = (1 - \<alpha> x0 * \<mu>) * (f x - f x_min)"
      using \<alpha>_const by simp
    also have "... \<le> (1 - \<alpha> x0 * \<mu>) * ((f x0 - f x_min) * (1 - \<alpha> x0 * \<mu>) ^ iter)"
      using gap_iter one_minus_nonneg by (intro mult_left_mono, simp)
    also have "... = (f x0 - f x_min) * ((1 - \<alpha> x0 * \<mu>) * (1 - \<alpha> x0 * \<mu>) ^ iter)"
      by (simp add: algebra_simps)
    finally show "f (x - \<alpha> x *\<^sub>R grad x) - f x_min 
      \<le> (f x0 - f x_min) * ((1 - \<alpha> x0 * \<mu>) * (1 - \<alpha> x0 * \<mu>) ^ iter)".
  qed
qed

theorem gradient_descent_linear_convergence:
  assumes \<epsilon>_pos:  "0 < \<epsilon>"
    and L_pos:  "0 < L"
    and \<mu>_pos:  "0 < \<mu>"
    and \<mu>_lt_L: "\<mu> < L"
    and step_size: "\<And>x. \<alpha> x = 1 / L"
    and f_min:  "\<And>x. f x_min \<le> f x"
    and grad_correct: "\<And>x. (f has_derivative (\<lambda>h. grad x \<bullet> h)) (at x)"
    and grad_Lipschitz: "\<And>x y. \<parallel>grad x - grad y\<parallel> \<le> L * \<parallel>x - y\<parallel>"
    and Polyak_Lojasiewicz: "\<And>x. 2 * \<mu> * (f x - f x_min) \<le> grad x \<bullet> grad x"
  shows "H[True] gradient_descent (grad, x0, \<alpha>, \<epsilon>)
      [\<parallel>grad x\<parallel> \<le> \<epsilon> \<and> iter \<le> nat \<lceil>ln ((2 * L * (f x0 - f x_min)) / \<epsilon>\<^sup>2) / ln (1 / (1 - \<mu> / L))\<rceil>]"
proof -
  have "H[True] gradient_descent_aux (grad, x0, \<alpha>, \<epsilon>, f, L, \<mu>, x_min)
      [\<parallel>grad x\<parallel> \<le> \<epsilon> \<and> iter \<le> nat \<lceil>ln ((2 * L * (f x0 - f x_min)) / \<epsilon>\<^sup>2) / ln (1 / (1 - \<mu> / L))\<rceil>]"
    using assms by (subst gradient_descent_aux_linear_convergence, auto)
  thus ?thesis    
    by (simp add: gradient_descent_aux_is_gradient_descent)
qed


section \<open>Quadratic case: f = (1/2) x^T Q x - b^T x, exact line search (Kantorovich rate)\<close>

section \<open>Paradigm A (quadratic): Imperative ITree Program, VCG-based Hoare Logic\<close>

program gradient_descent_quadratic_aux "(
    grad   :: real vec['i] \<Rightarrow> real vec['i],
    x0     :: real vec['i],
    \<alpha>      :: real vec['i] \<Rightarrow> real,
    \<epsilon>      :: real,
    Q      :: real^'i^'i,
    x_star :: real vec['i],
    a      :: real,
    A      :: real
  )" over "'i::finite st" =
"
  x    := x0;
  iter := 0;
  while (grad(x) \<bullet> grad(x) > \<epsilon>\<^sup>2)
  invariant ((x - x_star) \<bullet> (Q *v (x - x_star))) / 2
      \<le> ((x0 - x_star) \<bullet> (Q *v (x0 - x_star))) / 2 * ((A - a) / (A + a))\<^sup>2 ^ iter
    \<and> iter \<le> nat \<lceil>ln (A*((x0 - x_star) \<bullet> (Q *v (x0 - x_star))) / \<epsilon>\<^sup>2)  / ln ((A + a)\<^sup>2 / (A - a)\<^sup>2)\<rceil>
    \<and> (\<parallel>grad(x)\<parallel> > \<epsilon> \<longrightarrow>
        iter + 1 \<le> nat \<lceil>ln (A*((x0 - x_star)\<bullet>(Q *v (x0 - x_star))) / \<epsilon>\<^sup>2) / ln ((A + a)\<^sup>2 / (A - a)\<^sup>2)\<rceil>)
  variant nat \<lceil>ln (A * ((x0 - x_star) \<bullet> (Q *v (x0 - x_star))) / \<epsilon>\<^sup>2)
               / ln ((A + a)\<^sup>2 / (A - a)\<^sup>2)\<rceil> - iter
  do
    x    := x - (\<alpha> x) *\<^sub>R grad(x);
    iter := iter + 1
  od
"

lemma gradient_descent_quadratic_aux_is_gradient_descent: 
  "gradient_descent_quadratic_aux (grad, x0, \<alpha>, \<epsilon>, Q, x_star, a, A) = 
   gradient_descent (grad, x0, \<alpha>, \<epsilon>)"
  by (simp add: gradient_descent_quadratic_aux_def gradient_descent_def 
      while_inv_def while_inv_var_def)

lemma quadratic_form_has_derivative:
  fixes Q :: "real^'n^'n" and b z :: "real^'n"
  assumes sym_Q: "\<forall>i j. Q $ i $ j = Q $ j $ i"
  defines f: "f \<equiv> \<lambda>z. (1/2) * (z \<bullet> (Q *v z)) - b \<bullet> z"
  shows "(f has_derivative (\<lambda>h. (Q *v z - b) \<bullet> h)) (at z)"
proof -
  \<comment> \<open>Bounded linearity of Q *v and inner product\<close>
  have lin_Q: "bounded_linear ((*v) Q)"
    by simp
  have deriv_Qz: "((\<lambda>z. Q *v z) has_derivative (\<lambda>h. Q *v h)) (at z)"
    by (rule bounded_linear_imp_has_derivative[OF lin_Q])
  \<comment> \<open>Product rule for z \<mapsto> z \<bullet> (Q *v z) via bounded_bilinear\<close>
  have "((\<lambda>z. z \<bullet> (Q *v z)) has_derivative
           (\<lambda>h. z \<bullet> (Q *v h) + h \<bullet> (Q *v z))) (at z)"
    by (intro has_derivative_inner has_derivative_id deriv_Qz, auto)  
  then have deriv_quad: "((\<lambda>z. z \<bullet> (Q *v z)) has_derivative
                     (\<lambda>h. h \<bullet> (Q *v z) + z \<bullet> (Q *v h))) (at z)"
    by (simp add: add.commute)

  \<comment> \<open>Symmetry of Q: z \<bullet> (Q *v h) = (Q *v z) \<bullet> h, so both cross terms equal (Q *v z) \<bullet> h\<close>
  have sym_simp: "\<And>h. h \<bullet> (Q *v z) + z \<bullet> (Q *v h) = 2 * ((Q *v z) \<bullet> h)"
  proof -
    fix h
    have "z \<bullet> (Q *v h) = (Q *v z) \<bullet> h"
    proof -
      have "z \<bullet> (Q *v h) = (Finite_Cartesian_Product.transpose Q *v z) \<bullet> h"
        by (metis dot_lmul_matrix transpose_matrix_vector)
      also have "... = (Q *v z) \<bullet> h"
      proof -
        have "Finite_Cartesian_Product.transpose Q = Q"
          by (subst matrix_eq, intro allI,
              simp add: matrix_vector_mult_def Finite_Cartesian_Product.transpose_def sym_Q)
        thus ?thesis by simp
      qed
      finally show ?thesis.
    qed
    thus "h \<bullet> (Q *v z) + z \<bullet> (Q *v h) = 2 * ((Q *v z) \<bullet> h)"
      by (simp add: inner_commute)
  qed
  \<comment> \<open>Scale by 1/2: derivative of z \<mapsto> (1/2)*(z \<bullet> (Q *v z)) is h \<mapsto> (Q *v z) \<bullet> h\<close>
  have deriv_half_quad: "((\<lambda>z. (1/2) * (z \<bullet> (Q *v z))) has_derivative
                          (\<lambda>h. (Q *v z) \<bullet> h)) (at z)"
  proof -
    have "((\<lambda>z. (1/2) * (z \<bullet> (Q *v z))) has_derivative
           (\<lambda>h. (1/2) * (h \<bullet> (Q *v z) + z \<bullet> (Q *v h)))) (at z)"
      using has_derivative_scaleR_right[OF deriv_quad, where r = "1/2"] by simp
    moreover have "\<And>h. (1/2) * (h \<bullet> (Q *v z) + z \<bullet> (Q *v h)) = (Q *v z) \<bullet> h"
      using sym_simp by simp
    ultimately show ?thesis
      by (simp add: has_derivative_eq_rhs)
  qed
  \<comment> \<open>Derivative of z \<mapsto> b \<bullet> z is h \<mapsto> b \<bullet> h\<close>
  have deriv_bz: "((\<lambda>z. b \<bullet> z) has_derivative (\<lambda>h. b \<bullet> h)) (at z)"
    by (rule bounded_linear_imp_has_derivative[OF bounded_linear_inner_right])
  \<comment> \<open>Combine by subtraction and rewrite using inner_diff_left\<close>
  have deriv_combined: "((\<lambda>z. (1/2) * (z \<bullet> (Q *v z)) - b \<bullet> z) has_derivative
                         (\<lambda>h. (Q *v z - b) \<bullet> h)) (at z)"
    using has_derivative_diff[OF deriv_half_quad deriv_bz]
    by (simp add: inner_diff_left)
  show ?thesis
    unfolding f using deriv_combined.
qed

lemma energy_update_exact:
  fixes Q Qinv :: "real^'n^'n"
      and x x_star b :: "real^'n"
      and grad :: "real^'n \<Rightarrow> real^'n"
      and \<alpha> :: "real^'n \<Rightarrow> real"
  assumes sym_Q:     "\<forall>i j. Q $ i $ j = Q $ j $ i"
      and invL:      "Q ** Qinv = Finite_Cartesian_Product.mat 1"
      and grad_lin:  "\<forall>x. grad x = Q *v x - b"
      and minimiser: "grad x_star = 0"
      and step_size: "\<alpha> x = (grad x \<bullet> grad x) / (grad x \<bullet> (Q *v grad x))"
      and g_nz:      "grad x \<noteq> 0"
      and positive_definite:    "0 < grad x \<bullet> (Q *v grad x)"
      and energy_pos:     "0 < (x - x_star) \<bullet> (Q *v (x - x_star))"
  shows
    "(x - \<alpha> x *\<^sub>R grad x - x_star) \<bullet> (Q *v (x - \<alpha> x *\<^sub>R grad x - x_star))
     = (1 - (grad x \<bullet> grad x)^2
           / ((grad x \<bullet> (Q *v grad x)) * (grad x \<bullet> (Qinv *v grad x))))
       * ((x - x_star) \<bullet> (Q *v (x - x_star)))"
proof -
  let ?g  = "grad x"
  let ?Qg = "Q *v ?g"
  let ?y  = "x - x_star"
  let ?\<alpha>  = "\<alpha> x"
  \<comment> \<open>From grad_lin and minimiser: grad x = Q *v (x - x_star)\<close>
  have grad_eq: "?g = Q *v ?y"
    by (metis assms(3,4) cross3_simps(41) eq_iff_diff_eq_0)

  \<comment> \<open>Denominator positivity\<close>
  have Qg_pos: "0 < grad x \<bullet> (Q *v grad x)"
    using assms(7) by blast
  \<comment> \<open>Key identity: g \<bullet> (Qinv *v g) = y \<bullet> (Q *v y)\<close>
  have Qinv_inner: "?g \<bullet> (Qinv *v ?g) = ?y \<bullet> (Q *v ?y)"
  proof -
    \<comment> \<open>g = Q*y, so Qinv *v g = y, hence g \<bullet> (Qinv *v g) = g \<bullet> y = (Q*y) \<bullet> y = y \<bullet> (Q *v y)\<close>
    have "Qinv *v ?g = ?y"
      by (metis grad_eq invL matrix_left_right_inverse matrix_vector_mul_assoc matrix_vector_mul_lid)

    thus ?thesis
      by (simp add: grad_eq dot_lmul_matrix sym_Q inner_commute)
  qed
  \<comment> \<open>Expand the energy at the new point\<close>
  have expand: "(x - ?\<alpha> *\<^sub>R ?g - x_star) \<bullet> (Q *v (x - ?\<alpha> *\<^sub>R ?g - x_star))
      = (?y \<bullet> (Q *v ?y)) - 2 * ?\<alpha> * (?g \<bullet> ?g) + ?\<alpha>^2 * (?g \<bullet> ?Qg)"
  proof -
    have diff: "x - ?\<alpha> *\<^sub>R ?g - x_star = ?y - ?\<alpha> *\<^sub>R ?g"
      by (simp add: algebra_simps)
    have "(?y - ?\<alpha> *\<^sub>R ?g) \<bullet> (Q *v (?y - ?\<alpha> *\<^sub>R ?g))
        = ?y \<bullet> (Q *v ?y) - ?\<alpha> * (?g \<bullet> (Q *v ?y)) 
          - ?\<alpha> * (?y \<bullet> ?Qg) + ?\<alpha>^2 * (?g \<bullet> ?Qg)"
    proof -
      \<comment> \<open>Distribute Q over the subtraction\<close>
      have dist_Q: "Q *v (?y - ?\<alpha> *\<^sub>R ?g) = (Q *v ?y) - ?\<alpha> *\<^sub>R ?Qg"
        by (simp add: cross3_simps(41,42))
      \<comment> \<open>Distribute the inner product on the left\<close>
      have "(?y - ?\<alpha> *\<^sub>R ?g) \<bullet> (Q *v (?y - ?\<alpha> *\<^sub>R ?g))  = (?y - ?\<alpha> *\<^sub>R ?g) \<bullet> ((Q *v ?y) - ?\<alpha> *\<^sub>R ?Qg)"
        using dist_Q by simp
      also have "... = ?y \<bullet> (Q *v ?y) - ?\<alpha> *\<^sub>R ?g \<bullet> (Q *v ?y) - (?y \<bullet> (?\<alpha>*\<^sub>R?Qg) - ?\<alpha>*\<^sub>R?g \<bullet> (?\<alpha>*\<^sub>R?Qg))"
        by (metis (no_types, lifting) cross3_simps(36,37))
      also have "... = ?y \<bullet> (Q *v ?y) - ?\<alpha> * (?g \<bullet> (Q *v ?y)) - ?\<alpha> * (?y \<bullet> ?Qg) + ?\<alpha>^2 * (?g \<bullet> ?Qg)"
        by (simp add: power2_eq_square)
      finally show ?thesis.
    qed
    \<comment> \<open>By symmetry of Q and g = Q*y: g \<bullet> (Q *v y) = g \<bullet> g and y \<bullet> Qg = g \<bullet> g\<close>
    moreover have "?g \<bullet> (Q *v ?y) = ?g \<bullet> ?g"
      by (simp add: grad_eq)
    moreover have "?y \<bullet> ?Qg = ?g \<bullet> ?g"
    proof -
      \<comment> \<open>?Qg = Q *v ?g, so ?y \<bullet> (Q *v ?g) = (Qᵀ *v ?y) \<bullet> ?g\<close>
      have "?y \<bullet> ?Qg = ?y \<bullet> (Q *v ?g)"
        by simp
      \<comment> \<open>By symmetry of Q, Qᵀ = Q, so (Qᵀ *v ?y) = Q *v ?y = ?g\<close>
      also have "... = (Q *v ?y) \<bullet> ?g"
      proof -
        have "?y \<bullet> (Q *v ?g) = (Finite_Cartesian_Product.transpose Q *v ?y) \<bullet> ?g"
          by (metis dot_lmul_matrix transpose_matrix_vector)
        also have "... = (Q *v ?y) \<bullet> ?g"
        proof -
          have "Q\<^sup>T = Q"
            by (subst matrix_eq, intro allI,
                simp add: matrix_vector_mult_def Finite_Cartesian_Product.transpose_def sym_Q)
          thus ?thesis by simp
        qed
        finally show ?thesis.
      qed
      \<comment> \<open>And Q *v ?y = ?g by grad_eq\<close>
      also have "... = ?g \<bullet> ?g"
        using grad_eq by simp
      finally show ?thesis
        using \<open>(x - x_star) \<bullet> (Q *v grad x) = (Q *v (x - x_star)) \<bullet> grad x\<close> grad_eq by force 
    qed
    ultimately show ?thesis
      by (simp add: diff)
  qed
    \<comment> \<open>Substitute \<alpha> and simplify using Qinv_inner\<close>
  have \<alpha>_val: "?\<alpha> = (?g \<bullet> ?g) / (?g \<bullet> ?Qg)"
    by (simp add: step_size)
  show ?thesis
  proof -
    \<comment> \<open>Simplify expand by substituting \<alpha>_val: the quadratic in \<alpha> collapses\<close>
    have lhs_simplified:
      "(x - ?\<alpha> *\<^sub>R ?g - x_star) \<bullet> (Q *v (x - ?\<alpha> *\<^sub>R ?g - x_star))
       = (?y \<bullet> (Q *v ?y)) - (?g \<bullet> ?g)^2 / (?g \<bullet> ?Qg)"
    proof -
      have "2 * ?\<alpha> * (?g \<bullet> ?g) - ?\<alpha>^2 * (?g \<bullet> ?Qg) = (?g \<bullet> ?g)^2 / (?g \<bullet> ?Qg)"
        using Qg_pos by (simp add: \<alpha>_val field_simps power2_eq_square)
      thus ?thesis using expand by linarith
    qed
    \<comment> \<open>E = y \<bullet> (Q *v y) is positive: Qinv *v g = y and g \<noteq> 0 with Q pos def on g\<close>
    have E_pos: "0 < ?y \<bullet> (Q *v ?y)"
      using assms(8) by blast
    \<comment> \<open>Rewrite RHS using Qinv_inner, then field algebra with Qg_pos and E_pos\<close>
    have rhs_simplified:
      "(1 - (?g \<bullet> ?g)^2 / ((?g \<bullet> ?Qg) * (?g \<bullet> (Qinv *v ?g)))) * (?y \<bullet> (Q *v ?y))
       = (?y \<bullet> (Q *v ?y)) - (?g \<bullet> ?g)^2 / (?g \<bullet> ?Qg)"
    proof -
      have denom_pos: "0 < (?g \<bullet> ?Qg) * (?g \<bullet> (Qinv *v ?g))"
        using Qg_pos Qinv_inner E_pos by simp
      show ?thesis
        using Qg_pos E_pos Qinv_inner denom_pos
        by (simp add: field_simps power2_eq_square)
    qed
    show ?thesis
      using lhs_simplified rhs_simplified by simp
  qed
qed

section \<open>Paradigm B (quadratic): Lammich's Refinement Framework (\<open>nres\<close>)\<close>

text \<open>Same loop as the linear case (reusing \<open>R_gradient_descent\<close>), but with the
  exact line-search step and the quadratic Q-energy with the Kantorovich rate
  \<open>((A-a)/(A+a))\<^sup>2\<close>.  The per-step contraction \<open>q_contract\<close> and the gradient
  bound \<open>q_grad_E_upper\<close> are extracted from the VCG theorem's reasoning.\<close>

definition gd_bound_q ::
  "real vec['i] \<Rightarrow> real vec['i] \<Rightarrow> real^'i^'i \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat" where
  "gd_bound_q x0 x_star Q a A \<epsilon> =
     nat \<lceil>ln (A * ((x0 - x_star) \<bullet> (Q *v (x0 - x_star))) / \<epsilon>\<^sup>2) / ln ((A + a)\<^sup>2 / (A - a)\<^sup>2)\<rceil>"

definition gd_invar_q ::
  "(real vec['i] \<Rightarrow> real vec['i]) \<Rightarrow> real vec['i] \<Rightarrow> real vec['i] \<Rightarrow> real^'i^'i
     \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real vec['i] \<times> nat) \<Rightarrow> bool" where
  "gd_invar_q grad x0 x_star Q a A \<epsilon> \<equiv> \<lambda>(x, iter).
       (x - x_star) \<bullet> (Q *v (x - x_star))
         \<le> ((x0 - x_star) \<bullet> (Q *v (x0 - x_star))) * (((A - a)/(A + a))\<^sup>2) ^ iter
     \<and> iter \<le> gd_bound_q x0 x_star Q a A \<epsilon>
     \<and> (\<epsilon>\<^sup>2 < grad x \<bullet> grad x \<longrightarrow> iter < gd_bound_q x0 x_star Q a A \<epsilon>)"

context
  fixes grad :: "real vec['i] \<Rightarrow> real vec['i]" and f :: "real vec['i] \<Rightarrow> real"
    and b x0 x_star :: "real vec['i]" and Q D Dinv U :: "real^'i^'i"
    and \<alpha> :: "real vec['i] \<Rightarrow> real" and a A \<epsilon> :: real
  assumes \<epsilon>_pos: "0 < \<epsilon>" and a_pos: "0 < a" and a_lt_A: "a < A"
    and step_size: "\<And>x. \<alpha> x = (grad x \<bullet> grad x) / (grad x \<bullet> (Q *v grad x))"
    and f_def: "\<And>x. f x = (1/2) * (x \<bullet> (Q *v x)) - b \<bullet> x"
    and is_grad: "\<And>x. (f has_derivative (\<lambda>h. grad x \<bullet> h)) (at x)"
    and spd_decomp: "Q = Finite_Cartesian_Product.transpose U ** D ** U"
    and orthU: "orthogonal_matrix U" and diagD: "diagonal_mat D"
    and eig_bd: "\<And>i. a \<le> D $ i $ i \<and> D $ i $ i \<le> A"
    and invL: "D ** Dinv = Finite_Cartesian_Product.mat 1"
    and minimiser: "grad x_star = 0"
begin

lemma q_sym_Q: "\<forall>i j. Q $ i $ j = Q $ j $ i"
  by (simp add: spd_decomp diagD orthogonal_diag_orthogonal_symmetric[OF orthU diagD])

lemma q_invR: "Dinv ** D = Finite_Cartesian_Product.mat 1"
  by (simp add: invL matrix_left_right_inverse)

lemma q_grad_linear:
  fixes x :: "real vec['i]"
  shows "grad x = Q *v x - b"
  proof -
    have deriv_f: "(f has_derivative (\<lambda>h. grad x \<bullet> h)) (at x)"
      using is_grad by simp
    have deriv_direct: "(f has_derivative (\<lambda>h. (Q *v x - b) \<bullet> h)) (at x)"
    proof -
      have "((\<lambda>z. (1/2) * (z \<bullet> (Q *v z)) - b \<bullet> z) has_derivative
             (\<lambda>h. (Q *v x - b) \<bullet> h)) (at x)"
        using quadratic_form_has_derivative[OF q_sym_Q, where z = x] by simp
      moreover have "f = (\<lambda>z. (1/2) * (z \<bullet> (Q *v z)) - b \<bullet> z)"
        using f_def by fastforce
      ultimately show ?thesis by simp
    qed
    have "\<And>h. grad x \<bullet> h = (Q *v x - b) \<bullet> h"
      using has_derivative_unique[OF deriv_f deriv_direct]
      by (simp add: fun_eq_iff)
    thus "grad x = Q *v x - b"
      by (metis (no_types, lifting) inner_commute inner_eq_zero_iff inner_simps(3) right_minus_eq)
  qed

lemma q_grad_eq:
  fixes x :: "real vec['i]"
  shows "grad x = Q *v (x - x_star)"
  proof -
    have "grad x = Q *v x - b"
      using q_grad_linear by simp
    also have "... = Q *v x - Q *v x_star"
    proof -
      \<comment> \<open>From minimiser grad x_star = 0 and q_grad_linear: Q *v x_star - b = 0, so b = Q *v x_star\<close>
      have "Q *v x_star - b = 0"
        using q_grad_linear minimiser by simp
      thus ?thesis by simp
    qed
    also have "... = Q *v (x - x_star)"
      by (simp add: cross3_simps(41))
    finally show "grad x = Q *v (x - x_star)".
  qed

lemma q_grad_E_upper:
  fixes x :: "real vec['i]"
  shows "grad x \<bullet> grad x \<le> A * ((x - x_star) \<bullet> (Q *v (x - x_star)))"
  proof -
    let ?y = "x - x_star"
    have q_grad_eq: "grad x = Q *v ?y"
      using q_grad_eq by force

    have "grad x \<bullet> grad x = (Q *v ?y) \<bullet> (Q *v ?y)"
      using q_grad_eq by simp
    also have "... \<le> A * (?y \<bullet> (Q *v ?y))"
    proof -
      let ?w = "U *v ?y"
      \<comment> \<open>Conjugate both sides via U\<close>
      have lhs: "(Q *v ?y) \<bullet> (Q *v ?y) = (D *v ?w) \<bullet> (D *v ?w)"
        by (metis (no_types, lifting) spd_decomp orthU 
            matrix_vector_mul_assoc orthogonal_mat_inner_self orthogonal_matrix_transpose)
      have rhs: "?y \<bullet> (Q *v ?y) = ?w \<bullet> (D *v ?w)"
        by (metis spd_decomp orthU quad_form_fc_def quad_form_fc_orth_cong)
      \<comment> \<open>Expand both as sums\<close>
      have lhs_sum: "(D *v ?w) \<bullet> (D *v ?w) = (\<Sum>i\<in>UNIV. (D $ i $ i)^2 * (?w $ i)^2)"
        by (simp add: inner_vec_def mat_vec_mult_entry_diagonal[OF diagD]
            power2_eq_square sum_distrib_left,
            simp add: cross3_simps(11) vector_space_over_itself.scale_left_commute)
      have rhs_sum: "?w \<bullet> (D *v ?w) = (\<Sum>i\<in>UNIV. (D $ i $ i) * (?w $ i)^2)"
        using quad_form_fc_diagonal_sum[OF diagD] by (simp add: quad_form_fc_def inner_commute)
      \<comment> \<open>Bound each term: (D$i$i)² * w² \<le> A * D$i$i * w²  since D$i$i \<le> A\<close>
      have "\<And>i. (D $ i $ i)^2 * (?w $ i)^2 \<le> A * (D $ i $ i * (?w $ i)^2)"
        by (smt (verit, ccfv_SIG) a_pos eig_bd more_arith_simps(11)
            mult_le_cancel_right power2_eq_square)
      then have "(D *v ?w) \<bullet> (D *v ?w) \<le> A * (?w \<bullet> (D *v ?w))"
        using lhs_sum rhs_sum by (simp add: sum_distrib_left, intro sum_mono)
      thus ?thesis using lhs rhs by simp
    qed
      \<comment> \<open>From Q \<preceq> AI: (Qy)\<bullet>(Qy) = yᵀQ²y \<le> A\<sqdot>yᵀQy\<close>
    finally show "grad x \<bullet> grad x \<le> A * ((x - x_star) \<bullet> (Q *v (x - x_star)))".
  qed

lemma q_contract:
  fixes x :: "real vec['i]"
  shows "((x - \<alpha> x *\<^sub>R grad x - x_star) \<bullet> (Q *v (x - \<alpha> x *\<^sub>R grad x - x_star)))
          \<le> ((A - a) / (A + a))\<^sup>2 * ((x - x_star) \<bullet> (Q *v (x - x_star)))"
  proof -
    fix x
    let ?g    = "grad x"
    let ?Qg   = "Q *v ?g"
    let ?y    = "x - x_star"
    let ?Qinv = "Finite_Cartesian_Product.transpose U ** Dinv ** U"

    \<comment> \<open>Q ** Qinv = I via spectral decomposition\<close>
    have Q_Qinv: "Q ** ?Qinv = Finite_Cartesian_Product.mat 1"
    proof -
      have "Q ** ?Qinv
          = (Finite_Cartesian_Product.transpose U ** D ** U)
            ** (Finite_Cartesian_Product.transpose U ** Dinv ** U)"
        using spd_decomp by simp
      also have "... = Finite_Cartesian_Product.transpose U
                       ** (D ** (U ** Finite_Cartesian_Product.transpose U))
                       ** Dinv ** U"
        by (simp add: matrix_mul_assoc)
      also have "... = Finite_Cartesian_Product.transpose U ** (D ** Dinv) ** U"
        by (metis orthogonal_matrix_def orthU matrix_mul_assoc matrix_mul_rid)
      also have "... = Finite_Cartesian_Product.mat 1"
        using invL by (metis orthogonal_matrix_def orthU matrix_mul_rid)
      finally show ?thesis.
    qed

    \<comment> \<open>Symmetry of Q\<close>
    have sym_Q: "\<forall>i j. Q $ i $ j = Q $ j $ i"
      by (simp add: spd_decomp diagD orthogonal_diag_orthogonal_symmetric[OF orthU diagD])

    \<comment> \<open>Eigenvalue lower bound from spectral decomposition\<close>
    have eig_lower: "\<And>v. a * (v \<bullet> v) \<le> v \<bullet> (Q *v v)"
    proof -
      fix v
      have "a * (v \<bullet> v) 
          = a * ((U *v v) \<bullet> (U *v v))"
        using orthogonal_mat_inner_self[OF orthU] by simp
      also have "... = a * (\<Sum>i\<in>UNIV. ((U *v v) $ i)^2)"
        by (simp add: inner_vec_def power2_eq_square)
      also have "... = (\<Sum>i\<in>UNIV. a * ((U *v v) $ i)^2)"
        by (simp add: sum_distrib_left)
      also have "... \<le> (\<Sum>i\<in>UNIV. (D $ i $ i) * ((U *v v) $ i)^2)"
        using eig_bd by (intro sum_mono, simp add: mult_right_mono)
      also have "... = (U *v v) \<bullet> (D *v (U *v v))"
        using quad_form_fc_diagonal_sum[OF diagD] by (simp add: quad_form_fc_def)
      also have "... = v \<bullet> (Q *v v)"
        by (metis spd_decomp orthU quad_form_fc_def quad_form_fc_orth_cong)
      finally show "a * (v \<bullet> v) \<le> v \<bullet> (Q *v v)" .
    qed

    \<comment> \<open>Uniqueness of minimiser\<close>
    have unique_min: "grad x = 0 \<longleftrightarrow> x = x_star"
    proof
      assume "grad x = 0"
      have Qx:  "Q *v x      = b" using \<open>grad x = 0\<close> q_grad_linear by auto
      have Qxs: "Q *v x_star = b" using q_grad_linear minimiser by simp
      have "Q *v (x - x_star) = 0" by (simp add: Qx Qxs cross3_simps(41))
      thus "x = x_star"
        by (meson Q_Qinv eq_iff_diff_eq_0 matrix_left_invertible_ker matrix_left_right_inverse)
    next
      assume "x = x_star" thus "grad x = 0" using minimiser by simp
    qed

    \<comment> \<open>Algebraic identity for the contraction factor\<close>
    have factor_eq: "1 - (4 * a * A) / (a + A)^2 = ((A - a) / (A + a))^2"
    proof -
      have pos: "0 < a + A" using a_pos a_lt_A by linarith
      have nz:  "(a + A)^2 \<noteq> 0"
        using pos by auto 
      have "1 - (4 * a * A) / (a + A)^2 = ((a + A)^2 - 4 * a * A) / (a + A)^2"
        using nz by (simp add: field_simps)
      also have "(a + A)^2 - 4 * a * A = (A - a)^2"
        by (simp add: power2_eq_square algebra_simps)
      also have "(A - a)^2 / (a + A)^2 = ((A - a) / (A + a))^2"
        by (simp add: add.commute power_divide)
      finally show ?thesis by simp
    qed

    \<comment> \<open>Descent with Case split — trivial at minimiser, main argument elsewhere\<close>
    show "(x - \<alpha> x *\<^sub>R ?g - x_star) \<bullet> (Q *v (x - \<alpha> x *\<^sub>R ?g - x_star))
             \<le> ((A - a) / (A + a))\<^sup>2 * (?y \<bullet> (Q *v ?y))"
    proof (cases "x = x_star")
      case True
      then have "?y = 0" by simp
      then show ?thesis by (simp add: minimiser)
    next
      case False
      have g_nz:   "?g \<noteq> 0" using False unique_min by blast
      have Qg_pos: "0 < ?g \<bullet> ?Qg" using eig_lower_imp_pos_def[OF a_pos eig_lower g_nz].
      \<comment> \<open>Energy update formula (Lemma 1)\<close>
      have energy_update:
        "(x - \<alpha> x *\<^sub>R ?g - x_star) \<bullet> (Q *v (x - \<alpha> x *\<^sub>R ?g - x_star))
         = (1 - (?g \<bullet> ?g)^2 / ((?g \<bullet> ?Qg) * (?g \<bullet> (?Qinv *v ?g)))) * (?y \<bullet> (Q *v ?y))"
      proof -
        have y_nz: "?y \<noteq> 0" using False by simp
        have energy_pos: "0 < ?y \<bullet> (Q *v ?y)"
          using eig_lower_imp_pos_def[OF a_pos eig_lower y_nz] .
        show ?thesis
          using Q_Qinv Qg_pos minimiser step_size energy_pos energy_update_exact g_nz q_grad_linear sym_Q by blast

      qed
        \<comment> \<open>Kantorovich ratio bound\<close>
      have kant: "(?g \<bullet> ?g)^2 / ((?g \<bullet> ?Qg) * (?g \<bullet> (?Qinv *v ?g))) \<ge> (4 * a * A) / (a + A)^2"
      proof -
        have qf_Q:    "quad_form_fc Q    ?g = ?g \<bullet> ?Qg"           by (simp add: quad_form_fc_def)
        have qf_Qinv: "quad_form_fc ?Qinv ?g = ?g \<bullet> (?Qinv *v ?g)" by (simp add: quad_form_fc_def)
        have "((?g \<bullet> ?g)^2) / (quad_form_fc Q ?g * quad_form_fc ?Qinv ?g) \<ge> (4 * a * A) / (a + A)^2"
          by (simp add: a_pos a_lt_A spd_decomp orthU invL diagD eig_bd g_nz q_invR kantorovich less_imp_le)
        thus ?thesis using qf_Q qf_Qinv by simp
      qed
      \<comment> \<open>Combine: contraction factor \<le> ((A-a)/(A+a))²\<close>
      have  "1 - (?g \<bullet> ?g)^2 / ((?g \<bullet> ?Qg) * (?g \<bullet> (?Qinv *v ?g))) \<le> ((A - a) / (A + a))^2"
        using kant factor_eq by linarith
      then show ?thesis
        by (smt (verit, best) a_pos  eig_lower energy_update inner_ge_zero
            real_scaleR_def scaleR_right_mono zero_le_scaleR_iff)
    qed
  qed


lemma gd_iter_lt_bound_q:
  fixes x :: "real vec['i]" and iter :: nat
  assumes energy: "(x - x_star) \<bullet> (Q *v (x - x_star))
                     \<le> ((x0 - x_star) \<bullet> (Q *v (x0 - x_star))) * (((A - a)/(A + a))\<^sup>2) ^ iter"
    and looping: "\<epsilon>\<^sup>2 < grad x \<bullet> grad x"
  shows "iter < gd_bound_q x0 x_star Q a A \<epsilon>"
proof -
  define r where "r = ((A - a)/(A + a))\<^sup>2"
  define B where "B = A * ((x0 - x_star) \<bullet> (Q *v (x0 - x_star)))"
  have ApA: "0 < A + a" using a_pos a_lt_A by linarith
  have AmA: "0 < A - a" using a_lt_A by linarith
  have A_pos: "0 < A" using a_pos a_lt_A by linarith
  have ratio_pos: "0 < (A - a)/(A + a)" using AmA ApA by simp
  have ratio_lt1: "(A - a)/(A + a) < 1" using AmA ApA a_pos by (simp add: divide_less_eq)
  have r_pos: "0 < r" using AmA ApA by (simp add: r_def)
  have r_lt1: "r < 1" using ratio_pos ratio_lt1
    by (smt (verit) mult_less_cancel_left1 power2_eq_square r_def)
  have eps2_pos: "0 < \<epsilon>\<^sup>2" using \<epsilon>_pos by simp
  have pow_pos: "0 < r ^ iter" using r_pos by simp
  have e1: "\<epsilon>\<^sup>2 < B * r ^ iter"
  proof -
    have "\<epsilon>\<^sup>2 < grad x \<bullet> grad x" using looping .
    also have "... \<le> A * ((x - x_star) \<bullet> (Q *v (x - x_star)))" using q_grad_E_upper[of x] .
    also have "... \<le> A * (((x0 - x_star) \<bullet> (Q *v (x0 - x_star))) * r ^ iter)"
      using energy A_pos by (simp add: r_def mult_left_mono)
    finally show ?thesis by (simp add: B_def mult.assoc)
  qed
  have B_pos: "0 < B"
  proof -
    have "0 < B * r ^ iter" using e1 eps2_pos by linarith
    thus ?thesis using pow_pos r_pos by (simp add: zero_less_mult_iff)
  qed
  have inv_ge1: "1 \<le> (1 / r) ^ iter" using r_pos r_lt1 by (simp add: one_le_power)
  have key: "(1 / r) ^ iter < B / \<epsilon>\<^sup>2"
  proof -
    have "\<epsilon>\<^sup>2 / B < r ^ iter" using e1 B_pos by (simp add: divide_less_eq mult.commute)
    hence "1 / r ^ iter < B / \<epsilon>\<^sup>2" using pow_pos B_pos eps2_pos by (simp add: field_simps)
    thus ?thesis by (simp add: power_one_over)
  qed
  have BoverEps_gt1: "1 < B / \<epsilon>\<^sup>2" using key inv_ge1 by linarith
  have lnr_pos: "0 < ln (1 / r)" using r_pos r_lt1 by simp
  have invr_pos: "0 < 1 / r" using r_pos by simp
  have "ln ((1 / r) ^ iter) < ln (B / \<epsilon>\<^sup>2)"
    using key invr_pos BoverEps_gt1 by (simp add: zero_less_power)
  hence "real iter * ln (1 / r) < ln (B / \<epsilon>\<^sup>2)" using invr_pos by (simp add: ln_realpow)
  hence ltr: "real iter < ln (B / \<epsilon>\<^sup>2) / ln (1 / r)" using lnr_pos by (simp add: pos_less_divide_eq)
  have rinv_eq: "1 / r = (A + a)\<^sup>2 / (A - a)\<^sup>2" using AmA ApA by (simp add: r_def power_divide)
  have "int iter < \<lceil>ln (A * ((x0 - x_star) \<bullet> (Q *v (x0 - x_star))) / \<epsilon>\<^sup>2) / ln ((A + a)\<^sup>2 / (A - a)\<^sup>2)\<rceil>"
    using ltr by (simp add: B_def rinv_eq less_ceiling_iff)
  thus "iter < gd_bound_q x0 x_star Q a A \<epsilon>"
    by (simp add: gd_bound_q_def zless_nat_eq_int_zless)
qed

lemma gd_invar_step_q:
  fixes x :: "real vec['i]" and iter :: nat
  assumes inv: "gd_invar_q grad x0 x_star Q a A \<epsilon> (x, iter)"
    and guard: "\<epsilon>\<^sup>2 < grad x \<bullet> grad x"
  shows "gd_invar_q grad x0 x_star Q a A \<epsilon> (x - \<alpha> x *\<^sub>R grad x, iter + 1)
       \<and> ((x - \<alpha> x *\<^sub>R grad x, iter + 1), (x, iter))
           \<in> Wellfounded.measure (\<lambda>(x, iter). gd_bound_q x0 x_star Q a A \<epsilon> - iter)"
proof -
  let ?N = "gd_bound_q x0 x_star Q a A \<epsilon>"
  let ?x' = "x - \<alpha> x *\<^sub>R grad x"
  let ?r = "((A - a)/(A + a))\<^sup>2"
  from inv have energy: "(x - x_star) \<bullet> (Q *v (x - x_star))
                           \<le> ((x0 - x_star) \<bullet> (Q *v (x0 - x_star))) * ?r ^ iter"
    by (auto simp: gd_invar_q_def)
  have rnn: "0 \<le> ?r" by simp
  have iter_lt: "iter < ?N" using gd_iter_lt_bound_q[OF energy guard] .
  have contract: "(?x' - x_star) \<bullet> (Q *v (?x' - x_star)) \<le> ?r * ((x - x_star) \<bullet> (Q *v (x - x_star)))"
    using q_contract[of x] by simp
  have energy': "(?x' - x_star) \<bullet> (Q *v (?x' - x_star))
                   \<le> ((x0 - x_star) \<bullet> (Q *v (x0 - x_star))) * ?r ^ (iter + 1)"
  proof -
    have "(?x' - x_star) \<bullet> (Q *v (?x' - x_star)) \<le> ?r * ((x - x_star) \<bullet> (Q *v (x - x_star)))"
      using contract .
    also have "... \<le> ?r * (((x0 - x_star) \<bullet> (Q *v (x0 - x_star))) * ?r ^ iter)"
      using energy rnn by (rule mult_left_mono)
    also have "... = ((x0 - x_star) \<bullet> (Q *v (x0 - x_star))) * ?r ^ (iter + 1)" by (simp add: mult_ac)
    finally show ?thesis .
  qed
  have iterN': "iter + 1 \<le> ?N" using iter_lt by simp
  have inv': "gd_invar_q grad x0 x_star Q a A \<epsilon> (?x', iter + 1)"
    unfolding gd_invar_q_def using energy' iterN' gd_iter_lt_bound_q[OF energy'] by auto
  have "?N - (iter + 1) < ?N - iter" using iter_lt by linarith
  hence var: "((?x', iter + 1), (x, iter)) \<in> Wellfounded.measure (\<lambda>(x, iter). ?N - iter)"
    by (simp add: in_measure)
  show ?thesis using inv' var by simp
qed

lemma gd_exit_q:
  fixes x :: "real vec['i]" and iter :: nat
  assumes inv: "gd_invar_q grad x0 x_star Q a A \<epsilon> (x, iter)"
    and nguard: "\<not> \<epsilon>\<^sup>2 < grad x \<bullet> grad x"
  shows "\<parallel>grad x\<parallel> \<le> \<epsilon> \<and> iter \<le> gd_bound_q x0 x_star Q a A \<epsilon>"
proof -
  from inv have iterN: "iter \<le> gd_bound_q x0 x_star Q a A \<epsilon>" by (auto simp: gd_invar_q_def)
  have "\<parallel>grad x\<parallel>\<^sup>2 \<le> \<epsilon>\<^sup>2" using nguard by (simp add: power2_norm_eq_inner)
  hence "\<parallel>grad x\<parallel> \<le> \<epsilon>" using \<epsilon>_pos by (smt (verit) norm_ge_zero power2_le_imp_le)
  thus ?thesis using iterN by simp
qed

theorem R_gradient_descent_quadratic_correct:
  "R_gradient_descent grad x0 \<alpha> \<epsilon>
     \<le> SPEC (\<lambda>(x, iter). \<parallel>grad x\<parallel> \<le> \<epsilon> \<and> iter \<le> gd_bound_q x0 x_star Q a A \<epsilon>)"
  unfolding R_gradient_descent_def
  apply (refine_vcg WHILET_rule[where I = "gd_invar_q grad x0 x_star Q a A \<epsilon>"
            and R = "Wellfounded.measure (\<lambda>(x, iter). gd_bound_q x0 x_star Q a A \<epsilon> - iter)"])
  subgoal by simp
  subgoal using gd_iter_lt_bound_q[of x0 0] by (auto simp: gd_invar_q_def)
  subgoal for s using gd_invar_step_q by (cases s) (auto simp: in_measure)
  subgoal for s using gd_invar_step_q by (cases s) (auto simp: in_measure)
  subgoal for s using gd_exit_q by (cases s) auto
  subgoal for s using gd_exit_q by (cases s) auto
  done


end
theorem gradient_descent_quadratic_aux:
  assumes \<epsilon>_pos:       "0 < \<epsilon>"
      and a_pos:       "0 < a"
      and a_lt_A:      "a < A"
      and step_size:   "\<And>x. \<alpha> x = (grad x \<bullet> grad x) / (grad x \<bullet> (Q *v grad x))"
      and f_def:       "\<And>x. f x = (1/2) * (x \<bullet> (Q *v x)) - b \<bullet> x"
      and is_grad:     "\<And>x. (f has_derivative (\<lambda>h. grad x \<bullet> h)) (at x)"
      and spd_decomp:  "Q = Finite_Cartesian_Product.transpose U ** D ** U"
      and orthU:       "orthogonal_matrix U"
      and diagD:       "diagonal_mat D"
      and eig_bd:      "\<And>i. a \<le> D $ i $ i \<and> D $ i $ i \<le> A"
      and invL:        "D ** Dinv = Finite_Cartesian_Product.mat 1"
      and minimiser:   "grad x_star = 0"
  shows "H[True] gradient_descent_quadratic_aux (grad, x0, \<alpha>, \<epsilon>, Q, x_star, a, A)
     [\<parallel>grad x\<parallel> \<le> \<epsilon>
     \<and> iter \<le> nat \<lceil>ln (A * ((x0 - x_star) \<bullet> (Q *v (x0 - x_star))) / \<epsilon>\<^sup>2)
                   / ln ((A + a)\<^sup>2 / (A - a)\<^sup>2)\<rceil>]"
  apply (vcg)
  \<comment> \<open>VCs 1--4: the guard \<open>\<epsilon>\<^sup>2 < grad x \<bullet> grad x\<close> contradicts \<open>\<not> \<epsilon> < \<parallel>grad x\<parallel>\<close>.\<close>
  subgoal using norm_gt_square by blast
  subgoal using norm_gt_square by blast
  subgoal using norm_gt_square by blast
  subgoal using norm_gt_square by blast
  \<comment> \<open>VC 5: one step contracts the Q-energy (shared @{thm q_contract}).\<close>
  subgoal premises p for iter x
  proof -
    have con: "(x - \<alpha> x *\<^sub>R grad x - x_star) \<bullet> (Q *v (x - \<alpha> x *\<^sub>R grad x - x_star))
               \<le> ((A - a) / (A + a))\<^sup>2 * ((x - x_star) \<bullet> (Q *v (x - x_star)))"
      by (metis q_contract \<epsilon>_pos a_pos a_lt_A step_size f_def is_grad spd_decomp orthU diagD eig_bd invL minimiser)
    have inv: "(x - x_star) \<bullet> (Q *v (x - x_star))
               \<le> (x0 - x_star) \<bullet> (Q *v (x0 - x_star)) * ((A - a) / (A + a))\<^sup>2 ^ iter"
      using p by blast
    show ?thesis using con inv mult_left_mono zero_le_power2
      by (smt (verit, ccfv_SIG) mult.left_commute)
  qed
  \<comment> \<open>VC 6: while still looping, the iteration bound advances (shared @{thm gd_iter_lt_bound_q}).\<close>
  subgoal premises p for iter x
  proof -
    have con: "(x - \<alpha> x *\<^sub>R grad x - x_star) \<bullet> (Q *v (x - \<alpha> x *\<^sub>R grad x - x_star))
               \<le> ((A - a) / (A + a))\<^sup>2 * ((x - x_star) \<bullet> (Q *v (x - x_star)))"
      by (metis q_contract \<epsilon>_pos a_pos a_lt_A step_size f_def is_grad spd_decomp orthU diagD eig_bd invL minimiser)
    have inv: "(x - x_star) \<bullet> (Q *v (x - x_star))
               \<le> (x0 - x_star) \<bullet> (Q *v (x0 - x_star)) * ((A - a) / (A + a))\<^sup>2 ^ iter"
      using p by blast
    have e': "(x - \<alpha> x *\<^sub>R grad x - x_star) \<bullet> (Q *v (x - \<alpha> x *\<^sub>R grad x - x_star))
              \<le> (x0 - x_star) \<bullet> (Q *v (x0 - x_star)) * ((A - a) / (A + a))\<^sup>2 ^ (Suc iter)"
      using con inv mult_left_mono zero_le_power2
      by (smt (verit, ccfv_SIG) mult.left_commute power.simps(2))
    have g': "\<epsilon>\<^sup>2 < grad (x - \<alpha> x *\<^sub>R grad x) \<bullet> grad (x - \<alpha> x *\<^sub>R grad x)"
      using p \<epsilon>_pos norm_gt_square by (meson basic_trans_rules(20))
    have "Suc iter < gd_bound_q x0 x_star Q a A \<epsilon>"
      by (metis gd_iter_lt_bound_q \<epsilon>_pos a_pos a_lt_A step_size f_def is_grad spd_decomp orthU diagD eig_bd invL minimiser e' g')
    thus ?thesis by (simp add: gd_bound_q_def)
  qed
  \<comment> \<open>VC 7: the bound is positive at the start.\<close>
  subgoal premises p
  proof -
    have e0: "(x0 - x_star) \<bullet> (Q *v (x0 - x_star))
              \<le> (x0 - x_star) \<bullet> (Q *v (x0 - x_star)) * ((A - a) / (A + a))\<^sup>2 ^ 0" by simp
    have g0: "\<epsilon>\<^sup>2 < grad x0 \<bullet> grad x0"
      using p \<epsilon>_pos norm_gt_square by (meson basic_trans_rules(20))
    have "0 < gd_bound_q x0 x_star Q a A \<epsilon>"
      by (metis gd_iter_lt_bound_q \<epsilon>_pos a_pos a_lt_A step_size f_def is_grad spd_decomp orthU diagD eig_bd invL minimiser e0 g0)
    thus ?thesis unfolding gd_bound_q_def by linarith
  qed
  \<comment> \<open>VC 8: on loop exit the gradient is small.\<close>
  subgoal premises p for iter x
  proof -
    have "\<parallel>grad x\<parallel>\<^sup>2 \<le> \<epsilon>\<^sup>2" using p by (simp add: power2_norm_eq_inner)
    thus ?thesis using \<epsilon>_pos by (smt (verit) norm_ge_zero power2_le_imp_le)
  qed
  done

theorem gradient_descent_quadratic:
  assumes \<epsilon>_pos:   "0 < \<epsilon>"
      and a_pos:   "0 < a"
      and a_lt_A:  "a < A"
      and step_size: "\<And>x. \<alpha> x = (grad x \<bullet> grad x) / (grad x \<bullet> (Q *v grad x))"
      and f_def:   "\<And>x. f x = (1/2) * (x \<bullet> (Q *v x)) - b \<bullet> x"
      and is_grad: "\<And>x. (f has_derivative (\<lambda>h. grad x \<bullet> h)) (at x)"
      and spd_decomp: "Q = Finite_Cartesian_Product.transpose U ** D ** U"
      and orthU:   "orthogonal_matrix U"
      and diagD:   "diagonal_mat D"
      and eig_bd:  "\<And>i. a \<le> D $ i $ i \<and> D $ i $ i \<le> A"
      and invL:    "D ** Dinv = Finite_Cartesian_Product.mat 1"
      and minimiser: "grad x_star = 0"
  shows "H[True] gradient_descent (grad, x0, \<alpha>, \<epsilon>)
     [\<parallel>grad x\<parallel> \<le> \<epsilon>
     \<and> iter \<le> nat \<lceil>ln (A * ((x0 - x_star) \<bullet> (Q *v (x0 - x_star))) / \<epsilon>\<^sup>2)
                   / ln ((A + a)\<^sup>2 / (A - a)\<^sup>2)\<rceil>]"
proof -
  have "H[True] gradient_descent_quadratic_aux (grad, x0, \<alpha>, \<epsilon>, Q, x_star, a, A)
     [\<parallel>grad x\<parallel> \<le> \<epsilon>
     \<and> iter \<le> nat \<lceil>ln (A * ((x0 - x_star) \<bullet> (Q *v (x0 - x_star))) / \<epsilon>\<^sup>2) / ln ((A + a)\<^sup>2 / (A - a)\<^sup>2)\<rceil>]"
    using assms by (rule gradient_descent_quadratic_aux)
  thus ?thesis
    by (simp add: gradient_descent_quadratic_aux_is_gradient_descent)
qed




section \<open>Paradigm C: Floating-point gradient descent (direct, VCG)\<close>

text \<open>
  The direct-float counterpart of the \<^emph>\<open>general\<close> (merely \<open>L\<close>-smooth, no
  Polyak--\L ojasiewicz) gradient-descent convergence result. Unlike the PL
  regime, there is no geometric contraction: each iteration decreases the
  objective by a \<^emph>\<open>fixed amount\<close> \<open>G\<close> (the net per-step gain
  \<open>\<approx> \<epsilon>\<^sup>2 / (2L)\<close>, with the step's round-off already absorbed into \<open>G\<close>),
  so after \<open>iter\<close> iterations

  \[
     iter \cdot G \;\le\; f(valofL\,x_0) - f(valofL\,x).
  \]

  Because the objective is bounded below by \<open>f(x_min)\<close>, this directly bounds
  the iteration count by \<open>\<lceil>(f(valofL\,x_0) - f(x_min)) / G\<rceil>\<close>, and at exit
  the genuine floating-point gradient test \<open>grad x \<bullet> grad x \<le> eps2\<close>
  yields \<open>rdot (grad x) (grad x) \<le> valof eps2 + Eg\<close> via the
  first-principles inner-product bound \<open>fdot_error\<close>.

  As in the other direct-float developments, the smoothness / descent facts
  are abstract hypotheses over the real shadow; the genuine floating-point
  content is the inner product and its first-principles error bound. The
  iterates are genuine float vectors (\<^typ>\<open>float64 list\<close>).
\<close>


subsection \<open>The additive (energy-accumulation) recurrence\<close>

lemma gd_gen_recurrence:
  fixes Dold Dnew G :: real and k :: nat
  assumes old: "real k * G \<le> Dold"
    and new: "Dold + G \<le> Dnew"
  shows "real (Suc k) * G \<le> Dnew"
proof -
  have "real (Suc k) * G = real k * G + G" by (simp add: algebra_simps)
  also have "\<dots> \<le> Dold + G" using old by linarith
  also have "\<dots> \<le> Dnew" using new by linarith
  finally show ?thesis .
qed


subsection \<open>State and program\<close>

zstore stGDG =
  iter :: "nat"
  x    :: "float64 list"

program gd_gen_FD
  "(grad :: float64 list \<Rightarrow> float64 list, x0 :: float64 list, a :: float64, eps2 :: float64,
    f_R :: real list \<Rightarrow> real, x_min :: real list, G :: real, Eg :: real)" over stGDG
 = "x := x0; iter := 0;
    while fdot (grad x) (grad x) > eps2
    invariant real iter * G \<le> f_R (valofL x0) - f_R (valofL x)
    variant nat \<lceil>(f_R (valofL x0) - f_R x_min) / G\<rceil> - iter
    do x := fvsub x (fscaleR a (grad x)); iter := iter + 1 od"


subsection \<open>Direct convergence correctness\<close>

theorem gd_gen_FD_direct_correct:
  fixes grad :: "float64 list \<Rightarrow> float64 list"
  fixes f_R :: "real list \<Rightarrow> real"
  fixes x0 :: "float64 list" and a eps2 :: float64
  fixes x_min :: "real list"
  fixes G Eg :: real
  assumes G_pos: "0 < G"
  assumes Eg_nonneg: "0 \<le> Eg"
  assumes eps2_fin: "is_finite eps2"
  assumes f_min:
    "\<And>v :: float64 list. f_R x_min \<le> f_R (valofL v)"
  assumes gain_oracle:
    "\<And>v. f_R (valofL v) \<le> f_R (valofL x0) \<Longrightarrow> eps2 < fdot (grad v) (grad v)
        \<Longrightarrow> f_R (valofL (fvsub v (fscaleR a (grad v)))) \<le> f_R (valofL v) - G"
  assumes guard_ok:
    "\<And>v. f_R (valofL v) \<le> f_R (valofL x0) \<Longrightarrow> fdot_ok (grad v) (grad v)"
  assumes guard_err:
    "\<And>v. f_R (valofL v) \<le> f_R (valofL x0) \<Longrightarrow> fdot_err (grad v) (grad v) \<le> Eg"
  shows "H[True] gd_gen_FD (grad, x0, a, eps2, f_R, x_min, G, Eg)
       [rdot (grad x) (grad x) \<le> valof eps2 + Eg
        \<and> iter \<le> nat \<lceil>(f_R (valofL x0) - f_R x_min) / G\<rceil>]"
proof -
  have D0_nonneg: "0 \<le> f_R (valofL x0) - f_R x_min" using f_min[of x0] by simp

  \<comment> \<open>The accumulation invariant keeps every iterate at or below the start value.\<close>
  have reg_of_inv:
    "\<And>(it :: nat) (xv :: float64 list).
        real it * G \<le> f_R (valofL x0) - f_R (valofL xv)
        \<Longrightarrow> f_R (valofL xv) \<le> f_R (valofL x0)"
  proof -
    fix it :: nat and xv :: "float64 list"
    assume hw: "real it * G \<le> f_R (valofL x0) - f_R (valofL xv)"
    have "0 \<le> real it * G" using G_pos by simp
    thus "f_R (valofL xv) \<le> f_R (valofL x0)" using hw by linarith
  qed

  show ?thesis
    apply vcg
    \<comment> \<open>Preservation of the accumulation bound.\<close>
    subgoal premises prems for it xv
    proof -
      have inv: "real it * G \<le> f_R (valofL x0) - f_R (valofL xv)"
        and guard: "eps2 < fdot (grad xv) (grad xv)"
        using prems by auto
      have xreg: "f_R (valofL xv) \<le> f_R (valofL x0)" by (rule reg_of_inv[OF inv])
      have gain: "f_R (valofL (fvsub xv (fscaleR a (grad xv)))) \<le> f_R (valofL xv) - G"
        by (rule gain_oracle[OF xreg guard])
      have new: "(f_R (valofL x0) - f_R (valofL xv)) + G
                   \<le> f_R (valofL x0) - f_R (valofL (fvsub xv (fscaleR a (grad xv))))"
        using gain by linarith
      show "(1 + real it) * G
              \<le> f_R (valofL x0) - f_R (valofL (fvsub xv (fscaleR a (grad xv))))"
        using gd_gen_recurrence[OF inv new] by simp
    qed
    \<comment> \<open>The variant strictly decreases.\<close>
    subgoal premises prems for it xv
    proof -
      have inv: "real it * G \<le> f_R (valofL x0) - f_R (valofL xv)"
        and guard: "eps2 < fdot (grad xv) (grad xv)"
        using prems by auto
      have xreg: "f_R (valofL xv) \<le> f_R (valofL x0)" by (rule reg_of_inv[OF inv])
      have gain: "f_R (valofL (fvsub xv (fscaleR a (grad xv)))) \<le> f_R (valofL xv) - G"
        by (rule gain_oracle[OF xreg guard])
      have new: "(f_R (valofL x0) - f_R (valofL xv)) + G
                   \<le> f_R (valofL x0) - f_R (valofL (fvsub xv (fscaleR a (grad xv))))"
        using gain by linarith
      have step: "real (Suc it) * G
              \<le> f_R (valofL x0) - f_R (valofL (fvsub xv (fscaleR a (grad xv))))"
        by (rule gd_gen_recurrence[OF inv new])
      have "real (Suc it) * G \<le> f_R (valofL x0) - f_R x_min"
        using step f_min[of "fvsub xv (fscaleR a (grad xv))"] by linarith
      hence le_div: "real (Suc it) \<le> (f_R (valofL x0) - f_R x_min) / G"
        using G_pos by (simp add: pos_le_divide_eq mult.commute)
      have iter_lt_nat: "it < nat \<lceil>(f_R (valofL x0) - f_R x_min) / G\<rceil>"
        using le_div by linarith
      show "nat \<lceil>(f_R (valofL x0) - f_R x_min) / G\<rceil> - Suc it
             < nat \<lceil>(f_R (valofL x0) - f_R x_min) / G\<rceil> - it"
        using iter_lt_nat by (metis diff_less_mono2 lessI)
    qed
    \<comment> \<open>Initial establishment of the invariant.\<close>
    subgoal 
    \<comment> \<open>Post: small-gradient bound at exit.\<close>
      by (smt (verit) assms(3,6,7) fdot_error fdot_ok_finite float_lt reg_of_inv)
    subgoal premises prems for it xv
    proof -
      have inv: "real it * G \<le> f_R (valofL x0) - f_R (valofL xv)"
        and nguard: "\<not> eps2 < fdot (grad xv) (grad xv)"
        using prems by auto
      have xreg: "f_R (valofL xv) \<le> f_R (valofL x0)" by (rule reg_of_inv[OF inv])
      have fok: "fdot_ok (grad xv) (grad xv)" by (rule guard_ok[OF xreg])
      have fin: "is_finite (fdot (grad xv) (grad xv))" by (rule fdot_ok_finite[OF fok])
      have vle: "valof (fdot (grad xv) (grad xv)) \<le> valof eps2"
        using nguard float_le_neg[OF eps2_fin fin] float_le[OF fin eps2_fin] by simp
      have ferror: "\<bar>valof (fdot (grad xv) (grad xv)) - rdot (grad xv) (grad xv)\<bar>
                      \<le> fdot_err (grad xv) (grad xv)" by (rule fdot_error[OF fok])
      have ferr: "fdot_err (grad xv) (grad xv) \<le> Eg" by (rule guard_err[OF xreg])
      show "it \<le> nat \<lceil>(f_R (valofL x0) - f_R x_min) / G\<rceil>"
        using vle ferror ferr by (smt (verit, best) G_pos assms(4) 
            of_nat_le_iff pos_divide_less_eq prems(2) real_nat_ceiling_ge)
    qed    
    done
qed

text \<open>
  The direct-float counterpart of the real-valued development above, for the
  PL/contraction regime. Iterates are \<^emph>\<open>genuine float vectors\<close>
  (\<^typ>\<open>float64 list\<close>); the real-valued shadow is the componentwise
  \<^const>\<open>valofL\<close>, and the inner product appearing in the loop guard is the
  genuine floating-point \<^const>\<open>fdot\<close> built in \<open>Float_Vector\<close>, whose
  round-off is controlled \<^emph>\<open>first-principles\<close> by \<^const>\<open>fdot_err\<close>
  (\<open>fdot_error\<close>).

  As in the fixed-point development, the optimality gap
  \<open>gap(x) = f(valofL x) - f(x\<^sub>\<min>)\<close> obeys an affine recurrence
  \<open>gap\<^sub>k\<^sub>+\<^sub>1 \<le> q \<cdot> gap\<^sub>k + \<delta>\<close> with \<open>q = 1 - \<alpha>\<mu> < 1\<close> (the exact descent
  contraction, perturbed by one step's worth of rounding \<open>\<delta>\<close>). Provided
  \<open>\<delta> \<le> (1 - q) E\<close> the affine bound \<open>q ^ iter \<cdot> gap\<^sub>0 + E\<close> is preserved
  with a \<^emph>\<open>constant\<close> envelope, giving the direct bound

  \[
     f(valofL\,x) - f(x_{\min}) \;\le\; q^{\,iter}\,gap_0 + E
  \]

  throughout, and the a-posteriori bound \<open>gap \<le> (valof eps2 + Eg) / (2\<mu>)\<close>
  at exit (from the Polyak--\L ojasiewicz inequality). No growing
  \<open>iter \<cdot> \<delta>\<close> drift term appears.

  The smoothness, Polyak--\L ojasiewicz, step-contraction and round-off
  facts are taken as abstract hypotheses over the real shadow (exactly the
  facts the real development proves over \<^typ>\<open>real^'i\<close>); the genuine
  floating-point content is the inner product and its first-principles
  error bound.
\<close>


subsection \<open>The contraction recurrence\<close>

text \<open>Identical to the fixed-point envelope-preservation lemma, with the
  contraction factor written \<open>q\<close>.\<close>

lemma gd_recurrence:
  fixes Wold Wnew G q \<delta> E :: real and k :: nat
  assumes old: "Wold \<le> q ^ k * G + E"
    and new: "Wnew \<le> q * Wold + \<delta>"
    and qnn: "0 \<le> q"
    and env: "\<delta> \<le> (1 - q) * E"
  shows "Wnew \<le> q ^ Suc k * G + E"
proof -
  have e2: "\<delta> \<le> E - q * E" using env by (simp add: algebra_simps)
  have "Wnew \<le> q * Wold + \<delta>" by (rule new)
  also have "\<dots> \<le> q * (q ^ k * G + E) + \<delta>"
    using mult_left_mono[OF old qnn] by linarith
  also have "\<dots> = q ^ Suc k * G + (q * E + \<delta>)"
    by (simp add: algebra_simps)
  also have "\<dots> \<le> q ^ Suc k * G + E" using e2 by linarith
  finally show ?thesis .
qed


subsection \<open>State and program\<close>

zstore stGD =
  iter :: "nat"
  x    :: "float64 list"

text \<open>
  Pure floating-point gradient descent: the state is the genuine float
  iterate \<open>x\<close>; \<open>grad\<close> is the float gradient; \<open>a\<close> the float step size; the
  guard tests the float inner product \<open>grad x \<bullet> grad x\<close> against \<open>eps2\<close>.
  The real map \<open>f_R\<close>, the minimiser \<open>x_min\<close> and the reals
  \<open>q, \<delta>, E, M2, L2, Eg\<close> are specification-only.
\<close>

program gd_FD
  "(grad :: float64 list \<Rightarrow> float64 list, x0 :: float64 list, a :: float64, eps2 :: float64,
    f_R :: real list \<Rightarrow> real, x_min :: real list,
    q :: real, \<delta> :: real, E :: real, M2 :: real, L2 :: real, Eg :: real)" over stGD
 = "x := x0; iter := 0;
    while fdot (grad x) (grad x) > eps2
    invariant f_R (valofL x) - f_R x_min \<le> q ^ iter * (f_R (valofL x0) - f_R x_min) + E
    variant nat \<lceil>log (1 / q)
                  (L2 * (f_R (valofL x0) - f_R x_min) / (valof eps2 - Eg - L2 * E))\<rceil> - iter
    do x := fvsub x (fscaleR a (grad x)); iter := iter + 1 od"


subsection \<open>Direct convergence correctness\<close>

theorem gd_FD_direct_correct:
  fixes grad :: "float64 list \<Rightarrow> float64 list"
  fixes f_R :: "real list \<Rightarrow> real"
  fixes x0 :: "float64 list" and a eps2 :: float64
  fixes x_min :: "real list"
  fixes q \<delta> E M2 L2 Eg :: real
  assumes q_pos: "0 < q"
  assumes q_lt1: "q < 1"
  assumes delta_nonneg: "0 \<le> \<delta>"
  assumes envelope: "\<delta> \<le> (1 - q) * E"
  assumes M2_pos: "0 < M2"
  assumes L2_pos: "0 < L2"
  assumes eps2_fin: "is_finite eps2"
  assumes Eg_nonneg: "0 \<le> Eg"
  assumes gap0_pos: "0 < f_R (valofL x0) - f_R x_min"
  assumes margin: "Eg + L2 * E < valof eps2"
  assumes step_oracle:
    "\<And>v. f_R (valofL v) - f_R x_min \<le> (f_R (valofL x0) - f_R x_min) + E
        \<Longrightarrow> f_R (valofL (fvsub v (fscaleR a (grad v)))) - f_R x_min
              \<le> q * (f_R (valofL v) - f_R x_min) + \<delta>"
  assumes smooth_oracle:
    "\<And>v. f_R (valofL v) - f_R x_min \<le> (f_R (valofL x0) - f_R x_min) + E
        \<Longrightarrow> rdot (grad v) (grad v) \<le> L2 * (f_R (valofL v) - f_R x_min)"
  assumes pl_oracle:
    "\<And>v. f_R (valofL v) - f_R x_min \<le> (f_R (valofL x0) - f_R x_min) + E
        \<Longrightarrow> M2 * (f_R (valofL v) - f_R x_min) \<le> rdot (grad v) (grad v)"
  assumes guard_ok:
    "\<And>v. f_R (valofL v) - f_R x_min \<le> (f_R (valofL x0) - f_R x_min) + E
        \<Longrightarrow> fdot_ok (grad v) (grad v)"
  assumes guard_err:
    "\<And>v. f_R (valofL v) - f_R x_min \<le> (f_R (valofL x0) - f_R x_min) + E
        \<Longrightarrow> fdot_err (grad v) (grad v) \<le> Eg"
  shows "H[True] gd_FD (grad, x0, a, eps2, f_R, x_min, q, \<delta>, E, M2, L2, Eg)
       [f_R (valofL x) - f_R x_min \<le> q ^ iter * (f_R (valofL x0) - f_R x_min) + E
        \<and> rdot (grad x) (grad x) \<le> valof eps2 + Eg
        \<and> f_R (valofL x) - f_R x_min \<le> (valof eps2 + Eg) / M2]"
proof -
  have q_nonneg: "0 \<le> q" using q_pos by simp
  have onemq_pos: "0 < 1 - q" using q_lt1 by simp
  have E0: "0 \<le> E" using envelope delta_nonneg onemq_pos
    by (meson landau_o.R_trans not_less zero_le_mult_iff) 
  have gap0_nonneg: "0 \<le> f_R (valofL x0) - f_R x_min" using gap0_pos by simp

  \<comment> \<open>The affine bound keeps every iterate inside the reachable region.\<close>
  have reg_of_inv:
    "\<And>w :: real. \<And>k :: nat. w \<le> q ^ k * (f_R (valofL x0) - f_R x_min) + E
        \<Longrightarrow> w \<le> (f_R (valofL x0) - f_R x_min) + E"
  proof -
    fix w :: real and k :: nat
    assume hw: "w \<le> q ^ k * (f_R (valofL x0) - f_R x_min) + E"
    have qk: "q ^ k \<le> 1" using q_nonneg q_lt1 by (simp add: power_le_one)
    have "q ^ k * (f_R (valofL x0) - f_R x_min) \<le> 1 * (f_R (valofL x0) - f_R x_min)"
      by (rule mult_right_mono[OF qk gap0_nonneg])
    thus "w \<le> (f_R (valofL x0) - f_R x_min) + E" using hw by simp
  qed

  show ?thesis
    apply vcg
    \<comment> \<open>Preservation of the affine gap bound.\<close>
    subgoal premises prems for it xv
    proof -
      have inv: "f_R (valofL xv) - f_R x_min \<le> q ^ it * (f_R (valofL x0) - f_R x_min) + E"
        using prems by auto
      have xreg: "f_R (valofL xv) - f_R x_min \<le> (f_R (valofL x0) - f_R x_min) + E"
        by (rule reg_of_inv[OF inv])
      have step: "f_R (valofL (fvsub xv (fscaleR a (grad xv)))) - f_R x_min
                    \<le> q * (f_R (valofL xv) - f_R x_min) + \<delta>"
        by (rule step_oracle[OF xreg])
      have "f_R (valofL (fvsub xv (fscaleR a (grad xv)))) - f_R x_min
              \<le> q ^ Suc it * (f_R (valofL x0) - f_R x_min) + E"
        by (rule gd_recurrence[OF inv step q_nonneg envelope])
      thus "f_R (valofL (fvsub xv (fscaleR a (grad xv)))) - f_R x_min
              \<le> q * q ^ it * (f_R (valofL x0) - f_R x_min) + E" by simp
    qed
    \<comment> \<open>The variant strictly decreases.\<close>
    subgoal premises prems for it xv
    proof -
      have inv: "f_R (valofL xv) - f_R x_min \<le> q ^ it * (f_R (valofL x0) - f_R x_min) + E"
        and guard: "eps2 < fdot (grad xv) (grad xv)"
        using prems by auto
      have xreg: "f_R (valofL xv) - f_R x_min \<le> (f_R (valofL x0) - f_R x_min) + E"
        by (rule reg_of_inv[OF inv])
      have fok: "fdot_ok (grad xv) (grad xv)" by (rule guard_ok[OF xreg])
      have fin: "is_finite (fdot (grad xv) (grad xv))" by (rule fdot_ok_finite[OF fok])
      have vguard: "valof eps2 < valof (fdot (grad xv) (grad xv))"
        using guard float_lt[OF eps2_fin fin] by simp
      have ferror: "\<bar>valof (fdot (grad xv) (grad xv)) - rdot (grad xv) (grad xv)\<bar>
                      \<le> fdot_err (grad xv) (grad xv)" by (rule fdot_error[OF fok])
      have ferr: "fdot_err (grad xv) (grad xv) \<le> Eg" by (rule guard_err[OF xreg])
      have rdot_lb: "valof eps2 - Eg < rdot (grad xv) (grad xv)"
        using vguard ferror ferr by linarith
      have smooth: "rdot (grad xv) (grad xv) \<le> L2 * (f_R (valofL xv) - f_R x_min)"
        by (rule smooth_oracle[OF xreg])
      have onec: "0 < L2" by (rule L2_pos)
      have denpos: "0 < L2 * (f_R (valofL x0) - f_R x_min)" by (rule mult_pos_pos[OF L2_pos gap0_pos])
      have Bpos: "0 < valof eps2 - Eg - L2 * E" using margin by linarith
      have key: "valof eps2 - Eg - L2 * E < L2 * (q ^ it * (f_R (valofL x0) - f_R x_min))"
      proof -
        have lt: "valof eps2 - Eg < L2 * (f_R (valofL xv) - f_R x_min)"
          using rdot_lb smooth by linarith
        have W_mul: "L2 * (f_R (valofL xv) - f_R x_min)
                       \<le> L2 * (q ^ it * (f_R (valofL x0) - f_R x_min) + E)"
          by (rule mult_left_mono[OF inv]) (use L2_pos in simp)
        have expand: "L2 * (q ^ it * (f_R (valofL x0) - f_R x_min) + E)
                        = L2 * (q ^ it * (f_R (valofL x0) - f_R x_min)) + L2 * E"
          by (simp add: algebra_simps)
        from lt W_mul expand show ?thesis by linarith
      qed
      have cpow_lb: "(valof eps2 - Eg - L2 * E) / (L2 * (f_R (valofL x0) - f_R x_min)) < q ^ it"
        using key by (simp add: pos_divide_less_eq[OF denpos] mult_ac)
      have cpow_pos: "0 < q ^ it" using q_pos by simp
      have b_gt1: "1 < 1 / q" using q_pos q_lt1 by (simp add: field_simps)
      have recip: "(1 / q) ^ it
                     < L2 * (f_R (valofL x0) - f_R x_min) / (valof eps2 - Eg - L2 * E)"
      proof -
        have "(1 / q) ^ it = 1 / q ^ it" by (simp add: power_one_over)
        also have "\<dots> < 1 / ((valof eps2 - Eg - L2 * E) / (L2 * (f_R (valofL x0) - f_R x_min)))"
          by (rule divide_strict_left_mono[OF cpow_lb zero_less_one
                     mult_pos_pos[OF cpow_pos divide_pos_pos[OF Bpos denpos]]])
        also have "\<dots> = L2 * (f_R (valofL x0) - f_R x_min) / (valof eps2 - Eg - L2 * E)"
          by (simp only: divide_divide_eq_right)
        finally show ?thesis .
      qed
      have iter_lt: "it < log (1 / q)
                       (L2 * (f_R (valofL x0) - f_R x_min) / (valof eps2 - Eg - L2 * E))"
        using less_log_of_power[OF recip b_gt1] .
      have iter_lt_nat: "it < nat \<lceil>log (1 / q)
                       (L2 * (f_R (valofL x0) - f_R x_min) / (valof eps2 - Eg - L2 * E))\<rceil>"
        using iter_lt real_nat_ceiling_ge by linarith
      show "nat \<lceil>log (1 / q)
              (L2 * (f_R (valofL x0) - f_R x_min) / (valof eps2 - Eg - L2 * E))\<rceil> - Suc it
             < nat \<lceil>log (1 / q)
              (L2 * (f_R (valofL x0) - f_R x_min) / (valof eps2 - Eg - L2 * E))\<rceil> - it"
        using iter_lt_nat by (metis diff_less_mono2 lessI)
    qed
    \<comment> \<open>Initial establishment of the invariant.\<close>
    subgoal by (simp add: E0)
    \<comment> \<open>Post: small-gradient and a-posteriori gap bounds.\<close>
    subgoal premises prems for it xv
    proof -
      have inv: "f_R (valofL xv) - f_R x_min \<le> q ^ it * (f_R (valofL x0) - f_R x_min) + E"
        and nguard: "\<not> eps2 < fdot (grad xv) (grad xv)"
        using prems by auto
      have xreg: "f_R (valofL xv) - f_R x_min \<le> (f_R (valofL x0) - f_R x_min) + E"
        by (rule reg_of_inv[OF inv])
      have fok: "fdot_ok (grad xv) (grad xv)" by (rule guard_ok[OF xreg])
      have fin: "is_finite (fdot (grad xv) (grad xv))" by (rule fdot_ok_finite[OF fok])
      have vle: "valof (fdot (grad xv) (grad xv)) \<le> valof eps2"
        using nguard float_le_neg[OF eps2_fin fin] float_le[OF fin eps2_fin] by simp
      have ferror: "\<bar>valof (fdot (grad xv) (grad xv)) - rdot (grad xv) (grad xv)\<bar>
                      \<le> fdot_err (grad xv) (grad xv)" by (rule fdot_error[OF fok])
      have ferr: "fdot_err (grad xv) (grad xv) \<le> Eg" by (rule guard_err[OF xreg])
      have rdot_ub: "rdot (grad xv) (grad xv) \<le> valof eps2 + Eg"
        using vle ferror ferr by linarith
      have pl: "M2 * (f_R (valofL xv) - f_R x_min) \<le> rdot (grad xv) (grad xv)"
        by (rule pl_oracle[OF xreg])
      have gap_ub: "f_R (valofL xv) - f_R x_min \<le> (valof eps2 + Eg) / M2"
        using pl rdot_ub M2_pos by (simp add: pos_le_divide_eq mult.commute)
      from inv rdot_ub gap_ub
      show "rdot (grad xv) (grad xv) \<le> valof eps2 + Eg" by blast
    qed
    \<comment> \<open>Post: the a-posteriori gap bound (from the PL inequality).\<close>
    subgoal premises prems for it xv
    proof -
      have inv: "f_R (valofL xv) - f_R x_min \<le> q ^ it * (f_R (valofL x0) - f_R x_min) + E"
        and nguard: "\<not> eps2 < fdot (grad xv) (grad xv)"
        using prems by auto
      have xreg: "f_R (valofL xv) - f_R x_min \<le> (f_R (valofL x0) - f_R x_min) + E"
        by (rule reg_of_inv[OF inv])
      have fok: "fdot_ok (grad xv) (grad xv)" by (rule guard_ok[OF xreg])
      have fin: "is_finite (fdot (grad xv) (grad xv))" by (rule fdot_ok_finite[OF fok])
      have vle: "valof (fdot (grad xv) (grad xv)) \<le> valof eps2"
        using nguard float_le_neg[OF eps2_fin fin] float_le[OF fin eps2_fin] by simp
      have ferror: "\<bar>valof (fdot (grad xv) (grad xv)) - rdot (grad xv) (grad xv)\<bar>
                      \<le> fdot_err (grad xv) (grad xv)" by (rule fdot_error[OF fok])
      have ferr: "fdot_err (grad xv) (grad xv) \<le> Eg" by (rule guard_err[OF xreg])
      have rdot_ub: "rdot (grad xv) (grad xv) \<le> valof eps2 + Eg"
        using vle ferror ferr by linarith
      have pl: "M2 * (f_R (valofL xv) - f_R x_min) \<le> rdot (grad xv) (grad xv)"
        by (rule pl_oracle[OF xreg])
      show "f_R (valofL xv) - f_R x_min \<le> (valof eps2 + Eg) / M2"
        using pl rdot_ub M2_pos by (simp add: pos_le_divide_eq mult.commute)
    qed
    done
qed

text \<open>
  The direct-float counterpart of the \<^emph>\<open>quadratic\<close> gradient-descent
  result with exact line search (steepest descent on a strongly convex
  quadratic, Kantorovich rate). The Lyapunov function is the energy
  \<open>EN(x) = (x - x\<^sub>\<star>) \<cdot> Q (x - x\<^sub>\<star>)\<close>; over the real shadow it contracts by
  \<open>r2 = ((A - a)/(A + a))\<^sup>2\<close> per step, where \<open>a, A\<close> are the smallest and
  largest eigenvalues of \<open>Q\<close>.

  Exactly as for the PL regime, with one step's round-off folded into a
  constant width \<open>\<delta>\<close>, the energy obeys \<open>EN\<^sub>k\<^sub>+\<^sub>1 \<le> r2 \<cdot> EN\<^sub>k + \<delta>\<close>, and
  provided \<open>\<delta> \<le> (1 - r2) Ew\<close> the affine bound \<open>r2 ^ iter \<cdot> EN\<^sub>0 + Ew\<close> is
  preserved with a \<^emph>\<open>constant\<close> envelope, giving the direct bound

  \[
     EN(valofL\,x) \;\le\; r2^{\,iter}\,EN_0 + Ew
  \]

  throughout, an a-posteriori bound \<open>EN \<le> (valof eps2 + Eg) / a\<close> at exit
  (from the eigenvalue lower bound \<open>a \<cdot> EN \<le> grad \<cdot> grad\<close>), and no growing
  \<open>iter \<cdot> \<delta>\<close> drift. The eigenvalue facts (smoothness \<open>grad \<cdot> grad \<le> A \<cdot> EN\<close>,
  the Kantorovich contraction, the energy positivity) are abstract
  hypotheses over the real shadow; the genuine floating-point content is the
  inner product appearing in the guard and its first-principles error bound
  \<open>fdot_error\<close>. Iterates are genuine float vectors (\<^typ>\<open>float64 list\<close>); the
  exact-line-search step is a float function \<open>astep\<close>.
\<close>


subsection \<open>The contraction recurrence\<close>

lemma gd_quad_recurrence:
  fixes Wold Wnew G r2 \<delta> Ew :: real and k :: nat
  assumes old: "Wold \<le> r2 ^ k * G + Ew"
    and new: "Wnew \<le> r2 * Wold + \<delta>"
    and r2nn: "0 \<le> r2"
    and env: "\<delta> \<le> (1 - r2) * Ew"
  shows "Wnew \<le> r2 ^ Suc k * G + Ew"
proof -
  have e2: "\<delta> \<le> Ew - r2 * Ew" using env by (simp add: algebra_simps)
  have "Wnew \<le> r2 * Wold + \<delta>" by (rule new)
  also have "\<dots> \<le> r2 * (r2 ^ k * G + Ew) + \<delta>"
    using mult_left_mono[OF old r2nn] by linarith
  also have "\<dots> = r2 ^ Suc k * G + (r2 * Ew + \<delta>)"
    by (simp add: algebra_simps)
  also have "\<dots> \<le> r2 ^ Suc k * G + Ew" using e2 by linarith
  finally show ?thesis .
qed


subsection \<open>State and program\<close>

zstore stGDQ =
  iter :: "nat"
  x    :: "float64 list"

text \<open>
  Pure floating-point steepest descent with exact line search. The state is
  the genuine float iterate \<open>x\<close>; \<open>grad\<close> is the float gradient; \<open>astep\<close> the
  float line-search step (\<open>(g \<cdot> g)/(g \<cdot> Qg)\<close> in floating point); the guard
  tests the float inner product \<open>grad x \<bullet> grad x\<close> against \<open>eps2\<close>. The energy
  \<open>EN\<close> and the reals \<open>r2, \<delta>, Ew, a, A, Eg\<close> are specification-only.
\<close>

program gd_quad_FD
  "(grad :: float64 list \<Rightarrow> float64 list, x0 :: float64 list,
    astep :: float64 list \<Rightarrow> float64, eps2 :: float64,
    EN :: real list \<Rightarrow> real,
    r2 :: real, \<delta> :: real, Ew :: real, a :: real, A :: real, Eg :: real)" over stGDQ
 = "x := x0; iter := 0;
    while fdot (grad x) (grad x) > eps2
    invariant EN (valofL x) \<le> r2 ^ iter * EN (valofL x0) + Ew
    variant nat \<lceil>log (1 / r2)
                  (A * EN (valofL x0) / (valof eps2 - Eg - A * Ew))\<rceil> - iter
    do x := fvsub x (fscaleR (astep x) (grad x)); iter := iter + 1 od"


subsection \<open>Direct convergence correctness\<close>

theorem gd_quad_FD_direct_correct:
  fixes grad :: "float64 list \<Rightarrow> float64 list"
  fixes EN :: "real list \<Rightarrow> real"
  fixes x0 :: "float64 list" and astep :: "float64 list \<Rightarrow> float64" and eps2 :: float64
  fixes r2 \<delta> Ew a A Eg :: real
  assumes r2_pos: "0 < r2"
  assumes r2_lt1: "r2 < 1"
  assumes delta_nonneg: "0 \<le> \<delta>"
  assumes envelope: "\<delta> \<le> (1 - r2) * Ew"
  assumes a_pos: "0 < a"
  assumes A_pos: "0 < A"
  assumes eps2_fin: "is_finite eps2"
  assumes Eg_nonneg: "0 \<le> Eg"
  assumes en0_pos: "0 < EN (valofL x0)"
  assumes margin: "Eg + A * Ew < valof eps2"
  assumes contraction_oracle:
    "\<And>v. EN (valofL v) \<le> EN (valofL x0) + Ew
        \<Longrightarrow> EN (valofL (fvsub v (fscaleR (astep v) (grad v))))
              \<le> r2 * EN (valofL v) + \<delta>"
  assumes smooth_oracle:
    "\<And>v. EN (valofL v) \<le> EN (valofL x0) + Ew
        \<Longrightarrow> rdot (grad v) (grad v) \<le> A * EN (valofL v)"
  assumes eig_oracle:
    "\<And>v. EN (valofL v) \<le> EN (valofL x0) + Ew
        \<Longrightarrow> a * EN (valofL v) \<le> rdot (grad v) (grad v)"
  assumes guard_ok:
    "\<And>v. EN (valofL v) \<le> EN (valofL x0) + Ew \<Longrightarrow> fdot_ok (grad v) (grad v)"
  assumes guard_err:
    "\<And>v. EN (valofL v) \<le> EN (valofL x0) + Ew \<Longrightarrow> fdot_err (grad v) (grad v) \<le> Eg"
  shows "H[True] gd_quad_FD (grad, x0, astep, eps2, EN, r2, \<delta>, Ew, a, A, Eg)
       [EN (valofL x) \<le> r2 ^ iter * EN (valofL x0) + Ew
        \<and> rdot (grad x) (grad x) \<le> valof eps2 + Eg
        \<and> EN (valofL x) \<le> (valof eps2 + Eg) / a]"
proof -
  have r2_nonneg: "0 \<le> r2" using r2_pos by simp
  have onemr2_pos: "0 < 1 - r2" using r2_lt1 by simp
  have Ew0: "0 \<le> Ew" using envelope delta_nonneg onemr2_pos
    by (meson landau_o.R_trans not_less zero_le_mult_iff)
  have en0_nonneg: "0 \<le> EN (valofL x0)" using en0_pos by simp

  \<comment> \<open>The affine bound keeps every iterate inside the reachable region.\<close>
  have reg_of_inv:
    "\<And>w :: real. \<And>k :: nat. w \<le> r2 ^ k * EN (valofL x0) + Ew
        \<Longrightarrow> w \<le> EN (valofL x0) + Ew"
  proof -
    fix w :: real and k :: nat
    assume hw: "w \<le> r2 ^ k * EN (valofL x0) + Ew"
    have r2k: "r2 ^ k \<le> 1" using r2_nonneg r2_lt1 by (simp add: power_le_one)
    have "r2 ^ k * EN (valofL x0) \<le> 1 * EN (valofL x0)"
      by (rule mult_right_mono[OF r2k en0_nonneg])
    thus "w \<le> EN (valofL x0) + Ew" using hw by simp
  qed

  show ?thesis
    apply vcg
    \<comment> \<open>Preservation of the affine energy bound.\<close>
    subgoal premises prems for it xv
    proof -
      have inv: "EN (valofL xv) \<le> r2 ^ it * EN (valofL x0) + Ew"
        using prems by auto
      have xreg: "EN (valofL xv) \<le> EN (valofL x0) + Ew"
        by (rule reg_of_inv[OF inv])
      have step: "EN (valofL (fvsub xv (fscaleR (astep xv) (grad xv))))
                    \<le> r2 * EN (valofL xv) + \<delta>"
        by (rule contraction_oracle[OF xreg])
      have "EN (valofL (fvsub xv (fscaleR (astep xv) (grad xv))))
              \<le> r2 ^ Suc it * EN (valofL x0) + Ew"
        by (rule gd_quad_recurrence[OF inv step r2_nonneg envelope])
      thus "EN (valofL (fvsub xv (fscaleR (astep xv) (grad xv))))
              \<le> r2 * r2 ^ it * EN (valofL x0) + Ew" by simp
    qed
    \<comment> \<open>The variant strictly decreases.\<close>
    subgoal premises prems for it xv
    proof -
      have inv: "EN (valofL xv) \<le> r2 ^ it * EN (valofL x0) + Ew"
        and guard: "eps2 < fdot (grad xv) (grad xv)"
        using prems by auto
      have xreg: "EN (valofL xv) \<le> EN (valofL x0) + Ew"
        by (rule reg_of_inv[OF inv])
      have fok: "fdot_ok (grad xv) (grad xv)" by (rule guard_ok[OF xreg])
      have fin: "is_finite (fdot (grad xv) (grad xv))" by (rule fdot_ok_finite[OF fok])
      have vguard: "valof eps2 < valof (fdot (grad xv) (grad xv))"
        using guard float_lt[OF eps2_fin fin] by simp
      have ferror: "\<bar>valof (fdot (grad xv) (grad xv)) - rdot (grad xv) (grad xv)\<bar>
                      \<le> fdot_err (grad xv) (grad xv)" by (rule fdot_error[OF fok])
      have ferr: "fdot_err (grad xv) (grad xv) \<le> Eg" by (rule guard_err[OF xreg])
      have rdot_lb: "valof eps2 - Eg < rdot (grad xv) (grad xv)"
        using vguard ferror ferr by linarith
      have smooth: "rdot (grad xv) (grad xv) \<le> A * EN (valofL xv)"
        by (rule smooth_oracle[OF xreg])
      have denpos: "0 < A * EN (valofL x0)" by (rule mult_pos_pos[OF A_pos en0_pos])
      have Bpos: "0 < valof eps2 - Eg - A * Ew" using margin by linarith
      have key: "valof eps2 - Eg - A * Ew < A * (r2 ^ it * EN (valofL x0))"
      proof -
        have lt: "valof eps2 - Eg < A * EN (valofL xv)"
          using rdot_lb smooth by linarith
        have W_mul: "A * EN (valofL xv) \<le> A * (r2 ^ it * EN (valofL x0) + Ew)"
          by (rule mult_left_mono[OF inv]) (use A_pos in simp)
        have expand: "A * (r2 ^ it * EN (valofL x0) + Ew)
                        = A * (r2 ^ it * EN (valofL x0)) + A * Ew"
          by (simp add: algebra_simps)
        from lt W_mul expand show ?thesis by linarith
      qed
      have cpow_lb: "(valof eps2 - Eg - A * Ew) / (A * EN (valofL x0)) < r2 ^ it"
        using key by (simp add: pos_divide_less_eq[OF denpos] mult_ac)
      have cpow_pos: "0 < r2 ^ it" using r2_pos by simp
      have b_gt1: "1 < 1 / r2" using r2_pos r2_lt1 by (simp add: field_simps)
      have recip: "(1 / r2) ^ it
                     < A * EN (valofL x0) / (valof eps2 - Eg - A * Ew)"
      proof -
        have "(1 / r2) ^ it = 1 / r2 ^ it" by (simp add: power_one_over)
        also have "\<dots> < 1 / ((valof eps2 - Eg - A * Ew) / (A * EN (valofL x0)))"
          by (rule divide_strict_left_mono[OF cpow_lb zero_less_one
                     mult_pos_pos[OF cpow_pos divide_pos_pos[OF Bpos denpos]]])
        also have "\<dots> = A * EN (valofL x0) / (valof eps2 - Eg - A * Ew)"
          by (simp only: divide_divide_eq_right)
        finally show ?thesis .
      qed
      have iter_lt: "it < log (1 / r2)
                       (A * EN (valofL x0) / (valof eps2 - Eg - A * Ew))"
        using less_log_of_power[OF recip b_gt1] .
      have iter_lt_nat: "it < nat \<lceil>log (1 / r2)
                       (A * EN (valofL x0) / (valof eps2 - Eg - A * Ew))\<rceil>"
        using iter_lt real_nat_ceiling_ge by linarith
      show "nat \<lceil>log (1 / r2)
              (A * EN (valofL x0) / (valof eps2 - Eg - A * Ew))\<rceil> - Suc it
             < nat \<lceil>log (1 / r2)
              (A * EN (valofL x0) / (valof eps2 - Eg - A * Ew))\<rceil> - it"
        using iter_lt_nat by (metis diff_less_mono2 lessI)
    qed
    \<comment> \<open>Initial establishment of the invariant.\<close>
    subgoal by (simp add: Ew0)
    \<comment> \<open>Post: small-gradient bound at exit.\<close>
    subgoal premises prems for it xv
    proof -
      have inv: "EN (valofL xv) \<le> r2 ^ it * EN (valofL x0) + Ew"
        and nguard: "\<not> eps2 < fdot (grad xv) (grad xv)"
        using prems by auto
      have xreg: "EN (valofL xv) \<le> EN (valofL x0) + Ew"
        by (rule reg_of_inv[OF inv])
      have fok: "fdot_ok (grad xv) (grad xv)" by (rule guard_ok[OF xreg])
      have fin: "is_finite (fdot (grad xv) (grad xv))" by (rule fdot_ok_finite[OF fok])
      have vle: "valof (fdot (grad xv) (grad xv)) \<le> valof eps2"
        using nguard float_le_neg[OF eps2_fin fin] float_le[OF fin eps2_fin] by simp
      have ferror: "\<bar>valof (fdot (grad xv) (grad xv)) - rdot (grad xv) (grad xv)\<bar>
                      \<le> fdot_err (grad xv) (grad xv)" by (rule fdot_error[OF fok])
      have ferr: "fdot_err (grad xv) (grad xv) \<le> Eg" by (rule guard_err[OF xreg])
      show "rdot (grad xv) (grad xv) \<le> valof eps2 + Eg"
        using vle ferror ferr by linarith
    qed
    \<comment> \<open>Post: the a-posteriori energy bound (from the eigenvalue lower bound).\<close>
    subgoal premises prems for it xv
    proof -
      have inv: "EN (valofL xv) \<le> r2 ^ it * EN (valofL x0) + Ew"
        and nguard: "\<not> eps2 < fdot (grad xv) (grad xv)"
        using prems by auto
      have xreg: "EN (valofL xv) \<le> EN (valofL x0) + Ew"
        by (rule reg_of_inv[OF inv])
      have fok: "fdot_ok (grad xv) (grad xv)" by (rule guard_ok[OF xreg])
      have fin: "is_finite (fdot (grad xv) (grad xv))" by (rule fdot_ok_finite[OF fok])
      have vle: "valof (fdot (grad xv) (grad xv)) \<le> valof eps2"
        using nguard float_le_neg[OF eps2_fin fin] float_le[OF fin eps2_fin] by simp
      have ferror: "\<bar>valof (fdot (grad xv) (grad xv)) - rdot (grad xv) (grad xv)\<bar>
                      \<le> fdot_err (grad xv) (grad xv)" by (rule fdot_error[OF fok])
      have ferr: "fdot_err (grad xv) (grad xv) \<le> Eg" by (rule guard_err[OF xreg])
      have rdot_ub: "rdot (grad xv) (grad xv) \<le> valof eps2 + Eg"
        using vle ferror ferr by linarith
      have eig: "a * EN (valofL xv) \<le> rdot (grad xv) (grad xv)"
        by (rule eig_oracle[OF xreg])
      show "EN (valofL xv) \<le> (valof eps2 + Eg) / a"
        using eig rdot_ub a_pos by (simp add: pos_le_divide_eq mult.commute)
    qed
    done
qed

end