section \<open>The real face of \<open>k_times_Fr_differentiable_at\<close>\<close>

theory K_Times_Fr_Real
  imports Higher_Diff_Subsumption
begin

text \<open>
  For \<^typ>\<open>real \<Rightarrow> real\<close> the apex notion \<^const>\<open>k_times_Fr_differentiable_at\<close>
  yields the iterated ordinary derivative \<open>(deriv ^^ k)\<close> chain that Taylor's
  theorem needs --- without recourse to a bespoke real predicate.  The bridge
  is purely the first-order fact \<open>frechet_derivative f (at y) 1 = deriv f y\<close>
  (\<open>frechet_derivative_one_eq_deriv\<close>) iterated through the recursion of the
  apex predicate.
\<close>

subsection \<open>From the apex notion to the iterated real derivative\<close>

lemma kfr_real_deriv_step:
  fixes f :: "real \<Rightarrow> real"
  assumes "k_times_Fr_differentiable_at (Suc k) f x"
  shows "k_times_Fr_differentiable_at k (deriv f) x"
proof (cases k)
  case 0
  then show ?thesis
    using k_times_Fr_differentiable_at.simps(1) by blast
next
  case (Suc j)
  from assms obtain A where
    A: "open A" "x \<in> A" "\<forall>y\<in>A. k_times_Fr_differentiable_at k f y"
    and D: "\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative f (at y) v) x"
    by auto
  have diffA: "\<And>y. y \<in> A \<Longrightarrow> f differentiable (at y)"
    using A(3) Suc one_times_Fr_iff k_times_Fr_differentiable_at_mono[of 1 k]
    by (metis le_add1 plus_1_eq_Suc)
  have eq: "\<And>y. y \<in> A \<Longrightarrow> frechet_derivative f (at y) 1 = deriv f y"
    using diffA frechet_derivative_one_eq_deriv
    by blast
  have D1: "k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative f (at y) 1) x"
    using D
    by auto
  show ?thesis
    using eq_on_open_k_times_Fr_differentiable_at[OF A(1) A(2),
            of "\<lambda>y. frechet_derivative f (at y) 1" "deriv f" k] eq D1
    by fastforce
qed

lemma kfr_real_funpow_deriv:
  fixes f :: "real \<Rightarrow> real"
  shows "k_times_Fr_differentiable_at (k + m) f x
           \<Longrightarrow> k_times_Fr_differentiable_at m ((deriv ^^ k) f) x"
proof (induct k arbitrary: f)
  case 0
  then show ?case
    by simp
next
  case (Suc k)
  have "k_times_Fr_differentiable_at (k + m) (deriv f) x"
    using Suc.prems kfr_real_deriv_step
    by (metis add_Suc)
  from Suc.hyps[OF this] show ?case
    by (metis kth_deriv_shift)
qed

lemma kfr_real_kth_deriv_has_derivative:
  fixes f :: "real \<Rightarrow> real"
  assumes "k_times_Fr_differentiable_at n f x" and "k < n"
  shows "((deriv ^^ k) f has_derivative (\<lambda>h. (deriv ^^ Suc k) f x * h)) (at x)"
proof -
  have kk: "k_times_Fr_differentiable_at (n - k) ((deriv ^^ k) f) x"
    using kfr_real_funpow_deriv[of k "n - k" f x] assms
    by fastforce
  have "(deriv ^^ k) f differentiable (at x)"
    using kk assms one_times_Fr_iff k_times_Fr_differentiable_at_mono[of 1 "n - k"]
    by (metis Nat.le_diff_conv2 less_eq_Suc_le less_or_eq_imp_le plus_1_eq_Suc)
  then have "((deriv ^^ k) f has_real_derivative deriv ((deriv ^^ k) f) x) (at x)"
    using DERIV_deriv_iff_real_differentiable
    by blast
  thus ?thesis
    by (simp add: has_field_derivative_def)
qed

corollary kfr_real_lower_deriv_diff:
  fixes f :: "real \<Rightarrow> real"
  assumes "k_times_Fr_differentiable_at n f x" and "k < n"
  shows "((deriv ^^ k) f) differentiable (at x)"
  using kfr_real_kth_deriv_has_derivative[OF assms] differentiableI
  by blast


subsection \<open>Polynomial functions are \<open>k\<close>-times Fréchet differentiable\<close>

lemma real_poly_imp_kfr:
  fixes p :: "real \<Rightarrow> real"
  shows "real_polynomial_function p \<Longrightarrow> k_times_Fr_differentiable_at k p x"
proof (induction rule: real_polynomial_function.induct)
  case (linear f)
  then show ?case
    using k_times_Fr_compose_bounded_linear[of f k "\<lambda>x. x" x] k_times_Fr_id
    by blast
next
  case (const c)
  then show ?case
    using k_times_Fr_const
    by blast
next
  case (add f g)
  then show ?case
    using k_times_Fr_add
    by blast
next
  case (mult f g)
  then show ?case
    using k_times_Fr_mult
    by blast
qed

lemma deriv_real_polynomial_function:
  assumes "real_polynomial_function p"
  shows   "real_polynomial_function (deriv p)"
proof -
  obtain p' where p_def: "real_polynomial_function p' \<and>
             (\<forall>x. (p has_real_derivative (p' x)) (at x))"
    using assms has_real_derivative_polynomial_function
    by presburger
  have "p' = deriv p"
    using DERIV_imp_deriv p_def
    by (metis (no_types, lifting) ext)
  then show ?thesis
    using p_def
    by simp
qed

lemma polynomial_function_kth_deriv:
  assumes "real_polynomial_function p"
  shows   "real_polynomial_function ((deriv ^^ k) p)"
proof (induct k)
  case 0
  then show ?case
    using assms
    by auto
next
  case (Suc k)
  then show ?case
    using deriv_real_polynomial_function
    by auto
qed


subsection \<open>The iterated real derivative calculus (on polynomials)\<close>

lemma poly_kth_deriv_differentiable:
  assumes "real_polynomial_function p"
  shows "((deriv ^^ k) p) differentiable (at x)"
  using polynomial_function_kth_deriv[OF assms]
        differentiable_at_real_polynomial_function
  by blast

lemma kth_deriv_cmult_poly:
  fixes g :: "real \<Rightarrow> real"
  assumes "real_polynomial_function g"
  shows "(deriv ^^ k) (\<lambda>t. c * g t) x = c * (deriv ^^ k) g x"
  using assms
proof (induct k arbitrary: x)
  case 0
  then show ?case
    by simp
next
  case (Suc k)
  have ih: "(deriv ^^ k) (\<lambda>t. c * g t) = (\<lambda>y. c * (deriv ^^ k) g y)"
    using Suc
    by blast
  have "(deriv ^^ Suc k) (\<lambda>t. c * g t) x = deriv (\<lambda>y. c * (deriv ^^ k) g y) x"
    using ih
    by simp
  also have "\<dots> = c * deriv ((deriv ^^ k) g) x"
  proof -
    have "(deriv ^^ k) g field_differentiable (at x)"
      using poly_kth_deriv_differentiable[OF Suc.prems]
      by (meson assms field_differentiable_def has_real_derivative_polynomial_function polynomial_function_kth_deriv)
    then show ?thesis
      using deriv_cmult
      by blast
  qed
  finally show ?case
    by simp
qed

lemma kth_deriv_diff_pow:
  fixes a :: real
  shows "(deriv ^^ n) (\<lambda>y. (y - a) ^ k) x =
        (if n \<le> k then fact k / fact (k - n) * (x - a) ^ (k - n) else 0)"
proof (induct n arbitrary: x)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  show ?case
  proof (cases "n \<le> k")
    case True
    note nle = True
    have fd: "(\<lambda>u. (u - a) ^ (k - n)) field_differentiable (at x)"
      using field_differentiable_power field_differentiable_diff
            field_differentiable_ident field_differentiable_const
      by blast
    have fdua: "(\<lambda>u. u - a) field_differentiable (at x)"
      using field_differentiable_diff field_differentiable_ident field_differentiable_const
      by blast
    have d1: "((\<lambda>u. u - a) has_real_derivative (1 - 0)) (at x)"
      using DERIV_ident DERIV_const DERIV_diff
      by blast
    have dua: "deriv (\<lambda>u. u - a) x = 1"
      using d1 DERIV_imp_deriv
      by auto
    have dpow: "deriv (\<lambda>u. (u - a) ^ (k - n)) x = real (k - n) * (x - a) ^ (k - n - 1)"
      using deriv_pow[OF fdua] dua
      by auto
    have funeq: "(deriv ^^ n) (\<lambda>y. (y - a) ^ k)
                   = (\<lambda>w. (fact k / fact (k - n)) * (w - a) ^ (k - n))"
      using Suc.hyps True
      by presburger
    have arith: "(fact k / fact (k - n)) * (real (k - n) * (x - a) ^ (k - n - 1)) =
        (if Suc n \<le> k then fact k / fact (k - Suc n) * (x - a) ^ (k - Suc n) else 0)"
    proof (cases "Suc n \<le> k")
      case True
      then have e2: "k - n = Suc (k - Suc n)"
        by (metis Suc_diff_le diff_Suc_Suc)
      then have e3: "fact (k - n) = real (k - n) * fact (k - Suc n)"
        using fact_Suc
        by metis
      have e4: "(real (k - n)::real) \<noteq> 0"
        using True
        by force
      have e5: "k - n - 1 = k - Suc n"
        using True
        by simp
      show ?thesis
        using True e3 e4 e5
        by simp
    next
      case False
      then have e0: "k - n = 0"
        using nle
        by simp
      then show ?thesis
        using False
        by force
    qed
    have "(deriv ^^ Suc n) (\<lambda>y. (y - a) ^ k) x
            = deriv ((deriv ^^ n) (\<lambda>y. (y - a) ^ k)) x"
      by simp
    also have "\<dots> = deriv (\<lambda>w. (fact k / fact (k - n)) * (w - a) ^ (k - n)) x"
      using funeq
      by presburger
    also have "\<dots> = (fact k / fact (k - n)) * deriv (\<lambda>u. (u - a) ^ (k - n)) x"
      using deriv_cmult[OF fd]
      by blast
    also have "\<dots> = (fact k / fact (k - n)) * (real (k - n) * (x - a) ^ (k - n - 1))"
      using dpow
      by presburger
    finally show ?thesis
      using arith
      by presburger
  next
    case False
    have "(deriv ^^ Suc n) (\<lambda>y. (y - a) ^ k) x
            = deriv (\<lambda>w. (deriv ^^ n) (\<lambda>y. (y - a) ^ k) w) x"
      by simp
    also have "\<dots> = 0"
      using Suc False
      by auto
    finally show ?thesis
      using False
      by (meson Suc_leD)
  qed
qed


subsection \<open>Sums, additivity and subtraction via the operator bridge\<close>

text \<open>The value bridge: in direction \<open>1\<close> the AFP operator \<^const>\<open>nth_derivative\<close>
  coincides with the iterated real derivative \<open>(deriv ^^ k)\<close>.\<close>

lemma nth_deriv_one_eq_kth_deriv:
  fixes f :: "real \<Rightarrow> real"
  shows "k_times_Fr_differentiable_at k f x \<Longrightarrow> nth_derivative k f x 1 = (deriv ^^ k) f x"
proof (induct k arbitrary: f x)
  case 0
  then show ?case
    by simp
next
  case (Suc k)
  from Suc.prems obtain A where
    A: "open A" "x \<in> A" "\<forall>y\<in>A. k_times_Fr_differentiable_at k f y"
    by auto
  have ihA: "\<And>y. y \<in> A \<Longrightarrow> nth_derivative k f y 1 = (deriv ^^ k) f y"
    using A(3) Suc.hyps
    by blast
  have d: "(deriv ^^ k) f differentiable (at x)"
    using Suc.prems kfr_real_lower_deriv_diff by blast
  have "nth_derivative (Suc k) f x 1
          = frechet_derivative (\<lambda>y. nth_derivative k f y 1) (at x) 1"
    by (rule nth_derivative_Suc_outer)
  also have "\<dots> = frechet_derivative ((deriv ^^ k) f) (at x) 1"
    using frechet_derivative_cong_on[OF A(1) A(2)] ihA
    by (metis (no_types, lifting))
  also have "\<dots> = (deriv ^^ Suc k) f x"
    using frechet_derivative_one_eq_deriv[OF d]
    by auto
  finally show ?case
    by blast
qed

lemma kth_deriv_add_kfr:
  fixes f g :: "real \<Rightarrow> real"
  assumes "k_times_Fr_differentiable_at k f x" and "k_times_Fr_differentiable_at k g x"
  shows "(deriv ^^ k) (\<lambda>y. f y + g y) x = (deriv ^^ k) f x + (deriv ^^ k) g x"
proof -
  have fg: "k_times_Fr_differentiable_at k (\<lambda>y. f y + g y) x"
    using assms k_times_Fr_add
    by blast
  have "(deriv ^^ k) (\<lambda>y. f y + g y) x = nth_derivative k (\<lambda>y. f y + g y) x 1"
    using nth_deriv_one_eq_kth_deriv[OF fg]
    by presburger
  also have "\<dots> = nth_derivative k f x 1 + nth_derivative k g x 1"
    using nth_derivative_add_on_Fr[OF assms]
    by blast
  also have "\<dots> = (deriv ^^ k) f x + (deriv ^^ k) g x"
    using nth_deriv_one_eq_kth_deriv[OF assms(1)] nth_deriv_one_eq_kth_deriv[OF assms(2)]
    by presburger
  finally show ?thesis
    by blast
qed

lemma kth_deriv_sub_poly:
  fixes f g :: "real \<Rightarrow> real"
  assumes "k_times_Fr_differentiable_at k f x" and "real_polynomial_function g"
  shows "(deriv ^^ k) (\<lambda>y. f y - g y) x = (deriv ^^ k) f x - (deriv ^^ k) g x"
proof -
  have gk: "k_times_Fr_differentiable_at k g x"
    using assms(2) real_poly_imp_kfr
    by auto
  have fmg: "k_times_Fr_differentiable_at k (\<lambda>y. f y - g y) x"
    using assms(1) gk k_times_Fr_sub
    by auto
  have "(deriv ^^ k) f x = (deriv ^^ k) (\<lambda>y. (f y - g y) + g y) x"
    by simp
  also have "\<dots> = (deriv ^^ k) (\<lambda>y. f y - g y) x + (deriv ^^ k) g x"
    using kth_deriv_add_kfr[OF fmg gk]
    by auto
  finally show ?thesis
    by fastforce
qed

lemma kth_deriv_sum_upto_kfr:
  fixes F :: "nat \<Rightarrow> real \<Rightarrow> real"
  assumes "\<And>i. i \<le> n \<Longrightarrow> k_times_Fr_differentiable_at k (F i) x"
  shows "k_times_Fr_differentiable_at k (\<lambda>y. \<Sum>i\<le>n. F i y) x \<and>
         (deriv ^^ k) (\<lambda>y. \<Sum>i\<le>n. F i y) x = (\<Sum>i\<le>n. (deriv ^^ k) (F i) x)"
  using assms
proof (induct n arbitrary: x)
  case 0
  have "k_times_Fr_differentiable_at k (F 0) x"
    using 0
    by simp
  then show ?case
    by simp
next
  case (Suc n)
  have IH: "k_times_Fr_differentiable_at k (\<lambda>y. \<Sum>i\<le>n. F i y) x \<and>
            (deriv ^^ k) (\<lambda>y. \<Sum>i\<le>n. F i y) x = (\<Sum>i\<le>n. (deriv ^^ k) (F i) x)"
    using Suc
    using le_SucI by presburger
  have hSuc: "k_times_Fr_differentiable_at k (F (Suc n)) x"
    using Suc.prems
    by simp
  have split: "(\<lambda>y. \<Sum>i\<le>Suc n. F i y) = (\<lambda>y. (\<Sum>i\<le>n. F i y) + F (Suc n) y)"
    by simp
  have diff: "k_times_Fr_differentiable_at k (\<lambda>y. \<Sum>i\<le>Suc n. F i y) x"
    using k_times_Fr_add[OF conjunct1[OF IH] hSuc] split
    by argo
  have "(deriv ^^ k) (\<lambda>y. \<Sum>i\<le>Suc n. F i y) x
          = (deriv ^^ k) (\<lambda>y. (\<Sum>i\<le>n. F i y) + F (Suc n) y) x"
    using split
    by presburger
  also have "\<dots> = (deriv ^^ k) (\<lambda>y. \<Sum>i\<le>n. F i y) x + (deriv ^^ k) (F (Suc n)) x"
    using kth_deriv_add_kfr[OF conjunct1[OF IH] hSuc]
    by blast
  also have "\<dots> = (\<Sum>i\<le>Suc n. (deriv ^^ k) (F i) x)"
    using IH
    by simp
  finally show ?case
    using diff
    by blast
qed

end
