section \<open>Subsumption of the official derivative notions\<close>

theory Higher_Diff_Subsumption
  imports Ck_Differentiable Limits_Higher_Order_Derivatives
begin

text \<open>
  This theory collects, in one place, the generalisation results of the unified
  notions against the notions that carry an official Isabelle/AFP definition:
  \<^const>\<open>higher_differentiable_on\<close> (Smooth\_Manifolds), \<^const>\<open>C_k_on\<close>
  (\<open>Limits_Higher_Order_Derivatives\<close>), and \<^const>\<open>has_real_derivative\<close> /
  \<^const>\<open>has_vector_derivative\<close> (\<open>HOL-Analysis.Deriv\<close>).
\<close>

subsection \<open>Real-line bridge helpers\<close>

text \<open>A small set of \<open>deriv\<close> facts needed for the
  \<^const>\<open>higher_differentiable_on\<close> \<open>\<leftrightarrow>\<close> \<^const>\<open>C_k_on\<close> bridge on \<^typ>\<open>real\<close>.\<close>

lemma frechet_derivative_to_deriv:
  fixes f :: "real \<Rightarrow> real"
  assumes "f differentiable (at x)"
  shows "frechet_derivative f (at x) h = h * deriv f x"
  by (simp add: assms field_derivative_eq_vector_derivative
      frechet_derivative_eq_vector_derivative)

lemma frechet_derivative_one_eq_deriv:
  fixes f :: "real \<Rightarrow> real"
  assumes "f differentiable (at x)"
  shows "frechet_derivative f (at x) 1 = deriv f x"
  using frechet_derivative_to_deriv[OF assms] by simp

lemma kth_deriv_shift:
  "(deriv ^^ Suc n) g = (deriv ^^ n) (deriv g)"
  by (simp add: funpow_swap1)

lemma higher_differentiable_on_real_imp_Ck_on:
  assumes Uop: "open U"
  shows "higher_differentiable_on U f k \<Longrightarrow> C_k_on k f U"
proof (induction k arbitrary: f)
  case 0
  then show ?case
    by (simp add: C_k_on_def Uop higher_differentiable_on.simps)
next
  case (Suc k)
  assume H: "higher_differentiable_on U f (Suc k)"
  then have D0: "\<forall>x\<in>U. f differentiable (at x)"
    by (simp add: higher_differentiable_on.simps)
  have Hv: "\<forall>v. higher_differentiable_on U (\<lambda>x. frechet_derivative f (at x) v) k"
    using H by (simp add: higher_differentiable_on.simps)

  text \<open>On \<real>\<rightarrow>\<real>, the v=1 slice equals the ordinary derivative.\<close>
  have Hder: "higher_differentiable_on U (\<lambda>x. deriv f x) k"
  proof -
    have "higher_differentiable_on U (\<lambda>x. frechet_derivative f (at x) 1) k"
      using Hv by simp
    moreover have "\<And>x. x\<in>U \<Longrightarrow> frechet_derivative f (at x) 1 = deriv f x"
      using D0 by (simp add: frechet_derivative_one_eq_deriv)
    ultimately show ?thesis
      by (simp add: assms higher_differentiable_on_congI)
  qed

  text \<open>Apply the IH to the derivative field.\<close>
  have CKder: "C_k_on k (\<lambda>x. deriv f x) U"
    using Suc.IH[OF Hder].

  text \<open>We need continuity of the first derivative on U.\<close>
  have cont_deriv: "continuous_on U (deriv f)"
  proof (cases k)
    case 0
    then show ?thesis using CKder by (simp add: C_k_on_def)
  next
    case (Suc m)
    then have "\<forall>x\<in>U. (\<lambda>x. deriv f x) differentiable (at x)"
      using Hder by (simp add: higher_differentiable_on.simps)
    thus ?thesis
      using Hder higher_differentiable_on_imp_continuous_on by blast
  qed

  text \<open>And f is differentiable on U by openness.\<close>
  have f_on: "f differentiable_on U"
    using D0 Uop Suc.prems higher_differentiable_on_imp_differentiable_on by blast

  text \<open>Assemble all rows n < Suc k for C_{Suc k}.\<close>
  have grid:
    "\<forall>n < Suc k.
       (deriv ^^ n) f differentiable_on U
     \<and> continuous_on U ((deriv ^^ Suc n) f)"
  proof (intro allI impI)
    fix n assume nlt: "n < Suc k"
    consider (z) "n = 0" | (s) j where "n = Suc j" "j < k"
      by (meson less_Suc_eq_0_disj nlt)

    then show
      "(deriv ^^ n) f differentiable_on U
       \<and> continuous_on U ((deriv ^^ Suc n) f)"
    proof cases
      case z
      then show ?thesis using f_on cont_deriv by simp
    next
      case s
      then obtain j where jlt: "j < k" and nj: "n = Suc j" by auto
      from CKder have
        "(deriv ^^ j) (deriv f) differentiable_on U
         \<and> continuous_on U ((deriv ^^ Suc j) (deriv f))"
        using jlt by (simp add: C_k_on_def)
      thus ?thesis
        using kth_deriv_shift nj by metis
    qed
  qed

  show ?case
    using Uop grid by (simp add: C_k_on_def)
qed

lemma Ck_on_imp_higher_differentiable_on_real:
  fixes f :: "real \<Rightarrow> real" and U :: "real set"
  assumes Uop: "open U"
  shows "C_k_on k f U \<Longrightarrow> higher_differentiable_on U f k"
proof (induction k arbitrary: f)
  case 0
  then show ?case
    by (simp add: C_k_on_def higher_differentiable_on.simps)
next
  case (Suc k)
  assume C: "C_k_on (Suc k) f U"

  have Uop': "open U"
    using C by (simp add: C_k_on_def)

  text \<open>Pointwise differentiability of f on U from the n=0 row.\<close>

  have "f differentiable_on U"
    using C Uop' C_k_on_def by auto

  then have D0: "\<forall>x\<in>U. f differentiable (at x)"
    using assms differentiable_on_openD by blast

  text \<open>Build C_k_on for the derivative field from the grid for f.\<close>
  have Cg: "C_k_on k (\<lambda>x. deriv f x) U"
    using C_k_on_def Suc.prems kth_deriv_shift
    by (metis One_nat_def Suc_eq_plus1 diff_Suc_1'
        first_derivative_alt_def less_diff_conv old.nat.distinct(1) zero_less_Suc)

  text \<open>Convert that to higher_differentiable_on via IH.\<close>
  have HDg: "higher_differentiable_on U (\<lambda>x. deriv f x) k"
    by (simp add: Cg Suc.IH)


  text \<open>For each v, frechet derivative equals v * deriv f on \<real>, and scaling preserves Cᵏ.\<close>
  have Hv: "\<forall>v. higher_differentiable_on U (\<lambda>x. frechet_derivative f (at x) v) k"
  proof
    fix v :: real
    have "higher_differentiable_on U (\<lambda>x. v * deriv f x) k"
      using HDg
    proof (induction k)
      show "higher_differentiable_on U (deriv f) 0 \<Longrightarrow>
            higher_differentiable_on U (\<lambda>x. v * deriv f x) 0"
        using assms higher_differentiable_on.simps(1) continuous_on_mult_left
        by blast
    next
      fix k :: nat
      assume IH_imp: "(higher_differentiable_on U (deriv f) k \<Longrightarrow> higher_differentiable_on U (\<lambda>x. v * deriv f x) k)"
      assume IH: "higher_differentiable_on U (deriv f) (Suc k)"
      show "higher_differentiable_on U (\<lambda>x. v * deriv f x) (Suc k)"
        by (simp add: IH assms higher_differentiable_on_const higher_differentiable_on_mult)
    qed
    moreover have eqv: "\<And>x. x\<in>U \<Longrightarrow> frechet_derivative f (at x) v = v * deriv f x"
      using D0 frechet_derivative_to_deriv by blast

    ultimately show "higher_differentiable_on U (\<lambda>x. frechet_derivative f (at x) v) k"
      by (subst higher_differentiable_on_cong[OF _ _ eqv], simp_all, simp add: Uop)
  qed
  show ?case
    by (simp add: higher_differentiable_on.simps D0 Hv)
qed

corollary higher_differentiable_on_real_iff_Ck_on:
  fixes f :: "real \<Rightarrow> real" and U :: "real set"
  assumes Uop: "open U"
  shows "higher_differentiable_on U f k \<longleftrightarrow> C_k_on k f U"
  using Ck_on_imp_higher_differentiable_on_real assms
        higher_differentiable_on_real_imp_Ck_on by blast


subsection \<open>Subsumption of \<^const>\<open>higher_differentiable_on\<close> and \<^const>\<open>C_k_on\<close>\<close>

text \<open>\<open>Ck_on\<close> coincides with the AFP \<^const>\<open>higher_differentiable_on\<close> on open
  sets, and (on \<^typ>\<open>real\<close>) with \<^const>\<open>C_k_on\<close>.\<close>

theorem subsumes_higher_diff:
  assumes "open U"
  shows "Ck_on k f U \<longleftrightarrow> higher_differentiable_on U f k"
  using assms by (rule Ck_on_iff_higher_differentiable_on)

theorem subsumes_C_k_on:
  fixes f :: "real \<Rightarrow> real"
  assumes "open U"
  shows "Ck_on k f U \<longleftrightarrow> C_k_on k f U"
  using assms Ck_on_iff_higher_differentiable_on
        higher_differentiable_on_real_iff_Ck_on by blast


subsection \<open>Subsumption of \<^const>\<open>has_real_derivative\<close> and \<^const>\<open>has_vector_derivative\<close>\<close>

text \<open>The first-order notions of \<open>HOL-Analysis.Deriv\<close> are the \<open>k = 1\<close> slice of
  the unified notion: each asserts the existence of a (Fréchet) derivative.\<close>

theorem subsumes_has_real_derivative:
  "(f has_real_derivative D) (at x) \<Longrightarrow> k_times_Fr_differentiable_at 1 f x"
  using one_times_Fr_iff real_differentiable_def differentiableI
  by blast

theorem subsumes_has_vector_derivative:
  "(f has_vector_derivative D) (at x) \<Longrightarrow> k_times_Fr_differentiable_at 1 f x"
  using one_times_Fr_iff has_vector_derivative_def differentiableI
  by blast

end
