section \<open>\<open>k\<close>-times Fréchet differentiability\<close>

theory K_Times_Fr_Differentiable
  imports Smooth_Manifolds.Smooth
begin

text \<open>
  The apex higher-order differentiability notion of this development:
  \<open>k_times_Fr_differentiable_at\<close>, pure (no continuity) \<open>k\<close>-times Fréchet
  differentiability for maps between arbitrary real normed vector spaces.

  The higher-order \<^emph>\<open>operator\<close> is the AFP \<^const>\<open>nth_derivative\<close> of
  \<open>Smooth_Manifolds.Smooth\<close> (\<^const>\<open>frechet_derivative\<close> is the first-order one);
  we do not introduce a bespoke operator.  Its recursion step
  \<open>\<lambda>y. frechet_derivative f (at y) v\<close> is exactly the step used by the
  predicate, which yields the relating lemma
  \<open>k_times_Fr_imp_nth_derivative_differentiable\<close> below.
\<close>

subsection \<open>Preliminary\<close>

text \<open>Transferring a Fréchet derivative across functions agreeing on an open set.\<close>

lemma has_derivative_transfer_open:
  assumes "open X" and "x \<in> X"
  assumes eq_on_X: "\<forall>x\<in>X. f x = g x"
  assumes f_has_deriv: "(f has_derivative f') (at x)"
  shows "(g has_derivative f') (at x)"
  using at_within_open_subset[OF _ \<open>open X\<close>, of _ X, simplified]
  by (metis \<open>x \<in> X\<close> f_has_deriv eq_on_X has_derivative_transform)


subsection \<open>The predicate\<close>

primrec k_times_Fr_differentiable_at
  :: "nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a \<Rightarrow> bool"
where
  "k_times_Fr_differentiable_at 0 f x \<longleftrightarrow> True"
| "k_times_Fr_differentiable_at (Suc k) f x \<longleftrightarrow>
     (\<exists>A. open A \<and> x \<in> A \<and> (\<forall>y\<in>A. k_times_Fr_differentiable_at k f y))
   \<and> f differentiable (at x)
   \<and> (\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative f (at y) v) x)"

text \<open>Sanity check: \<open>1\<close>-times differentiable = Fréchet differentiable.\<close>

lemma one_times_Fr_iff:
  "k_times_Fr_differentiable_at 1 f x \<longleftrightarrow> f differentiable (at x)"
  by auto

text \<open>Monotonicity: higher differentiability implies lower.\<close>

lemma k_times_Fr_differentiable_at_mono:
  assumes "m \<le> k" and "k_times_Fr_differentiable_at k f x"
  shows   "k_times_Fr_differentiable_at m f x"
  using assms
proof (induction k arbitrary: m f x)
  case 0
  then have "m = 0" by simp
  then show ?case by simp
next
  case (Suc k)
  note IH = Suc.IH
  note asm = Suc.prems

  show ?case
  proof (cases m)
    case 0
    then show ?thesis by simp
  next
    case (Suc m')
    from asm(1) Suc have m'_le: "m' \<le> k"
      by simp

    from asm(2) obtain A where
      A: "open A"
         "x \<in> A"
         "\<forall>y\<in>A. k_times_Fr_differentiable_at k f y"
      and fdiff: "f differentiable (at x)"
      and D: "\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative f (at y) v) x"
      by auto

    have A': "\<forall>y\<in>A. k_times_Fr_differentiable_at m' f y"
      using A(3) IH[OF m'_le] by blast

    have D': "\<forall>v. k_times_Fr_differentiable_at m' (\<lambda>y. frechet_derivative f (at y) v) x"
      using D IH[OF m'_le] by blast

    show ?thesis
      using Suc A fdiff D' A'
      by (metis IH asm(1,2) le_Suc_eq)
  qed
qed

text \<open>Peeling off the top layer.\<close>

lemma k_times_Fr_differentiable_at_SucD:
  assumes "k_times_Fr_differentiable_at (Suc k) f x"
  shows   "k_times_Fr_differentiable_at k f x"
    and   "f differentiable (at x)"
    and   "\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative f (at y) v) x"
  using assms k_times_Fr_differentiable_at_mono
  by auto

text \<open>The derivative field inherits differentiability.\<close>

lemma k_times_Fr_differentiable_at_derivative:
  assumes "k_times_Fr_differentiable_at (Suc k) f x"
  shows   "\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative f (at y) v) x"
  using assms by simp


subsection \<open>Set-wise version\<close>

definition k_times_Fr_differentiable_on
  :: "nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a set \<Rightarrow> bool"
where
  "k_times_Fr_differentiable_on k f S \<longleftrightarrow> (\<forall>x\<in>S. k_times_Fr_differentiable_at k f x)"

lemma k_times_Fr_differentiable_onI:
  "(\<And>x. x \<in> S \<Longrightarrow> k_times_Fr_differentiable_at k f x) \<Longrightarrow> k_times_Fr_differentiable_on k f S"
  by (simp add: k_times_Fr_differentiable_on_def)

lemma k_times_Fr_differentiable_onD:
  "k_times_Fr_differentiable_on k f S \<Longrightarrow> x \<in> S \<Longrightarrow> k_times_Fr_differentiable_at k f x"
  by (simp add: k_times_Fr_differentiable_on_def)

lemma k_times_Fr_differentiable_on_mono:
  "m \<le> k \<Longrightarrow> k_times_Fr_differentiable_on k f S \<Longrightarrow> k_times_Fr_differentiable_on m f S"
  by (simp add: k_times_Fr_differentiable_on_def k_times_Fr_differentiable_at_mono)

lemma k_times_Fr_differentiable_on_subset:
  "S \<subseteq> T \<Longrightarrow> k_times_Fr_differentiable_on k f T \<Longrightarrow> k_times_Fr_differentiable_on k f S"
  by (simp add: k_times_Fr_differentiable_on_def subset_iff)


subsection \<open>Locality (transfer on an open neighbourhood)\<close>

lemma k_times_Fr_differentiable_at_transfer_open:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes U: "open U" "x \<in> U"
    and eq: "\<And>y. y \<in> U \<Longrightarrow> f y = g y"
    and Hf: "k_times_Fr_differentiable_at k f x"
  shows "k_times_Fr_differentiable_at k g x"
  using U eq Hf
proof (induction k arbitrary: f g x U)
  case 0
  then show ?case by simp
next
  case (Suc k)

  from Suc.prems(4) obtain A where
    A: "open A" "x \<in> A" "\<forall>y\<in>A. k_times_Fr_differentiable_at k f y"
    and df: "f differentiable (at x)"
    and Df: "\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative f (at y) v) x"
    unfolding k_times_Fr_differentiable_at.simps(2)
    by blast

  let ?C = "A \<inter> U"
  have C: "open ?C" "x \<in> ?C"
    using A Suc.prems by auto

  have neigh: "\<forall>y\<in>?C. k_times_Fr_differentiable_at k g y"
    by (metis A(3) Int_iff Suc.IH Suc.prems(1,3))
  have evx: "eventually (\<lambda>y. y \<in> U) (nhds x)"
    using Suc.prems(1,2) by (simp add: eventually_nhds, auto)
  have evx_fg: "eventually (\<lambda>y. f y = g y) (nhds x)"
    by (rule eventually_mono[OF evx]) (use Suc.prems(3) in auto)


  have dg: "g differentiable (at x)"
    by (metis Suc.prems(1,2,3) df differentiable_eqI)

  have Dg: "\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative g (at y) v) x"
  proof
    fix v
    show "k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative g (at y) v) x"
    proof (cases k)
      case 0
      then show ?thesis by simp
    next
      case (Suc j)

      have eqD:
        "\<And>y. y \<in> ?C \<Longrightarrow> frechet_derivative f (at y) v = frechet_derivative g (at y) v"
      proof -
        fix y
        assume yC: "y \<in> ?C"
        hence yA: "y \<in> A" and yU: "y \<in> U"
          by auto

        have fy: "k_times_Fr_differentiable_at (Suc j) f y"
          using A(3) Suc yA by blast

        hence dfy: "f differentiable (at y)"
          using k_times_Fr_differentiable_at_mono[of 1 "Suc j" f y]
          by (simp add: one_times_Fr_iff)

        have gy: "k_times_Fr_differentiable_at (Suc j) g y"
          using Suc neigh yC by blast

        hence dgy: "g differentiable (at y)"
          using k_times_Fr_differentiable_at_mono[of 1 "Suc j" g y]
          by (simp add: one_times_Fr_iff)

        have evy: "eventually (\<lambda>z. f z = g z) (nhds y)"
          using Suc.prems(1) yU Suc.prems(3)
          by (simp add: eventually_nhds, auto)

        have "(f has_derivative frechet_derivative f (at y)) (at y)"
          by (simp add: dfy frechet_derivative_worksI)
        then have "(g has_derivative frechet_derivative f (at y)) (at y)"
          using Suc.prems(1,3) has_derivative_transfer_open yU by blast
        moreover have "(g has_derivative frechet_derivative g (at y)) (at y)"
          using dgy frechet_derivative_worksI by blast
        ultimately have "frechet_derivative f (at y) = frechet_derivative g (at y)"
          by (rule has_derivative_unique)
        then show "frechet_derivative f (at y) v = frechet_derivative g (at y) v"
          by simp
      qed

      have "k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative f (at y) v) x"
        using Df by blast
      then show ?thesis
        using Suc.IH[OF C(1,2), of
            "\<lambda>y. frechet_derivative f (at y) v"
            "\<lambda>y. frechet_derivative g (at y) v"]
          eqD
        by blast
    qed
  qed

  show "k_times_Fr_differentiable_at (Suc k) g x"
    unfolding k_times_Fr_differentiable_at.simps(2)
    using C neigh dg Dg by blast
qed

lemma eq_on_open_k_times_Fr_differentiable_at:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes U: "open U" "x \<in> U"
    and eq: "\<And>y. y \<in> U \<Longrightarrow> f y = g y"
  shows "k_times_Fr_differentiable_at k f x \<longleftrightarrow> k_times_Fr_differentiable_at k g x"
  using k_times_Fr_differentiable_at_transfer_open[OF U eq]
        k_times_Fr_differentiable_at_transfer_open[OF U(1,2), of g f k] eq
  by auto


subsection \<open>Closure properties\<close>

lemma k_times_Fr_const:
  "k_times_Fr_differentiable_at k (\<lambda>_. c) x"
proof (induction k arbitrary: x c)
  case 0
  then show ?case
    by simp
next
  case (Suc k)
  have "\<exists>A. open A \<and> x \<in> A \<and> (\<forall>y\<in>A. k_times_Fr_differentiable_at k (\<lambda>_. c) y)"
    using Suc.IH by (intro exI[of _ UNIV]) auto
  moreover have "(\<lambda>_. c) differentiable (at x)"
    by simp
  moreover have "\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative (\<lambda>_. c) (at y) v) x"
    by (simp add: Suc)
  ultimately show ?case
    by simp
qed

lemma k_times_Fr_id:
  "k_times_Fr_differentiable_at k (\<lambda>x. x) x"
proof (induction k arbitrary: x)
  case 0
  then show ?case
    by simp
next
  case (Suc k)
  have nbhd:
    "\<exists>A. open A \<and> x \<in> A \<and> (\<forall>y\<in>A. k_times_Fr_differentiable_at k (\<lambda>x. x) y)"
    using Suc.IH by (intro exI[of _ UNIV]) auto
  have diff: "(\<lambda>x. x) differentiable (at x)"
    by simp
  have derivs: "\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative (\<lambda>x. x) (at y) v) x"
    by (simp add: k_times_Fr_const)
  show ?case
    using nbhd diff derivs
    by simp
qed

lemma k_times_Fr_add:
  assumes "k_times_Fr_differentiable_at k f x"
      and "k_times_Fr_differentiable_at k g x"
  shows "k_times_Fr_differentiable_at k (\<lambda>y. f y + g y) x"
  using assms
proof (induction k arbitrary: f g x)
  case 0
  then show ?case
    by simp
next
  case (Suc k)
  from Suc.prems(1) obtain A where
    A: "open A" "x \<in> A" "\<forall>y\<in>A. k_times_Fr_differentiable_at k f y"
    and df: "f differentiable (at x)"
    and Df: "\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative f (at y) v) x"
    unfolding k_times_Fr_differentiable_at.simps(2)
    by blast

  from Suc.prems(2) obtain B where
    B: "open B" "x \<in> B" "\<forall>y\<in>B. k_times_Fr_differentiable_at k g y"
    and dg: "g differentiable (at x)"
    and Dg: "\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative g (at y) v) x"
    unfolding k_times_Fr_differentiable_at.simps(2)
    by blast

  let ?C = "A \<inter> B"
  have C: "open ?C" "x \<in> ?C"
    using A B by auto

  have neigh: "\<forall>y\<in>?C. k_times_Fr_differentiable_at k (\<lambda>z. f z + g z) y"
  proof
    fix y
    assume yC: "y \<in> ?C"
    then have yA: "y \<in> A" and yB: "y \<in> B"
      by auto
    show "k_times_Fr_differentiable_at k (\<lambda>z. f z + g z) y"
      using Suc.IH A(3)[rule_format, OF yA] B(3)[rule_format, OF yB] by blast
  qed

  have diff: "(\<lambda>y. f y + g y) differentiable (at x)"
    by (simp add: df dg)
  have Dsum:"\<forall>v. k_times_Fr_differentiable_at k
           (\<lambda>y. frechet_derivative (\<lambda>z. f z + g z) (at y) v) x"
  proof
    fix v
    show "k_times_Fr_differentiable_at k
            (\<lambda>y. frechet_derivative (\<lambda>z. f z + g z) (at y) v) x"
    proof (cases k)
      case 0
      then show ?thesis
        by simp
    next
      case (Suc j)

      have ksum:
        "k_times_Fr_differentiable_at k
           (\<lambda>y. frechet_derivative f (at y) v + frechet_derivative g (at y) v) x"
        using Suc.IH Df Dg by blast

      have eqD:
        "\<And>y. y \<in> ?C \<Longrightarrow>
          frechet_derivative (\<lambda>z. f z + g z) (at y) v =
          frechet_derivative f (at y) v + frechet_derivative g (at y) v"
      proof -
        fix y
        assume yC: "y \<in> ?C"
        then have yA: "y \<in> A" and yB: "y \<in> B"
          by auto

        have fy: "k_times_Fr_differentiable_at (Suc j) f y"
          using A(3) Suc yA by blast

        have gy: "k_times_Fr_differentiable_at (Suc j) g y"
          using B(3) Suc yB by blast


        have dfy: "f differentiable (at y)"
          using fy k_times_Fr_differentiable_at_mono[of 1 "Suc j" f y]
          by (simp add: one_times_Fr_iff)

        have dgy: "g differentiable (at y)"
          using gy k_times_Fr_differentiable_at_mono[of 1 "Suc j" g y]
          by (simp add: one_times_Fr_iff)

        have hder: "((\<lambda>z. f z + g z) has_derivative
             (\<lambda>h. frechet_derivative f (at y) h + frechet_derivative g (at y) h)) (at y)"
          by (simp add: dfy dgy frechet_derivative_worksI)

        then have "frechet_derivative (\<lambda>z. f z + g z) (at y) =
              (\<lambda>h. frechet_derivative f (at y) h + frechet_derivative g (at y) h)"
          using frechet_derivative_at' by blast
        then show
          "frechet_derivative (\<lambda>z. f z + g z) (at y) v =
           frechet_derivative f (at y) v + frechet_derivative g (at y) v"
          by simp
      qed

      have
        "k_times_Fr_differentiable_at k
           (\<lambda>y. frechet_derivative (\<lambda>z. f z + g z) (at y) v) x \<longleftrightarrow>
         k_times_Fr_differentiable_at k
           (\<lambda>y. frechet_derivative f (at y) v + frechet_derivative g (at y) v) x"
        by (smt (verit) C(1,2) eqD eq_on_open_k_times_Fr_differentiable_at)
      then show ?thesis
        using ksum by blast
    qed
  qed
  show ?case
    unfolding k_times_Fr_differentiable_at.simps(2)
    using C neigh diff Dsum by blast
qed

lemma k_times_Fr_scaleR:
  assumes "k_times_Fr_differentiable_at k f x"
  shows "k_times_Fr_differentiable_at k (\<lambda>y. c *\<^sub>R f y) x"
  using assms
proof (induction k arbitrary: f x)
  case 0
  then show ?case
    by simp
next
  case (Suc k)
  from Suc.prems obtain A where
    A: "open A" "x \<in> A" "\<forall>y\<in>A. k_times_Fr_differentiable_at k f y"
    and df: "f differentiable (at x)"
    and Df: "\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative f (at y) v) x"
    unfolding k_times_Fr_differentiable_at.simps(2)
    by blast

  have neigh: "\<forall>y\<in>A. k_times_Fr_differentiable_at k (\<lambda>z. c *\<^sub>R f z) y"
    using A(3) Suc.IH by blast

  have diff: "(\<lambda>y. c *\<^sub>R f y) differentiable (at x)"
    by (simp add: df)

  have Dscale: "\<forall>v. k_times_Fr_differentiable_at k
           (\<lambda>y. frechet_derivative (\<lambda>z. c *\<^sub>R f z) (at y) v) x"
  proof
    fix v
    show "k_times_Fr_differentiable_at k
            (\<lambda>y. frechet_derivative (\<lambda>z. c *\<^sub>R f z) (at y) v) x"
    proof (cases k)
      case 0
      then show ?thesis
        by simp
    next
      case (Suc j)

      have kscaled:
        "k_times_Fr_differentiable_at k
           (\<lambda>y. c *\<^sub>R frechet_derivative f (at y) v) x"
        using Suc.IH Df by blast

      have eqD:
        "\<And>y. y \<in> A \<Longrightarrow>
          frechet_derivative (\<lambda>z. c *\<^sub>R f z) (at y) v =
          c *\<^sub>R frechet_derivative f (at y) v"
      proof -
        fix y
        assume yA: "y \<in> A"

        have fy: "k_times_Fr_differentiable_at (Suc j) f y"
          using A(3) Suc yA by blast

        hence dfy: "f differentiable (at y)"
          using k_times_Fr_differentiable_at_mono[of 1 "Suc j" f y]
          by (simp add: one_times_Fr_iff)

        have hder: "((\<lambda>z. c *\<^sub>R f z) has_derivative (\<lambda>h. c *\<^sub>R frechet_derivative f (at y) h)) (at y)"
          by (simp add: dfy frechet_derivative_worksI has_derivative_scaleR_right)

        have "frechet_derivative (\<lambda>z. c *\<^sub>R f z) (at y) = (\<lambda>h. c *\<^sub>R frechet_derivative f (at y) h)"
          by (metis frechet_derivative_at hder)
        then show "frechet_derivative (\<lambda>z. c *\<^sub>R f z) (at y) v =  c *\<^sub>R frechet_derivative f (at y) v"
          by simp
      qed

      have  "k_times_Fr_differentiable_at k
           (\<lambda>y. frechet_derivative (\<lambda>z. c *\<^sub>R f z) (at y) v) x \<longleftrightarrow>
         k_times_Fr_differentiable_at k
           (\<lambda>y. c *\<^sub>R frechet_derivative f (at y) v) x"
        by (smt (verit) A(1,2) eqD eq_on_open_k_times_Fr_differentiable_at)
      then show ?thesis
        using kscaled by blast
    qed
  qed

  show ?case
    unfolding k_times_Fr_differentiable_at.simps(2)
    using A(1,2) neigh diff Dscale by blast
qed

text \<open>Post-composition with a bounded-linear map preserves the predicate.
  Not added to the automation set (its conclusion has a schematic functional
  head, so as an \<open>intro!\<close> rule it loops on higher-order unification).\<close>

lemma k_times_Fr_compose_bounded_linear:
  assumes "bounded_linear L"
  shows "k_times_Fr_differentiable_at k g x
           \<Longrightarrow> k_times_Fr_differentiable_at k (\<lambda>y. L (g y)) x"
proof (induct k arbitrary: g x)
  case 0
  show ?case
    by simp
next
  case (Suc k)
  note g = Suc.prems
  obtain A where A: "open A" "x \<in> A" "\<forall>y\<in>A. k_times_Fr_differentiable_at k g y"
    using g k_times_Fr_differentiable_at_SucD(1) k_times_Fr_differentiable_at.simps(2)
    by auto
  have gdiff: "g differentiable (at x)"
    using g k_times_Fr_differentiable_at_SucD(2)
    by blast
  have gdir: "\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative g (at y) v) x"
    using g k_times_Fr_differentiable_at_SucD(3)
    by blast
  have Lnb: "\<forall>y\<in>A. k_times_Fr_differentiable_at k (\<lambda>z. L (g z)) y"
  proof
    fix y assume yA: "y \<in> A"
    have gy: "k_times_Fr_differentiable_at k g y"
      using yA A
      by blast
    show "k_times_Fr_differentiable_at k (\<lambda>z. L (g z)) y"
      using Suc.hyps[OF gy]
      by simp
  qed
  obtain D where D: "(g has_derivative D) (at x)"
    using gdiff
    unfolding differentiable_def
    by blast
  have Ldiff: "(\<lambda>y. L (g y)) differentiable (at x)"
    using bounded_linear.has_derivative[OF assms D] differentiableI
    by auto
  have Ldir: "\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative (\<lambda>z. L (g z)) (at y) v) x"
  proof (cases k)
    case 0
    then show ?thesis
      using k_times_Fr_differentiable_at.simps(1)
      by blast
  next
    case (Suc k')
    have gdiffA: "\<forall>y\<in>A. g differentiable (at y)"
    proof
      fix y assume yA: "y \<in> A"
      have gy: "k_times_Fr_differentiable_at k g y"
        using yA A
        by simp
      have "k_times_Fr_differentiable_at 1 g y"
        using k_times_Fr_differentiable_at_mono[of 1 k g y] gy Suc
        by linarith
      then show "g differentiable (at y)"
        using one_times_Fr_iff
        by blast
    qed
    show ?thesis
    proof
      fix v
      have eqA: "\<forall>y\<in>A. frechet_derivative (\<lambda>z. L (g z)) (at y) v = L (frechet_derivative g (at y) v)"
      proof
        fix y assume yA: "y \<in> A"
        have dy: "g differentiable (at y)"
          using gdiffA yA
          by blast
        have gd: "(g has_derivative frechet_derivative g (at y)) (at y)"
          using dy frechet_derivative_works
          by auto
        have "((\<lambda>z. L (g z)) has_derivative (\<lambda>z. L (frechet_derivative g (at y) z))) (at y)"
          using bounded_linear.has_derivative[OF assms gd]
          by blast
        then show "frechet_derivative (\<lambda>z. L (g z)) (at y) v = L (frechet_derivative g (at y) v)"
          using frechet_derivative_at
          by metis
      qed
      have gdv: "k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative g (at y) v) x"
        using gdir
        by presburger
      have IHv: "k_times_Fr_differentiable_at k (\<lambda>y. L (frechet_derivative g (at y) v)) x"
        using Suc.hyps[OF gdv]
        by blast
      show "k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative (\<lambda>z. L (g z)) (at y) v) x"
        using eq_on_open_k_times_Fr_differentiable_at[OF A(1) A(2),
                of "\<lambda>y. frechet_derivative (\<lambda>z. L (g z)) (at y) v" "\<lambda>y. L (frechet_derivative g (at y) v)" k]
              eqA IHv
        by blast
    qed
  qed
  show ?case
    using k_times_Fr_differentiable_at.simps(2)[of k "\<lambda>y. L (g y)" x] Lnb Ldiff Ldir A
    by blast
qed

text \<open>Negation and subtraction (any normed vector space), from \<open>scaleR\<close>/\<open>add\<close>.\<close>

lemma k_times_Fr_neg:
  assumes "k_times_Fr_differentiable_at k f x"
  shows "k_times_Fr_differentiable_at k (\<lambda>y. - f y) x"
  using k_times_Fr_scaleR[OF assms, of "-1"]
  by fastforce

lemma k_times_Fr_sub:
  assumes "k_times_Fr_differentiable_at k f x"
      and "k_times_Fr_differentiable_at k g x"
  shows "k_times_Fr_differentiable_at k (\<lambda>y. f y - g y) x"
  using k_times_Fr_add[OF assms(1) k_times_Fr_neg[OF assms(2)]]
  by fastforce

text \<open>Single-step product rule for \<^const>\<open>frechet_derivative\<close> on a normed algebra.\<close>

lemma frechet_derivative_mult_at:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_algebra"
  assumes "f differentiable (at x)" "g differentiable (at x)"
  shows "frechet_derivative (\<lambda>y. f y * g y) (at x) v
           = f x * frechet_derivative g (at x) v + frechet_derivative f (at x) v * g x"
proof -
  have "((\<lambda>y. f y * g y) has_derivative
          (\<lambda>h. f x * frechet_derivative g (at x) h + frechet_derivative f (at x) h * g x)) (at x)"
    using assms frechet_derivative_works has_derivative_mult
    by blast
  then have "frechet_derivative (\<lambda>y. f y * g y) (at x)
               = (\<lambda>h. f x * frechet_derivative g (at x) h + frechet_derivative f (at x) h * g x)"
    using frechet_derivative_at
    by force
  then show ?thesis by presburger
qed

text \<open>Product closure: the key rule for certifying polynomials.  Mirrors the
  structure of \<open>k_times_Fr_add\<close>: the derivative field of \<open>f * g\<close> is the sum of
  two products \<open>f \<cdot> Dg\<close> and \<open>Df \<cdot> g\<close>, each handled by the induction hypothesis.\<close>

lemma k_times_Fr_mult:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_algebra"
  assumes "k_times_Fr_differentiable_at k f x"
      and "k_times_Fr_differentiable_at k g x"
  shows "k_times_Fr_differentiable_at k (\<lambda>y. f y * g y) x"
  using assms
proof (induction k arbitrary: f g x)
  case 0
  then show ?case by simp
next
  case (Suc k)
  from Suc.prems(1) obtain A where
    A: "open A" "x \<in> A" "\<forall>y\<in>A. k_times_Fr_differentiable_at k f y"
    and df: "f differentiable (at x)"
    and Df: "\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative f (at y) v) x"
    unfolding k_times_Fr_differentiable_at.simps(2) by blast
  from Suc.prems(2) obtain B where
    B: "open B" "x \<in> B" "\<forall>y\<in>B. k_times_Fr_differentiable_at k g y"
    and dg: "g differentiable (at x)"
    and Dg: "\<forall>v. k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative g (at y) v) x"
    unfolding k_times_Fr_differentiable_at.simps(2) by blast

  let ?C = "A \<inter> B"
  have C: "open ?C" "x \<in> ?C" using A B by auto

  have neigh: "\<forall>y\<in>?C. k_times_Fr_differentiable_at k (\<lambda>z. f z * g z) y"
  proof
    fix y assume yC: "y \<in> ?C"
    then have yA: "y \<in> A" and yB: "y \<in> B" by auto
    show "k_times_Fr_differentiable_at k (\<lambda>z. f z * g z) y"
      using Suc.IH A(3)[rule_format, OF yA] B(3)[rule_format, OF yB] by blast
  qed

  have diff: "(\<lambda>y. f y * g y) differentiable (at x)"
    using df dg
    by simp

  have Dprod: "\<forall>v. k_times_Fr_differentiable_at k
           (\<lambda>y. frechet_derivative (\<lambda>z. f z * g z) (at y) v) x"
  proof
    fix v
    show "k_times_Fr_differentiable_at k
            (\<lambda>y. frechet_derivative (\<lambda>z. f z * g z) (at y) v) x"
    proof (cases k)
      case 0
      then show ?thesis by simp
    next
      case (Suc j)
      have kf: "k_times_Fr_differentiable_at k f x"
        using Suc.prems(1) k_times_Fr_differentiable_at_SucD(1) by blast
      have kg: "k_times_Fr_differentiable_at k g x"
        using Suc.prems(2) k_times_Fr_differentiable_at_SucD(1) by blast
      have kDf: "k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative f (at y) v) x"
        using Df by blast
      have kDg: "k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative g (at y) v) x"
        using Dg by blast
      have t1: "k_times_Fr_differentiable_at k (\<lambda>y. f y * frechet_derivative g (at y) v) x"
        using Suc.IH[OF kf kDg] .
      have t2: "k_times_Fr_differentiable_at k (\<lambda>y. frechet_derivative f (at y) v * g y) x"
        using Suc.IH[OF kDf kg] .
      have kprod: "k_times_Fr_differentiable_at k
           (\<lambda>y. f y * frechet_derivative g (at y) v + frechet_derivative f (at y) v * g y) x"
        using k_times_Fr_add[OF t1 t2] .

      have eqD: "\<And>y. y \<in> ?C \<Longrightarrow>
          frechet_derivative (\<lambda>z. f z * g z) (at y) v =
          f y * frechet_derivative g (at y) v + frechet_derivative f (at y) v * g y"
      proof -
        fix y assume yC: "y \<in> ?C"
        then have yA: "y \<in> A" and yB: "y \<in> B" by auto
        have dfy: "f differentiable (at y)"
          using A(3) Suc yA k_times_Fr_differentiable_at_mono[of 1 "Suc j" f y] one_times_Fr_iff
          by auto
        have dgy: "g differentiable (at y)"
          using B(3) Suc yB k_times_Fr_differentiable_at_mono[of 1 "Suc j" g y] one_times_Fr_iff
          by auto
        show "frechet_derivative (\<lambda>z. f z * g z) (at y) v =
              f y * frechet_derivative g (at y) v + frechet_derivative f (at y) v * g y"
          using frechet_derivative_mult_at[OF dfy dgy] by blast
      qed

      have transfer:
        "k_times_Fr_differentiable_at k
           (\<lambda>y. frechet_derivative (\<lambda>z. f z * g z) (at y) v) x
       = k_times_Fr_differentiable_at k
           (\<lambda>y. f y * frechet_derivative g (at y) v + frechet_derivative f (at y) v * g y) x"
        using eq_on_open_k_times_Fr_differentiable_at[OF C(1) C(2),
                of "\<lambda>y. frechet_derivative (\<lambda>z. f z * g z) (at y) v"
                   "\<lambda>y. f y * frechet_derivative g (at y) v + frechet_derivative f (at y) v * g y" k]
              eqD
        by blast
      show ?thesis
        using transfer kprod
        by meson
    qed
  qed

  show ?case
    unfolding k_times_Fr_differentiable_at.simps(2)
    using C neigh diff Dprod by blast
qed

text \<open>Powers, by induction on the exponent (needs a unit for \<open>n = 0\<close>).\<close>

lemma k_times_Fr_power:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_algebra_1"
  assumes "k_times_Fr_differentiable_at k f x"
  shows "k_times_Fr_differentiable_at k (\<lambda>y. f y ^ n) x"
proof (induction n)
  case 0
  show ?case
    using k_times_Fr_const
    by auto
next
  case (Suc n)
  have "k_times_Fr_differentiable_at k (\<lambda>y. f y * f y ^ n) x"
    using k_times_Fr_mult[OF assms Suc.IH] .
  then show ?case
    by simp
qed


subsection \<open>Relation to the operator \<^const>\<open>nth_derivative\<close>\<close>

text \<open>\<^const>\<open>nth_derivative\<close> iterates \<^const>\<open>frechet_derivative\<close> in a single fixed
  direction \<^term>\<open>v\<close>; its recursion step coincides with the step of the
  predicate.  Hence the predicate at level \<^term>\<open>j + k\<close> guarantees that the
  \<open>k\<close>-th iterate \<^term>\<open>\<lambda>y. nth_derivative k f y v\<close> is itself \<open>j\<close>-times Fréchet
  differentiable.  (\<^const>\<open>nth_derivative\<close> captures the ``diagonal'' of the
  genuine multilinear higher derivative, so this is an implication, not an
  equivalence.)\<close>

lemma k_times_Fr_imp_nth_derivative_differentiable:
  "k_times_Fr_differentiable_at (j + k) f x
     \<Longrightarrow> k_times_Fr_differentiable_at j (\<lambda>y. nth_derivative k f y v) x"
proof (induct k arbitrary: f)
  case 0
  show ?case
    using 0
    by simp
next
  case (Suc k)
  have step: "k_times_Fr_differentiable_at (j + k) (\<lambda>y. frechet_derivative f (at y) v) x"
    using Suc.prems k_times_Fr_differentiable_at_SucD(3)
    by auto
  show ?case
    using Suc.hyps[OF step] nth_derivative.simps(2)
    by auto
qed

corollary k_times_Fr_Suc_imp_nth_derivative_differentiable:
  "k_times_Fr_differentiable_at (Suc k) f x
     \<Longrightarrow> (\<lambda>y. nth_derivative k f y v) differentiable (at x)"
  using k_times_Fr_imp_nth_derivative_differentiable[of 1 k f x v] one_times_Fr_iff
  by (metis plus_1_eq_Suc)


subsection \<open>Additivity of the higher-order operator\<close>

text \<open>Single-step additivity of the directional Fréchet derivative.\<close>

lemma frechet_derivative_add_at:
  assumes "f differentiable (at x)" "g differentiable (at x)"
  shows "frechet_derivative (\<lambda>y. f y + g y) (at x) v
           = frechet_derivative f (at x) v + frechet_derivative g (at x) v"
proof -
  have "((\<lambda>y. f y + g y) has_derivative
          (\<lambda>z. frechet_derivative f (at x) z + frechet_derivative g (at x) z)) (at x)"
    using assms has_derivative_add frechet_derivative_works by blast
  then have "frechet_derivative (\<lambda>y. f y + g y) (at x)
               = (\<lambda>z. frechet_derivative f (at x) z + frechet_derivative g (at x) z)"
    using frechet_derivative_at by fastforce
  then show ?thesis by presburger
qed

text \<open>The \<open>k\<close>-th iterate as one outer differentiation of the \<open>(k-1)\<close>-th iterate.\<close>

lemma nth_derivative_Suc_outer:
  "nth_derivative (Suc k) F x v
     = frechet_derivative (\<lambda>y. nth_derivative k F y v) (at x) v"
  using nth_derivative_funpow [where i = "Suc k"]
        nth_derivative_funpow [where i = k]
        funpow_simps_right(2)
  by (simp add: frechet_derivative_nth_derivative_commute)

text \<open>Locality of \<^const>\<open>frechet_derivative\<close> (a directional restatement).\<close>

lemma frechet_derivative_cong_on:
  assumes "open A" "x \<in> A" "\<And>y. y \<in> A \<Longrightarrow> g y = h y"
  shows "frechet_derivative g (at x) v = frechet_derivative h (at x) v"
  using assms has_derivative_transform_within_open
  unfolding frechet_derivative_def
  by (metis Eps_cong)

lemma nth_derivative_add_on_Fr:
  assumes "k_times_Fr_differentiable_at k f x" "k_times_Fr_differentiable_at k g x"
  shows "nth_derivative k (\<lambda>y. f y + g y) x v
           = nth_derivative k f x v + nth_derivative k g x v"
  using assms
proof (induct k arbitrary: f g x)
  case 0
  show ?case
    by simp
next
  case (Suc k)
  obtain Af where Af: "open Af" "x \<in> Af" "\<forall>y\<in>Af. k_times_Fr_differentiable_at k f y"
    using Suc.prems(1) k_times_Fr_differentiable_at.simps(2)
    by auto
  obtain Ag where Ag: "open Ag" "x \<in> Ag" "\<forall>y\<in>Ag. k_times_Fr_differentiable_at k g y"
    using Suc.prems(2) k_times_Fr_differentiable_at.simps(2)
    by auto
  define A where "A = Af \<inter> Ag"
  have AoO: "open A"
    using Af(1) Ag(1) unfolding A_def by blast
  have AoX: "x \<in> A"
    using Af(2) Ag(2) unfolding A_def by blast
  have eqA: "\<forall>y\<in>A. nth_derivative k (\<lambda>z. f z + g z) y v
                     = nth_derivative k f y v + nth_derivative k g y v"
  proof
    fix y assume yA: "y \<in> A"
    have kf: "k_times_Fr_differentiable_at k f y"
      using yA Af(3) unfolding A_def by blast
    have kg: "k_times_Fr_differentiable_at k g y"
      using yA Ag(3) unfolding A_def by fastforce
    show "nth_derivative k (\<lambda>z. f z + g z) y v
                 = nth_derivative k f y v + nth_derivative k g y v"
      using kf kg Suc.hyps by blast
  qed
  have df: "(\<lambda>y. nth_derivative k f y v) differentiable (at x)"
    using Suc.prems(1) k_times_Fr_Suc_imp_nth_derivative_differentiable by blast
  have dg: "(\<lambda>y. nth_derivative k g y v) differentiable (at x)"
    using Suc.prems(2) k_times_Fr_Suc_imp_nth_derivative_differentiable by blast
  have "nth_derivative (Suc k) (\<lambda>y. f y + g y) x v
          = frechet_derivative (\<lambda>y. nth_derivative k (\<lambda>z. f z + g z) y v) (at x) v"
    by (rule nth_derivative_Suc_outer)
  also have "\<dots> = frechet_derivative (\<lambda>y. nth_derivative k f y v + nth_derivative k g y v) (at x) v"
    using frechet_derivative_cong_on[OF AoO AoX] eqA by fastforce
  also have "\<dots> = frechet_derivative (\<lambda>y. nth_derivative k f y v) (at x) v
                  + frechet_derivative (\<lambda>y. nth_derivative k g y v) (at x) v"
    using frechet_derivative_add_at[OF df dg] by simp
  also have "\<dots> = nth_derivative (Suc k) f x v + nth_derivative (Suc k) g x v"
    by (simp only: nth_derivative_Suc_outer)
  finally show ?case .
qed


subsection \<open>Automation\<close>

named_theorems k_fr_diff "existence rules for higher-order Fréchet differentiability"

declare
  k_times_Fr_const   [k_fr_diff]
  k_times_Fr_id      [k_fr_diff]
  k_times_Fr_add     [k_fr_diff]
  k_times_Fr_scaleR  [k_fr_diff]
  k_times_Fr_neg     [k_fr_diff]
  k_times_Fr_sub     [k_fr_diff]
  k_times_Fr_mult    [k_fr_diff]
  k_times_Fr_power   [k_fr_diff]

named_theorems k_fr_derivs "n-th Fréchet derivative formulas"

lemma nth_derivative_add_eq [k_fr_derivs]:
  assumes "k_times_Fr_differentiable_at k f x" "k_times_Fr_differentiable_at k g x"
      and "c = nth_derivative k f x v + nth_derivative k g x v"
  shows "nth_derivative k (\<lambda>y. f y + g y) x v = c"
  using assms nth_derivative_add_on_Fr by blast

subsection \<open>Worked examples (automation acceptance test)\<close>

lemma example_k_fr_diff:
  fixes a :: real
  assumes "k_times_Fr_differentiable_at k f x" "k_times_Fr_differentiable_at k g x"
  shows "k_times_Fr_differentiable_at k (\<lambda>y. a *\<^sub>R f y + g y) x"
  using assms
  by (auto intro!: k_fr_diff)

lemma example_k_fr_derivs:
  assumes "k_times_Fr_differentiable_at k f x" "k_times_Fr_differentiable_at k g x"
  shows "nth_derivative k (\<lambda>y. f y + g y) x v = nth_derivative k f x v + nth_derivative k g x v"
  using assms
  by (simp add: k_fr_derivs)

text \<open>Polynomials are certified automatically, in the style of \<open>vderiv_intros\<close>.\<close>

lemma example_poly_complex:
  "k_times_Fr_differentiable_at k (\<lambda>z::complex. z^3 + 2 * z^2 + z + 1) x"
  by (auto intro!: k_fr_diff)

lemma example_poly_in_fun:
  fixes a :: complex
  assumes "k_times_Fr_differentiable_at k f x" "k_times_Fr_differentiable_at k g x"
  shows "k_times_Fr_differentiable_at k (\<lambda>y. f y ^ 3 + a * f y * g y - 2 * g y ^ 2 + 1) x"
  using assms
  by (auto intro!: k_fr_diff)

end
