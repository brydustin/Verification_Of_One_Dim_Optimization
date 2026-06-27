section \<open>\<open>C\<^sup>k\<close> differentiability\<close>

theory Ck_Differentiable
  imports K_Times_Fr_Differentiable
begin

text \<open>
  \<open>C\<^sup>k\<close> smoothness at a point and on an open set, built on the same
  directional-derivative recursion as \<open>k_times_Fr_differentiable_at\<close> but with
  continuity in the base case.  The equivalence with the AFP predicate
  \<^const>\<open>higher_differentiable_on\<close> is established here because the whole closure
  family is then obtained from the AFP closure lemmas through it.
\<close>

subsection \<open>\<open>C\<^sup>k\<close> at a point\<close>

primrec Ck_at
  :: "nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a \<Rightarrow> bool"
where
  "Ck_at 0 f x \<longleftrightarrow> continuous (at x) f"
| "Ck_at (Suc k) f x \<longleftrightarrow>
     (\<exists>A. open A \<and> x \<in> A \<and> (\<forall>y\<in>A. Ck_at k f y))
   \<and> f differentiable (at x)
   \<and> (\<forall>v. Ck_at k (\<lambda>y. frechet_derivative f (at y) v) x)"


subsection \<open>\<open>C\<^sup>k\<close> on an open set\<close>

definition Ck_on
  :: "nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a set \<Rightarrow> bool"
where
  "Ck_on k f U \<longleftrightarrow> open U \<and> (\<forall>x\<in>U. Ck_at k f x)"


subsection \<open>\<open>C\<^sup>k\<close> implies \<open>k\<close>-times Fréchet differentiable\<close>

lemma Ck_at_imp_k_times_Fr:
  "Ck_at k f x \<Longrightarrow> k_times_Fr_differentiable_at k f x"
proof (induction k arbitrary: f x)
  case 0 then show ?case by simp
next
  case (Suc k)
  then show ?case
    by auto
qed

corollary Ck_on_imp_k_times_Fr_on:
  "Ck_on k f U \<Longrightarrow> k_times_Fr_differentiable_on k f U"
  by (simp add: Ck_on_def k_times_Fr_differentiable_on_def Ck_at_imp_k_times_Fr)


subsection \<open>Equivalence with the AFP \<open>higher_differentiable_on\<close>\<close>

lemma Ck_on_iff_higher_differentiable_on:
  assumes "open U"
  shows "Ck_on k f U \<longleftrightarrow> higher_differentiable_on U f k"
  using assms
proof (induction k arbitrary: f U)
  case 0
  show ?case
  proof
    assume "Ck_on 0 f U"
    then have "\<forall>x\<in>U. continuous (at x) f"
      by (simp add: Ck_on_def)
    then have "\<forall>x\<in>U. continuous (at x within U) f"
      using continuous_at_imp_continuous_at_within by blast
    then show "higher_differentiable_on U f 0"
      by (simp add: continuous_on_eq_continuous_within higher_differentiable_on.simps(1))
  next
    assume "higher_differentiable_on U f 0"
    then have "continuous_on U f"
      using higher_differentiable_on.simps(1) by blast
    then have "\<forall>x\<in>U. continuous (at x within U) f"
      using continuous_on_eq_continuous_within by blast
    then have "\<forall>x\<in>U. continuous (at x) f"
      by (metis "0" at_within_open)
    then show "Ck_on 0 f U"
      using "0" by (simp add: Ck_on_def)
  qed
next
  case (Suc k)
  show ?case
  proof
    assume "Ck_on (Suc k) f U"
    then have U_open: "open U"
      and Cat: "\<forall>x\<in>U. Ck_at (Suc k) f x"
      by (auto simp: Ck_on_def)
    have diff: "\<forall>x\<in>U. f differentiable (at x)"
      using Cat by auto
    have der_Ck_on: "\<forall>v. Ck_on k (\<lambda>y. frechet_derivative f (at y) v) U"
      using Cat Ck_on_def U_open by fastforce
    have der_higher: "\<forall>v. higher_differentiable_on U (\<lambda>y. frechet_derivative f (at y) v) k"
      using Suc.IH[OF U_open] der_Ck_on by blast
    then show "higher_differentiable_on U f (Suc k)"
      using diff higher_differentiable_on.simps(2) by blast
  next
    assume H: "higher_differentiable_on U f (Suc k)"
    then have diff: "\<forall>x\<in>U. f differentiable (at x)"
      and der_higher:
        "\<forall>v. higher_differentiable_on U (\<lambda>y. frechet_derivative f (at y) v) k"
      using H higher_differentiable_on.simps(2) by blast+
    have Hk: "higher_differentiable_on U f k"
      using H by (rule higher_differentiable_on_SucD)
    have CkU: "Ck_on k f U"
      using Suc.IH[OF Suc.prems] Hk by blast
    have der_Ck_on: "\<forall>v. Ck_on k (\<lambda>y. frechet_derivative f (at y) v) U"
      using Suc.IH[OF Suc.prems] der_higher by blast
    show "Ck_on (Suc k) f U"
      by (metis CkU Ck_at.simps(2) Ck_on_def der_Ck_on diff)
  qed
qed


subsection \<open>Closure properties\<close>

lemma Ck_at_const:
  "Ck_at k (\<lambda>_. c) x"
proof (induction k arbitrary: x c)
  case 0
  then show ?case
    by simp
next
  case (Suc k)
  have nbhd: "\<exists>A. open A \<and> x \<in> A \<and> (\<forall>y\<in>A. Ck_at k (\<lambda>_. c) y)"
    using Suc.IH by (intro exI[of _ UNIV]) auto

  have diff: "(\<lambda>_. c) differentiable (at x)"
    by simp

  have derivs: "\<forall>v. Ck_at k (\<lambda>y. frechet_derivative (\<lambda>_. c) (at y) v) x"
    by (simp add: Suc)

  show ?case
    using nbhd diff derivs
    by simp
qed

lemma Ck_on_const:
  "open U \<Longrightarrow> Ck_on k (\<lambda>_. c) U"
  by (simp add: Ck_on_def Ck_at_const)

lemma Ck_on_add:
  assumes "Ck_on k f U" and "Ck_on k g U"
  shows   "Ck_on k (\<lambda>y. f y + g y) U"
proof -
  have U: "open U"
    using assms by (auto simp: Ck_on_def)
  have hf: "higher_differentiable_on U f k"
    using assms(1) U by (simp add: Ck_on_iff_higher_differentiable_on)
  have hg: "higher_differentiable_on U g k"
    using assms(2) U by (simp add: Ck_on_iff_higher_differentiable_on)
  have hsum: "higher_differentiable_on U (\<lambda>y. f y + g y) k"
    using hf hg U by (rule higher_differentiable_on_add)
  show ?thesis
    using U hsum by (simp add: Ck_on_iff_higher_differentiable_on)
qed

lemma Ck_on_sum:
  fixes F :: "'i \<Rightarrow> 'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes fin: "finite I"
      and ne: "I \<noteq> {}"
      and Ck: "\<And>i. i \<in> I \<Longrightarrow> Ck_on k (F i) U"
  shows "Ck_on k (\<lambda>y. \<Sum>i\<in>I. F i y) U"
  using fin ne Ck
proof (induction rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert i I)
  have Ci: "Ck_on k (F i) U"
    using insert.prems by simp
  show ?case
  proof (cases "I = {}")
    case True
    then show ?thesis
      using Ci insert.hyps by simp
  next
    case False
    have CI: "Ck_on k (\<lambda>y. \<Sum>j\<in>I. F j y) U"
      using insert.IH[OF False] insert.prems by blast
    show ?thesis
      using Ck_on_add[OF Ci CI] insert.hyps by simp
  qed
qed

lemma Ck_on_scaleR:
  assumes "Ck_on k f U"
  shows   "Ck_on k (\<lambda>y. c *\<^sub>R f y) U"
proof -
  have U: "open U"
    using assms by (simp add: Ck_on_def)
  have hf: "higher_differentiable_on U f k"
    using assms U by (simp add: Ck_on_iff_higher_differentiable_on)
  have hscale: "higher_differentiable_on U (\<lambda>y. c *\<^sub>R f y) k"
    by (simp add: U hf higher_differentiable_on_const higher_differentiable_on_scaleR)
  show ?thesis
    using U hscale by (simp add: Ck_on_iff_higher_differentiable_on)
qed

lemma Ck_on_id:
  "open U \<Longrightarrow> Ck_on k (\<lambda>x. x) U"
  by (simp add: Ck_on_iff_higher_differentiable_on higher_differentiable_on_id)

lemma Ck_on_neg:
  assumes "Ck_on k f U"
  shows "Ck_on k (\<lambda>y. - f y) U"
proof -
  have "Ck_on k (\<lambda>y. (-1) *\<^sub>R f y) U"
    by (rule Ck_on_scaleR[OF assms])
  thus ?thesis by simp
qed

lemma Ck_on_sub:
  assumes "Ck_on k f U" and "Ck_on k g U"
  shows "Ck_on k (\<lambda>y. f y - g y) U"
proof -
  have "Ck_on k (\<lambda>y. f y + (- g y)) U"
    by (rule Ck_on_add[OF assms(1) Ck_on_neg[OF assms(2)]])
  thus ?thesis by simp
qed

lemma Ck_on_mult:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> real"
  assumes "Ck_on k f U" and "Ck_on k g U"
  shows "Ck_on k (\<lambda>y. f y * g y) U"
proof -
  have oU: "open U"
    using assms(1) by (simp add: Ck_on_def)
  have hf: "higher_differentiable_on U f k"
    using assms(1) oU by (simp add: Ck_on_iff_higher_differentiable_on)
  have hg: "higher_differentiable_on U g k"
    using assms(2) oU by (simp add: Ck_on_iff_higher_differentiable_on)
  have "higher_differentiable_on U (\<lambda>y. f y * g y) k"
    using hf hg oU by (rule higher_differentiable_on_mult)
  thus ?thesis
    using oU by (simp add: Ck_on_iff_higher_differentiable_on)
qed

lemma Ck_on_pow:
  fixes f :: "'a::real_normed_vector \<Rightarrow> real"
  assumes "Ck_on k f U"
  shows "Ck_on k (\<lambda>y. (f y) ^ n) U"
proof (induction n)
  case 0
  have "open U" using assms by (simp add: Ck_on_def)
  then show ?case
    using Ck_on_const by simp
next
  case (Suc n)
  have "Ck_on k (\<lambda>y. f y * (f y) ^ n) U"
    by (rule Ck_on_mult[OF assms Suc])
  thus ?case by (simp add: power_Suc2)
qed

lemma Ck_on_inverse:
  fixes f :: "'a::real_normed_vector \<Rightarrow> real"
  assumes "Ck_on k f U" and "\<And>y. y \<in> U \<Longrightarrow> f y \<noteq> 0"
  shows "Ck_on k (\<lambda>y. inverse (f y)) U"
proof -
  have oU: "open U"
    using assms(1) by (simp add: Ck_on_def)
  have hf: "higher_differentiable_on U f k"
    using assms(1) oU by (simp add: Ck_on_iff_higher_differentiable_on)
  have "higher_differentiable_on U (\<lambda>y. inverse (f y)) k"
    using hf assms(2) oU by(subst higher_differentiable_on_inverse, simp_all, simp add: image_iff)
  thus ?thesis
    using oU by (simp add: Ck_on_iff_higher_differentiable_on)
qed

lemma Ck_on_divide:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> real"
  assumes "Ck_on k f U" and "Ck_on k g U" and "\<And>y. y \<in> U \<Longrightarrow> g y \<noteq> 0"
  shows "Ck_on k (\<lambda>y. f y / g y) U"
proof -
  have inv_g: "Ck_on k (\<lambda>y. inverse (g y)) U"
    by (rule Ck_on_inverse[OF assms(2,3)])
  have "Ck_on k (\<lambda>y. f y * inverse (g y)) U"
    by (rule Ck_on_mult[OF assms(1) inv_g])
  thus ?thesis by (simp add: divide_inverse)
qed

lemma Ck_on_inner:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> 'b::real_inner"
  assumes "Ck_on k f U" and "Ck_on k g U"
  shows "Ck_on k (\<lambda>y. f y \<bullet> g y) U"
proof -
  have oU: "open U"
    using assms(1) by (simp add: Ck_on_def)
  have hf: "higher_differentiable_on U f k"
    using assms(1) oU by (simp add: Ck_on_iff_higher_differentiable_on)
  have hg: "higher_differentiable_on U g k"
    using assms(2) oU by (simp add: Ck_on_iff_higher_differentiable_on)
  have "higher_differentiable_on U (\<lambda>y. f y \<bullet> g y) k"
    using hf hg oU by (rule higher_differentiable_on_inner)
  thus ?thesis
    using oU by (simp add: Ck_on_iff_higher_differentiable_on)
qed

lemma Ck_on_norm_sq:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_inner"
  assumes "Ck_on k f U"
  shows "Ck_on k (\<lambda>y. (norm (f y))\<^sup>2) U"
proof -
  have "Ck_on k (\<lambda>y. f y \<bullet> f y) U"
    by (rule Ck_on_inner[OF assms assms])
  thus ?thesis by (simp add: dot_square_norm)
qed

lemma Ck_on_compose:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::euclidean_space"
    and g :: "'b \<Rightarrow> 'c::real_normed_vector"
  assumes "Ck_on k g V" and "Ck_on k f U" and "\<And>y. y \<in> U \<Longrightarrow> f y \<in> V"
  shows "Ck_on k (\<lambda>y. g (f y)) U"
proof -
  have oU: "open U"
    using assms(2) by (simp add: Ck_on_def)
  have oV: "open V"
    using assms(1) by (simp add: Ck_on_def)
  have hf: "higher_differentiable_on U f k"
    using assms(2) oU by (simp add: Ck_on_iff_higher_differentiable_on)
  have hg: "higher_differentiable_on V g k"
    using assms(1) oV by (simp add: Ck_on_iff_higher_differentiable_on)
  have fUV: "f ` U \<subseteq> V"
    using assms(3) by blast
  have "higher_differentiable_on U (g \<circ> f) k"
    by (rule higher_differentiable_on_compose[OF hg hf fUV oU oV])
  hence "higher_differentiable_on U (\<lambda>y. g (f y)) k"
    by (simp add: o_def)
  thus ?thesis
    using oU by (simp add: Ck_on_iff_higher_differentiable_on)
qed

lemma Ck_on_subset:
  assumes "Ck_on k f U" and "open V" and "V \<subseteq> U"
  shows "Ck_on k f V"
proof -
  have oU: "open U"
    using assms(1) by (simp add: Ck_on_def)
  have hf: "higher_differentiable_on U f k"
    using assms(1) oU by (simp add: Ck_on_iff_higher_differentiable_on)
  have "higher_differentiable_on V f k"
    using hf assms(3) by (rule higher_differentiable_on_subset)
  thus ?thesis
    using assms(2) by (simp add: Ck_on_iff_higher_differentiable_on)
qed

lemma Ck_on_mono:
  assumes "Ck_on k f U" and "m \<le> k"
  shows "Ck_on m f U"
proof -
  have oU: "open U"
    using assms(1) by (simp add: Ck_on_def)
  have hf: "higher_differentiable_on U f k"
    using assms(1) oU by (simp add: Ck_on_iff_higher_differentiable_on)
  have "higher_differentiable_on U f m"
    using hf assms(2) by (rule higher_differentiable_on_le)
  thus ?thesis
    using oU by (simp add: Ck_on_iff_higher_differentiable_on)
qed


subsection \<open>Automation\<close>

text \<open>Compositional \<open>C\<^sup>k\<close> existence rules, modelled on \<open>derivative_intros\<close>.
  \<open>Ck_on_compose\<close> is \<^emph>\<open>not\<close> in the set (its schematic functional head loops
  under higher-order unification); apply it explicitly.\<close>

named_theorems Ck_intros "existence rules for C\<^sup>k smoothness"

declare
  Ck_on_const   [Ck_intros]
  Ck_on_id      [Ck_intros]
  Ck_on_add     [Ck_intros]
  Ck_on_scaleR  [Ck_intros]
  Ck_on_neg     [Ck_intros]
  Ck_on_sub     [Ck_intros]
  Ck_on_mult    [Ck_intros]
  Ck_on_pow     [Ck_intros]
  Ck_on_inner   [Ck_intros]

lemma example_Ck:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> real"
  assumes "Ck_on k f U" "Ck_on k g U"
  shows "Ck_on k (\<lambda>y. f y * g y + (f y) ^ 2) U"
  using assms
  by (auto intro!: Ck_intros)

end
