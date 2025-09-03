section \<open>Higher-Order Differentiability\<close>

theory  Higher_Differentiability
  imports  "HOL-Analysis.Analysis" Auxiliary_Facts Smooth_Manifolds.Smooth
begin

subsection \<open> Definitions \<close>

text \<open> First, notice that the AFP definition of @{term Nth_derivative} coincides with 
that of the HOL-Analysis library. \<close>

lemma Nth_deriv_eq_compow_deriv: 
  "Nth_derivative n f = (deriv ^^ n) f"
  by (induct n; simp_all)

corollary deriv_commutes_Nth_deriv: 
  "Nth_derivative (Suc n) g = Nth_derivative n (deriv g)"
  by (simp add: Nth_deriv_eq_compow_deriv funpow_swap1)

text \<open> Next, observe that the Frechet derivative in the HOL-Analysis library typically 
generalises the other derivative definitions via a binary operator. \<close>

definition has_binop_deriv_at :: "('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector \<Rightarrow> 'b) 
  \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> bool"
  where "has_binop_deriv_at binop f f' x = (f has_derivative (\<lambda>y. binop y (f' x))) (at x)"

lemma has_binop_deriv_at_gen_vector_deriv:
  "has_binop_deriv_at (\<lambda>x y. x *\<^sub>R y) f f' t \<longleftrightarrow> (f has_vector_derivative f' t) (at t)"
  unfolding has_binop_deriv_at_def has_vector_derivative_def
  by simp

lemma has_binop_deriv_at_gen_real_deriv:
  "has_binop_deriv_at (\<lambda>x y. y * x) f f' x \<longleftrightarrow> (f has_real_derivative f' x) (at x)"
  unfolding has_binop_deriv_at_def has_field_derivative_def
  by simp

definition "binop_deriv_at binop f x \<equiv> (SOME D. (f has_derivative (\<lambda>y. binop y D)) (at x))"

lemma binop_deriv_at_eq_deriv: "binop_deriv_at (\<lambda>a b. b * a) f x = deriv f x"
  unfolding binop_deriv_at_def deriv_def has_field_derivative_def
  by simp

text \<open> Thus, in the nth-differentiable case at a point, we also generalise all those 
definitions using an auxiliary binary operator. We leave as future work obtaining a 
generalisation using any other filter. \<close>

primrec th_differentiable_at :: "('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector \<Rightarrow> 'b) 
  \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> bool"
  where "th_differentiable_at bop 0 f a  \<longleftrightarrow>  True"
  | "th_differentiable_at bop (Suc k) f a \<longleftrightarrow> 
      (\<exists>A. open A \<and> a \<in> A \<and> (\<forall>x\<in>A. th_differentiable_at bop k f x))       
      \<and> has_binop_deriv_at bop ((binop_deriv_at bop ^^ k) f) ((binop_deriv_at bop ^^ (Suc k)) f) a" 

text \<open>Yet, we will focus on the real version of this definition: \<close>

abbreviation times_real_differentiable_at :: "(real \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> bool"
  ("(_ _-times'_real'_differentiable'_at _)" [100,100,100] 100)
  where "f k-times_real_differentiable_at a \<equiv> th_differentiable_at (\<lambda>a b. b * a) k f a"

primrec k_times_differentiable_at :: "nat \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool" 
  where "k_times_differentiable_at 0 f a  \<longleftrightarrow>  True"
  | "k_times_differentiable_at (Suc k) f a \<longleftrightarrow>
      (\<exists>\<epsilon>>0. (\<forall>x. \<bar>x - a\<bar> < \<epsilon> \<longrightarrow> k_times_differentiable_at k f x))       
    \<and> 
      (Nth_derivative k f has_derivative (\<lambda>h. Nth_derivative (Suc k) f a * h)) (at a)" 

lemma times_real_differentiable_at_equiv:
  "f n-times_real_differentiable_at a \<longleftrightarrow> k_times_differentiable_at n f a"
proof (induct n arbitrary: a)
  case (Suc n)
  let "?deriv n f " = "(binop_deriv_at (\<lambda>a b. b * a) ^^ n) f"
  have "(\<exists>A. open A \<and> a \<in> A \<and> (\<forall>x\<in>A. th_differentiable_at (\<lambda>a b. b * a) n f x))
    \<longleftrightarrow> (\<exists>\<epsilon>>0. \<forall>x. \<bar>x - a\<bar> < \<epsilon> \<longrightarrow> k_times_differentiable_at n f x)"
    using Suc 
    by simp
      (metis (no_types, lifting) open_real Elementary_Metric_Spaces.open_ball 
        abs_minus_commute centre_in_ball dist_real_def mem_ball)
  moreover have "(?deriv n f has_derivative (*) (?deriv (Suc n) f a)) (at a)
    \<longleftrightarrow> ((deriv ^^ n) f has_derivative (*) (deriv ((deriv ^^ n) f) a)) (at a)"
    using Suc
    by (simp add: binop_deriv_at_eq_deriv)
  ultimately show ?case
    by (simp_all add: has_binop_deriv_at_def Nth_deriv_eq_compow_deriv)
qed simp

lemma times_real_differentiable_at_simps:
  shows "f 0-times_real_differentiable_at a \<longleftrightarrow> True"
    and "f (Suc k)-times_real_differentiable_at a 
    \<longleftrightarrow> (\<exists>\<epsilon>>0.  (\<forall>x. \<bar>x - a\<bar> < \<epsilon> \<longrightarrow> f k-times_real_differentiable_at x))       
      \<and> (Nth_derivative k f has_derivative (\<lambda>h. Nth_derivative (Suc k) f a * h)) (at a)"
  unfolding times_real_differentiable_at_equiv
  by simp_all

text \<open>We move to provide syntactic sugar for the most common cases: \<close>

abbreviation times_differentiable_at :: "(real \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> bool"
  ("(_ _-times'_differentiable'_at _)" [100,100,100] 100)
  where "f k-times_differentiable_at a \<equiv> k_times_differentiable_at k f a"

abbreviation twice_differentiable_at :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
  ("(_ twice'_differentiable'_at _)" [100,100] 100)
  where "f twice_differentiable_at a \<equiv> f 2-times_differentiable_at a"

abbreviation thrice_differentiable_at :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
  ("(_ thrice'_differentiable'_at _)" [100,100] 100)
  where "f thrice_differentiable_at a \<equiv> f 3-times_differentiable_at a"


subsection \<open>Basic Facts \<close>

text \<open>Now, we provide properties about our definition. \<close>

lemma k_times_differentiable_at_SucD:
  assumes "f (Suc k)-times_differentiable_at a"
  shows "f k-times_differentiable_at a"
    and "(Nth_derivative k f has_derivative (\<lambda>h. Nth_derivative (Suc k) f a * h)) (at a)"
    and "((deriv ^^k) f has_derivative (\<lambda>h. (deriv ^^(Suc k)) f a * h)) (at a)"
  using assms
  by (auto simp: Nth_deriv_eq_compow_deriv)

lemma k_times_differentiable_at_mono:
  assumes "m \<le> k" 
    and "f k-times_differentiable_at a"
  shows "f m-times_differentiable_at a"
  using assms
  by (induct k; auto simp: le_Suc_eq dest: k_times_differentiable_at_SucD)

lemma one_time_differentiable_at_iff:
  "f 1-times_differentiable_at a \<longleftrightarrow> (\<exists>f'. (f has_field_derivative f') (at a))"
  by (clarsimp, metis DERIV_imp_deriv has_field_derivative_def gt_ex)

lemma k_times_differentiable_at_le_deriv:
  assumes "f k-times_differentiable_at a"
    and "m < k"
  shows "(Nth_derivative m f has_derivative (\<lambda>h. Nth_derivative (Suc m) f a * h)) (at a)"
    and "(Nth_derivative m f has_real_derivative Nth_derivative (Suc m) f a) (at a)"
  unfolding has_field_derivative_def
  using k_times_differentiable_at_mono k_times_differentiable_at_SucD Suc_le_eq assms 
  by presburger+

corollary k_times_differentiable_at_Suc_le_deriv:
  assumes "f (Suc k)-times_differentiable_at a"
    and "m \<le> k"
  shows "(Nth_derivative m f has_derivative (\<lambda>h. Nth_derivative (Suc m) f a * h)) (at a)"
    and "(Nth_derivative m f has_real_derivative Nth_derivative (Suc m) f a) (at a)"
  unfolding has_field_derivative_def
  using assms k_times_differentiable_at_le_deriv(1) le_imp_less_Suc 
  by presburger+

corollary k_times_differentiable_ball_has_derivative_chain:
  fixes  f :: "real \<Rightarrow> real"
  assumes diff_ball: "\<forall>z. \<bar>z - x0\<bar> < \<epsilon> \<longrightarrow> f n-times_differentiable_at z"
  shows   "\<forall>i<n. \<forall>z. \<bar>z - x0\<bar> < \<epsilon> 
    \<longrightarrow> ((deriv ^^ i) f has_derivative (\<lambda>h. (deriv ^^ Suc i) f z * h)) (at z)"
  by (metis assms Nth_deriv_eq_compow_deriv k_times_differentiable_at_le_deriv(1))

lemma k_times_differentiable_at_SucE:
  fixes f :: "real \<Rightarrow> real" and k :: nat and a :: real
  assumes KD: "f (Suc k)-times_differentiable_at a"
  obtains \<epsilon> where "\<epsilon> > 0"
    and "\<And>x. \<bar>x - a\<bar> < \<epsilon> \<Longrightarrow> f k-times_differentiable_at x"
    and "(Nth_derivative k f
           has_field_derivative Nth_derivative (Suc k) f a) (at a)"
  using assms has_field_derivative_def 
    k_times_differentiable_at.simps(2) by blast

lemma k_times_differentiable_at_derivative:
  assumes "f (Suc k)-times_differentiable_at a"
  shows   "(deriv f) k-times_differentiable_at a"
using assms
proof (induction k arbitrary: f a)
  case (Suc p)
  obtain \<epsilon> where
      \<epsilon>_pos: "\<epsilon> > 0" and
      near:  "\<forall>x. \<bar>x - a\<bar> < \<epsilon> \<longrightarrow> k_times_differentiable_at (Suc p) f x" and
      deriv_cond:
        "(Nth_derivative (Suc p) f
            has_derivative (\<lambda>h. Nth_derivative (Suc (Suc p)) f a * h)) (at a)"
    using Suc.prems
    unfolding k_times_differentiable_at.simps by blast

  have near_deriv:
    "\<forall>x. \<bar>x - a\<bar> < \<epsilon> \<longrightarrow> k_times_differentiable_at p (deriv f) x"
  proof clarify
    fix x assume hx: "\<bar>x - a\<bar> < \<epsilon>"
    from near[rule_format, OF hx]
      have "k_times_differentiable_at (Suc p) f x".
    hence "k_times_differentiable_at p (deriv f) x"
      by (rule Suc.IH)          
    thus "k_times_differentiable_at p (deriv f) x".
  qed

  have deriv_cond':
    "(Nth_derivative p (deriv f)
        has_derivative (\<lambda>h. Nth_derivative (Suc p) (deriv f) a * h)) (at a)"
    using deriv_cond deriv_commutes_Nth_deriv by auto
                       
  show ?case
    using \<epsilon>_pos deriv_cond' near_deriv 
      k_times_differentiable_at.simps(2) by blast 
qed simp


subsection \<open>Continuity corollaries\<close>

lemma k_times_differentiable_at_imp_isCont:
  assumes "f (Suc k)-times_differentiable_at a"
  shows   "continuous (at a) f"
  using k_times_differentiable_at_le_deriv[OF assms, where m=0]
  by (simp add: DERIV_isCont has_field_derivative_def)

lemma k_times_differentiable_at_imp_isCont_Nth:
  assumes KD: "f (Suc k)-times_differentiable_at a"
      and JL: "j \<le> k"         
  shows   "continuous (at a) (Nth_derivative j f)"
  using assms
  by (meson has_derivative_continuous le_imp_less_Suc k_times_differentiable_at_le_deriv)


subsection \<open>Set‑wise Higher-Order Derivatives\<close>

definition k_times_differentiable_on ::
  "nat \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real set \<Rightarrow> bool" where
  "k_times_differentiable_on k f S \<longleftrightarrow> (\<forall>x\<in>S. k_times_differentiable_at k f x)"

(* Syntactic sugar for set-based version *)
abbreviation times_differentiable_on
  :: "(real \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real set \<Rightarrow> bool"
  ("(_ _-times'_differentiable'_on _)" [100,100,100] 100)
where
  "f k-times_differentiable_on S \<equiv> k_times_differentiable_on k f S"

lemma k_times_differentiable_onD:
  "f k-times_differentiable_on S \<Longrightarrow> x \<in> S 
  \<Longrightarrow> f k-times_differentiable_at x"
  by (simp add: k_times_differentiable_on_def)

lemma k_times_differentiable_onI:
  "(\<And>x. x \<in> S \<Longrightarrow> f k-times_differentiable_at x) \<Longrightarrow>
    f k-times_differentiable_on S"
  by (simp add: k_times_differentiable_on_def)

lemma times_differentiable_on_iff_le:
  "f k-times_differentiable_on S
  \<longleftrightarrow> (\<forall>m\<le>k. f m-times_differentiable_on S)"
  unfolding k_times_differentiable_on_def
  using k_times_differentiable_at_mono
  by blast

lemma times_differentiable_on_Suc:
  "f (Suc k)-times_differentiable_on S
  \<Longrightarrow> f k-times_differentiable_on S"
  unfolding k_times_differentiable_on_def
  using k_times_differentiable_at_SucD(1) 
  by blast

lemma times_differentiable_on_subset: 
  "X \<subseteq> Y \<Longrightarrow> f k-times_differentiable_on Y
  \<Longrightarrow> f k-times_differentiable_on X"
  by (auto simp: k_times_differentiable_on_def)

lemma times_differentiable_on_transfer:
  "open S \<Longrightarrow> f k-times_differentiable_on S
  \<Longrightarrow> \<forall>x\<in>S. f x = g x
  \<Longrightarrow> g k-times_differentiable_on S
    \<and> (\<forall>x\<in>S. \<forall>m<k. ((deriv ^^ m) g has_derivative (*) ((deriv ^^ Suc m) f x)) (at x))"
proof (induct k arbitrary: S)
  case (Suc k)
  show ?case
  proof(cases "k=0")
    case True
    hence "g (Suc k)-times_differentiable_on S"
      using Suc
      by (clarsimp simp: k_times_differentiable_on_def)
        (metis at_within_open deriv_transfer(1) has_derivative_transform)
    moreover have "\<forall>x\<in>S. \<forall>m<Suc k. ((deriv ^^ m) g 
      has_derivative (*) ((deriv ^^ Suc m) f x)) (at x)"
      using Suc.prems True calculation k_times_differentiable_on_def
      by (simp add: has_derivative_transfer_on_open)
    ultimately show ?thesis
      by simp
  next
    case False
    show ?thesis
    proof
      obtain n where "k = Suc n"
        using False not0_implies_Suc by presburger
      note IH1 = Suc.hyps[THEN conjunct2, OF \<open>open S\<close> _ Suc.prems(3),
              unfolded k_times_differentiable_on_def, rule_format]
      have obs: "\<And>x. x \<in> S \<Longrightarrow> (deriv ^^ k) g x = (deriv ^^ k) f x"
        using \<open>k = Suc n\<close>
        by (simp, intro deriv_eq IH1[simplified]; 
            clarsimp simp del: k_times_differentiable_at.simps)
          (metis Suc.prems(2) k_times_differentiable_on_def times_differentiable_on_Suc)
      have at_within_S: "at x within S = at x" if "x \<in> S" for x
        using at_within_open_subset[OF \<open>x \<in> S\<close> \<open>open S\<close>]
        by blast
      show first: "\<forall>x\<in>S.\<forall>m<Suc k. ((deriv^^m) g has_derivative (*) ((deriv^^Suc m) f x)) (at x)"
        using False
      proof(safe)
        fix z and m
        assume "0 < k" and "z \<in> S" and "m < Suc k"
        show "((deriv ^^ m) g has_derivative (*) ((deriv ^^ Suc m) f z)) (at z)"
        proof(cases "m = k")
          case True
          note transfer = has_derivative_transfer_on_open[OF \<open>open S\<close>, where f = "(deriv ^^ m) f"]
          show ?thesis 
            using \<open>z \<in> S\<close> True less_Suc_eq obs
            by - ((rule transfer; clarsimp simp del: funpow.simps), 
                metis Suc.prems(2) k_times_differentiable_at_SucD(3) k_times_differentiable_onD)
        next
          case False
          note f_k_diff = k_times_differentiable_at_SucD[OF 
              Suc.prems(2)[unfolded k_times_differentiable_on_def, rule_format]]
          have "m < k"
            using False \<open>m < Suc k\<close> less_Suc_eq by blast
          thus ?thesis
            using \<open>z \<in> S\<close>
            by - (rule IH1, auto intro!: f_k_diff)
        qed
      qed
      show "g (Suc k)-times_differentiable_on S"
      proof(rule k_times_differentiable_onI)
        fix x
        assume "x \<in> S"
        then obtain \<epsilon> where "\<epsilon> > 0" and "ball x \<epsilon> \<subseteq> S"
          and "\<forall>y. y \<in> ball x \<epsilon> \<longrightarrow> f y = g y"
          using \<open>open S\<close>
          by (meson Suc.prems(3) open_contains_ball subset_eq)
        hence fact1: "\<exists>\<epsilon>>0. \<forall>y. \<bar>y - x\<bar> < \<epsilon> \<longrightarrow> g k-times_differentiable_at y"
          using Suc(1)[OF open_ball] Suc(3)[THEN times_differentiable_on_Suc]
          times_differentiable_on_subset[OF \<open>ball x \<epsilon> \<subseteq> S\<close>]
          by (metis abs_minus_commute dist_real_def 
              k_times_differentiable_on_def mem_ball)
        moreover have "((deriv ^^ k) g has_derivative (*) ((deriv ^^ Suc k) f x)) (at x)"
          using first \<open>x \<in> S\<close> by blast
        ultimately show "g (Suc k)-times_differentiable_at x"
          using fact1
          by (clarsimp simp: k_times_differentiable_on_def Nth_deriv_eq_compow_deriv,
              simp add: DERIV_imp_deriv has_field_derivative_def)
      qed
    qed
  qed
qed (simp add: k_times_differentiable_on_def)


lemma k_times_differentiable_on_imp_continuous_on:
  assumes KD: "f (Suc k)-times_differentiable_on S"
      and JL: "j \<le> k"  
  shows   "continuous_on S (Nth_derivative j f)"
  using JL KD
  by (meson continuous_at_imp_continuous_on 
      k_times_differentiable_at_imp_isCont_Nth
      k_times_differentiable_on_def)


subsection \<open>Linearity of Higher Differentiability\<close>

lemma Nth_derivative_commute_and_shift:
  fixes f :: "real \<Rightarrow> real" and a :: real and m k :: nat
  assumes "k \<le> m"
      and "f m-times_differentiable_at a"
  shows
    "(Nth_derivative k (Nth_derivative (m - k) f) = Nth_derivative (m - k) (Nth_derivative k f)) \<and>
     (Nth_derivative k (Nth_derivative (m - k) f) = Nth_derivative m f) \<and>
     (Nth_derivative k f) (m - k)-times_differentiable_at  a" 
  using assms by(induct k arbitrary: m, simp, metis Nth_derivative.simps(2)
  Suc_diff_Suc Suc_leD Suc_le_lessD deriv_commutes_Nth_deriv k_times_differentiable_at_derivative)

corollary Nth_derivative_commute_and_shift_dualE:
  fixes f :: "real \<Rightarrow> real" and a :: real and m k :: nat
  assumes "k \<le> m"
      and "f m-times_differentiable_at a"
  shows "(Nth_derivative (m - k) f) k-times_differentiable_at a"
  by (metis Nth_derivative_commute_and_shift assms diff_diff_cancel diff_le_self)

corollary Nth_derivative_commute_and_shiftE:
  fixes f :: "real \<Rightarrow> real" and a :: real and m k :: nat
  assumes "k \<le> m"
      and "f m-times_differentiable_at  a"
  shows "(Nth_derivative k f) (m - k)-times_differentiable_at a"
  using Nth_derivative_commute_and_shift assms by simp

lemma k_times_differentiable_at_const:
  "Nth_derivative (Suc m) (\<lambda>_. c) x = 0 \<and> k_times_differentiable_at (Suc m) (\<lambda>_. c) x"
proof (induct m arbitrary: x)
  case 0
  show ?case
  proof -
    have "k_times_differentiable_at 1 (\<lambda>r. c) x"
      by (metis has_derivative_const has_real_derivative one_time_differentiable_at_iff)
    then show ?thesis
      by simp
  qed   
next
  fix m :: nat
  fix x :: real
  assume IH: "(\<And>x. Nth_derivative (Suc m) (\<lambda>_. c) x = 0 \<and> k_times_differentiable_at (Suc m) (\<lambda>_. c) x)"

  then have deriv_zero: "Nth_derivative (Suc (Suc m)) (\<lambda>_. c) x = 0"
    using deriv_commutes_Nth_deriv by auto

  moreover have diff_suc:
    "k_times_differentiable_at (Suc (Suc m)) (\<lambda>_. c) x"
  proof -
    have clause1:
      "\<exists>\<epsilon>>0. \<forall>y. \<bar>y - x\<bar> < \<epsilon> \<longrightarrow> k_times_differentiable_at (Suc m) (\<lambda>_. c) y"     
      using IH by (intro exI[of _ 1], fastforce)

    have clause2:
      "(Nth_derivative (Suc m) (\<lambda>_. c)
          has_derivative
           (\<lambda>h. Nth_derivative (Suc (Suc m)) (\<lambda>_. c) x * h)) (at x)"
    proof -
      have "\<exists>r. (\<lambda>r. Nth_derivative (Suc (Suc m)) (\<lambda>r. c) x) 
          = (*) (Nth_derivative (Suc (Suc m)) (\<lambda>r. c) x) 
        \<and> (\<lambda>ra. r) = Nth_derivative (Suc m) (\<lambda>r. c)"
      proof -
        have "\<exists>r. (\<forall>ra. r = Nth_derivative (Suc m) (\<lambda>r. c) ra) 
          \<and> (\<forall>r. Nth_derivative (Suc (Suc m)) (\<lambda>r. c) x 
            = Nth_derivative (Suc (Suc m)) (\<lambda>r. c) x * r)"
          using IH deriv_zero by fastforce
        then show ?thesis
          by blast
      qed
      then show ?thesis
        by (metis (no_types) deriv_zero has_derivative_const)
    qed
    show ?thesis
      unfolding k_times_differentiable_at.simps
      using clause1 clause2 by auto
  qed
  ultimately show "Nth_derivative (Suc (Suc m)) (\<lambda>_. c) x = 0 
    \<and> k_times_differentiable_at (Suc (Suc m)) (\<lambda>_. c) x"
    unfolding k_times_differentiable_at.simps by simp
qed

corollary Nth_derivative_const_eq:
  fixes c :: real and k :: nat and x :: real
  assumes "k > 0"
  shows   "Nth_derivative k (\<lambda>_. c) x = 0"
  by (metis Suc_le_D Suc_le_eq assms k_times_differentiable_at_const)

corollary Nth_derivative_const_cases:
  "Nth_derivative k (\<lambda>t::real. c) x = (if k = 0 then c else 0)"
  using Nth_derivative_const_eq
  by force 

corollary k_times_differentiable_at_constE:
  "k_times_differentiable_at m (\<lambda>_. c) x"
  using k_times_differentiable_at_SucD k_times_differentiable_at_const 
  by blast

lemma k_times_differentiable_at_id:
  fixes x :: real and m :: nat
  shows
    "Nth_derivative (Suc m) (\<lambda>t. t) x = (if m = 0 then 1 else 0) \<and>
     k_times_differentiable_at (Suc m) (\<lambda>t. t) x"
proof (induct m arbitrary: x)
  show "\<And>x. Nth_derivative (Suc 0) (\<lambda>t. t) x = (if 0 = 0 then 1 else 0) 
    \<and> k_times_differentiable_at (Suc 0) (\<lambda>t. t) x"
    by (metis One_nat_def deriv_ident first_derivative_alt_def 
        has_derivative_ident has_real_derivative one_time_differentiable_at_iff)
next
  fix m :: nat
  fix x :: real

  assume IH: "(\<And>x. Nth_derivative (Suc m) (\<lambda>t. t) x = (if m = 0 then 1 else 0) 
    \<and> k_times_differentiable_at (Suc m) (\<lambda>t. t) x)"

  have Dm1: "Nth_derivative (Suc (Suc m)) (\<lambda>t. t) x = 0"
  proof - 
    have "Nth_derivative (Suc (Suc m)) (\<lambda>t. t) x  = (Nth_derivative (Suc m) (deriv (\<lambda>t. t))) x"
      using deriv_commutes_Nth_deriv by auto
    also have "... = (Nth_derivative (Suc m) (\<lambda>_.1)) x"
      by simp
    also have "... = 0"
      using k_times_differentiable_at_const by auto
    finally show ?thesis.
  qed

  have clause1:
    "\<exists>\<epsilon>>0. \<forall>y. \<bar>y - x\<bar> < \<epsilon> \<longrightarrow> k_times_differentiable_at (Suc m) (\<lambda>t. t) y"
    by (intro exI[of _ 1] conjI, simp_all, 
        metis Nth_derivative.simps(2) IH k_times_differentiable_at.simps(2))

  have clause2:
    "(Nth_derivative (Suc m) (\<lambda>t. t)
        has_derivative (\<lambda>h. Nth_derivative (Suc (Suc m)) (\<lambda>t. t) x * h)) (at x)"
    using IH[of x] Dm1 by (cases m, simp_all, metis IH Nth_derivative.simps(2) 
        UNIV_I has_derivative_transform            k_times_differentiable_at.simps(2) 
        k_times_differentiable_at_const lambda_zero)

  show "Nth_derivative (Suc (Suc m)) (\<lambda>t. t) x = (if Suc m = 0 then 1 else 0) 
    \<and> k_times_differentiable_at (Suc (Suc m)) (\<lambda>t. t) x"
    using Dm1 clause1 clause2 by auto
qed


corollary Nth_derivative_id_eq':
  fixes x :: real and m :: nat
  shows "Nth_derivative (Suc m) (\<lambda>t. t) x = (if m = 0 then 1 else 0)"
  using k_times_differentiable_at_id by simp

lemma Nth_derivative_id_cases:
  "Nth_derivative k (\<lambda>t::real. t) x =
     (if k = 0 then x else if k = 1 then 1 else 0)"
  by (metis Nth_derivative.simps(1) Nth_derivative_id_eq' One_nat_def not0_implies_Suc)

corollary Nth_derivative_id_ge2_at:
  assumes "k \<ge> 2"
  shows   "Nth_derivative k (\<lambda>t::real. t) x = 0"
  using Nth_derivative_id_cases assms by fastforce

corollary Nth_derivative_id_1_eq:
  fixes x :: real
  shows "Nth_derivative (Suc 0) (\<lambda>t. t) x = (1 :: real)"
  using Nth_derivative_id_eq' by simp

corollary Nth_derivative_id_eq:
  fixes x :: real and m :: nat
  assumes "m > 0"
  shows "Nth_derivative (Suc m) (\<lambda>t. t) x = (0 :: real)"
  using Nth_derivative_id_eq' assms by simp

corollary k_times_differentiable_at_idE:
  fixes x :: real and m :: nat
  shows "(\<lambda>t. t) k-times_differentiable_at x"
  using k_times_differentiable_at_SucD k_times_differentiable_at_id by blast

\<comment> \<open>The lemma below, \texttt{kth\_deriv\_cmult}, generalises the
    first‑derivative fact \texttt{deriv\_cmult}:
    \begin{itemize}
      \item For $k=1$, it \emph{is} @{thm deriv_cmult}.
      \item For $k=0$, it reduces to the tautology $(c\,f)(x) = c\,f(x)$.
      \item For every $k\ge2$, it yields the higher‑order identity
        \[
          (c\,f)^{(k)}(x) = c\,f^{(k)}(x),
        \]
        while preserving $k$‑times differentiability at the point~$x$.
    \end{itemize}
\<close>

lemma kth_deriv_cmult:
  fixes f :: "real \<Rightarrow> real"  and  c :: real  and  k :: nat  and  x :: real
  assumes "f k-times_differentiable_at x"
  shows   "(\<lambda>z. c * f z) k-times_differentiable_at  x \<and> 
          Nth_derivative k (\<lambda>z. c * f z) x = c * Nth_derivative k f x"
  using assms
proof (induct k arbitrary: x)
  case 0
  show ?case by simp
next
  fix k :: nat
  fix x :: real
  assume IH: "(\<And>x. k_times_differentiable_at k f x 
    \<Longrightarrow> k_times_differentiable_at k (\<lambda>z. c * f z) x 
      \<and> Nth_derivative k (\<lambda>z. c * f z) x = c * Nth_derivative k f x)"
  show "k_times_differentiable_at (Suc k) f x 
    \<Longrightarrow> k_times_differentiable_at (Suc k) (\<lambda>z. c * f z) x 
      \<and> Nth_derivative (Suc k) (\<lambda>z. c * f z) x = c * Nth_derivative (Suc k) f x"
  proof -
    assume k1: "k_times_differentiable_at (Suc k) f x"
    then obtain \<epsilon> where \<epsilon>_pos: "\<epsilon> > 0"
                 and neigh: "\<forall>y. \<bar>y - x\<bar> < \<epsilon> \<longrightarrow> k_times_differentiable_at k f y"
                 and deriv_f: "(Nth_derivative k f
                                 has_field_derivative Nth_derivative (Suc k) f x) (at x)"
      using k_times_differentiable_at_SucE by blast

    have mult_rule:
      "((\<lambda>y. c * Nth_derivative k f y)
              has_field_derivative (c * Nth_derivative (Suc k) f x)) (at x)"
          using DERIV_chain' DERIV_cmult_Id deriv_f by blast

    then have deriv_trans:"(Nth_derivative k (\<lambda>y. c * f y) has_derivative 
            (\<lambda>h. (c * Nth_derivative (Suc k) f x) * h)) (at x)"
      unfolding has_field_derivative_def
      by(subst has_derivative_transfer_on_ball[where \<epsilon>=\<epsilon> and f="(\<lambda>y. c * Nth_derivative k f y)"],
         auto simp: \<epsilon>_pos IH dist_real_def neigh)
    then have "(Nth_derivative k (\<lambda>y. c * f y)
           has_field_derivative  (c * Nth_derivative (Suc k) f x)) (at x)"
      using has_field_derivative_def by blast    
    then have g2: "Nth_derivative (Suc k) (\<lambda>z. c * f z) x = c * Nth_derivative (Suc k) f x"
      by (simp add: DERIV_imp_deriv)

    have "k_times_differentiable_at (Suc k) (\<lambda>z. c * f z) x"
      using IH \<epsilon>_pos deriv_trans g2 neigh by auto    
    then show ?thesis
      using g2 by blast
  qed
qed

corollary Nth_derivative_cmult_eq:
  fixes f :: "real \<Rightarrow> real" and c :: real and k :: nat and x :: real
  assumes "f k-times_differentiable_at x"
      and "Nth_derivative k f = f'"
  shows   "Nth_derivative k (\<lambda>y. c * f y) x = c * f' x"
  by (simp add: assms kth_deriv_cmult)

corollary kth_deriv_cmultE:
  fixes f :: "real \<Rightarrow> real"  and  c :: real  and  k :: nat  and  x :: real
  assumes "f k-times_differentiable_at x"
  shows   "k_times_differentiable_at k (\<lambda>z. c * f z) x"
  using assms by(subst kth_deriv_cmult, simp_all)

corollary kth_derivative_uminus:
  assumes "f k-times_differentiable_at x"
  shows   "Nth_derivative k (\<lambda>t. - f t) x = - Nth_derivative k f x"
proof- 
  have "k_times_differentiable_at k (\<lambda>z. (-1) * f z) x \<and> 
          Nth_derivative k (\<lambda>z. (-1) * f z) x = (-1) * Nth_derivative k f x"
    using assms by(rule kth_deriv_cmult)
  then show ?thesis
    by auto
qed

corollary Nth_derivative_uminus_eq:
  fixes f :: "real \<Rightarrow> real" and k :: nat and x :: real
  assumes "f k-times_differentiable_at x"
      and "Nth_derivative k f = f'"
  shows   "Nth_derivative k (\<lambda>t. - f t) x = - f' x"
  by (simp add: assms kth_derivative_uminus)

corollary kth_derivative_uminusE:
  assumes "f k-times_differentiable_at x"
  shows   "(\<lambda>t. - f t) k-times_differentiable_at x"
proof - 
  have "k_times_differentiable_at k (\<lambda>t. -1 * f t) x"
    using assms by(subst kth_deriv_cmult, simp_all)
  then show ?thesis
    by simp
qed

\<comment> \<open>The lemma below, \texttt{kth\_deriv\_add}, generalises the
    first‑derivative fact \texttt{deriv\_add}:
    \begin{itemize}
      \item For $k=1$, it \emph{is} @{thm deriv_add}.
      \item For $k=0$, it reduces to the tautology $(f+g)(x) = f(x) + g(x)$.
      \item For every $k\ge2$, it yields the higher‑order identity
        \[ (f+g)^{(k)}(x) = f^{(k)}(x) + g^{(k)}(x), \]
        while preserving $k$‑times differentiability at the point~$x$.
    \end{itemize}\<close>
    
lemma kth_deriv_add:
  fixes f g :: "real \<Rightarrow> real"  and  k :: nat  and  x :: real
  assumes "f k-times_differentiable_at x"
      and "g k-times_differentiable_at x"
  shows   "(\<lambda>y. f y + g y) k-times_differentiable_at x \<and>
             Nth_derivative k (\<lambda>y. f y + g y) x =
             Nth_derivative k f x + Nth_derivative k g x"
  using assms
proof (induct k arbitrary: x)
  case 0
  show ?case by simp
next
  fix k :: nat
  fix x :: real
  assume IH: "(\<And>x. k_times_differentiable_at k f x 
    \<Longrightarrow> k_times_differentiable_at k g x 
    \<Longrightarrow> k_times_differentiable_at k (\<lambda>y. f y + g y) x 
      \<and> Nth_derivative k (\<lambda>y. f y + g y) x = Nth_derivative k f x + Nth_derivative k g x)"
  show "k_times_differentiable_at (Suc k) f x 
    \<Longrightarrow> k_times_differentiable_at (Suc k) g x 
    \<Longrightarrow> k_times_differentiable_at (Suc k) (\<lambda>y. f y + g y) x 
      \<and> Nth_derivative (Suc k) (\<lambda>y. f y + g y) x 
        = Nth_derivative (Suc k) f x + Nth_derivative (Suc k) g x"
  proof -
    assume f_ksuc_diff: "k_times_differentiable_at (Suc k) f x"
    then obtain \<epsilon>f where \<epsilon>f: "\<epsilon>f > 0"
              and neigh_f:  "\<forall> y. \<bar>y - x\<bar> < \<epsilon>f \<longrightarrow> k_times_differentiable_at k f y"
              and diff_f:
                "(Nth_derivative k f
                   has_field_derivative Nth_derivative (Suc k) f x) (at x)"
      using k_times_differentiable_at_SucE by blast
    assume g_ksuc_diff: "k_times_differentiable_at (Suc k) g x"      
    then obtain \<epsilon>g where \<epsilon>g: "\<epsilon>g > 0"
                and neigh_g:  "\<forall> y. \<bar>y - x\<bar> < \<epsilon>g \<longrightarrow> k_times_differentiable_at k g y"
                and diff_g:
                  "(Nth_derivative k g
                     has_field_derivative Nth_derivative (Suc k) g x) (at x)"
        using k_times_differentiable_at_SucE by blast

    define \<epsilon> where "\<epsilon> = min \<epsilon>f \<epsilon>g"
    have \<epsilon>_pos: "\<epsilon> > 0" by (simp add: \<epsilon>_def \<epsilon>f \<epsilon>g)
  
    have neigh_sum:
      "\<And>y. \<bar>y - x\<bar> < \<epsilon> \<Longrightarrow> k_times_differentiable_at k (\<lambda>z. f z + g z) y"
      by (simp add: IH \<epsilon>_def neigh_f neigh_g)
  
    have deriv_k_sum:
      "\<And>y. \<bar>y - x\<bar> < \<epsilon> \<Longrightarrow>
          Nth_derivative k (\<lambda>z. f z + g z) y =
          Nth_derivative k f y + Nth_derivative k g y"
      using IH neigh_f neigh_g \<epsilon>_def 
      by (auto simp: less_le_trans)
  
    have add_rule:
      "((\<lambda>y. Nth_derivative k f y + Nth_derivative k g y)
          has_field_derivative
           (Nth_derivative (Suc k) f x + Nth_derivative (Suc k) g x)) (at x)"
      using diff_f diff_g DERIV_add by blast 
  
    then have diff_sum:
    "(Nth_derivative k (\<lambda>y. f y + g y)
        has_derivative
          (\<lambda>h. (Nth_derivative (Suc k) f x +
                Nth_derivative (Suc k) g x) * h)) (at x)"
      by (subst has_derivative_transfer_on_ball[where \<epsilon>=\<epsilon> 
            and f="(\<lambda>y. Nth_derivative k f y + Nth_derivative k g y)"],
          auto simp: \<epsilon>_pos deriv_k_sum dist_real_def has_field_derivative_def)

    have val_sum:
      "Nth_derivative (Suc k) (\<lambda>y. f y + g y) x =
         Nth_derivative (Suc k) f x + Nth_derivative (Suc k) g x"
      using diff_sum has_derivative_imp by force

    have sum_Suc:
      "k_times_differentiable_at (Suc k) (\<lambda>y. f y + g y) x"
      unfolding k_times_differentiable_at.simps
      using \<epsilon>_pos diff_sum neigh_sum val_sum by auto                             
    with val_sum show ?thesis
      by simp
  qed
qed

corollary Nth_derivative_add_eq:
  fixes f g :: "real \<Rightarrow> real"  and  k :: nat  and  x :: real
  assumes "f k-times_differentiable_at x"
      and "g k-times_differentiable_at x"
  assumes "Nth_derivative k f = f'"
  assumes "Nth_derivative k g = g'"   
  shows   "Nth_derivative k (\<lambda>y. f y + g y) x  =  f'(x) + g'(x)"
  by (simp add: assms kth_deriv_add)

corollary kth_deriv_addE:
  fixes f g :: "real \<Rightarrow> real"  and  k :: nat  and  x :: real
  assumes "f k-times_differentiable_at x"
      and "g k-times_differentiable_at x"
    shows "(\<lambda>y. f y + g y) k-times_differentiable_at x"
  using assms 
  by (subst kth_deriv_add, simp_all)

lemma kth_deriv_sub:
  fixes f g :: "real \<Rightarrow> real"  and k :: nat  and x :: real
  assumes "f k-times_differentiable_at x"
      and "g k-times_differentiable_at x"
  shows   "Nth_derivative k (\<lambda>y. f y - g y) x =
           Nth_derivative k f x - Nth_derivative k g x"
proof -
  have "Nth_derivative k (\<lambda>y. f y - g y) x =
        Nth_derivative k (\<lambda>y. f y + (-1) * g y) x"
    by simp
  also have "... = Nth_derivative k f x  + Nth_derivative k (\<lambda>y. (-1) * g y) x"
    using assms kth_deriv_add kth_deriv_cmult by presburger  
  also have "... = Nth_derivative k f x  - Nth_derivative k g x"
    by (metis add_uminus_conv_diff assms(2) kth_deriv_cmult mult_minus1)
  finally show ?thesis.
qed

corollary Nth_derivative_sub_eq:
  fixes f g :: "real \<Rightarrow> real" and k :: nat and x :: real
  assumes "f k-times_differentiable_at x"
      and "g k-times_differentiable_at x"
      and "Nth_derivative k f = f'"
      and "Nth_derivative k g = g'"
  shows   "Nth_derivative k (\<lambda>t. f t - g t) x = f' x - g' x"
  by (simp add: assms kth_deriv_sub)

corollary kth_deriv_subE:
  fixes f g :: "real \<Rightarrow> real"  and  k :: nat  and  x :: real
  assumes "f k-times_differentiable_at x"
      and "g k-times_differentiable_at x"
    shows "(\<lambda>y. f y - g y) k-times_differentiable_at x"
proof -
  from assms(1) have "k_times_differentiable_at k (\<lambda>y. f y + (\<lambda>z. -1* g z) y) x"
    by(rule kth_deriv_addE, simp_all, simp add: assms(2) kth_derivative_uminusE)
  then show ?thesis
    by auto
qed

\<comment> \<open>Leibniz formula for the \(n\)-th derivative of a product:
    \[
      (fg)^{(n)}(x) \;=\; \sum_{k=0}^{n} \binom{n}{k}\, f^{(k)}(x)\, g^{(n-k)}(x)
    \]
\<close>
lemma kth_deriv_mult:
  fixes f g :: "real \<Rightarrow> real"  and k :: nat and x :: real
  assumes fCk: "f k-times_differentiable_at x"
      and gCk: "g k-times_differentiable_at x"
  shows   "(\<lambda>y. f y * g y) k-times_differentiable_at x \<and>
           Nth_derivative k (\<lambda>y. f y * g y) x =
           (\<Sum>j\<le>k. of_nat (k choose j) * Nth_derivative j f x * Nth_derivative (k - j) g x)"
  using assms
proof (induct k arbitrary: x)
  case 0
  show ?case by (simp add: fCk gCk)
next
  fix k :: nat
  fix x :: real

  let ?\<beta>  = "\<lambda>y. (\<Sum>j\<le>k. of_nat (k choose j) *
                        Nth_derivative j f y *
                        Nth_derivative (k - j) g y)"

  assume IH: "(\<And>x. k_times_differentiable_at k f x \<Longrightarrow>
                k_times_differentiable_at k g x \<Longrightarrow>
                k_times_differentiable_at k (\<lambda>y. f y * g y) x \<and> 
  Nth_derivative k (\<lambda>y. f y * g y) x = 
  (\<Sum>j\<le>k. real (k choose j) * Nth_derivative j f x * Nth_derivative (k - j) g x))"
  
  show "k_times_differentiable_at (Suc k) f x 
    \<Longrightarrow> k_times_differentiable_at (Suc k) g x 
    \<Longrightarrow> k_times_differentiable_at (Suc k) (\<lambda>y. f y * g y) x 
      \<and> Nth_derivative (Suc k) (\<lambda>y. f y * g y) x 
    = (\<Sum>j\<le>Suc k. real (Suc k choose j) * Nth_derivative j f x * Nth_derivative (Suc k - j) g x)"
  proof - 
    assume f_ksuc_diff: "k_times_differentiable_at (Suc k) f x"
    assume g_ksuc_diff: "k_times_differentiable_at (Suc k) g x"

    obtain \<epsilon>f where \<epsilon>f: "\<epsilon>f > 0"
        and neigh_f:  "\<And>y. \<bar>y - x\<bar> < \<epsilon>f \<Longrightarrow> k_times_differentiable_at k f y"
        and diff_f:   "(Nth_derivative k f has_field_derivative Nth_derivative (Suc k) f x) (at x)"
      using f_ksuc_diff k_times_differentiable_at_SucE by blast
  
    obtain \<epsilon>g where \<epsilon>g: "\<epsilon>g > 0"
      and neigh_g:  "\<And>y. \<bar>y - x\<bar> < \<epsilon>g \<Longrightarrow> k_times_differentiable_at k g y"
        and diff_g:   "(Nth_derivative k g has_field_derivative Nth_derivative (Suc k) g x) (at x)"
      using g_ksuc_diff k_times_differentiable_at_SucE by blast

    define \<epsilon> where "\<epsilon> = min \<epsilon>f \<epsilon>g"
    have \<epsilon>_pos: "\<epsilon> > 0" by (simp add: \<epsilon>_def \<epsilon>f \<epsilon>g)
  
    have neigh_prod:
      "\<And>y. \<bar>y - x\<bar> < \<epsilon> \<Longrightarrow> k_times_differentiable_at k (\<lambda>z. f z * g z) y"
      by (simp add: IH \<epsilon>_def neigh_f neigh_g)

    have deriv_k_prod:
      "\<And>y. \<bar>y - x\<bar> < \<epsilon> \<Longrightarrow>
        Nth_derivative k (\<lambda>z. f z * g z) y =
          (\<Sum>j\<le>k. of_nat (k choose j) * Nth_derivative j f y * Nth_derivative (k - j) g y)"
      by (simp add: IH \<epsilon>_def neigh_f neigh_g)

    have beta_deriv:
      "((\<lambda>y. ?\<beta> y) has_field_derivative
         (\<Sum>j\<le>k. of_nat (k choose j) *
                 (Nth_derivative j f x * Nth_derivative (Suc (k - j)) g x +
                  Nth_derivative (Suc j) f x * Nth_derivative (k - j) g x))) (at x)"
    proof -       
      have f1: "((\<lambda>x. of_nat (k choose j) *
                 (Nth_derivative j f x * Nth_derivative (k - j) g x))
             has_field_derivative
               of_nat (k choose j) *
                 (Nth_derivative j f x * Nth_derivative (Suc (k - j)) g x +
                  Nth_derivative (Suc j) f x * Nth_derivative (k - j) g x)) (at x)"
         if "j \<le> k" for j
      proof -
        have "k_times_differentiable_at (Suc (k - j)) g x \<and> k_times_differentiable_at (Suc j) f x"
          by (metis (no_types) f_ksuc_diff g_ksuc_diff k_times_differentiable_at_mono 
              le_add_same_cancel2 not_less_eq_eq that zero_le
              ordered_cancel_comm_monoid_diff_class.add_diff_inverse)
        then have "((\<lambda>r. Nth_derivative j f r * Nth_derivative (k - j) g r) has_real_derivative 
          Nth_derivative j f x * Nth_derivative (Suc (k - j)) g x 
          + Nth_derivative (Suc j) f x * Nth_derivative (k - j) g x) (at x)"
          using DERIV_mult' k_times_differentiable_at_SucE by blast
        then show ?thesis
          using DERIV_chain' DERIV_cmult_Id by blast
      qed       
      then have f2:
      "j \<le> k \<Longrightarrow>
       ((\<lambda>x. of_nat (k choose j) *
              Nth_derivative j f x * Nth_derivative (k - j) g x)
          has_derivative
            (\<lambda>h. (of_nat (k choose j) *
                  (Nth_derivative j f x * Nth_derivative (Suc (k - j)) g x +
                   Nth_derivative (Suc j) f x * Nth_derivative (k - j) g x)) * h))
          (at x)"
      for j
      unfolding has_field_derivative_def
      by (meson UNIV_I ab_semigroup_mult_class.mult_ac(1) has_derivative_transform) 

      then have beta_deriv:
      "((\<lambda>y. ?\<beta> y) has_derivative
          (\<lambda>h. \<Sum>j\<le>k. (of_nat (k choose j) *
                     (Nth_derivative j f x * Nth_derivative (Suc (k - j)) g x +
                      Nth_derivative (Suc j) f x * Nth_derivative (k - j) g x)) * h))
         (at x)"
        by(rule has_derivative_sum, simp)
      then show ?thesis
        by (metis (no_types, lifting) DERIV_imp_deriv has_derivative_imp 
            has_real_derivative mult_cancel_left2 sum.cong)
    qed

    then have diff_prod:
    "(Nth_derivative k (\<lambda>y. f y * g y)
        has_derivative
          (\<lambda>h. (\<Sum>j\<le>k. of_nat (k choose j) *
                   (Nth_derivative j f x * Nth_derivative (Suc (k - j)) g x +
                    Nth_derivative (Suc j) f x * Nth_derivative (k - j) g x)) * h))
      (at x)"
      by(subst has_derivative_transfer_on_ball[where \<epsilon> = \<epsilon> and f = "(\<lambda>y. ?\<beta> y)"],      
         auto simp: \<epsilon>_pos deriv_k_prod dist_real_def has_field_derivative_def)

    have comb_id:
      "(\<Sum>j\<le>k. of_nat (k choose j) *
                (Nth_derivative j f x * Nth_derivative (Suc (k - j)) g x +
                 Nth_derivative (Suc j) f x * Nth_derivative (k - j) g x))
       = (\<Sum>j\<le>Suc k. of_nat (Suc k choose j) *
                      Nth_derivative j f x * Nth_derivative (Suc k - j) g x)"
      by(rule binomial_convolution_sum)    
    then have
      "Nth_derivative (Suc k) (\<lambda>y. f y * g y) x =
         (\<Sum>j\<le>Suc k. of_nat (Suc k choose j) *
                      Nth_derivative j f x * Nth_derivative (Suc k - j) g x)"
      using diff_prod has_derivative_imp by force        
    then show ?thesis
      using \<epsilon>_pos comb_id diff_prod neigh_prod  by auto
  qed
qed

corollary Leibniz_prod_eq:
  fixes f g :: "real \<Rightarrow> real" and F G :: "nat \<Rightarrow> real \<Rightarrow> real"
  fixes k :: nat and x :: real
  assumes fCk: "f k-times_differentiable_at x"
      and gCk: "g k-times_differentiable_at x"
      and Ffam: "\<And>j. j \<le> k \<Longrightarrow> Nth_derivative j f = F j"
      and Gfam: "\<And>j. j \<le> k \<Longrightarrow> Nth_derivative j g = G j"
  shows "Nth_derivative k (\<lambda>y. f y * g y) x
         = (\<Sum> j\<le>k. of_nat (k choose j) * F j x * G (k - j) x)"
  by (subst kth_deriv_mult[OF fCk gCk], rule sum.cong[OF refl], simp_all add: Ffam Gfam)

corollary kth_deriv_multE:
  fixes f g :: "real \<Rightarrow> real"  and k :: nat and x :: real
  assumes fCk: "f k-times_differentiable_at x"
      and gCk: "g k-times_differentiable_at x"
    shows      "(\<lambda>y. f y * g y) k-times_differentiable_at x"
  using assms by(subst kth_deriv_mult, simp_all)

lemma kth_deriv_sum_upto:
  fixes F :: "nat \<Rightarrow> real \<Rightarrow> real"
    and k :: nat
    and x :: real
    and n :: nat
  assumes diff: "\<And>i. i \<le> n \<Longrightarrow> (F i) k-times_differentiable_at x"
  shows   "(\<lambda>y. \<Sum>i\<le>n. F i y) k-times_differentiable_at x \<and>
               Nth_derivative k (\<lambda>y. \<Sum>i\<le>n. F i y) x =
             (\<Sum>i\<le>n. Nth_derivative k (F i) x)"
  using assms
proof (induct n arbitrary: x)
  case 0
  thus ?case
    by (simp add: diff)
next
  fix n :: nat
  fix x :: real
  assume IH: "(\<And>x. (\<And>i. i \<le> n \<Longrightarrow> k_times_differentiable_at k (F i) x) 
    \<Longrightarrow> k_times_differentiable_at k (\<lambda>y. \<Sum>i\<le>n. F i y) x 
    \<and> Nth_derivative k (\<lambda>y. \<Sum>i\<le>n. F i y) x = (\<Sum>i\<le>n. Nth_derivative k (F i) x))"
  show "(\<And>j. j \<le> Suc n \<Longrightarrow> k_times_differentiable_at k (F j) x) 
    \<Longrightarrow> k_times_differentiable_at k (\<lambda>y. \<Sum>i\<le>Suc n. F i y) x 
    \<and> Nth_derivative k (\<lambda>y. \<Sum>i\<le>Suc n. F i y) x = (\<Sum>i\<le>Suc n. Nth_derivative k (F i) x)"
  proof -
    assume when_differentiable: "(\<And>j. j \<le> Suc n \<Longrightarrow> k_times_differentiable_at k (F j) x)"
    show "k_times_differentiable_at k (\<lambda>y. \<Sum>i\<le>Suc n. F i y) x \<and>
          Nth_derivative k (\<lambda>y. \<Sum>i\<le>Suc n. F i y) x =
            (\<Sum>i\<le>Suc n. Nth_derivative k (F i) x)"
    proof -
      have IH_inst:
        "k_times_differentiable_at k (\<lambda>y. \<Sum>i\<le>n. F i y) x \<and>
         Nth_derivative k (\<lambda>y. \<Sum>i\<le>n. F i y) x =
           (\<Sum>i\<le>n. Nth_derivative k (F i) x)"
        using IH[of x] when_differentiable
        by (simp add: le_Suc_eq)

      have add_rule:
        "k_times_differentiable_at k
            (\<lambda>y. (\<Sum>i\<le>n. F i y) + F (Suc n) y) x \<and>
         Nth_derivative k
            (\<lambda>y. (\<Sum>i\<le>n. F i y) + F (Suc n) y) x =
            Nth_derivative k (\<lambda>y. \<Sum>i\<le>n. F i y) x +
            Nth_derivative k (F (Suc n)) x"
        using kth_deriv_add[OF conjunct1[OF IH_inst] when_differentiable[of "Suc n"]] 
        by blast

      show "k_times_differentiable_at k (\<lambda>y. \<Sum>i\<le>Suc n. F i y) x \<and>
         Nth_derivative k (\<lambda>y. \<Sum>i\<le>Suc n. F i y) x =
           (\<Sum>i\<le>Suc n. Nth_derivative k (F i) x)"
        by (simp add: add_rule conjunct2[OF IH_inst])       
    qed
  qed
qed

corollary Nth_derivative_sum_upto_eq:
  fixes F H :: "nat \<Rightarrow> real \<Rightarrow> real"
  fixes k n :: nat and x :: real
  assumes diff: "\<And>i. i \<le> n \<Longrightarrow> (F i) k-times_differentiable_at x"
      and fam:  "\<And>i. i \<le> n \<Longrightarrow> Nth_derivative k (F i) = H i"
  shows "Nth_derivative k (\<lambda>y. \<Sum> i\<le>n. F i y) x
         = (\<Sum> i\<le>n. H i x)"
  using fam by(subst kth_deriv_sum_upto[OF diff], simp, force)
       
lemma kth_deriv_sum_uptoE:
  fixes F :: "nat \<Rightarrow> real \<Rightarrow> real"
    and k :: nat
    and x :: real
    and n :: nat
  assumes diff: "\<And>i. i \<le> n \<Longrightarrow> (F i) k-times_differentiable_at x"
  shows   "(\<lambda>y. \<Sum>i\<le>n. F i y) k-times_differentiable_at x"
  using assms by(subst kth_deriv_sum_upto, simp_all)

lemma k_times_differentiable_at_pow_funE:
  "f m-times_differentiable_at x \<Longrightarrow>
   (\<lambda>t. (f t)^n) m-times_differentiable_at x"
  by (induct n, simp add: k_times_differentiable_at_constE, simp add: kth_deriv_multE)

corollary Nth_derivative_pow_fun_eq:
  fixes f :: "real \<Rightarrow> real" and m r :: nat and x :: real
  fixes F :: "nat \<Rightarrow> real \<Rightarrow> real"
  assumes fCk: "f m-times_differentiable_at x"
      and fam: "\<And>j. j \<le> m \<Longrightarrow> Nth_derivative j f = F j"
  shows
    "Nth_derivative m (\<lambda>t. (f t)^(Suc r)) x
     = (\<Sum> j\<le>m. of_nat (m choose j) * F j x
              * Nth_derivative (m - j) (\<lambda>t. (f t)^r) x)"
  by (simp add: kth_deriv_mult[OF fCk k_times_differentiable_at_pow_funE[OF fCk]] fam)





  
named_theorems kdiff "Theorems about the existence of higher derivatives."
declare Nth_derivative_commute_and_shift_dualE[kdiff]
declare Nth_derivative_commute_and_shiftE[kdiff]
declare k_times_differentiable_at_constE[kdiff]
declare k_times_differentiable_at_idE[kdiff]
declare kth_deriv_cmultE[kdiff]
declare kth_derivative_uminusE[kdiff]
declare kth_deriv_addE[kdiff]
declare kth_deriv_subE[kdiff]
declare kth_deriv_multE[kdiff]
declare kth_deriv_sum_uptoE[kdiff]
declare k_times_differentiable_at_pow_funE[kdiff]

named_theorems kderivs "Theorems about higher derivative equalities"
declare first_derivative_alt_def[kderivs]
declare second_derivative_alt_def[kderivs]
declare Nth_derivative_const_eq[kderivs]
declare Nth_derivative_const_cases[kderivs]
declare Nth_derivative_id_eq'[kderivs]
declare Nth_derivative_id_cases[kderivs]
declare Nth_derivative_id_ge2_at[kderivs]
declare Nth_derivative_id_1_eq[kderivs]
declare Nth_derivative_id_eq[kderivs]
declare Nth_derivative_cmult_eq[kderivs]
declare Nth_derivative_uminus_eq[kderivs]
declare Nth_derivative_add_eq[kderivs]
declare Nth_derivative_sub_eq[kderivs]
declare Leibniz_prod_eq[kderivs]
declare Nth_derivative_sum_upto_eq[kderivs]
declare Nth_derivative_pow_fun_eq[kderivs]


subsection \<open>Derivative Formulas for Shifted Monomials\<close>

lemma deriv_shifted_pow:
  fixes a x :: real and n :: nat
  shows "deriv (\<lambda>w. (w - a) ^ n) x =
           (if n = 0 then 0 else of_nat n * (x - a) ^ (n - 1))"
proof -
  \<comment> \<open>`f w = w - a` is differentiable everywhere with derivative 1\<close>
  have fd: "(\<lambda>w. w - a) field_differentiable at x"
    by (simp add: Derivative.field_differentiable_diff)
  have df: "deriv (\<lambda>w. w - a) x = 1"
    by simp
  \<comment> \<open>Instantiate the general power rule with this `f`.\<close>
  from deriv_pow[OF fd, where n = n] df
  show ?thesis
    by simp
qed

lemma nth_derivative_diff_pow:
  fixes a :: real and k n :: nat
  shows
    "\<And>x.
      Nth_derivative n (\<lambda>y. (y - a) ^ k) x =
        (if n \<le> k
         then fact k / fact (k - n) * (x - a) ^ (k - n)
         else 0)"
proof (induct n)
  case 0
  show ?case
    by simp
next
  fix n x
  assume IH: "(\<And>x. Nth_derivative n (\<lambda>y. (y - a) ^ k) x 
    = (if n \<le> k then fact k / fact (k - n) * (x - a) ^ (k - n) else 0))"  
  show "Nth_derivative (Suc n) (\<lambda>y. (y - a) ^ k) x 
    = (if Suc n \<le> k then fact k / fact (k - Suc n) * (x - a) ^ (k - Suc n) else 0)"
  proof(cases "n \<le> k")
    assume n_leq_k: "n \<le> k"
    have "Nth_derivative (Suc n) (\<lambda>y. (y - a) ^ k) x 
      = deriv (\<lambda>w. (fact k / fact (k - n)) *((\<lambda>u. (u - a) ^ (k - n)) w)) x"
      using IH Nth_derivative.simps(2) n_leq_k by presburger
    also have "... = (fact k / fact (k - n)) * deriv (\<lambda>w. (\<lambda> u. (u - a) ^ (k - n) ) w) x"
      by (subst deriv_cmult, simp_all, 
          simp add: Derivative.field_differentiable_diff field_differentiable_power)
    also have "... = (fact k / fact (k - n)) * real (k - n) * (x - a) ^ (k - n - 1)"
      by(subst deriv_pow, simp_all, simp add: Derivative.field_differentiable_diff)
    also have "... = (if Suc n \<le> k then fact k / fact (k - Suc n) * (x - a) ^ (k - Suc n) else 0)"
      by (smt (verit, best) diff_Suc_eq_diff_pred diff_commute diff_is_0_eq fact_num_eq_if 
          mult_eq_0_iff nonzero_mult_divide_mult_cancel_right2 not_less_eq_eq of_nat_eq_0_iff 
          times_divide_eq_left)
    finally show ?thesis.
  next
    assume k_lt_n: "\<not> n \<le> k"
    have "Nth_derivative (Suc n) (\<lambda>y. (y - a) ^ k) x 
      = deriv (\<lambda>w. Nth_derivative n (\<lambda>y. (y - a) ^ k) w) x"
      by simp
    also have "... = 0"
      by (simp add: IH k_lt_n)
    also have "... = (if Suc n \<le> k then fact k / fact (k - Suc n) * (x - a) ^ (k - Suc n) else 0)"
      using k_lt_n by auto
    finally show ?thesis.
  qed
qed

lemma k_times_differentiable_at_pow[kdiff]:
  fixes a x :: real  and i m :: nat
  shows "(\<lambda>t. (t - a) ^ i) m-times_differentiable_at x"
  by(rule k_times_differentiable_at_pow_funE, rule kth_deriv_subE;
     (simp add: k_times_differentiable_at_constE k_times_differentiable_at_idE)+)

corollary Nth_derivative_monomial[kderivs]:
  fixes x :: real
  assumes kn: "k \<le> n"
  shows   "Nth_derivative k (\<lambda>t. t^n) x
           = (of_nat (fact n) / of_nat (fact (n - k))) * x^(n - k)"
proof -
  have "Nth_derivative k (\<lambda>t::real. t^n) x
        = Nth_derivative k (\<lambda>t. (t - 0)^n) x"
    by simp
  also have "... =
        (if k \<le> n
         then fact n / fact (n - k) * (x - 0)^(n - k)
         else 0)"
    using nth_derivative_diff_pow by blast
  also have "... =
        (of_nat (fact n) / of_nat (fact (n - k))) * x^(n - k)"
    using kn by simp
  finally show ?thesis.
qed

corollary Nth_derivative_monomial_zero [kderivs]:
  fixes x :: real
  assumes kn: "k > n"
  shows   "Nth_derivative k (\<lambda>t::real. t^n) x = 0"
proof -
  have "Nth_derivative k (\<lambda>t. t^n) x = Nth_derivative k (\<lambda>t. (t - 0)^n) x"
    by simp
  also have "... =
        (if k \<le> n
         then fact n / fact (n - k) * (x - 0)^(n - k)
         else 0)"
    using nth_derivative_diff_pow by blast
  also from kn have "... = 0" by simp
  finally show ?thesis.
qed




(*Be cautious with these ! ! !*)
(*Am I overdoing this?!*)
lemma cmult_pow_simp [kderivs]:
  "(\<lambda>t::real. (c * t) ^ n) = (\<lambda>t. (c ^ n) * t ^ n)"
  by (simp add: power_mult_distrib)

corollary Nth_derivative_cmult_pow [kderivs]:
  "Nth_derivative k (\<lambda>t::real. (c * t) ^ n) x
   = (c ^ n) * Nth_derivative k (\<lambda>t. t ^ n) x"
  by(simp add: kdiff kderivs) 

lemma add_same_factor [algebra_simps]:
  "(\<lambda>t::real. t + r * t) = (\<lambda>t. (1 + r) * t)"
  by (simp add: ring_class.ring_distribs(2))

lemma Nth_derivative_affine_cases [kderivs]:
  "Nth_derivative k (\<lambda>t::real. a*t + b) x =
     (if k = 0 then a*x + b else if k = 1 then a else 0)"
  by  (simp_all add: kdiff kderivs)

lemma sum_upto_two [simp]:
  fixes A :: "nat \<Rightarrow> 'a::{comm_monoid_add}"
  shows "(\<Sum> i\<le>2. A i) = A 0 + A 1 + A 2"
  by (simp add: Groups.add_ac(2) atMost_atLeast0 sum.atLeast_Suc_lessThan sum.last_plus)

lemma sum_upto_three [simp]:
  fixes A :: "nat \<Rightarrow> 'a::{comm_monoid_add}"
  shows "(\<Sum> i\<le>3. A i) = A 0 + A 1 + A 2 + A 3"
  by (smt (z3) Suc_eq_plus1 numeral_Bit0 numeral_Bit1 sum.atMost_Suc sum_upto_two)

lemma Nth_derivative_prod_high_order_zero[kderivs]:
  fixes f g :: "real \<Rightarrow> real" and x :: real
  assumes fvan: "\<And>j. j \<ge> a \<Longrightarrow> Nth_derivative j f x = 0"
      and gvan: "\<And>m. m \<ge> b \<Longrightarrow> Nth_derivative m g x = 0"
      and kdeg: "k \<ge> a + b - 1"
      and fdiff: "f k-times_differentiable_at x"
      and gdiff: "g k-times_differentiable_at x"
  shows "Nth_derivative k (\<lambda>t. f t * g t) x = 0"
proof -
  have Leib:
    "Nth_derivative k (\<lambda>t. f t * g t) x
     = (\<Sum> j\<le>k. of_nat (k choose j) * Nth_derivative j f x * Nth_derivative (k - j) g x)"
    by (simp add: Leibniz_prod_eq kdiff fdiff gdiff)
  have "\<dots> = 0"
  proof (rule sum.neutral, intro ballI)
    fix j assume jl: "j \<in> {..k}"
    have jle: "j \<le> k" using jl by simp
    have "j \<ge> a \<or> k - j \<ge> b"
      using kdeg jle by arith
    then show "of_nat (k choose j) * Nth_derivative j f x * Nth_derivative (k - j) g x = 0"
      using fvan gvan by auto
  qed
  with Leib show ?thesis by simp
qed

corollary Nth_derivative_power2_ge3[kderivs]:
  assumes "k \<ge> 3"
  shows   "Nth_derivative k power2 x = 0"
  using assms
  by (simp add: Nth_derivative_monomial_zero)  

corollary Nth_derivative_power2_0[kderivs]:
  "Nth_derivative 0 power2 x = x^2"
  by simp

corollary Nth_derivative_power2_1[kderivs]:
  "Nth_derivative 1 power2 x = 2 * x"
  by(simp add: kderivs, simp add: fun_eq_iff power2_eq_square)

corollary Nth_derivative_power2_2[kderivs]:
  "Nth_derivative 2 power2 x = 2"
proof -
  have f1: "\<forall>r. Nth_derivative 1 power2 r = 2 * r"
    using Nth_derivative_power2_1 by blast
  have "deriv ((*) 2) x = 2 \<and> Suc 1 = 2"
    by simp
  then have "\<exists>n. Suc n = 2 \<and> deriv (Nth_derivative n power2) x = 2"
  proof -
    have f1: "1 = Suc 0"
      using One_nat_def by satx
    then have f2: "\<forall>r. Nth_derivative (Suc 0) power2 r = 2 * r"
      using Nth_derivative_power2_1 by presburger
    have "\<forall>r ra. Nth_derivative (Suc 0) ((*) ra) r = ra"
      by fastforce
    then have "Nth_derivative (Suc 0) (Nth_derivative (Suc 0) power2) x = 2"
      using f2 by presburger
    then show ?thesis
      using f1 by (metis (full_types) \<open>deriv ((*) 2) x = 2 \<and> Suc 1 = 2\<close> first_derivative_alt_def)
  qed   
  then show ?thesis
    by (metis (no_types) Nth_derivative.simps(2))
qed

corollary Nth_derivative_power2_cases[kderivs]:
  "Nth_derivative k power2 x =
     (if k = 0 then x^2 else if k = 1 then 2*x else if k = 2 then 2 else 0)"
  using Nth_derivative_monomial_zero Nth_derivative_power2_1 Nth_derivative_power2_2 by force

lemma Nth_derivative_power_high_order_zero:
  fixes f :: "real \<Rightarrow> real" and x :: real
  fixes M p n :: nat
  assumes diff: "\<And>q. q \<le> p \<Longrightarrow> f q-times_differentiable_at x"
      and van : "\<And>m. m \<ge> M \<Longrightarrow> Nth_derivative m f x = 0"
  shows "\<And>r. r \<le> p \<Longrightarrow> r > n * (M - 1) \<Longrightarrow> Nth_derivative r (\<lambda>t. (f t) ^ n) x = 0"
proof (induction n)
  case 0
  then show ?case
    using Nth_derivative_monomial_zero by fastforce
next
  case (Suc n)
  fix r assume rle: "r \<le> p" and rgt: "r > Suc n * (M - 1)"
  from diff[OF rle] have fC: "f r-times_differentiable_at x" .
  from fC have fnC: "(\<lambda>t. (f t) ^ n) r-times_differentiable_at x"
    using k_times_differentiable_at_pow_funE by auto


  have Leib:
    "Nth_derivative r (\<lambda>t. (f t) ^ Suc n) x
       = (\<Sum> j\<le>r. of_nat (r choose j)
                 * Nth_derivative j f x
                 * Nth_derivative (r - j) (\<lambda>t. (f t) ^ n) x)"
    by (simp add: Leibniz_prod_eq kdiff fC fnC)

  have each_zero:
    "\<And>j. j \<le> r \<Longrightarrow>
      of_nat (r choose j) * Nth_derivative j f x
        * Nth_derivative (r - j) (\<lambda>t. (f t) ^ n) x = 0"
  proof -
    fix j assume jl: "j \<le> r"
    show "of_nat (r choose j) * Nth_derivative j f x
            * Nth_derivative (r - j) (\<lambda>t. (f t) ^ n) x = 0"
    proof (cases "j \<ge> M")
      case True
      then show ?thesis by (simp add: van)
    next
      case False
      hence jlt: "j \<le> M - 1" by simp
      have rj_gt: "r - j > n * (M - 1)"
        using jlt rgt by fastforce

      have rj_le: "r - j \<le> p" using rle jl by simp
      have "Nth_derivative (r - j) (\<lambda>t. (f t) ^ n) x = 0"
        using Suc.IH rj_le rj_gt diff van by blast
      thus ?thesis by simp
    qed
  qed

  have "(\<Sum> j\<le>r. of_nat (r choose j)
                 * Nth_derivative j f x
                 * Nth_derivative (r - j) (\<lambda>t. (f t) ^ n) x) = 0"
    by (rule sum.neutral) (auto simp: each_zero)
  with Leib 
  show "Nth_derivative r (\<lambda>t. (f t) ^ Suc n) x = 0"
    by presburger
qed





lemma demo_all_kderivs:
  fixes x :: real
  defines "F i \<equiv> (\<lambda>t::real. ((-1) ^ i) * (((of_nat (i + 1)) * t) ^ i))"
  defines "P \<equiv> (\<lambda>t::real. (3 * t - 5) * (t ^ 2))"
  defines "Q \<equiv> (\<lambda>t::real. - (2 * t) + 7)"
  defines "H \<equiv> (\<lambda>t::real. P t + (\<Sum> i\<le>0. F i t) - Q t + (t ^ 4 - 3 * (t ^ 4)))"
  shows   "Nth_derivative 5 H x = 0"
  unfolding H_def P_def Q_def F_def
  by (simp add: kdiff kderivs, 
      smt (verit, best) One_nat_def Suc_1 add.commute add.left_commute add_diff_cancel_right'
      mult_eq_0_iff numeral_Bit1 one_plus_numeral plus_1_eq_Suc sum.neutral zero_neq_numeral)



lemma demo_all_kderivs_big:
  fixes x :: real
  defines "F i \<equiv> (\<lambda>t::real. ((-1) ^ i) * (((of_nat (i + 1)) * t) ^ i))"
  defines "S1 \<equiv> (\<lambda>t::real. (\<Sum> i\<le>2. F i t) - (-(2 * t) + 7))"
  defines "S2 \<equiv> (\<lambda>t::real. (-2) * t^4 + (3 * t - 5) * (t ^ 2))"
  defines "R  \<equiv> (\<lambda>t::real. t^5 - 10 * t^3 + 9 * t)"
  defines "H2 \<equiv> (\<lambda>t::real. S1 t * S2 t + (\<Sum> i\<le>3. F i t) + (R t)^2)"
  shows   "Nth_derivative 11 H2 x = 0"
proof -
  (* discharge finite-sum side conditions once *)
  have diffF2: "\<And>i. i \<le> 2 \<Longrightarrow> (F i) 11-times_differentiable_at x"
    unfolding F_def by (auto intro!: kdiff)
  have diffF3: "\<And>i. i \<le> 3 \<Longrightarrow> (F i) 11-times_differentiable_at x"
    unfolding F_def by (auto intro!: kdiff)

  have Sstep2:
    "Nth_derivative 11 (\<lambda>t. \<Sum> i\<le>2. F i t) x = (\<Sum> i\<le>2. Nth_derivative 11 (F i) x)"
    by (subst Nth_derivative_sum_upto_eq[OF diffF2]) simp_all
  have Sstep3:
    "Nth_derivative 11 (\<lambda>t. \<Sum> i\<le>3. F i t) x = (\<Sum> i\<le>3. Nth_derivative 11 (F i) x)"
    by (rule Nth_derivative_sum_upto_eq[OF diffF3]) simp_all

  have Sstep4: "Nth_derivative 11 (\<lambda>t. (t ^ 5 - 10 * t ^ 3 + 9 * t)\<^sup>2) x =   0"
    by(subst Nth_derivative_power_high_order_zero[where p = 11 and M = 6], simp_all,
        (simp add: kdiff kderivs)+)
    (* S1 and S2 as plain polynomials *)
  have S1_poly: "(\<lambda>t::real. S1 t) = (\<lambda>t. 9 * t^2 - 6)"
    unfolding S1_def F_def by (simp add:  algebra_simps)
  have S2_poly: "(\<lambda>t::real. S2 t) = (\<lambda>t. -2 * t^4 + 3 * t^3 - 5 * t^2)"
    unfolding S2_def  
    by (simp add: algebra_simps, simp add: mult.commute mult.left_commute 
        power2_eq_square power3_eq_cube)

(* High-order vanishing for S1 and S2 *)
  have S1_vanish: "\<And>j. j \<ge> 3 \<Longrightarrow> Nth_derivative j (\<lambda>t. S1 t) x = 0"
    by (simp add: S1_poly kdiff kderivs)
  have S2_vanish: "\<And>m. m \<ge> 5 \<Longrightarrow> Nth_derivative m (\<lambda>t. S2 t) x = 0"
    by (simp add: S2_poly kdiff kderivs)

  (* Differentiability side-conditions for Leibniz *)
  have S1_diff: "(\<lambda>t::real. S1 t) 11-times_differentiable_at x"
    by (simp add: S1_poly kdiff)
  have S2_diff: "(\<lambda>t::real. S2 t) 11-times_differentiable_at x"
    by (simp add: S2_poly kdiff)

  (* D^11(S1 * S2)(x) = 0 by wiping each Leibniz summand *)
  have prod0: "Nth_derivative 11 (\<lambda>t. S1 t * S2 t) x = 0"
  proof -
    have Leib:
      "Nth_derivative 11 (\<lambda>t. S1 t * S2 t) x
       = (\<Sum> j\<le>11. of_nat (11 choose j)
                  * Nth_derivative j (\<lambda>t. S1 t) x
                  * Nth_derivative (11 - j) (\<lambda>t. S2 t) x)"
      by (simp add: Leibniz_prod_eq kdiff S1_diff S2_diff)
    also have "... = 0"
    proof (rule sum.neutral, intro ballI)
      fix j :: nat
      assume "j \<in> {..11}"
      then have "j \<ge> 3 \<or> 11 - j \<ge> 5" by arith
      thus "of_nat (11 choose j)
              * Nth_derivative j (\<lambda>t. S1 t) x
              * Nth_derivative (11 - j) (\<lambda>t. S2 t) x = 0"
        by (cases "j \<ge> 3") (simp add: S1_vanish, simp add: S2_vanish)
    qed
    finally show ?thesis.
  qed

  (* D^11 of the finite sum and the square tail *)
  have sum0: "Nth_derivative 11 (\<lambda>t. \<Sum> i\<le>3. F i t) x = 0"
    using Sstep3 by (simp add: F_def kdiff kderivs)

  have sq0: "Nth_derivative 11 (\<lambda>t. (R t)^2) x = 0"
    unfolding R_def using Sstep4 by blast


  have d1: "(\<lambda>y. F 0 y + F (Suc 0) y + F 2 y + F 3 y) 11-times_differentiable_at x"
    by (metis (full_types) One_nat_def Suc_1 diffF3 eval_nat_numeral(3) 
        kth_deriv_addE le_Suc_eq le_zero_eq)
  then have d2: "(\<lambda>y. F 0 y + F (Suc 0) y + F 2 y + F 3 y + (R y)\<^sup>2) 11-times_differentiable_at x"
    unfolding R_def by(subst kth_deriv_addE, simp_all, simp add: kdiff)

  have split1:
    "Nth_derivative 11 H2 x
       = Nth_derivative 11 (\<lambda>t. S1 t * S2 t) x
         + Nth_derivative 11 (\<lambda>t. (\<Sum> i\<le>3. F i t) + (R t)^2) x"
  proof -
    have "Nth_derivative 11 H2 x
            = Nth_derivative 11 (\<lambda>t. S1 t * S2 t + (\<Sum> i\<le>3. F i t) + (R t)^2) x"
      by (simp add: H2_def)
    also have "... = Nth_derivative 11 (\<lambda>t. S1 t * S2 t + ((\<Sum> i\<le>3. F i t) + (R t)^2)) x"
      by (simp add: algebra_simps)
    also have "... =
          Nth_derivative 11 (\<lambda>t. S1 t * S2 t) x
        + Nth_derivative 11 (\<lambda>t. (\<Sum> i\<le>3. F i t) + (R t)^2) x"
      using d2 by (subst Nth_derivative_add_eq, simp_all, simp add: S1_diff S2_diff kth_deriv_multE)      
    finally show ?thesis.
  qed
  from d1
  have split2:
  "Nth_derivative 11 (\<lambda>t. (\<Sum> i\<le>3. F i t) + (R t)^2) x
     = Nth_derivative 11 (\<lambda>t. \<Sum> i\<le>3. F i t) x
       + Nth_derivative 11 (\<lambda>t. (R t)^2) x"
    unfolding R_def by (subst Nth_derivative_add_eq, simp_all, simp add: kdiff)
  also have "... = 0"
    using sq0 sum0 by linarith 
  finally show ?thesis
    using prod0 split1 by linarith 
qed


subsection \<open>Relationship between Differentiability at a Point and $C^k(U)$\<close>

lemma n_times_diff_imp_lower_deriv_diff:
  assumes "f n-times_differentiable_at x"
      and "k < n"
  shows "(Nth_derivative k f) differentiable (at x)"
  using assms
  using differentiable_def k_times_differentiable_at_le_deriv by blast

lemma SucSucn_times_diff_imp_Cn_on:
  fixes f :: "real \<Rightarrow> real" and n :: nat
  assumes diff_at: "f (Suc (Suc n))-times_differentiable_at x"
  shows   "\<exists>\<epsilon>>0. C_k_on n f {x - \<epsilon> <..< x + \<epsilon>}"
proof -
  have "(\<exists>(\<epsilon> :: real) >0.  (\<forall>y. \<bar>y - x\<bar> < \<epsilon> \<longrightarrow> k_times_differentiable_at (Suc n) f y))"
    using diff_at by auto
  then obtain \<epsilon> where \<epsilon>_pos: "\<epsilon> > 0" 
    and n_diff_ball: "(\<forall>y. \<bar>y - x\<bar> < \<epsilon> \<longrightarrow> k_times_differentiable_at (Suc n) f y)"
    by blast
  then have n_diff_on: "k_times_differentiable_on (Suc n) f {y. \<bar>y - x\<bar> < \<epsilon>}"
    by (simp add: k_times_differentiable_on_def)

  define U where "U \<equiv> {x - \<epsilon> <..< x + \<epsilon>}"
  have openU: "open U" by (simp add: U_def)

  have U_def2:"U = {y. \<bar>y - x\<bar> < \<epsilon>}"
    by(auto, (simp add: U_def abs_diff_less_iff)+)     
  have n_cont_U:
    "continuous_on U (Nth_derivative n f)"
    using k_times_differentiable_on_imp_continuous_on
      U_def2 n_diff_on 
    by force
    
  have Cn_on_U:
    "C_k_on n f U"
  proof (cases n)
    case 0
    show ?thesis
      using "0" C_k_on_def Nth_derivative.simps(1) 
        n_cont_U openU by presburger
  next
    case (Suc m)
    have 1: "open U" by (simp add: openU)
    have 2: "\<forall>k < n.
               (Nth_derivative k f) differentiable_on U
             \<and> continuous_on U (Nth_derivative (Suc k) f)"
      by (metis DERIV_deriv_iff_real_differentiable Nth_derivative.simps(2) 
          k_times_differentiable_at_Suc_le_deriv(2) Suc_leD Suc_leI U_def2
          differentiable_on_eq_differentiable_at k_times_differentiable_on_def 
          k_times_differentiable_on_imp_continuous_on n_diff_on openU)  
    from 1 2 Suc show ?thesis
      unfolding C_k_on_def by simp
  qed
  show ?thesis
    using \<epsilon>_pos Cn_on_U U_def by blast
qed

lemma C_k_on_imp_k_times_differentiable_on:
  fixes f :: "real \<Rightarrow> real"
  assumes "C_k_on k f U"
  shows   "f k-times_differentiable_on U"
using assms
proof (induction k)
  case 0
  show ?case
    unfolding C_k_on_def k_times_differentiable_on_def by simp
next
  case (Suc k)
  from Suc.prems have
    open_ball: "open U" and
    Ck: "\<forall>j<k. (Nth_derivative j f) differentiable_on U
         \<and> continuous_on U (Nth_derivative (Suc j) f)"
    unfolding C_k_on_def by simp_all

  have step:
    "(Nth_derivative k f) differentiable_on U"
    using Ck [rule_format, of k]
    using C_k_on_def Suc.prems by auto 

  have cont:
    "continuous_on U (Nth_derivative (Suc k) f)"
    using Ck[rule_format, of]
    using C_k_on_def Suc.prems by auto

  have "\<forall>j\<le>k.
          (Nth_derivative j f) differentiable_on U
        \<and> continuous_on U
            (Nth_derivative (Suc j) f)"
    using Ck step cont
    by (metis dual_order.order_iff_strict) 

  have
    "k_times_differentiable_on (Suc k) f U"
  proof(rule k_times_differentiable_onI)
    fix y :: real
    assume y_in: "y \<in> U"
    show "k_times_differentiable_at (Suc k) f y"
    proof - 
      have clause1: "(\<exists>\<epsilon>>0.  (\<forall>x. \<bar>x - y\<bar> < \<epsilon> \<longrightarrow> k_times_differentiable_at k f x)) "
      proof -
        from Ck open_ball have kdiff_on:
          "k_times_differentiable_on k f U"
          unfolding C_k_on_def
          by (metis C_k_on_def Nth_derivative.simps(1) Suc.IH 
              differentiable_imp_continuous_on local.step) 
        then have kdiff_at_U:
          "\<forall>z\<in>U. k_times_differentiable_at k f z"
          unfolding k_times_differentiable_on_def by simp

        from open_ball y_in obtain \<delta> where \<delta>_pos:
          "\<delta> > 0" and \<delta>_ball: "ball y \<delta> \<subseteq> U"
          by (meson open_contains_ball)
        then have sub: "\<forall>z. \<bar>z - y\<bar> < \<delta> \<longrightarrow> z \<in> U"
          by (metis dist_commute dist_real_def mem_ball subset_eq)             
        then show ?thesis
          using \<delta>_pos kdiff_at_U by blast
      qed
      have clause2: 
        "(Nth_derivative k f has_derivative (\<lambda>h. Nth_derivative (Suc k) f y * h)) (at y)"
        using DERIV_deriv_iff_real_differentiable has_field_derivative_def
          differentiable_on_eq_differentiable_at local.open_ball local.step y_in 
        by fastforce
      thus ?thesis
        by (simp add: clause1)
    qed
  qed
  thus ?case.
qed

subsection \<open>Closure of \(C^{k}\)\<close>
\<comment> \<open>This section develops standard closure properties of \(C^{k}\).
    These include preservation of \(C^{k}\) under pointwise addition, scalar
    multiplication, multiplication of functions, division, and finite sums of functions.

    Such results are essential because they justify the existing definition for \(C^{k}\) and relate
    it to higher differentiability. Formally, these properties allow us to treat
    \(C^{k}(U)\) as an algebra over \(\mathbb{R}\) that is closed under the
    natural operations on functions.\<close>

lemma C_k_const:
  fixes c :: real  and k :: nat  and U :: "real set"
  assumes "open U"
  shows   "C_k_on k (\<lambda>_. c) U"
proof (cases k)
  case 0
  have "continuous_on U (\<lambda>x. c)"
    by simp
  with 0 assms show ?thesis
    unfolding C_k_on_def by simp
next
  case (Suc m)
  have diff0:
    "k_times_differentiable_on k (\<lambda>x. c) U"
    by (simp add: k_times_differentiable_at_constE k_times_differentiable_onI)
  moreover have
    "\<forall>j<k. (Nth_derivative j (\<lambda>x. c)) differentiable_on U
           \<and> continuous_on U (Nth_derivative (Suc j) (\<lambda>x. c))"
  proof clarify
    fix j :: nat
    assume j_bound: "j < k"
    with k_times_differentiable_at_const 
    show "Nth_derivative j (\<lambda>x. c) differentiable_on U 
      \<and> continuous_on U (Nth_derivative (Suc j) (\<lambda>x. c))"
      by (meson differentiable_at_imp_differentiable_on 
          differentiable_imp_continuous_on lessI n_times_diff_imp_lower_deriv_diff)
  qed
  ultimately show ?thesis
    by (simp add: C_k_on_def assms)
qed

lemma C_k_ident:
  fixes k :: nat and U :: "real set"
  assumes "open U"
  shows   "C_k_on k (\<lambda>x. x) U"
proof (induction k)
  case 0
  have "continuous_on U (\<lambda>x. x)"
    by simp
  with 0 assms show ?case
    unfolding C_k_on_def by simp
next
  case (Suc k)
  have openU: "open U" by fact
  have derivs:
    "\<forall>j< Suc k.
        (Nth_derivative j (\<lambda>x. x)) differentiable_on U \<and>
        continuous_on U (Nth_derivative (Suc j) (\<lambda>x. x))"
  proof clarify
    fix j 
    assume jlt: "j < Suc k"
    have "(Nth_derivative j (\<lambda>x. x)) differentiable_on U"
      by (cases j; metis k_times_differentiable_at_idE less_iff_Suc_add
          differentiable_at_imp_differentiable_on 
          n_times_diff_imp_lower_deriv_diff)
    moreover have
      "continuous_on U (Nth_derivative (Suc j) (\<lambda>x. x))"
      by (cases j; metis k_times_differentiable_at_idE k_times_differentiable_onI 
          k_times_differentiable_on_imp_continuous_on less_or_eq_imp_le)
        
    ultimately show
      "(Nth_derivative j (\<lambda>x. x)) differentiable_on U \<and>
       continuous_on U (Nth_derivative (Suc j) (\<lambda>x. x))"
      by simp
  qed
  with openU Suc show ?case
    unfolding C_k_on_def by simp
qed

lemma C_k_scale:
  fixes f      :: "real \<Rightarrow> real"
    and c      :: real
    and x      :: real
  assumes     fCk   : "C_k_on n f U"
  shows   "C_k_on n (\<lambda>y. c * f y) U"
proof -  
  have openU: "open U"
    using C_k_on_def fCk by presburger 
  show ?thesis
    using assms
  proof (cases n)
    case 0
    from fCk have cont: "continuous_on U f"
      unfolding C_k_on_def 0 by simp
    hence "continuous_on U (\<lambda>y. c * f y)"
      using continuous_on_mult_left by blast
    with openU 0 show ?thesis
      unfolding C_k_on_def by simp
  next
    fix m :: nat
    assume n_nonzero: "n = Suc m"

    from fCk obtain f_diff:
      "k_times_differentiable_on n f U"
      using C_k_on_imp_k_times_differentiable_on by blast

    hence scale_diff:
      "k_times_differentiable_on n (\<lambda>y. c * f y) U"
      using k_times_differentiable_on_def kth_deriv_cmultE by force
    from fCk have
      f_D_C: "\<forall>k<n. (Nth_derivative k f) differentiable_on U
                    \<and> continuous_on U (Nth_derivative (Suc k) f)"
      by (simp add: C_k_on_def n_nonzero)
    have Ck_less_n:
      "\<forall>k<n.
         (Nth_derivative k (\<lambda>y. c * f y)) differentiable_on U \<and>
         continuous_on U (Nth_derivative (Suc k) (\<lambda>y. c * f y))"
    proof clarify
      fix k assume k_lt_n: "k < n"
      from f_D_C[rule_format, OF k_lt_n] obtain
          Df: "(Nth_derivative k f) differentiable_on U"
        and Cf: "continuous_on U (Nth_derivative (Suc k) f)"
        by blast
      have Dscale:
        "(Nth_derivative k (\<lambda>y. c * f y)) differentiable_on U"
        by (metis differentiable_at_imp_differentiable_on k_lt_n
            k_times_differentiable_on_def n_times_diff_imp_lower_deriv_diff scale_diff)
      have Cscale:
        "continuous_on U (Nth_derivative (Suc k) (\<lambda>y. c * f y))"
      proof -
        have eq_on:
          "\<forall>y\<in>U.
             Nth_derivative (Suc k) (\<lambda>y. c * f y) y =
             c * Nth_derivative (Suc k) f y"
        proof(clarify)
          fix y :: real
          assume "y \<in> U"
          then show "Nth_derivative (Suc k) (\<lambda>y. c * f y) y = c * Nth_derivative (Suc k) f y"
            by(subst kth_deriv_cmult, 
               meson Suc_leI f_diff k_lt_n k_times_differentiable_at_mono 
               k_times_differentiable_onD, simp)
        qed
        have cont_rhs:
          "continuous_on U (\<lambda>y. c * Nth_derivative (Suc k) f y)"
          using Cf  continuous_on_mult_left by blast
        show ?thesis
          using cont_rhs eq_on
          by (metis continuous_on_cong)
      qed
      show "(Nth_derivative k (\<lambda>y. c * f y)) differentiable_on U \<and>
            continuous_on U (Nth_derivative (Suc k) (\<lambda>y. c * f y))"
        using Dscale Cscale by blast
    qed
    with openU n_nonzero scale_diff 
    show ?thesis
      unfolding C_k_on_def by simp
  qed
qed

lemma C_k_neg:
  fixes f :: "real \<Rightarrow> real" and U :: "real set"
  assumes fCk: "C_k_on n f U"
  shows   "C_k_on n (\<lambda>y. - f y) U"
proof -
  have "C_k_on n (\<lambda>y. (-1) * f y) U"
    by (rule C_k_scale[OF fCk])
  thus ?thesis
    by (simp add: fun_eq_iff)
qed

lemma C_k_add:
  fixes f g :: "real \<Rightarrow> real"  and x :: real
  assumes fCk: "C_k_on n f U"
      and gCk: "C_k_on n g U"
  shows   "C_k_on n (\<lambda>y. f y + g y) U"
proof -
  have openU: "open U"
    using C_k_on_def fCk by presburger 

  show ?thesis
    using assms
  proof (cases n)
    case 0
    with fCk gCk have cont:
      "continuous_on U f"  "continuous_on U g"
      unfolding C_k_on_def by auto
    have "continuous_on U (\<lambda>y. f y + g y)"
      using cont by (simp add: continuous_on_add)
    with openU 0 show ?thesis
      unfolding C_k_on_def by simp
  next
    fix m :: nat
    assume f_Cn: "C_k_on n f U"
    then have f_n_diff: "k_times_differentiable_on n f U"
      using C_k_on_imp_k_times_differentiable_on by blast
    assume g_Cn: "C_k_on n g U"
    then have g_n_diff: "k_times_differentiable_on n g U"
      using C_k_on_imp_k_times_differentiable_on by blast
    assume n_nonzero: "n = Suc m"
    
    have sum_n_diff: "k_times_differentiable_on n (\<lambda>y. f(y)+ g(y)) U"
      using f_n_diff g_n_diff k_times_differentiable_on_def kth_deriv_add by auto

    with f_Cn have f_diff: "(\<forall>k < n. (Nth_derivative k f) differentiable_on U 
                         \<and> continuous_on U (Nth_derivative (Suc k) f))"
      unfolding C_k_on_def by auto

    with g_Cn have g_diff: "(\<forall>k < n. (Nth_derivative k g) differentiable_on U 
                         \<and> continuous_on U (Nth_derivative (Suc k) g))"
      unfolding C_k_on_def by auto

    with f_n_diff g_n_diff sum_n_diff 
    have Ck_less_n:
      "(\<forall>k < n.
          (Nth_derivative k (\<lambda>x. f x + g x)) differentiable_on U
        \<and> continuous_on U (Nth_derivative (Suc k) (\<lambda>x. f x + g x)))"
    proof (clarify)
      fix k :: nat      
      assume "k < n"
      
      have f_diff: "\<forall>k<n. Nth_derivative k f differentiable_on U"
        using f_diff by blast
      have g_diff: "\<forall>k<n. Nth_derivative k g differentiable_on U"
        using g_diff by blast
      have Ck_less_n:
        "\<forall>k<n.
            (Nth_derivative k (\<lambda>x. f x + g x)) differentiable_on U \<and>
            continuous_on U (Nth_derivative (Suc k) (\<lambda>x. f x + g x))"
        using f_n_diff g_n_diff

      proof clarify
        fix k :: nat
        assume k_lt_n: "k < n"
        from f_diff[rule_format, OF k_lt_n] have
                Df: "(Nth_derivative k f) differentiable_on U"
            and Cf: "continuous_on U (Nth_derivative (Suc k) f)"
          by(blast, metis C_k_on_def f_Cn k_lt_n n_nonzero nat.distinct(1))
          
        from g_diff[rule_format, OF k_lt_n] have 
                Dg: "(Nth_derivative k g) differentiable_on U"
            and Cg: "continuous_on U (Nth_derivative (Suc k) g)"
          by(blast, metis C_k_on_def g_Cn k_lt_n n_nonzero nat.distinct(1))
        have Dsum:
          "(Nth_derivative k (\<lambda>x. f x + g x)) differentiable_on U"
          by (metis differentiable_at_imp_differentiable_on k_lt_n k_times_differentiable_onD 
              n_times_diff_imp_lower_deriv_diff sum_n_diff)
    
        from Cf Cg 
        have "continuous_on U (\<lambda>x. Nth_derivative (Suc k) f x + Nth_derivative (Suc k) g x)"
          by(rule continuous_on_add)
        then have continuous_on: "\<forall>y\<in> U.  continuous (at y within U)
             (\<lambda>t. Nth_derivative (Suc k) f t + Nth_derivative (Suc k) g t)"
          using continuous_on_eq_continuous_within by blast
          
        have "\<forall>y\<in> U. continuous (at y within U)(\<lambda>t. Nth_derivative (Suc k) (\<lambda>x. f x + g x) t)"
        proof clarify
          fix y :: real
          assume y_bound: "y \<in> U"
          have f_Suc_k_diff_on: "k_times_differentiable_on (Suc k) f U"
            by (meson Suc_leI f_n_diff k_times_differentiable_on_def
                k_times_differentiable_at_mono k_lt_n)
          then have f_Suc_k_diff: "k_times_differentiable_at (Suc k) f y"
            using k_times_differentiable_on_def y_bound by blast
    
          have g_Suc_k_diff_on: "k_times_differentiable_on (Suc k) g U"
            by (meson Suc_leI g_n_diff k_times_differentiable_on_def
                k_times_differentiable_at_mono k_lt_n)
          then have g_Suc_k_diff: "k_times_differentiable_at (Suc k) g y"
            using k_times_differentiable_on_def y_bound by blast
     
          have continuity_at_y: "continuous (at y within U)
             (\<lambda>t. Nth_derivative (Suc k) f t + Nth_derivative (Suc k) g t)"
            using continuous_on y_bound by blast  
          then have continuity_at_y': "\<forall>y \<in> U. continuous (at y)
            (\<lambda>t. Nth_derivative (Suc k) f t + Nth_derivative (Suc k) g t)"
            by (metis at_within_open local.continuous_on openU)
     
          have deriv_assoc: "\<forall>y \<in> U. 
                Nth_derivative (Suc k) (\<lambda>y. f y + g y) y = 
                Nth_derivative (Suc k) f y + Nth_derivative (Suc k) g y"
            by (metis f_Suc_k_diff_on g_Suc_k_diff_on 
                k_times_differentiable_on_def kth_deriv_add)
          
          have "\<forall>y\<in>U. continuous (at y within U)
              (\<lambda>t. Nth_derivative (Suc k) (\<lambda>x. f x + g x) t)"
          proof clarify
            fix y 
            assume y_in: "y \<in> U"
          
            have "continuous (at y within U)
                 (\<lambda>t. Nth_derivative (Suc k) f t + Nth_derivative (Suc k) g t)"
              using f_Suc_k_diff g_Suc_k_diff local.continuous_on y_in by blast

            with y_in deriv_assoc assms(1)
            show "continuous (at y within U)
                    (Nth_derivative (Suc k) (\<lambda>x. f x + g x))"                                
              by (subst continuous_transform_within[where 
                    f = "\<lambda>t. Nth_derivative (Suc k) f t + Nth_derivative (Suc k) g t" 
                    and d = 1], simp_all)
          qed
          then show "continuous (at y within U) (Nth_derivative (Suc k) (\<lambda>x. f x + g x))"
            using y_bound by blast
        qed  
        then show "Nth_derivative k (\<lambda>x. f x + g x) differentiable_on U 
          \<and> continuous_on U (Nth_derivative (Suc k) (\<lambda>x. f x + g x))"
          using Dsum continuous_on_eq_continuous_within by blast  
      qed        
  
      show "Nth_derivative k (\<lambda>x. f x + g x) differentiable_on U 
        \<and> continuous_on U (Nth_derivative (Suc k) (\<lambda>x. f x + g x))"
        using Ck_less_n \<open>k < n\<close> by blast
    qed  
    then show ?thesis
      by (simp add: C_k_on_def n_nonzero openU)
  qed
qed

lemma C_k_sub:
  fixes f g :: "real \<Rightarrow> real" and U :: "real set"
  assumes fCk: "C_k_on n f U"
      and gCk: "C_k_on n g U"
  shows   "C_k_on n (\<lambda>y. f y - g y) U"
proof -
  have g_neg: "C_k_on n (\<lambda>y. - g y) U"
    using gCk by (simp add: C_k_neg)

  have "C_k_on n (\<lambda>y. f y + (- g y)) U"
    by (rule C_k_add[OF fCk g_neg])

  thus ?thesis
    by (simp add: fun_eq_iff)  
qed

lemma C_k_mult:
  fixes f g :: "real \<Rightarrow> real"  and \<epsilon> x :: real
  assumes fCk   : "C_k_on n f U"
      and gCk   : "C_k_on n g U"
  shows   "C_k_on n (\<lambda>y. f y * g y) U"
proof -
  have openU: "open U"
    using C_k_on_def fCk by presburger 

  show ?thesis
    using assms
  proof (cases n)
    case 0
    with fCk gCk have cont:
      "continuous_on U f"  "continuous_on U g"
      unfolding C_k_on_def by auto
    have "continuous_on U (\<lambda>y. f y + g y)"
      using cont by (simp add: continuous_on_add)
    with openU show "C_k_on n (\<lambda>y. f y * g y) U"
      by (simp add: "0" C0_on_def cont continuous_on_mult)
  next
    from fCk have f_diff:
      "k_times_differentiable_on n f U"
      using C_k_on_imp_k_times_differentiable_on by blast
  
    from gCk have g_diff:
      "k_times_differentiable_on n g U"
      using C_k_on_imp_k_times_differentiable_on by blast

    fix m :: nat
    assume f_Cn: "C_k_on n f U"
    then have f_n_diff: "k_times_differentiable_on n f U"
      using C_k_on_imp_k_times_differentiable_on by blast
    assume g_Cn: "C_k_on n g U"
    then have g_n_diff: "k_times_differentiable_on n g U"
      using C_k_on_imp_k_times_differentiable_on by blast
    assume n_nonzero: "n = Suc m"
    
    have prod_n_diff: "k_times_differentiable_on n (\<lambda>y. f(y)* g(y)) U"
      using f_n_diff g_n_diff k_times_differentiable_on_def kth_deriv_mult by auto

    with f_Cn have f_D_C: "(\<forall>k < n. (Nth_derivative k f) differentiable_on U 
                         \<and> continuous_on U (Nth_derivative (Suc k) f))"
      unfolding C_k_on_def by auto
      
    with g_Cn have g_D_C: "(\<forall>k < n. (Nth_derivative k g) differentiable_on U 
                         \<and> continuous_on U (Nth_derivative (Suc k) g))"
      unfolding C_k_on_def by auto

    with f_n_diff g_n_diff prod_n_diff 
    have Ck_less_n:
      "\<forall>k<n.
         (Nth_derivative k (\<lambda>y. f y * g y)) differentiable_on U \<and>
         continuous_on U (Nth_derivative (Suc k) (\<lambda>y. f y * g y))"
    proof clarify
      fix k 
      assume k_lt_n: "k < n"     
      have prod_diff:
          "(Nth_derivative k (\<lambda>x. f x * g x)) differentiable_on U"
        by (metis differentiable_at_imp_differentiable_on k_lt_n 
            k_times_differentiable_on_def n_times_diff_imp_lower_deriv_diff prod_n_diff)

      have prod_cont:
      "continuous_on U (Nth_derivative (Suc k) (\<lambda>y. f y * g y))"
      proof -
        have cont_every:
          "\<forall>j\<le>Suc k. continuous_on U
             (\<lambda>y. of_nat (Suc k choose j) *
                  (Nth_derivative j f y *
                   Nth_derivative (Suc k - j) g y))"
        proof (clarify)
          fix j :: nat
          assume j_le: "j \<le> Suc k"          
          have cont_inner:
            "continuous_on U
               (\<lambda>y. Nth_derivative j f y * Nth_derivative (Suc k - j) g y)"
            by (metis Suc_diff_le cancel_comm_monoid_add_class.diff_cancel continuous_on_mult 
                differentiable_imp_continuous_on dual_order.strict_trans2 
                f_D_C g_D_C j_le k_lt_n le_Suc_eq less_imp_diff_less)
                              
          have cont_const: "continuous_on U (\<lambda>y. of_nat (Suc k choose j))"
            by simp
          show "continuous_on U
                  (\<lambda>y. of_nat (Suc k choose j) *
                       (Nth_derivative j f y *
                        Nth_derivative (Suc k - j) g y))"
            using cont_const cont_inner
            by (simp add: continuous_on_mult mult.assoc)
        qed

        then have cont_sum:
          "continuous_on U
             (\<lambda>x. \<Sum>j\<le>Suc k. of_nat (Suc k choose j) *
                            Nth_derivative j f x *
                            Nth_derivative (Suc k - j) g x)"
          by(subst continuous_on_sum, simp_all, simp add: ab_semigroup_mult_class.mult_ac(1))
          
        have eq_on:
          "\<forall>x\<in>U.
             (\<Sum>j\<le>Suc k. of_nat (Suc k choose j) *
                        Nth_derivative j f x *
                        Nth_derivative (Suc k - j) g x)
           = Nth_derivative (Suc k) (\<lambda>y. f y * g y) x"
        proof clarify
          fix x :: real
          assume xU: "x \<in> U"
          have "k_times_differentiable_at (Suc k) f x"
               "k_times_differentiable_at (Suc k) g x"
            using f_n_diff g_n_diff xU
            unfolding k_times_differentiable_on_def
            using Suc_leI k_lt_n k_times_differentiable_at_mono by blast+
          with kth_deriv_mult[where k = "Suc k"]
          show "(\<Sum>j\<le>Suc k. of_nat (Suc k choose j) *
                   Nth_derivative j f x *
                   Nth_derivative (Suc k - j) g x)
                = Nth_derivative (Suc k) (\<lambda>y. f y * g y) x"
            by simp
        qed

        from cont_sum eq_on
        show ?thesis
          using continuous_on_cong by fastforce          
      qed    
      show "Nth_derivative k (\<lambda>y. f y * g y) differentiable_on U \<and>
            continuous_on U (Nth_derivative (Suc k) (\<lambda>y. f y * g y))"
        using prod_diff prod_cont by blast
    qed
    then show ?thesis
      by (simp add: C_k_on_def n_nonzero openU)
  qed
qed

lemma C_1_inv:
  fixes f :: "real \<Rightarrow> real" and \<epsilon> x :: real
  assumes fC1   : "C_k_on 1 f U"
      and nz    : "\<forall>y\<in>U. f y \<noteq> 0"
    shows   "C_k_on 1 (\<lambda>y. inverse (f y)) U"
proof -    
  have openU: "open U"
    using C_k_on_def fC1 by presburger 

  have derivative_exists: "\<forall>y\<in>U. \<exists>d .(f has_field_derivative d) (at y within U)"
    by (metis C1_cont_diff at_within_open fC1 openU)

  from fC1 obtain
     cont_f : "continuous_on U f"
   and diff_f : "\<forall>y\<in>U. (\<lambda>t. f t) differentiable (at y)"
    using C1_cont_diff DERIV_deriv_iff_real_differentiable 
      differentiable_imp_continuous_on by blast
  
  have cont_inv: "continuous_on U (\<lambda>y. inverse (f y))"
    using Limits.continuous_on_inverse cont_f nz by blast

  have diff_inv:
    "\<forall>y\<in>U. (\<lambda>t. inverse (f t)) differentiable (at y)"
    using diff_f differentiable_inverse nz by blast

  have "C_k_on 1 (\<lambda>y. inverse (f y)) U"
  proof -
    have "Nth_derivative 0 (\<lambda>y. inverse (f y)) differentiable_on U"
      using diff_inv differentiable_at_imp_differentiable_on by auto
    moreover have "continuous_on U (Nth_derivative (Suc 0) (\<lambda>y. inverse (f y)))"
    proof -
      have eq_on:
        "\<forall>y\<in>U. Nth_derivative 1 (\<lambda>y. inverse (f y)) y =
                - deriv f y / (f y)^2"
      proof clarify
        fix y 
        assume yU: "y \<in> U"
        then obtain d where d_def: "(f has_field_derivative d) (at y within U)"
          using derivative_exists by blast

        have "((\<lambda>x. inverse (f x)) has_field_derivative 
          - (d * inverse (f y ^ Suc (Suc 0)))) (at y within U)"
          by(rule DERIV_inverse_fun, smt d_def, smt nz yU)
        then have "((\<lambda>t. inverse (f t)) has_field_derivative (- deriv f y / (f y)^2)) (at y)"
          by (metis DERIV_imp_deriv at_within_open d_def
              divide_minus_left divide_real_def numeral_2_eq_2 openU yU)
        thus "Nth_derivative 1 (\<lambda>y. inverse (f y)) y =  - deriv f y / (f y)^2"
          by (simp add: DERIV_imp_deriv)
      qed

      have "continuous_on U (\<lambda>y. deriv f y)"
        using C1_cont_diff fC1 by blast
      then have cont_derf: "continuous_on U (\<lambda>y. - deriv f y)"
        using continuous_on_minus by blast
      have "(\<lambda>y. inverse (f y) * inverse (f y)) = (\<lambda>y. inverse ((f y)^2))"
        by (simp add: power2_eq_square)
      then have cont_rhs:
        "continuous_on U (\<lambda>y. - deriv f y * inverse ((f y)\<^sup>2))"
        by (metis (full_types) cont_derf cont_inv continuous_on_mult)
      then show "continuous_on U (Nth_derivative (Suc 0) (\<lambda>y. inverse (f y)))"
        using continuous_on_cong divide_real_def eq_on by fastforce
    qed
    ultimately show ?thesis
      by (simp add: C_k_on_def openU)      
  qed
  thus ?thesis.
qed

lemma C_1_div:
  fixes f g :: "real \<Rightarrow> real"  and U :: "real set"
  assumes fC1 : "C_k_on 1 f U"
      and gC1 : "C_k_on 1 g U"
      and nz   : "\<forall>y\<in>U. g y \<noteq> 0"
  shows   "C_k_on 1 (\<lambda>y. f y / g y) U"
proof -
  have inv_g_C1: "C_k_on 1 (\<lambda>y. inverse (g y)) U"
    by (rule C_1_inv[OF gC1 nz])

  have "C_k_on 1 (\<lambda>y. f y * inverse (g y)) U"
    by (rule C_k_mult[OF fC1 inv_g_C1])
  thus ?thesis
    by (simp add: field_simps)
qed

lemma C_k_sum_upto:
  fixes F :: "nat \<Rightarrow> real \<Rightarrow> real" and k N :: nat and U :: "real set"
  assumes FCk: "\<And>i. i \<le> N \<Longrightarrow> C_k_on k (F i) U"
  shows   "C_k_on k (\<lambda>x. \<Sum> i\<le>N. F i x) U"
proof (cases k)
  case 0
  then have cont_i: "\<And>i. i \<le> N \<Longrightarrow> continuous_on U (F i)"
    using FCk by (simp add: C_k_on_def)
  have "continuous_on U (\<lambda>x. \<Sum> i\<le>N. F i x)"
    by (subst continuous_on_sum) (use cont_i in auto)
  with 0 show ?thesis
    using C_k_on_def assms by auto 
next
  case (Suc k')
  have openU: "open U"
    using FCk[of 0] by (cases k) (simp_all add: C_k_on_def)
  have F_kdiff_on: "\<And>i. i \<le> N \<Longrightarrow> k_times_differentiable_on (Suc k') (F i) U"
    using FCk Suc by (simp add: C_k_on_imp_k_times_differentiable_on)

  have sum_kdiff_on: "k_times_differentiable_on (Suc k') (\<lambda>x. \<Sum> i\<le>N. F i x) U"
  proof (rule k_times_differentiable_onI)
    fix x :: real
    assume xU: "x \<in> U"
    have each_at: "\<And>i. i \<le> N \<Longrightarrow> (F i) (Suc k')-times_differentiable_at x"
      using F_kdiff_on xU by (simp add: k_times_differentiable_on_def)
    then show "(\<lambda>y. \<Sum> i\<le>N. F i y) (Suc k')-times_differentiable_at x"
      by(rule kth_deriv_sum_uptoE, auto)
  qed

  have Dj:
    "\<And>j. j < Suc k' \<Longrightarrow> (Nth_derivative j (\<lambda>x. \<Sum> i\<le>N. F i x)) differentiable_on U"
  proof -
    fix j :: nat
    assume jlt: "j < Suc k'"
    from openU jlt sum_kdiff_on
    show "(Nth_derivative j (\<lambda>x. \<Sum> i\<le>N. F i x)) differentiable_on U"
      by (metis at_within_open differentiable_on_def
                k_times_differentiable_onD n_times_diff_imp_lower_deriv_diff)
  qed

  have Cj:
    "\<And>j. j < Suc k' \<Longrightarrow> continuous_on U (Nth_derivative (Suc j) (\<lambda>x. \<Sum> i\<le>N. F i x))"
  proof -
    fix j :: nat
    assume jlt: "j < Suc k'"
    have eq_on:
      "\<And>x. x \<in> U \<Longrightarrow>
          Nth_derivative (Suc j) (\<lambda>x. \<Sum> i\<le>N. F i x) x
        = (\<Sum> i\<le>N. Nth_derivative (Suc j) (F i) x)"
    proof -
      fix x :: real
      assume xU: "x \<in> U"
      have each_at_j:
        "\<And>i. i \<le> N \<Longrightarrow> (F i) (Suc j)-times_differentiable_at x"
      proof -
        fix i assume "i \<le> N"
        from F_kdiff_on[OF \<open>i \<le> N\<close>] xU have
          "(F i) (Suc k')-times_differentiable_at x"
          by (simp add: k_times_differentiable_on_def)
        with jlt show "(F i) (Suc j)-times_differentiable_at x"
          by (meson Suc_leI k_times_differentiable_at_mono)
      qed

      then show "Nth_derivative (Suc j) (\<lambda>x. \<Sum> i\<le>N. F i x) x
            = (\<Sum> i\<le>N. Nth_derivative (Suc j) (F i) x)" 
        by(subst kth_deriv_sum_upto, simp_all)
    qed
    have cont_sum:
      "continuous_on U (\<lambda>x. \<Sum> i\<le>N. Nth_derivative (Suc j) (F i) x)"
    proof -
      have "\<And>i. i \<le> N \<Longrightarrow> continuous_on U (Nth_derivative (Suc j) (F i))"
        using FCk Suc jlt
        by (simp add: C_k_on_def)
      then show ?thesis
        by (subst continuous_on_sum) auto
    qed
    show "continuous_on U (Nth_derivative (Suc j) (\<lambda>x. \<Sum> i\<le>N. F i x))"
      using cont_sum eq_on by auto
  qed

  have "C_k_on (Suc k') (\<lambda>x. \<Sum> i\<le>N. F i x) U"
    using openU Dj Cj Suc sum_kdiff_on
    by (simp add: C_k_on_def)
  then show ?thesis using Suc by simp
qed


lemma higher_differentiable_on_real_iff_k_times_on_Suc:
  fixes f :: "real \<Rightarrow> real"
  assumes "open S"
  shows
    "higher_differentiable_on S f (Suc n)
     \<longleftrightarrow> (\<forall>x\<in>S. k_times_differentiable_at (Suc n) f x)"
proof (induction n) 
  show "higher_differentiable_on S f (Suc 0) = Ball S (times_differentiable_at f (Suc 0))"
  proof
    assume H: "higher_differentiable_on S f (Suc 0)"
    show "Ball S (times_differentiable_at f (Suc 0))"
    proof (rule ballI)
      fix x 
      assume "x \<in> S"
      with H assms
      show "times_differentiable_at f (Suc 0) x"
        by (metis One_nat_def higher_differentiable_on.simps(2) one_time_differentiable_at_iff real_differentiable_def)        
    qed
  next
    assume B: "Ball S (times_differentiable_at f (Suc 0))"
    have D: "\<forall>x\<in>S. f differentiable (at x)"
    proof
      fix x 
      assume xS: "x \<in> S"
      from B xS obtain U where open_U: "open U" and x_in_U: "x \<in> U" and
            f_Diff: "higher_differentiable_on U f (Suc 0)"
        sorry
      then have "\<forall>y\<in>U. f differentiable (at y)"
        using higher_differentiable_on.simps(2) by blast
      thus "f differentiable (at x)" 
        using x_in_U by blast
    qed
    have C: "\<forall>v. continuous_on S (\<lambda>x. frechet_derivative f (at x) v)"
    proof
      fix v
      show "continuous_on S (\<lambda>x. frechet_derivative f (at x) v)"
      proof (rule continuous_on_eq_continuous_within[THEN iffD2], intro ballI)
        fix x 
        assume xS: "x \<in> S"
        from B xS obtain U where open_U: "open U" and  x_in_U: "x \<in> U" and
              f_Diff: "higher_differentiable_on U f (Suc 0)"
          sorry
        hence "continuous_on U (\<lambda>x. frechet_derivative f (at x) v)"
          using higher_differentiable_on.simps(1) higher_differentiable_on.simps(2) by blast 

        hence "isCont (\<lambda>x. frechet_derivative f (at x) v) x"
          using open_U x_in_U continuous_on_eq_continuous_at by blast

        thus "continuous (at x within S) (\<lambda>x. frechet_derivative f (at x) v)"
          using continuous_at_imp_continuous_at_within by blast
      qed
    qed
    show "higher_differentiable_on S f (Suc 0)"
      by (simp add: C D higher_differentiable_on.simps(1,2)) 
  qed
next
  fix n :: nat
  assume IH: "higher_differentiable_on S f (Suc n) = Ball S (times_differentiable_at f (Suc n))"
  show "higher_differentiable_on S f (Suc (Suc n)) = Ball S (times_differentiable_at f (Suc (Suc n)))"
  proof
    assume H: "higher_differentiable_on S f (Suc (Suc n))"
    show "Ball S (times_differentiable_at f (Suc (Suc n)))"
    proof (rule ballI)
      fix x assume "x \<in> S"
      with assms H show "times_differentiable_at f (Suc (Suc n)) x"
        sorry
    qed
  next
    assume B: "Ball S (times_differentiable_at f (Suc (Suc n)))"
    have D: "\<forall>x\<in>S. f differentiable (at x)"
    proof
      fix x assume xS: "x \<in> S"
      from B xS obtain U where open_U: "open U" and x_in_U: "x \<in> U"
        and fDiffU: "higher_differentiable_on U f (Suc (Suc n))"
        sorry
      then show "f differentiable (at x)"
        by (auto simp: higher_differentiable_on.simps)
    qed
    have C: "\<forall>v. higher_differentiable_on S (\<lambda>x. frechet_derivative f (at x) v) (Suc n)"
    proof
      fix v :: real
      have Bv: "Ball S (times_differentiable_at (\<lambda>x. frechet_derivative f (at x) v) (Suc n))"
      proof (intro ballI)
        fix x assume xS: "x \<in> S"
        from B xS obtain U where open_U: "open U" and x_in_U: "x \<in> U"
          and fDiffU: "higher_differentiable_on U f (Suc (Suc n))"
          sorry
        hence "higher_differentiable_on U (\<lambda>x. frechet_derivative f (at x) v) (Suc n)"
          using higher_differentiable_on.simps(2) by blast
        thus "times_differentiable_at (\<lambda>x. frechet_derivative f (at x) v) (Suc n) x"
          sorry
      qed
        (* Auxiliary: local C^(Suc n) on an open cover \<Rightarrow> C^(Suc n) on S (S is open) *)
      have Aux:
        "\<And>g::real\<Rightarrow>real. Ball S (times_differentiable_at g (Suc n))
         \<Longrightarrow> higher_differentiable_on S g (Suc n)"
      using assms
      proof (induction n arbitrary: g)
        case 0
        then show ?case
        proof -
          have Dg: "\<forall>x\<in>S. g differentiable (at x)"
          proof
            fix x assume xS: "x \<in> S"
            from 0 xS obtain U where "open U" "x \<in> U"
              "higher_differentiable_on U g (Suc 0)"
              sorry
            then show "g differentiable (at x)"
              by (auto simp: higher_differentiable_on.simps)
          qed
          have Cg: "\<forall>w. continuous_on S (\<lambda>x. frechet_derivative g (at x) w)"
          proof
            fix w :: real
            show "continuous_on S (\<lambda>x. frechet_derivative g (at x) w)"
            proof (rule continuous_on_eq_continuous_within[THEN iffD2], intro ballI)
              fix x assume xS: "x \<in> S"
              from 0 xS obtain U where U: "open U" "x \<in> U"
                "higher_differentiable_on U g (Suc 0)"
                sorry
              hence "continuous_on U (\<lambda>x. frechet_derivative g (at x) w)"
                by (simp add: higher_differentiable_on.simps)
              hence "isCont (\<lambda>x. frechet_derivative g (at x) w) x"
                using U by (simp add: continuous_on_eq_continuous_at)
              thus "continuous (at x within S) (\<lambda>x. frechet_derivative g (at x) w)"
                using continuous_at_imp_continuous_at_within by blast
            qed
          qed
          show ?thesis
            by (simp add: Dg Cg higher_differentiable_on.simps)
        qed
      next
        case (Suc m)
        then show ?case
        proof -
          have Dg: "\<forall>x\<in>S. g differentiable (at x)"
          proof
            fix x assume xS: "x \<in> S"
            from Suc.prems xS obtain U where "open U" "x \<in> U"
              "higher_differentiable_on U g (Suc (Suc m))"
              sorry
            then show "g differentiable (at x)"
              by (auto simp: higher_differentiable_on.simps)
          qed
          have Cg: "\<forall>w. higher_differentiable_on S (\<lambda>x. frechet_derivative g (at x) w) (Suc m)"
          proof
            fix w :: real
            have Bw: "Ball S (times_differentiable_at (\<lambda>x. frechet_derivative g (at x) w) (Suc m))"
            proof (intro ballI)
              fix x assume xS: "x \<in> S"
              from Suc.prems xS obtain U where U: "open U" "x \<in> U"
                "higher_differentiable_on U g (Suc (Suc m))"
                sorry
              hence "higher_differentiable_on U (\<lambda>x. frechet_derivative g (at x) w) (Suc m)"
                using higher_differentiable_on.simps(2) by blast
              thus "times_differentiable_at (\<lambda>x. frechet_derivative g (at x) w) (Suc m) x"
                sorry
            qed
            from Suc.IH[of "\<lambda>x. frechet_derivative g (at x) w"]
            show "higher_differentiable_on S (\<lambda>x. frechet_derivative g (at x) w) (Suc m)"
              using Bw assms by blast
          qed
          show ?thesis
            using Cg Dg higher_differentiable_on.simps(2) by blast
        qed
      qed
      from Aux Bv show "higher_differentiable_on S (\<lambda>x. frechet_derivative f (at x) v) (Suc n)" .
    qed
    show "higher_differentiable_on S f (Suc (Suc n))"
      using C D higher_differentiable_on.simps(2) by blast
  qed
qed

end