section \<open>Fixed-Point Method: VCG, Lammich, and Floating-Point Verification\<close>

theory Fixed_Point_Method
  imports
    "Refine_Monadic.Refine_Monadic"
    Higher_Diffs.Taylor_Peano
    Float_Default
begin

text \<open>This theory verifies the fixed-point iteration \<open>x \<mapsto> f x\<close> twice, so the two
  verification paradigms can be compared side by side on the same algorithm:

    \<^item> \<^bold>\<open>Paradigm A\<close> --- the imperative ITree program \<open>fpm\<close>, verified with
      VCG-based total-correctness Hoare logic (\<open>H[P] prog [Q]\<close>); and
    \<^item> \<^bold>\<open>Paradigm B\<close> --- Lammich's Refinement Framework, the \<open>nres\<close> program
      \<open>R_fpm\<close> built from a single \<open>WHILET\<close>, verified by \<open>\<le> SPEC\<close>.

  Both paradigms draw on the \<^emph>\<open>same\<close> shared mathematics (the contractive-map facts
  and the geometric/iteration-count lemmas below); only the loop-correctness glue
  differs between them. The shared math is therefore proved once and cited from
  both sides. We mirror all three convergence regimes on both sides: the local
  linear contraction bound, its C1 corollary (\<open>\<bar>f'(r)\<bar> < 1\<close>), and quadratic
  convergence (\<open>f'(r) = 0\<close>, via Taylor's theorem with the Peano remainder).\<close>

section \<open>Shared contraction and convergence mathematics (used by both paradigms)\<close>

subsection \<open>Contractive Map Facts\<close>

lemma contractive_deriv_bound_closed:
  assumes C1:   "C_k_on 1 f U"
      and zU:   "z \<in> U"
      and Dz_lt: "\<bar>deriv f z\<bar> < B"
  shows "\<exists>\<epsilon>>0. \<exists>\<delta>>0. {z - \<delta> .. z + \<delta>} \<subseteq> U \<and> (\<forall>x \<in> {z - \<delta> .. z + \<delta>}. \<bar>deriv f x\<bar> \<le> B - \<epsilon>)"
proof -
  obtain \<nu> where \<nu>_pos: "\<nu> > 0" and \<nu>_in: "{z - \<nu> .. z + \<nu>} \<subseteq> U"
    by (metis C_k_on_def C1 zU cball_eq_atLeastAtMost open_contains_cball_eq)
  obtain \<epsilon> where \<epsilon>_def: "\<epsilon> = (B - \<bar>deriv f z\<bar>) / 2" and \<epsilon>_pos: "\<epsilon> > 0"
    using Dz_lt by fastforce
  have cont_on: "continuous_on U (deriv f)"
    using C1_cont_diff C1 by blast
  have cont_at: "continuous (at z) (deriv f)"
    using cont_on C1 zU by (simp add: C_k_on_def continuous_on_eq_continuous_at)
  then have "\<forall> \<epsilon> > 0. \<exists> \<delta> > 0.  \<forall>x. \<bar>x - z\<bar> < \<delta> \<longrightarrow> \<bar>deriv f x - deriv f z\<bar> < \<epsilon>"
    using continuous_at_eps_delta by blast
  then obtain \<delta>1 where \<delta>1_pos: "\<delta>1 > 0"
    and near: "\<forall>x. \<bar>x - z\<bar> < \<delta>1 \<longrightarrow> \<bar>deriv f x - deriv f z\<bar> < \<epsilon>"
    by (meson \<epsilon>_pos)
  define \<delta> where "\<delta> = min \<nu> (\<delta>1 / 2)"
  have \<delta>_pos: "\<delta> > 0" using \<nu>_pos \<delta>1_pos by (simp add: \<delta>_def)
  have \<delta>_le_\<nu>: "\<delta> \<le> \<nu>" by (simp add: \<delta>_def)
  have \<delta>_lt_\<delta>1: "\<delta> < \<delta>1" using \<delta>1_pos by (simp add: \<delta>_def)
  have subsetU: "{z - \<delta> .. z + \<delta>} \<subseteq> U"
    using \<nu>_in \<delta>_le_\<nu> by auto
  have bound_strict: "\<forall>x \<in> {z - \<delta> .. z + \<delta>}. \<bar>deriv f x - deriv f z\<bar> < \<epsilon>"
  proof
    fix x assume xI: "x \<in> {z - \<delta> .. z + \<delta>}"
    have "\<bar>x - z\<bar> \<le> \<delta>" using xI by (simp add: abs_le_iff)
    hence "\<bar>x - z\<bar> < \<delta>1" using \<delta>_lt_\<delta>1 by linarith
    thus "\<bar>deriv f x - deriv f z\<bar> < \<epsilon>" using near by simp
  qed
  have bound_closed: "\<forall>x \<in> {z - \<delta> .. z + \<delta>}. \<bar>deriv f x\<bar> \<le> B - \<epsilon>"
  proof
    fix x assume xI: "x \<in> {z - \<delta> .. z + \<delta>}"
    have "\<bar>deriv f x\<bar> \<le> \<bar>deriv f z\<bar> + \<bar>deriv f x - deriv f z\<bar>"
      by (simp add: abs_triangle_ineq4)
    also have "\<dots> < \<bar>deriv f z\<bar> + \<epsilon>"
      using bound_strict xI by simp
    also have "\<dots> = \<bar>deriv f z\<bar> + (B - \<bar>deriv f z\<bar>)/2"
      by (simp add: \<epsilon>_def)
    also have "\<dots> = B - \<epsilon>"
      by (smt (z3) \<epsilon>_def field_sum_of_halves)
    finally show "\<bar>deriv f x\<bar> \<le> B - \<epsilon>" by (rule less_imp_le)
  qed
  show ?thesis
    by (intro exI[of _ \<epsilon>] exI[of _ \<delta>] conjI \<epsilon>_pos conjI \<delta>_pos conjI subsetU bound_closed)
qed

corollary contractive_deriv_bound:
  assumes "C_k_on 1 f U"
  assumes "z \<in> U"
  assumes "\<bar>deriv f z\<bar> < B"
  shows "\<exists> \<epsilon> > 0. \<exists>\<delta> > 0. ({z - \<delta> <..< z + \<delta>} \<subseteq> U) \<and> (\<forall> x \<in> {z - \<delta> <..< z + \<delta>}. \<bar>deriv f x\<bar> < B - \<epsilon>)"
proof -
  from assms have "\<exists>\<epsilon>>0. \<exists>\<delta>>0.
           {z - \<delta> .. z + \<delta>} \<subseteq> U \<and>
           (\<forall>x \<in> {z - \<delta> .. z + \<delta>}. \<bar>deriv f x\<bar> \<le> B - \<epsilon>)"
    by(rule contractive_deriv_bound_closed)
  then obtain \<epsilon>0 \<delta>0 where \<epsilon>0: "\<epsilon>0 > 0" and \<delta>0: "\<delta>0 > 0"
      and sub: "{z - \<delta>0 .. z + \<delta>0} \<subseteq> U"
      and bd:  "\<forall>x\<in>{z - \<delta>0 .. z + \<delta>0}. \<bar>deriv f x\<bar> \<le> B - \<epsilon>0"
    by meson
  define \<epsilon> where "\<epsilon> = \<epsilon>0 / 2"
  define \<delta> where "\<delta> = \<delta>0"
  have "\<epsilon> > 0" by (simp add: \<epsilon>_def \<epsilon>0)
  have "\<delta> > 0" by (simp add: \<delta>_def \<delta>0)
  have open_sub: "{z - \<delta><..<z + \<delta>} \<subseteq> U"
    using \<delta>_def atLeastAtMost_eq_cball ball_subset_cball greaterThanLessThan_eq_ball sub by blast
  have bound_open: "\<forall>x\<in>{z - \<delta><..<z + \<delta>}. \<bar>deriv f x\<bar> < B - \<epsilon>"
  proof
    fix x assume "x \<in> {z - \<delta><..<z + \<delta>}"
    hence x_closed: "x \<in> {z - \<delta>0 .. z + \<delta>0}" by (simp add: \<delta>_def)
    have "\<bar>deriv f x\<bar> \<le> B - \<epsilon>0" using bd x_closed by blast
    moreover have "B - \<epsilon>0 < B - \<epsilon>"
      by (simp add: \<epsilon>0 \<epsilon>_def)
    ultimately show "\<bar>deriv f x\<bar> < B - \<epsilon>" by linarith
  qed
  show ?thesis
    using \<delta>0 \<delta>_def \<open>0 < \<epsilon>\<close> bound_open open_sub by blast
qed

corollary contractive_deriv_imp_contra_closed:
  assumes "C_k_on 1 f U"
      and "z \<in> U"
      and "\<bar>deriv f z\<bar> < B"
    shows "\<exists>\<epsilon> > 0. \<exists>\<delta> > 0.((\<epsilon> < B) \<and> {z - \<delta> .. z + \<delta>} \<subseteq> U) \<and>
        (\<forall>x y. (x\<in>{z - \<delta> .. z + \<delta>} \<and> y\<in>{x .. z + \<delta>}) \<longrightarrow> \<bar>f x - f y\<bar> \<le> (B - \<epsilon>) * \<bar>x - y\<bar>)"
proof -
  from contractive_deriv_bound_closed[OF assms]
  obtain \<epsilon>0 \<delta> where \<epsilon>0_pos: "\<epsilon>0 > 0" and \<delta>_pos: "\<delta> > 0"
    and subset: "{z - \<delta> .. z + \<delta>} \<subseteq> U"
    and dBd: "\<forall>x \<in> {z - \<delta> .. z + \<delta>}. \<bar>deriv f x\<bar> \<le> B - \<epsilon>0"
    by blast
  define \<epsilon> where "\<epsilon> = min \<epsilon>0 (B/2)"
  have \<epsilon>_pos: "\<epsilon> > 0"
    using \<epsilon>0_pos assms(3) by (simp add: \<epsilon>_def half_gt_zero_iff less_imp_le)
  have \<epsilon>_lt_B: "\<epsilon> < B"
    using \<epsilon>_def \<epsilon>_pos by linarith
  have mvt: "\<forall>x y. (x \<in> {z - \<delta> .. z + \<delta>} \<and> y \<in> {x .. z + \<delta>}) \<longrightarrow> \<bar>f x - f y\<bar> \<le> (B - \<epsilon>) * \<bar>x - y\<bar>"
  proof clarify
    fix x y :: real
    assume x_in: "x \<in> {z - \<delta> .. z + \<delta>}" and y_in: "y \<in> {x .. z + \<delta>}"
    show "\<bar>f x - f y\<bar> \<le> (B - \<epsilon>) * \<bar>x - y\<bar>"
    proof (cases "x = y")
      case True  show ?thesis by (simp add: True)
    next
      case False
      hence x_lt_y: "x < y"
        using less_eq_real_def y_in by presburger
      have "\<exists>t>x. t < y \<and> f y - f x = (y - x) * deriv f t"
      proof (rule MVT2[where a = x and b = y and f = f and f' = "deriv f"])
        fix t assume "x \<le> t" "t \<le> y"
        hence "t \<in> {z - \<delta> .. z + \<delta>}" using x_in y_in by auto
        then have "t \<in> U" using subset by blast
        thus "(f has_real_derivative deriv f t) (at t)"
          using C1_cont_diff assms(1) by blast
      qed (use x_lt_y in auto)
      then obtain \<theta> where \<theta>_in: "\<theta> \<in> {x <..< y}"
                        and \<theta>_eq: "f y - f x = (y - x) * deriv f \<theta>"
        by auto
      have \<theta>_closed: "\<theta> \<in> {z - \<delta> .. z + \<delta>}" using x_in y_in \<theta>_in by auto
      have "\<bar>deriv f \<theta>\<bar> \<le> B - \<epsilon>0" using dBd \<theta>_closed by blast
      also have "\<dots> \<le> B - \<epsilon>" by (simp add: \<epsilon>_def)
      finally have "\<bar>deriv f \<theta>\<bar> \<le> B - \<epsilon>".
      thus "\<bar>f x - f y\<bar> \<le> (B - \<epsilon>) * \<bar>x - y\<bar>"
        by (smt (z3) \<theta>_eq mult.commute mult_left_mono mult_minus_right)
    qed
  qed
  show ?thesis
    using \<epsilon>_pos \<delta>_pos \<epsilon>_lt_B subset mvt by blast
qed

corollary contractive_deriv_imp_contra:
  assumes "C_k_on 1 f U"
  assumes "z \<in> U"
  assumes "\<bar>deriv f z\<bar> < B"
  shows "\<exists>\<epsilon> > 0. \<exists>\<delta> > 0. ((\<epsilon> < B) \<and> {z - \<delta> <..< z + \<delta>} \<subseteq> U) \<and>
   (\<forall>x y. (x \<in> {z - \<delta> <..< z + \<delta>} \<and> y \<in> {x <..< z + \<delta>}) \<longrightarrow> \<bar>f x - f y\<bar> < (B - \<epsilon>) * \<bar>x - y\<bar>)"
proof -
  from contractive_deriv_bound[OF assms] obtain \<epsilon> \<delta>
    where \<epsilon>_pos: "\<epsilon> > 0" and \<delta>_pos: "\<delta> > 0"
      and bound:   "\<forall>x \<in> {z - \<delta> <..< z + \<delta>}. \<bar>deriv f x\<bar> < B - \<epsilon>"
      and subset': "{z - \<delta> <..< z + \<delta>} \<subseteq> U"
    by auto
  then have \<epsilon>_lt_B: "\<epsilon> < B"
    by (smt (verit) dist_real_def field_sum_of_halves greaterThanLessThan_eq_ball mem_ball)
  have mvt: "\<forall>x y. (x\<in>{z - \<delta> <..< z + \<delta>} \<and> y\<in>{x <..< z + \<delta>}) \<longrightarrow> \<bar>f x - f y\<bar> < (B - \<epsilon>) * \<bar>x - y\<bar>"
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
      by (metis add_0 cross3_simps(11,54) diff_diff_eq2 greaterThanLessThan_iff)
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
  fixes f :: "real \<Rightarrow> real"
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
  fixes f :: "real \<Rightarrow> real"
  assumes order_bound:"\<forall>x y. x\<in>{r - \<delta>0<..<r + \<delta>0} \<longrightarrow> y\<in>{x<..<r + \<delta>0} \<longrightarrow> \<bar>f x - f y\<bar> < (1-\<epsilon>)*\<bar>x-y\<bar>"
    and \<epsilon>_pos : "0 < \<epsilon>"
    and \<delta>_pos : "0 < \<delta>" and \<delta>_le: "\<delta> \<le> \<delta>0"
  shows "\<forall>s t. s \<noteq> t \<longrightarrow> \<bar>s - r\<bar> < \<delta> \<longrightarrow> \<bar>t - r\<bar> < \<delta>  \<longrightarrow> \<bar>f s - f t\<bar> < (1 - \<epsilon>) * \<bar>s - t\<bar>"
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

lemma contraction_cball_closure:
  fixes f :: "real \<Rightarrow> real"
  assumes fr: "f r = r"
      and lips_cball: "\<And>s t. \<bar>s - r\<bar> \<le> \<delta> \<Longrightarrow> \<bar>t - r\<bar> \<le> \<delta> \<Longrightarrow> \<bar>f s - f t\<bar> \<le> c * \<bar>s - t\<bar>"
      and c_ge0: "0 \<le> c" and c_lt1: "c < 1"
  shows "\<forall>n x. \<bar>x - r\<bar> \<le> \<delta> \<longrightarrow> \<bar>(f ^^ n) x - r\<bar> \<le> \<delta>"
proof (intro allI impI)
  fix n x assume "\<bar>x - r\<bar> \<le> \<delta>"
  then show "\<bar>(f ^^ n) x - r\<bar> \<le> \<delta>"
  proof (induction n arbitrary: x)
    case 0 show ?case
      by (simp add: "0.prems")
  next
    case (Suc n x)
    have "\<bar>(f ^^ Suc n) x - r\<bar> = \<bar>f ((f ^^ n) x) - f r\<bar>"
      by (simp add: assms(1))
    also have "\<dots> \<le> c * \<bar>(f ^^ n) x - r\<bar>"
      using lips_cball Suc.IH Suc(2) by force
    also have "\<dots> \<le> \<bar>(f ^^ n) x - r\<bar>"
      using c_ge0
      by (meson abs_ge_zero c_lt1 less_eq_real_def mult_left_le_one_le)
    also have "\<dots> \<le> \<delta>" using Suc.IH Suc(2) by blast
    finally show ?case.
  qed
qed

lemma inv_cball_of_budget:
  fixes f :: "real \<Rightarrow> real" and x0 R c :: real
  assumes "0 \<le> c" "c < 1" "R \<ge> 0"
      and lips:   "\<And>s t. \<bar>s - x0\<bar> \<le> R \<Longrightarrow> \<bar>t - x0\<bar> \<le> R \<Longrightarrow> \<bar>f s - f t\<bar> \<le> c * \<bar>s - t\<bar>"
      and budget: "\<bar>f x0 - x0\<bar> \<le> (1 - c) * R"
  shows "f ` cball x0 R \<subseteq> cball x0 R"
proof
  fix y
  assume "y \<in> f ` cball x0 R"
  then obtain s where sB: "s \<in> cball x0 R" and y: "y = f s" by auto
  have "\<bar>y - x0\<bar> = \<bar>f s - x0\<bar>"
    by (simp add: norm_triangle_ineq4 y)
  also have "\<dots> \<le> \<bar>f s - f x0\<bar> + \<bar>f x0 - x0\<bar>"
    by simp
  also have "\<dots> \<le> c * \<bar>s - x0\<bar> + (1 - c) * R"
    by (smt (verit) assms(4,5) dist_real_def mem_cball sB)
  also have "\<dots> \<le> c * R + (1 - c) * R"
    by (smt (verit, best) assms(1) dist_real_def mem_cball mult_left_mono sB)
  also have "\<dots> \<le>  R"
    by argo
  finally show "y \<in> cball x0 R"
    by (simp add: dist_real_def)
qed

subsection \<open>Per-iteration decay under a closed-ball local contraction (shared)\<close>

text \<open>These geometric facts about the iterates of a locally contractive \<open>f\<close> are the
  heart of every convergence result below.  They are proved \<^emph>\<open>once\<close> here and cited by
  both the VCG core proofs (Paradigm A) and the Lammich loop lemmas (Paradigm B); only
  the loop glue differs between the two.\<close>

context
  fixes f :: "real \<Rightarrow> real" and r x0 tol c \<delta> :: real
  assumes c_nonneg: "0 \<le> c" and c_strict: "c < 1" and tol_pos: "0 < tol"
    and \<delta>_pos: "0 < \<delta>" and r_fixed: "f r = r" and x0_in: "\<bar>x0 - r\<bar> \<le> \<delta>"
    and contractive: "\<forall>s t. \<bar>s - r\<bar> \<le> \<delta> \<and> \<bar>t - r\<bar> \<le> \<delta> \<longrightarrow> \<bar>f s - f t\<bar> \<le> c * \<bar>s - t\<bar>"
begin

lemma fpm_lips_cball: "\<bar>s - r\<bar> \<le> \<delta> \<Longrightarrow> \<bar>t - r\<bar> \<le> \<delta> \<Longrightarrow> \<bar>f s - f t\<bar> \<le> c * \<bar>s - t\<bar>"
  using contractive by blast

lemma fpm_iters_in_cball: "\<bar>(f ^^ n) x0 - r\<bar> \<le> \<delta>"
  using contraction_cball_closure[OF r_fixed fpm_lips_cball c_nonneg c_strict] x0_in by blast

lemma fpm_err_decay: "\<bar>(f ^^ n) x0 - r\<bar> \<le> c ^ n * \<bar>x0 - r\<bar>"
proof (induction n)
  show "\<bar>(f ^^ 0) x0 - r\<bar> \<le> c ^ 0 * \<bar>x0 - r\<bar>" by simp
next
  case (Suc n)
  have t_in: "\<bar>(f ^^ n) x0 - r\<bar> \<le> \<delta>" by (rule fpm_iters_in_cball)
  have r_in: "\<bar>r - r\<bar> \<le> \<delta>" using \<delta>_pos by simp
  have "\<bar>(f ^^ Suc n) x0 - r\<bar> = \<bar>f ((f ^^ n) x0) - f r\<bar>" using r_fixed by simp
  also have "\<dots> \<le> c * \<bar>(f ^^ n) x0 - r\<bar>" using fpm_lips_cball[OF t_in r_in] .
  also have "\<dots> \<le> c * (c ^ n * \<bar>x0 - r\<bar>)" using Suc.IH c_nonneg by (simp add: mult_left_mono)
  also have "\<dots> = c ^ Suc n * \<bar>x0 - r\<bar>" by simp
  finally show ?case .
qed

lemma fpm_step_decay: "\<bar>f ((f ^^ n) x0) - (f ^^ n) x0\<bar> \<le> c ^ n * \<bar>f x0 - x0\<bar>"
proof (induction n)
  show "\<bar>f ((f ^^ 0) x0) - (f ^^ 0) x0\<bar> \<le> c ^ 0 * \<bar>f x0 - x0\<bar>" by simp
next
  case (Suc n)
  have b_in: "\<bar>(f ^^ n) x0 - r\<bar> \<le> \<delta>" by (rule fpm_iters_in_cball)
  have fb_in: "\<bar>(f ^^ Suc n) x0 - r\<bar> \<le> \<delta>" by (rule fpm_iters_in_cball)
  have key: "\<bar>f ((f ^^ Suc n) x0) - f ((f ^^ n) x0)\<bar> \<le> c * \<bar>(f ^^ Suc n) x0 - (f ^^ n) x0\<bar>"
    using fpm_lips_cball[OF fb_in b_in] .
  have eq1: "f ((f ^^ n) x0) = (f ^^ Suc n) x0" by simp
  have "\<bar>f ((f ^^ Suc n) x0) - (f ^^ Suc n) x0\<bar> = \<bar>f ((f ^^ Suc n) x0) - f ((f ^^ n) x0)\<bar>"
    using eq1 by simp
  also have "\<dots> \<le> c * \<bar>(f ^^ Suc n) x0 - (f ^^ n) x0\<bar>" using key .
  also have "\<dots> = c * \<bar>f ((f ^^ n) x0) - (f ^^ n) x0\<bar>" using eq1 by simp
  also have "\<dots> \<le> c * (c ^ n * \<bar>f x0 - x0\<bar>)" using Suc.IH c_nonneg by (simp add: mult_left_mono)
  also have "\<dots> = c ^ Suc n * \<bar>f x0 - x0\<bar>" by simp
  finally show ?case .
qed

end

subsection \<open>Per-iteration decay under an open-ball local contraction (shared)\<close>

text \<open>The strict / open-ball analogue of the previous block, used for the quadratic
  regime.  Same statements, with \<open>contraction_ball_closure\<close> in place of its
  closed-ball cousin.\<close>

context
  fixes f :: "real \<Rightarrow> real" and r x0 tol c \<delta> :: real
  assumes c_nonneg: "0 \<le> c" and c_strict: "c < 1" and tol_pos: "0 < tol"
    and \<delta>_pos: "0 < \<delta>" and r_fixed: "f r = r" and x0_in: "\<bar>x0 - r\<bar> < \<delta>"
    and contractive: "\<forall>s t. \<bar>s - r\<bar> < \<delta> \<and> \<bar>t - r\<bar> < \<delta> \<longrightarrow> \<bar>f s - f t\<bar> \<le> c * \<bar>s - t\<bar>"
begin

lemma fpm_lips_ball: "\<bar>s - r\<bar> < \<delta> \<Longrightarrow> \<bar>t - r\<bar> < \<delta> \<Longrightarrow> \<bar>f s - f t\<bar> \<le> c * \<bar>s - t\<bar>"
  using contractive by blast

lemma fpm_iters_in_ball: "\<bar>(f ^^ n) x0 - r\<bar> < \<delta>"
proof -
  have contr': "\<forall>s t. \<bar>s - r\<bar> < \<delta> \<longrightarrow> \<bar>t - r\<bar> < \<delta> \<longrightarrow> \<bar>f s - f t\<bar> \<le> c * \<bar>s - t\<bar>"
    using contractive by blast
  have "\<forall>n x. \<bar>x - r\<bar> < \<delta> \<longrightarrow> \<bar>(f ^^ n) x - r\<bar> < \<delta>"
    using contraction_ball_closure[OF r_fixed contr'] c_nonneg c_strict by blast
  thus ?thesis using x0_in by blast
qed

lemma fpm_err_decay_lt: "\<bar>(f ^^ n) x0 - r\<bar> \<le> c ^ n * \<bar>x0 - r\<bar>"
proof (induction n)
  show "\<bar>(f ^^ 0) x0 - r\<bar> \<le> c ^ 0 * \<bar>x0 - r\<bar>" by simp
next
  case (Suc n)
  have t_in: "\<bar>(f ^^ n) x0 - r\<bar> < \<delta>" by (rule fpm_iters_in_ball)
  have r_in: "\<bar>r - r\<bar> < \<delta>" using \<delta>_pos by simp
  have "\<bar>(f ^^ Suc n) x0 - r\<bar> = \<bar>f ((f ^^ n) x0) - f r\<bar>" using r_fixed by simp
  also have "\<dots> \<le> c * \<bar>(f ^^ n) x0 - r\<bar>" using fpm_lips_ball[OF t_in r_in] .
  also have "\<dots> \<le> c * (c ^ n * \<bar>x0 - r\<bar>)" using Suc.IH c_nonneg by (simp add: mult_left_mono)
  also have "\<dots> = c ^ Suc n * \<bar>x0 - r\<bar>" by simp
  finally show ?case .
qed

lemma fpm_step_decay_lt: "\<bar>f ((f ^^ n) x0) - (f ^^ n) x0\<bar> \<le> c ^ n * \<bar>f x0 - x0\<bar>"
proof (induction n)
  show "\<bar>f ((f ^^ 0) x0) - (f ^^ 0) x0\<bar> \<le> c ^ 0 * \<bar>f x0 - x0\<bar>" by simp
next
  case (Suc n)
  have b_in: "\<bar>(f ^^ n) x0 - r\<bar> < \<delta>" by (rule fpm_iters_in_ball)
  have fb_in: "\<bar>(f ^^ Suc n) x0 - r\<bar> < \<delta>" by (rule fpm_iters_in_ball)
  have key: "\<bar>f ((f ^^ Suc n) x0) - f ((f ^^ n) x0)\<bar> \<le> c * \<bar>(f ^^ Suc n) x0 - (f ^^ n) x0\<bar>"
    using fpm_lips_ball[OF fb_in b_in] .
  have eq1: "f ((f ^^ n) x0) = (f ^^ Suc n) x0" by simp
  have "\<bar>f ((f ^^ Suc n) x0) - (f ^^ Suc n) x0\<bar> = \<bar>f ((f ^^ Suc n) x0) - f ((f ^^ n) x0)\<bar>"
    using eq1 by simp
  also have "\<dots> \<le> c * \<bar>(f ^^ Suc n) x0 - (f ^^ n) x0\<bar>" using key .
  also have "\<dots> = c * \<bar>f ((f ^^ n) x0) - (f ^^ n) x0\<bar>" using eq1 by simp
  also have "\<dots> \<le> c * (c ^ n * \<bar>f x0 - x0\<bar>)" using Suc.IH c_nonneg by (simp add: mult_left_mono)
  also have "\<dots> = c ^ Suc n * \<bar>f x0 - x0\<bar>" by simp
  finally show ?case .
qed

end

section \<open>Paradigm A: Imperative ITree Program, VCG-based Hoare Logic\<close>

subsection \<open>Algorithm\<close>

zstore st = lvstore +
  x :: real
  fx :: real
  f'x :: real
  gx :: real
  x_new :: real
  iter :: nat
  Break :: nat

program fpm "(f::real\<Rightarrow>real , x0::real , tol::real)" over st
="x := x0; x_new := f x; iter := 0;
 while (\<bar>x_new - x\<bar> \<ge> tol) do x := x_new; x_new := f x; iter := iter + 1 od"

program fpm_aux "(f::real\<Rightarrow>real , x0::real , tol::real , c::real)" over st
="x := x0; x_new := f x; iter := 0;
 while (\<bar>x_new - x\<bar> \<ge> tol)
 invariant x = (f ^^ iter) x0  \<and> x_new = f x \<and> \<bar>x_new - x\<bar> \<le> (c ^ iter) * \<bar>f x0 - x0\<bar>
     \<and> iter \<le> Suc (nat \<lceil> ln (max 1 (\<bar>f x0 - x0\<bar> / tol)) / ln (1 / c) \<rceil>)
 variant  Suc (nat \<lceil> ln (max 1 (\<bar>f x0 - x0\<bar> / tol)) / ln (1 / c) \<rceil>) - iter
 do x := x_new; x_new := f x; iter := iter + 1 od"

lemma fpm_aux_is_fpm: "fpm_aux (f, x0, tol, c) = fpm (f, x0, tol)"
  unfolding fpm_def fpm_aux_def by (simp add: while_inv_var_def)

execute "fpm(\<lambda> x. x*x, 0.5, 0.1)"
\<comment> \<open>This program terminates after 2 iterations with an estimate of the fixed point \(0\),
     namely \(0.00390625), when starting from \(0.5\), within an error tolerance
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

lemma fpm_step_lt_tol_at_bound:
  fixes d0 tol c :: real
  assumes d0_nonneg: "0 \<le> d0"
    and c_nonneg:  "0 \<le> c"
    and c_strict:  "c < 1"
    and tol_pos:   "0 < tol"
  shows "(c ^ Suc (nat \<lceil> ln (max 1 (d0 / tol)) / ln (1 / c) \<rceil>)) * d0 < tol"
proof (cases "c = 0")
  case True
  then show ?thesis
    using tol_pos by simp
next
  case False
  have c_pos: "0 < c"
    using c_nonneg False by linarith
  have one_div_c_gt1: "1 < 1 / c"
    using c_pos c_strict by (simp add: field_simps)
  have ln_one_div_c_pos: "0 < ln (1 / c)"
    using one_div_c_gt1 by (rule ln_gt_zero)
  have max1_pos: "0 < max 1 (d0 / tol)"
    by simp
  have frac_nonneg: "0 \<le> ln (max 1 (d0 / tol)) / ln (1 / c)"
    using ln_one_div_c_pos by (simp add: divide_nonneg_pos)
  have frac_le_nat_ceiling: "ln (max 1 (d0 / tol)) / ln (1 / c)
        \<le> real (nat \<lceil> ln (max 1 (d0 / tol)) / ln (1 / c) \<rceil>)"
  proof -
    have "ln (max 1 (d0 / tol)) / ln (1 / c)
            \<le> real_of_int \<lceil> ln (max 1 (d0 / tol)) / ln (1 / c) \<rceil>"
      by linarith
    moreover have "0 \<le> \<lceil> ln (max 1 (d0 / tol)) / ln (1 / c) \<rceil>"
      using frac_nonneg by linarith
    ultimately show ?thesis
      by simp
  qed
  have ln_max1_le: "ln (max 1 (d0 / tol))
        \<le> real (nat \<lceil> ln (max 1 (d0 / tol)) / ln (1 / c) \<rceil>) * ln (1 / c)"
    using frac_le_nat_ceiling ln_one_div_c_pos by (smt (verit, best) pos_less_divide_eq)
  have max1_le_pow:  "max 1 (d0 / tol) \<le> (1 / c) ^ (nat \<lceil> ln (max 1 (d0 / tol)) / ln (1 / c) \<rceil>)"
    by (smt (verit, best) exp_ln_iff log_exp one_div_c_gt1 power_of_nat_log_ge)
   have c_pow_pos: "0 < c ^ (nat \<lceil> ln (max 1 (d0 / tol)) / ln (1 / c) \<rceil>)"
    using c_pos by simp
  have max1_le_one_over_cpow: "max 1 (d0 / tol) \<le> 1/(c^(nat \<lceil> ln (max 1 (d0 / tol)) / ln (1 / c)\<rceil>))"
    using max1_le_pow False by (simp add: power_one_over)
  have cpow_le_one_over_max1: "c^(nat \<lceil> ln (max 1 (d0 / tol)) / ln (1 / c)\<rceil>)\<le> 1 / max 1 (d0 / tol)"
    by (smt (verit) arith_simps(16) card.empty div_by_1 divide_divide_eq_right divide_inverse
        fpm_aux_def inner_real_def inverse_eq_divide ln_div ln_divide_pos ln_max1_le
        ln_one_div_c_pos ln_realpow ln_strict_mono max1_pos mult_cancel_left mult_le_cancel_left_pos
        mult_minus_left numeral_code(1,1) one_div_c_gt1 power_eq_0_iff power_one_over powr_real_def
        real_inner_1_left times_divide_eq_left zero_compare_simps(7))
  have d0_over_max1_le_tol: "d0 / max 1 (d0 / tol) \<le> tol"
    by (smt (verit, best) assms(4) div_by_1 less_divide_eq_1_pos
        nonzero_eq_divide_eq nonzero_mult_div_cancel_left)
  have c_pow_times_d0_le_tol: "(c ^ (nat \<lceil> ln (max 1 (d0 / tol)) / ln (1 / c) \<rceil>)) * d0 \<le> tol"
    by (smt (verit) c_pow_pos cpow_le_one_over_max1 div_by_1 divide_divide_eq_right tol_pos
        less_divide_eq_1_pos nonzero_eq_divide_eq times_divide_eq_left zero_compare_simps(7))
  have "(c ^ Suc (nat \<lceil> ln (max 1 (d0 / tol)) / ln (1 / c) \<rceil>)) * d0
          = c * ((c ^ (nat \<lceil> ln (max 1 (d0 / tol)) / ln (1 / c) \<rceil>)) * d0)"
    by simp
  also have "... \<le> c * tol"
    using c_pow_times_d0_le_tol c_nonneg by (simp add: mult_left_mono)
  also have "... < tol"
    using c_strict tol_pos by (simp add: mult_less_cancel_right_pos)
  finally show ?thesis.
qed

lemma fpm_aux_iter_bnd_local_lt:
  assumes c_nonneg:    "0 \<le> c"
    and c_strict:      "c < 1"
    and tol_pos:       "0 < tol"
    and \<delta>_pos:         "0 < \<delta>"
    and r_is_fixed:    "f r = r"
    and x0_in_ball:    "\<bar>r - x\<^sub>0\<bar> < \<delta>"
    and contractive:  "\<forall>s t. \<bar>s - r\<bar> < \<delta> \<and> \<bar>t - r\<bar> < \<delta> \<longrightarrow> \<bar>f s - f t\<bar> \<le> c * \<bar>s - t\<bar>"
  shows "H[True] fpm_aux(f, x\<^sub>0, tol, c) [ \<bar>x - r\<bar> \<le> c ^ iter * \<bar>x\<^sub>0 - r\<bar> \<and> \<bar>x_new - x\<bar> < tol
       \<and> iter \<le> Suc(nat \<lceil> ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol)) / ln (1 / c)\<rceil>) ]"
proof (vcg)
  fix iter :: nat
  assume step_bound: "\<bar>f ((f ^^ iter) x\<^sub>0) - (f ^^ iter) x\<^sub>0\<bar> \<le> c ^ iter * \<bar>f x\<^sub>0 - x\<^sub>0\<bar>"
  and iter_le_bound: "iter \<le> Suc (nat \<lceil>ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol)) / ln (1 / c)\<rceil>)"
  and tol_le_step: "tol \<le> \<bar>f ((f ^^ iter) x\<^sub>0) - (f ^^ iter) x\<^sub>0\<bar>"
  have x0_in: "\<bar>x\<^sub>0 - r\<bar> < \<delta>" using x0_in_ball by (simp add: abs_minus_commute)
  show "\<bar>f (f ((f ^^ iter) x\<^sub>0)) - f ((f ^^ iter) x\<^sub>0)\<bar> \<le> c * c ^ iter * \<bar>f x\<^sub>0 - x\<^sub>0\<bar>"
    using fpm_step_decay_lt[OF c_nonneg c_strict tol_pos \<delta>_pos r_is_fixed x0_in contractive, of "Suc iter"]
    by simp
next
  fix iter :: nat
  assume step_bound: "\<bar>f ((f ^^ iter) x\<^sub>0) - (f ^^ iter) x\<^sub>0\<bar> \<le> c ^ iter * \<bar>f x\<^sub>0 - x\<^sub>0\<bar>"
    and iter_le_suc: "iter \<le> Suc (nat \<lceil>ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol)) / ln (1 / c)\<rceil>)"
    and tol_le_step: "tol \<le> \<bar>f ((f ^^ iter) x\<^sub>0) - (f ^^ iter) x\<^sub>0\<bar>"
  let ?B = "nat \<lceil>ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol)) / ln (1 / c)\<rceil>"
  show "iter \<le> ?B"
  proof (rule ccontr)
    assume "\<not> iter \<le> ?B"
    then have iter_eq: "iter = Suc ?B"
      using iter_le_suc by arith
    have geom_strict: "(c ^ Suc ?B) * \<bar>f x\<^sub>0 - x\<^sub>0\<bar> < tol"
      using fpm_step_lt_tol_at_bound  c_nonneg c_strict tol_pos by simp
    have "\<bar>f ((f ^^ iter) x\<^sub>0) - (f ^^ iter) x\<^sub>0\<bar>  \<le> c ^ iter * \<bar>f x\<^sub>0 - x\<^sub>0\<bar>"
      using step_bound .
    also have "... = (c ^ Suc ?B) * \<bar>f x\<^sub>0 - x\<^sub>0\<bar>"
      using iter_eq by simp
    also have "... < tol"
      using geom_strict .
    finally have "\<bar>f ((f ^^ iter) x\<^sub>0) - (f ^^ iter) x\<^sub>0\<bar> < tol".
    with tol_le_step show False
      by linarith
  qed
next
  fix iter :: nat
  have x0_in: "\<bar>x\<^sub>0 - r\<bar> < \<delta>" using x0_in_ball by (simp add: abs_minus_commute)
  show "\<bar>(f ^^ iter) x\<^sub>0 - r\<bar> \<le> c ^ iter * \<bar>x\<^sub>0 - r\<bar>"
    by (rule fpm_err_decay_lt[OF c_nonneg c_strict tol_pos \<delta>_pos r_is_fixed x0_in contractive])
next
  show "\<And>iter.
       \<lbrakk>\<bar>f ((f ^^ iter) x\<^sub>0) - (f ^^ iter) x\<^sub>0\<bar> \<le> c ^ iter * \<bar>f x\<^sub>0 - x\<^sub>0\<bar>;
        iter \<le> Suc (nat \<lceil>ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol)) / ln (1 / c)\<rceil>);
        tol \<le> \<bar>f ((f ^^ iter) x\<^sub>0) - (f ^^ iter) x\<^sub>0\<bar>\<rbrakk>
       \<Longrightarrow> nat \<lceil>ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol)) / ln (1 / c)\<rceil> - iter
         < Suc (nat \<lceil>ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol)) / ln (1 / c)\<rceil>) - iter"
    by (smt (z3) Suc_diff_le assms(1,2) fpm_step_lt_tol_at_bound le_Suc_eq lessI tol_pos)
qed

corollary fpm_iter_bnd_local_lt:
  assumes c_nonneg:    "0 \<le> c"
    and c_strict:      "c < 1"
    and tol_pos:       "0 < tol"
    and \<delta>_pos:         "0 < \<delta>"
    and r_is_fixed:    "f r = r"
    and x0_in_ball:    "\<bar>r - x\<^sub>0\<bar> < \<delta>"
    and contractive:   "\<forall>s t. \<bar>s - r\<bar> < \<delta> \<and> \<bar>t - r\<bar> < \<delta> \<longrightarrow> \<bar>f s - f t\<bar> \<le> c * \<bar>s - t\<bar>"
  shows "H[True] fpm(f, x\<^sub>0, tol) [ \<bar>x - r\<bar> \<le> c ^ iter * \<bar>x\<^sub>0 - r\<bar> \<and> \<bar>x_new - x\<bar> < tol
       \<and> iter \<le> Suc (nat \<lceil> ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol)) / ln (1 / c) \<rceil>) ]"
proof -
  have aux: "H[True] fpm_aux(f, x\<^sub>0, tol, c) [ \<bar>x - r\<bar> \<le> c ^ iter * \<bar>x\<^sub>0 - r\<bar> \<and> \<bar>x_new - x\<bar> < tol
       \<and> iter \<le> Suc (nat \<lceil> ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol)) / ln (1 / c) \<rceil>) ]"
    using fpm_aux_iter_bnd_local_lt assms by blast
  then show ?thesis
    by (metis fpm_aux_is_fpm)
qed

lemma fpm_aux_iter_bnd_local_leq:
  fixes f :: "real \<Rightarrow> real"
  assumes c_nonneg:  "0 \<le> c"
      and c_strict:  "c < 1"
      and tol_pos:   "0 < tol"
      and \<delta>_pos:     "0 < \<delta>"
      and r_fixed:   "f r = r"
      and x0_in:     "\<bar>x\<^sub>0 - r\<bar> \<le> \<delta>"
      and contractive: "\<forall>s t. \<bar>s - r\<bar> \<le> \<delta> \<and> \<bar>t - r\<bar> \<le> \<delta> \<longrightarrow> \<bar>f s - f t\<bar> \<le> c * \<bar>s - t\<bar>"
  shows
    "H[True] fpm_aux(f, x\<^sub>0, tol, c)
      [ \<bar>x - r\<bar> \<le> c ^ iter * \<bar>x\<^sub>0 - r\<bar>
        \<and> \<bar>x_new - x\<bar> < tol
        \<and> iter \<le> Suc (nat \<lceil> ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol)) / ln (1 / c) \<rceil>) ]"
proof (vcg)
  fix iter :: nat
  assume step_bound: "\<bar>f ((f ^^ iter) x\<^sub>0) - (f ^^ iter) x\<^sub>0\<bar> \<le> c ^ iter * \<bar>f x\<^sub>0 - x\<^sub>0\<bar>"
  and iter_le_suc:  "iter \<le> Suc (nat \<lceil> ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol)) / ln (1 / c) \<rceil>)"
  and tol_le_step:  "tol \<le> \<bar>f ((f ^^ iter) x\<^sub>0) - (f ^^ iter) x\<^sub>0\<bar>"
  let ?B = "nat \<lceil> ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol)) / ln (1 / c) \<rceil>"
  show "iter \<le> ?B"
  proof (rule ccontr)
    assume "\<not> iter \<le> ?B"
    then have iter_eq: "iter = Suc ?B"
      using iter_le_suc by arith
    have geom_strict: "(c ^ Suc ?B) * \<bar>f x\<^sub>0 - x\<^sub>0\<bar> < tol"
      using fpm_step_lt_tol_at_bound c_nonneg c_strict tol_pos by simp
    have "\<bar>f ((f ^^ iter) x\<^sub>0) - (f ^^ iter) x\<^sub>0\<bar> \<le> c ^ iter * \<bar>f x\<^sub>0 - x\<^sub>0\<bar>"
      using step_bound .
    also have "... = (c ^ Suc ?B) * \<bar>f x\<^sub>0 - x\<^sub>0\<bar>"
      using iter_eq by simp
    also have "... < tol"
      using geom_strict.
    finally have "\<bar>f ((f ^^ iter) x\<^sub>0) - (f ^^ iter) x\<^sub>0\<bar> < tol" .
    with tol_le_step show False
      by linarith
  qed
next
  fix iter :: nat
  assume step_bound: "\<bar>f ((f ^^ iter) x\<^sub>0) - (f ^^ iter) x\<^sub>0\<bar> \<le> c ^ iter * \<bar>f x\<^sub>0 - x\<^sub>0\<bar>"
  and iter_le_bound: "iter \<le> Suc (nat \<lceil> ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol)) / ln (1 / c) \<rceil>)"
  and tol_le_step: "tol \<le> \<bar>f ((f ^^ iter) x\<^sub>0) - (f ^^ iter) x\<^sub>0\<bar>"
  show "\<bar>f (f ((f ^^ iter) x\<^sub>0)) - f ((f ^^ iter) x\<^sub>0)\<bar> \<le> c * c ^ iter * \<bar>f x\<^sub>0 - x\<^sub>0\<bar>"
    using fpm_step_decay[OF c_nonneg c_strict tol_pos \<delta>_pos r_fixed x0_in contractive, of "Suc iter"]
    by simp
next
  fix iter :: nat
  show "\<bar>(f ^^ iter) x\<^sub>0 - r\<bar> \<le> c ^ iter * \<bar>x\<^sub>0 - r\<bar>"
    by (rule fpm_err_decay[OF c_nonneg c_strict tol_pos \<delta>_pos r_fixed x0_in contractive])
next
  show "\<And>iter.
       \<lbrakk> \<bar>f ((f ^^ iter) x\<^sub>0) - (f ^^ iter) x\<^sub>0\<bar> \<le> c ^ iter * \<bar>f x\<^sub>0 - x\<^sub>0\<bar>;
          iter \<le> Suc (nat \<lceil> ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol)) / ln (1 / c) \<rceil>);
          tol \<le> \<bar>f ((f ^^ iter) x\<^sub>0) - (f ^^ iter) x\<^sub>0\<bar> \<rbrakk>
       \<Longrightarrow> nat \<lceil> ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol)) / ln (1 / c) \<rceil> - iter
          < Suc (nat \<lceil> ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol)) / ln (1 / c) \<rceil>) - iter"
    by (smt (z3) Suc_diff_le assms(1,2) fpm_step_lt_tol_at_bound le_Suc_eq lessI tol_pos)
qed

corollary fpm_iter_bnd_local_leq:
  fixes f :: "real \<Rightarrow> real"
  assumes c_nonneg:  "0 \<le> c"
      and c_strict:  "c < 1"
      and tol_pos:   "0 < tol"
      and \<delta>_pos:     "0 < \<delta>"
      and r_fixed:   "f r = r"
      and x0_in:     "\<bar>x\<^sub>0 - r\<bar> \<le> \<delta>"
      and contractive: "\<forall>s t. \<bar>s - r\<bar> \<le> \<delta> \<and> \<bar>t - r\<bar> \<le> \<delta> \<longrightarrow> \<bar>f s - f t\<bar> \<le> c * \<bar>s - t\<bar>"
  shows "H[True] fpm(f, x\<^sub>0, tol)[ \<bar>x - r\<bar> \<le> c ^ iter * \<bar>x\<^sub>0 - r\<bar> \<and> \<bar>x_new - x\<bar> < tol
        \<and> iter \<le> Suc (nat \<lceil> ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol)) / ln (1 / c) \<rceil>) ]"
proof -
  have aux_result:
    "H[True] fpm_aux(f, x\<^sub>0, tol, c)
      [ \<bar>x - r\<bar> \<le> c ^ iter * \<bar>x\<^sub>0 - r\<bar>
        \<and> \<bar>x_new - x\<bar> < tol
        \<and> iter \<le> Suc (nat \<lceil> ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol)) / ln (1 / c) \<rceil>) ]"
    using fpm_aux_iter_bnd_local_leq using assms by blast
  then show ?thesis
    by (metis fpm_aux_is_fpm)
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

lemma fpm_iter_bnd_C1_lt:
  assumes r_fixed   : "f r = r"
      and r_in_U    : "r \<in> U"
      and cont_deriv: "C_k_on 1 f U"
      and f_strict  : "\<bar>deriv f r\<bar> < 1"
      and tol_pos   : "0 < tol"
  shows "\<exists> \<delta> > 0. \<exists> \<epsilon> > 0. (\<forall>(x\<^sub>0 :: real). \<bar>r - x\<^sub>0\<bar> < \<delta> \<longrightarrow>
  H[True] fpm(f, x\<^sub>0, tol) [ \<bar>x - r\<bar> \<le> (1 - \<epsilon>) ^ iter * \<bar>x\<^sub>0 - r\<bar> \<and> \<bar>x_new - x\<bar> < tol
   \<and> iter \<le> Suc (nat \<lceil> ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol)) / ln (1 / (1 - \<epsilon>)) \<rceil>) ])"
proof -
  obtain \<epsilon> \<delta> where
      \<epsilon>_pos: "0 < \<epsilon>"
    and \<epsilon>_lt : "\<epsilon> < 1"
    and \<delta>_pos: "\<delta> > 0"
    and subset: "{r - \<delta><..<r + \<delta>} \<subseteq> U"
    and lip:
      "\<forall>x y. x \<in> {r - \<delta><..<r + \<delta>} \<longrightarrow> y \<in> {x<..<r + \<delta>}
            \<longrightarrow> \<bar>f x - f y\<bar> < (1 - \<epsilon>) * \<bar>x - y\<bar>"
    by (meson r_in_U f_strict cont_deriv contractive_deriv_imp_contra)
  show "\<exists>\<delta>>0. \<exists>\<epsilon>>0. \<forall>x\<^sub>0. \<bar>r - x\<^sub>0\<bar> < \<delta> \<longrightarrow> H[True] fpm (f, x\<^sub>0, tol)
                      [\<bar>x - r\<bar> \<le> (1 - \<epsilon>) ^ st.iter * \<bar>x\<^sub>0 - r\<bar> \<and>
                       \<bar>x_new - x\<bar> < tol \<and> st.iter \<le>
          Suc (nat \<lceil>ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol)) / ln (1 / (1 - \<epsilon>))\<rceil>)]"
  proof (intro exI[where x=\<delta>], intro conjI insert \<delta>_pos)
    show "\<exists>\<epsilon>>0. \<forall>x\<^sub>0. \<bar>r - x\<^sub>0\<bar> < \<delta> \<longrightarrow> H[True] fpm (f, x\<^sub>0, tol)
         [\<bar>x - r\<bar> \<le> (1 - \<epsilon>) ^ st.iter * \<bar>x\<^sub>0 - r\<bar> \<and> \<bar>x_new - x\<bar> < tol \<and>
         st.iter \<le> Suc (nat \<lceil>ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol)) / ln (1 / (1 - \<epsilon>))\<rceil>)]"
    proof (intro exI[where x=\<epsilon>], intro conjI insert \<epsilon>_pos, clarify)
      fix x\<^sub>0
      assume sufficiently_close: "\<bar>r - x\<^sub>0\<bar> < \<delta>"
      show "H[True] fpm(f, x\<^sub>0, tol)
               [\<bar>x - r\<bar> \<le> (1 - \<epsilon>) ^ st.iter * \<bar>x\<^sub>0 - r\<bar> \<and> \<bar>x_new - x\<bar> < tol
                         \<and> st.iter \<le> Suc (nat \<lceil>ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol)) / ln (1 / (1 - \<epsilon>))\<rceil>)]"
      proof (subst fpm_iter_bnd_local_lt[where \<delta> = \<delta>], safe)
        show "0 \<le> 1 - \<epsilon>"  using \<epsilon>_lt by force
        show "1 - \<epsilon> < 1"  using \<epsilon>_pos by force
        show "0 < tol" using tol_pos by force
        show "0 < \<delta>" using \<delta>_pos by auto
        show "f r = r" using r_fixed by auto
        show "\<bar>r - x\<^sub>0\<bar> < \<delta>"  using sufficiently_close by blast
      next
        fix s t
        assume s_near: "\<bar>s - r\<bar> < \<delta>"
        assume t_near: "\<bar>t - r\<bar> < \<delta>"
        have s_dist: "s \<in> {r - \<delta><..<r + \<delta>}"
          using s_near by force
        have t_dist: "t \<in> {r - \<delta><..<r + \<delta>}"
          using t_near by force
        show "\<bar>f s - f t\<bar> \<le> (1 - \<epsilon>) * \<bar>s - t\<bar>"
        proof (cases "t < s")
          case True
          have s_in_right: "s \<in> {t<..<r + \<delta>}"
          proof -
            have "t < s" using True .
            moreover have "s < r + \<delta>"
              using s_dist by simp
            ultimately show ?thesis by simp
          qed
          have step_lt: "\<bar>f t - f s\<bar> < (1 - \<epsilon>) * \<bar>t - s\<bar>"
            using lip t_dist s_in_right by blast
          have "\<bar>f s - f t\<bar> = \<bar>f t - f s\<bar>"
            by (simp add: abs_minus_commute)
          also have "... < (1 - \<epsilon>) * \<bar>t - s\<bar>"
            using step_lt .
          also have "... = (1 - \<epsilon>) * \<bar>s - t\<bar>"
            by (simp add: abs_minus_commute)
          finally show ?thesis
            by (rule less_imp_le)
        next
          assume t_nlt_s: "\<not> t < s"
          show "\<bar>f s - f t\<bar> \<le> (1 - \<epsilon>) * \<bar>s - t\<bar>"
          proof (cases "s = t")
            case True
            then show ?thesis
              by simp
          next
            assume "s \<noteq> t"
            then have s_lt_t: "s < t"
              using t_nlt_s by force
            have t_in_right: "t \<in> {s<..<r + \<delta>}"
            proof -
              have "s < t" using s_lt_t .
              moreover have "t < r + \<delta>"
                using t_dist by simp
              ultimately show ?thesis by simp
            qed
            have step_lt: "\<bar>f s - f t\<bar> < (1 - \<epsilon>) * \<bar>s - t\<bar>"
              using lip s_dist t_in_right by blast
            show ?thesis
              using step_lt by (rule less_imp_le)
          qed
        qed
      qed
    qed
  qed
qed

lemma fpm_known_iter_bnd_C1_leq:
  fixes f :: "real \<Rightarrow> real" and r tol :: real and max_iter :: nat
  assumes r_fixed : "f r = r"
      and r_in_U  : "r \<in> U"
      and C1_on_U : "C_k_on 1 f U"
      and deriv_strict: "\<bar>deriv f r\<bar> < 1"
      and tol_pos: "0 < tol"
  shows
    "\<exists> \<delta> > 0. \<exists> \<epsilon> > 0. (\<forall>(x\<^sub>0 :: real). \<bar>r - x\<^sub>0\<bar> \<le> \<delta> \<longrightarrow>
        H[True] fpm(f, x\<^sub>0, tol)
          [ \<bar>x - r\<bar> \<le> (1 - \<epsilon>) ^ iter * \<bar>x\<^sub>0 - r\<bar>
            \<and> \<bar>x_new - x\<bar> < tol
            \<and> iter \<le> Suc (nat \<lceil> ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol))
                              / ln (1 / (1 - \<epsilon>)) \<rceil>) ])"
proof -
  obtain \<epsilon> \<delta> where
      \<epsilon>_pos : "0 < \<epsilon>"
    and \<epsilon>_lt1: "\<epsilon> < 1"
    and \<delta>_pos : "\<delta> > 0"
    and subset: "{r - \<delta> .. r + \<delta>} \<subseteq> U"
    and lip_ord:
      "\<forall>x y. x \<in> {r - \<delta> .. r + \<delta>} \<longrightarrow> y \<in> {x .. r + \<delta>}
           \<longrightarrow> \<bar>f x - f y\<bar> \<le> (1 - \<epsilon>) * \<bar>x - y\<bar>"
    by (meson C1_on_U r_in_U deriv_strict  contractive_deriv_imp_contra_closed[of f U r 1])
  show "\<exists>\<delta>>0. \<exists>\<epsilon>>0. \<forall>x\<^sub>0. \<bar>r - x\<^sub>0\<bar> \<le> \<delta> \<longrightarrow>
          H[True] fpm (f, x\<^sub>0, tol)
            [ \<bar>x - r\<bar> \<le> (1 - \<epsilon>) ^ st.iter * \<bar>x\<^sub>0 - r\<bar>
              \<and> \<bar>x_new - x\<bar> < tol
              \<and> st.iter \<le> Suc (nat \<lceil> ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol))
                                / ln (1 / (1 - \<epsilon>)) \<rceil>) ]"
  proof (intro exI[where x=\<delta>], intro conjI insert \<delta>_pos)
    show "\<exists>\<epsilon>>0. \<forall>x\<^sub>0. \<bar>r - x\<^sub>0\<bar> \<le> \<delta> \<longrightarrow> H[True] fpm (f, x\<^sub>0, tol)
                [\<bar>x - r\<bar> \<le> (1 - \<epsilon>) ^ st.iter * \<bar>x\<^sub>0 - r\<bar> \<and>
     \<bar>x_new - x\<bar> < tol \<and> st.iter \<le> Suc (nat \<lceil>ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol)) / ln (1 / (1 - \<epsilon>))\<rceil>)]"
    proof (intro exI[where x=\<epsilon>], intro conjI insert \<epsilon>_pos, clarify)
      fix x\<^sub>0
      assume sufficiently_close: "\<bar>r - x\<^sub>0\<bar> \<le> \<delta>"
      show "H[True] fpm (f, x\<^sub>0, tol)
               [\<bar>x - r\<bar> \<le> (1 - \<epsilon>) ^ st.iter * \<bar>x\<^sub>0 - r\<bar> \<and> \<bar>x_new - x\<bar> < tol
              \<and> st.iter \<le> Suc (nat \<lceil>ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol)) / ln (1 / (1 - \<epsilon>))\<rceil>)]"
      proof (subst fpm_iter_bnd_local_leq[where \<delta> = \<delta>], safe)
        show "0 \<le> 1 - \<epsilon>" using \<epsilon>_lt1 by force
        show "1 - \<epsilon> < 1"  using \<epsilon>_pos by force
        show "0 < tol" using tol_pos by force
        show "0 < \<delta>" using \<delta>_pos by auto
        show "f r = r" using r_fixed by auto
        show "\<bar>x\<^sub>0 - r\<bar> \<le> \<delta>"
          using sufficiently_close by linarith
      next
        fix s t
        assume s_near: "\<bar>s - r\<bar> \<le> \<delta>"
        assume t_near: "\<bar>t - r\<bar> \<le> \<delta>"

        have s_mem: "s \<in> {r - \<delta> .. r + \<delta>}"
          using s_near by force
        have t_mem: "t \<in> {r - \<delta> .. r + \<delta>}"
          using t_near by force
        show "\<bar>f s - f t\<bar> \<le> (1 - \<epsilon>) * \<bar>s - t\<bar>"
        proof (cases "s \<le> t")
          case True
          have t_seg: "t \<in> {s .. r + \<delta>}"
          proof -
            have "s \<le> t" using True .
            moreover have "t \<le> r + \<delta>"
              using t_mem by simp
            ultimately show ?thesis
              by simp
          qed
          show ?thesis
            using lip_ord s_mem t_seg by blast
        next
          case False
          then have t_le_s: "t \<le> s"
            by simp
          have s_seg: "s \<in> {t .. r + \<delta>}"
          proof -
            have "t \<le> s" using t_le_s .
            moreover have "s \<le> r + \<delta>"
              using s_mem by simp
            ultimately show ?thesis
              by simp
          qed
          have "\<bar>f t - f s\<bar> \<le> (1 - \<epsilon>) * \<bar>t - s\<bar>"
            using lip_ord t_mem s_seg by blast
          then show ?thesis
            by (simp add: abs_minus_commute)
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

lemma fpm_aux_iter_quadratic_convergence:
  assumes r_fixed   : "f r = r"
      and r_in_U    : "r \<in> U"
      and cont_deriv: "C_k_on 1 f U"
      and der0      : "deriv f r = 0"
      and twice_dff : "k_times_Fr_differentiable_at 2 f r"
      and tol_pos   : "0 < tol"
  shows
    "\<exists>(\<delta> :: real)>0. \<exists>(\<epsilon> :: real)>0.
       (\<forall>x\<^sub>0. \<bar>r - x\<^sub>0\<bar> < \<delta> \<longrightarrow>
          H[True] fpm_aux(f, x\<^sub>0, tol, (1 - \<epsilon>))
            [ \<bar>x - r\<bar> \<le> (((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) ^ (2 ^ iter - 1)) * \<bar>x\<^sub>0 - r\<bar> ^ (2 ^ iter)
              \<and> \<bar>x_new - x\<bar> < tol
              \<and> iter \<le> Suc (nat \<lceil> ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol)) / ln (1 / (1 - \<epsilon>)) \<rceil>) ])"
proof -
  obtain \<epsilon> \<delta>0 where
      \<epsilon>_pos: "0 < \<epsilon>"
    and \<epsilon>_lt: "\<epsilon> < 1"
    and \<delta>0_pos  : "\<delta>0 > 0"
    and subset : "{r - \<delta>0<..<r + \<delta>0} \<subseteq> U"
    and lip    : "\<forall>x y. x \<in> {r-\<delta>0<..<r+\<delta>0} \<longrightarrow> y \<in> {x<..<r+\<delta>0}
                       \<longrightarrow> \<bar>f x - f y\<bar> < (1 - \<epsilon>) * \<bar>x - y\<bar>"
    by (metis abs_0 assms(2,4) cont_deriv contractive_deriv_imp_contra zero_less_one)
  have "(\<lambda>x. peano_remainder (1+1) f r x / (x - r) ^ (1+1)) \<midarrow>r\<rightarrow> 0"
      using Suc_1 twice_dff by (subst Taylor_Peano_remainder, argo, simp)
  then have "(\<lambda>x. (f x - (\<Sum>i\<le>2. (deriv^^i) f r / fact i * (x - r) ^ i)) / (x - r) ^ 2) \<midarrow>r\<rightarrow> 0"
    unfolding peano_remainder_def taylor_poly_def
    by (metis (no_types, lifting) ext Suc_1 Suc_eq_plus1)
  then have "(\<forall>\<epsilon>>0. \<exists>\<delta>>0. \<forall>y. y \<noteq> r \<and> \<bar>y - r\<bar> < \<delta> \<longrightarrow>
  \<bar>(\<lambda>x. (f x - (\<Sum>m\<le>2. (deriv^^m) f r / fact m * (x - r) ^ m)) / (x - r) ^ 2) y - 0\<bar> < \<epsilon>)"
    by (simp add: Limits_Higher_Order_Derivatives.tendsto_at_x_epsilon_def)
  then obtain \<delta>1 where \<delta>1_pos: "\<delta>1 > 0"
    and r0_prop:
    "\<And>x. x \<noteq> r \<Longrightarrow> \<bar>x - r\<bar> < \<delta>1 \<longrightarrow>
         \<bar>(f x - (\<Sum>m\<le>2. (deriv^^m) f r / fact m * (x - r)^m)) / (x - r)^2\<bar> < \<epsilon> / 2"
    using \<epsilon>_pos by (smt (verit, del_insts) half_gt_zero)
  then obtain h :: "real \<Rightarrow> real"
    where h_def: "h = (\<lambda> x. (f x - (\<Sum>m\<le>2. (deriv^^m) f r / fact m * (x - r)^m)) / (x - r)^2)"
    and h_bound: "\<And>x. x \<noteq> r \<Longrightarrow> \<bar>x - r\<bar> < \<delta>1 \<longrightarrow> \<bar>h x\<bar> < \<epsilon> / 2"
    by presburger
  obtain \<delta> where \<delta>_def: "\<delta> = min \<delta>0 \<delta>1"
    by blast
  then have \<delta>_pos: "0 < \<delta>" and \<delta>_leq_\<delta>0: "\<delta> \<le> \<delta>0" and \<delta>_leq_\<delta>1: "\<delta> \<le> \<delta>1"
    using \<delta>0_pos \<delta>1_pos by linarith+
  from lip have contraction: "\<forall>s t. s \<noteq> t \<longrightarrow> \<bar>s-r\<bar> < \<delta> \<longrightarrow> \<bar>t-r\<bar> < \<delta> \<longrightarrow> \<bar>f s - f t\<bar> < (1-\<epsilon>)*\<bar>s-t\<bar>"
    by(rule contraction_ball_closure', (simp add: \<epsilon>_pos \<delta>_pos \<delta>_leq_\<delta>0)+)
  show " \<exists>\<delta>>0. \<exists>\<epsilon>>0. \<forall>x\<^sub>0. \<bar>r - x\<^sub>0\<bar> < \<delta> \<longrightarrow> H[True] fpm_aux (f, x\<^sub>0, tol, 1 - \<epsilon>)
    [\<bar>x - r\<bar> \<le> ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) ^ (2 ^ st.iter - 1) * \<bar>x\<^sub>0 - r\<bar> ^ 2 ^ st.iter \<and>
     \<bar>x_new - x\<bar> < tol \<and> st.iter \<le> Suc (nat \<lceil>ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol)) / ln (1 / (1 - \<epsilon>))\<rceil>)] "
  proof(intro exI[where x=\<delta>], intro conjI insert \<delta>_pos)
    show " \<exists>\<epsilon>>0. \<forall>x\<^sub>0. \<bar>r - x\<^sub>0\<bar> < \<delta> \<longrightarrow> H[True] fpm_aux (f, x\<^sub>0, tol, 1 - \<epsilon>)
    [\<bar>x - r\<bar> \<le> ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) ^ (2 ^ st.iter - 1) * \<bar>x\<^sub>0 - r\<bar> ^ 2 ^ st.iter \<and>
     \<bar>x_new - x\<bar> < tol \<and> st.iter \<le> Suc (nat \<lceil>ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol)) / ln (1 / (1 - \<epsilon>))\<rceil>)]"
    proof(intro exI[where x=\<epsilon>], intro conjI insert \<epsilon>_pos, clarify)
      fix x\<^sub>0 :: real
      assume sufficiently_close: "\<bar>r - x\<^sub>0\<bar> < \<delta>"
      have contractive_iters: "\<forall> (Itr :: nat). \<bar>(f ^^ Itr) x\<^sub>0 - r\<bar> < \<delta>"
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
            by (metis abs_0 cancel_comm_monoid_add_class.diff_cancel
                contraction less_eq_real_def mult.commute mult_zero_left)
        qed
      qed
   show "H[True] fpm_aux (f, x\<^sub>0, tol, 1 - \<epsilon>)
   [\<bar>x - r\<bar> \<le> ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) ^ (2 ^ st.iter - 1) * \<bar>x\<^sub>0 - r\<bar> ^ 2 ^ st.iter \<and>
     \<bar>x_new - x\<bar> < tol \<and> st.iter \<le> Suc (nat \<lceil>ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol)) / ln (1 / (1 - \<epsilon>))\<rceil>)]"
   proof(vcg)
     show "\<And>iter.
       \<lbrakk>\<bar>f ((f ^^ iter) x\<^sub>0) - (f ^^ iter) x\<^sub>0\<bar> \<le> (1 - \<epsilon>) ^ iter * \<bar>f x\<^sub>0 - x\<^sub>0\<bar>;
        iter \<le> Suc (nat \<lceil>ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol)) / ln (1 / (1 - \<epsilon>))\<rceil>); tol \<le> \<bar>f ((f ^^ iter) x\<^sub>0) - (f ^^ iter) x\<^sub>0\<bar>\<rbrakk>
       \<Longrightarrow> iter \<le> nat \<lceil>ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol)) / ln (1 / (1 - \<epsilon>))\<rceil>"
       by (smt (verit, del_insts) \<epsilon>_lt \<epsilon>_pos fpm_step_lt_tol_at_bound le_Suc_eq tol_pos)
     then show "\<And>iter.
       \<lbrakk>\<bar>f ((f ^^ iter) x\<^sub>0) - (f ^^ iter) x\<^sub>0\<bar> \<le> (1 - \<epsilon>) ^ iter * \<bar>f x\<^sub>0 - x\<^sub>0\<bar>;
        iter \<le> Suc (nat \<lceil>ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol)) / ln (1 / (1 - \<epsilon>))\<rceil>); tol \<le> \<bar>f ((f ^^ iter) x\<^sub>0) - (f ^^ iter) x\<^sub>0\<bar>\<rbrakk>
       \<Longrightarrow> nat \<lceil>ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol)) / ln (1 / (1 - \<epsilon>))\<rceil> - iter
           < Suc (nat \<lceil>ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol)) / ln (1 / (1 - \<epsilon>))\<rceil>) - iter"
       using Suc_diff_le less_Suc_eq by presburger
   next
     fix iter :: nat
     assume step_decay: "\<bar>f ((f ^^ iter) x\<^sub>0) - (f ^^ iter) x\<^sub>0\<bar> \<le> (1 - \<epsilon>) ^ iter * \<bar>f x\<^sub>0 - x\<^sub>0\<bar>"
     assume iter_bd:  "iter \<le> Suc (nat \<lceil>ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol)) / ln (1 / (1 - \<epsilon>))\<rceil>)"
     assume tol_le: "tol \<le> \<bar>f ((f ^^ iter) x\<^sub>0) - (f ^^ iter) x\<^sub>0\<bar>"


     have c_nonneg: "0 \<le> 1 - \<epsilon>" using \<epsilon>_pos \<epsilon>_lt by linarith
     have c_lt1: "1 - \<epsilon> < 1" using \<epsilon>_pos by simp
     have x0_in: "\<bar>x\<^sub>0 - r\<bar> < \<delta>" using sufficiently_close by (simp add: abs_minus_commute)
     have contr_le: "\<forall>s t. \<bar>s - r\<bar> < \<delta> \<and> \<bar>t - r\<bar> < \<delta> \<longrightarrow> \<bar>f s - f t\<bar> \<le> (1 - \<epsilon>) * \<bar>s - t\<bar>"
     proof (intro allI impI)
       fix s t assume H: "\<bar>s - r\<bar> < \<delta> \<and> \<bar>t - r\<bar> < \<delta>"
       show "\<bar>f s - f t\<bar> \<le> (1 - \<epsilon>) * \<bar>s - t\<bar>"
       proof (cases "s = t")
         case True thus ?thesis by simp
       next
         case False
         with H contraction have "\<bar>f s - f t\<bar> < (1 - \<epsilon>) * \<bar>s - t\<bar>" by blast
         thus ?thesis by simp
       qed
     qed
     show "\<bar>f (f ((f ^^ iter) x\<^sub>0)) - f ((f ^^ iter) x\<^sub>0)\<bar> \<le> (1 - \<epsilon>) * (1 - \<epsilon>) ^ iter * \<bar>f x\<^sub>0 - x\<^sub>0\<bar>"
       using fpm_step_decay_lt[OF c_nonneg c_lt1 tol_pos \<delta>_pos r_fixed x0_in contr_le, of "Suc iter"]
       by simp
   next
     fix iter :: nat
     assume stop_cond:  "\<not> tol \<le> \<bar>f ((f ^^ iter) x\<^sub>0) - (f ^^ iter) x\<^sub>0\<bar>"
     assume step_decay:  "\<bar>f ((f ^^ iter) x\<^sub>0) - (f ^^ iter) x\<^sub>0\<bar> \<le> (1 - \<epsilon>) ^ iter * \<bar>f x\<^sub>0 - x\<^sub>0\<bar>"
     assume iter_bd:  "iter \<le> Suc (nat \<lceil>ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol)) / ln (1 / (1 - \<epsilon>))\<rceil>)"
     have one_step: "\<forall>(x::real). \<bar>x-r\<bar> < \<delta> \<longrightarrow> \<bar>f(x)-r\<bar> \<le> ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>)/ 2)*\<bar>x-r\<bar>^2"
     proof(clarify)
       fix x :: real
       assume delta_close: "\<bar>x - r\<bar> < \<delta>"
       then have h_bnd:"\<bar>h x\<bar> < \<epsilon> / 2"
          by (smt (verit, del_insts) h_bound \<delta>_leq_\<delta>1 \<epsilon>_pos division_ring_divide_zero
              h_def half_gt_zero mult_cancel_left2 power2_eq_square)
       show "\<bar>f x - r\<bar> \<le> (\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2 * \<bar>x - r\<bar>\<^sup>2"
       proof(cases "x = r")
         show " \<lbrakk>x = r\<rbrakk> \<Longrightarrow> \<bar>f x - r\<bar> \<le> (\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2 * \<bar>x - r\<bar>\<^sup>2"
            by (simp add: assms(1))
       next
         assume x_neq_r: "x \<noteq> r"
         then have pos_dist: "0 < \<bar>x - r\<bar>"
          by auto
         have "f = (\<lambda>x. f r + ((deriv (deriv f) r) / 2) * (x - r)^2 +(x - r)^2 * h x)"
         proof -
           have f_eq: "f = (\<lambda>x. (\<Sum> m \<le> 2. (deriv^^m) f r / fact m * (x-r)^m) + (x-r)^2 *h x)"
             by (auto simp: h_def fun_eq_iff)
           then have "f  =  (\<lambda> x.(\<Sum> m \<le> 1. (deriv^^m) f r / fact m * (x - r)^m)
                                + ((deriv^^2) f r / fact 2 * (x - r)^2)
                                + (x - r)^2 * h x)"
              by (metis (no_types, lifting) Suc_1 sum.atMost_Suc)
           also have "... = (\<lambda> x. ((deriv^^0) f r / fact 0 * (x - r)^0)
                                 + ((deriv^^1) f r / fact 1 * (x - r)^1)
                                 + ((deriv^^2) f r / fact 2 * (x - r)^2)
                                 + (x - r)^2 * h x)"
             by simp
           also have "... = (\<lambda> x.  (f r) + (deriv f r  * (x - r))
                                 + ((deriv (deriv f) r) /  2 * (x - r)^2)
                                 + (x - r)^2 * h x)"
              by (simp add: fun_eq_iff One_nat_def numeral_2_eq_2)
           also have "... =(\<lambda> x. (f r)+((deriv (deriv f) r) /  2 * (x - r)^2) + (x - r)^2 * h x)"
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
    have Inductive_Step: "\<forall> (Itr :: nat). \<bar>(f ^^ Itr) x\<^sub>0 - r\<bar>
            \<le> ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) ^ (2 ^ Itr - Suc 0) * \<bar>x\<^sub>0 - r\<bar> ^ 2 ^ Itr"
    proof(clarify)
      fix Itr :: nat
      show "\<bar>(f ^^ Itr) x\<^sub>0 -r\<bar> \<le> ((\<bar>deriv (deriv f) r\<bar>+\<epsilon>)/2)^(2^Itr - Suc 0)*\<bar>x\<^sub>0 -r\<bar>^2^ Itr"
      proof(induct Itr)
        show "\<bar>(f ^^ 0) x\<^sub>0 - r\<bar> \<le> ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>)/2)^(2^0 - Suc 0)* \<bar>x\<^sub>0 - r\<bar> ^ 2 ^ 0"
          by simp
      next
        fix Itr
        assume IH:  "\<bar>(f ^^ Itr) x\<^sub>0 - r\<bar>
                      \<le> ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2)^ (2 ^ Itr - Suc 0) * \<bar>x\<^sub>0 - r\<bar> ^ 2 ^ Itr"
        have step_eq: "\<bar>(f ^^ Suc Itr) x\<^sub>0 - r\<bar> = \<bar>f ((f ^^ Itr) x\<^sub>0) - r\<bar>"
          by simp
        also have "\<dots> \<le> ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) * \<bar>(f ^^ Itr) x\<^sub>0 - r\<bar>^2"
          using one_step contractive_iters
          by blast
        also have "\<dots> \<le> ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2)
                   * ( ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) ^ (2 ^ Itr - Suc 0)
                   * \<bar>x\<^sub>0 - r\<bar> ^ (2 ^ Itr) ) ^ 2"
          by (smt (z3) IH \<epsilon>_pos field_sum_of_halves mult_left_mono power_less_imp_less_base)
        also have "\<dots> = ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) ^ (1 + 2 * (2 ^ Itr - Suc 0))
                   * \<bar>x\<^sub>0 - r\<bar> ^ (2 * (2 ^ Itr))"
          by (simp add: power_even_eq power_mult_distrib)
        ultimately show "\<bar>(f ^^ Suc Itr) x\<^sub>0 - r\<bar>
             \<le> ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) ^ (2 ^ Suc Itr - Suc 0) * \<bar>x\<^sub>0 - r\<bar> ^ 2 ^ Suc Itr"
          by (smt (verit, ccfv_SIG) Suc_1 Suc_pred bot_nat_0.not_eq_extremum diff_diff_left
              nat.discI nat.simps(1) nat_power_eq_Suc_0_iff plus_1_eq_Suc power_Suc0_right
              power_add power_eq_0_iff power_eq_if right_diff_distrib')
      qed
    qed
    show "\<bar>(f ^^ iter) x\<^sub>0 - r\<bar> \<le> ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) ^ (2 ^ iter - Suc 0) * \<bar>x\<^sub>0 - r\<bar> ^ 2 ^ iter "
      using Inductive_Step by blast
   qed
  qed
 qed
qed

lemma fpm_iter_quadratic_convergence:
  assumes r_fixed   : "f r = r"
      and r_in_U    : "r \<in> U"
      and cont_deriv: "C_k_on 1 f U"
      and der0      : "deriv f r = 0"
      and twice_dff : "k_times_Fr_differentiable_at 2 f r"
      and tol_pos   : "0 < tol"
  shows
    "\<exists>(\<delta> :: real)>0. \<exists>(\<epsilon> :: real)>0.
       (\<forall>x\<^sub>0. \<bar>r - x\<^sub>0\<bar> < \<delta> \<longrightarrow>
          H[True] fpm(f, x\<^sub>0, tol)
            [ \<bar>x - r\<bar> \<le> (((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) ^ (2 ^ iter - 1)) * \<bar>x\<^sub>0 - r\<bar> ^ (2 ^ iter)
              \<and> \<bar>x_new - x\<bar> < tol
              \<and> iter \<le> Suc (nat \<lceil> ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol)) / ln (1 / (1 - \<epsilon>)) \<rceil>) ])"
proof -
  have aux: "\<exists>(\<delta> :: real)>0. \<exists>(\<epsilon> :: real)>0.
       (\<forall>x\<^sub>0. \<bar>r - x\<^sub>0\<bar> < \<delta> \<longrightarrow>
          H[True] fpm_aux(f, x\<^sub>0, tol, (1 - \<epsilon>))
            [ \<bar>x - r\<bar> \<le> (((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) ^ (2 ^ iter - 1)) * \<bar>x\<^sub>0 - r\<bar> ^ (2 ^ iter)
              \<and> \<bar>x_new - x\<bar> < tol
              \<and> iter \<le> Suc (nat \<lceil> ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol)) / ln (1 / (1 - \<epsilon>)) \<rceil>) ])"
    using assms by (rule fpm_aux_iter_quadratic_convergence)

  show ?thesis
  proof -
    obtain \<delta> \<epsilon> where
        \<delta>_pos: "0 < (\<delta>::real)"
      and \<epsilon>_pos: "0 < (\<epsilon>::real)"
      and Haux:
        "\<forall>x\<^sub>0. \<bar>r - x\<^sub>0\<bar> < \<delta> \<longrightarrow>
           H[True] fpm_aux(f, x\<^sub>0, tol, (1 - \<epsilon>))
             [ \<bar>x - r\<bar> \<le> (((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) ^ (2 ^ iter - 1)) * \<bar>x\<^sub>0 - r\<bar> ^ (2 ^ iter)
               \<and> \<bar>x_new - x\<bar> < tol
               \<and> iter \<le> Suc (nat \<lceil> ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol)) / ln (1 / (1 - \<epsilon>)) \<rceil>) ]"
      using aux by blast

    have Hnonaux:
      "\<forall>x\<^sub>0. \<bar>r - x\<^sub>0\<bar> < \<delta> \<longrightarrow>
         H[True] fpm(f, x\<^sub>0, tol)
           [ \<bar>x - r\<bar> \<le> (((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) ^ (2 ^ iter - 1)) * \<bar>x\<^sub>0 - r\<bar> ^ (2 ^ iter)
             \<and> \<bar>x_new - x\<bar> < tol
             \<and> iter \<le> Suc (nat \<lceil> ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol)) / ln (1 / (1 - \<epsilon>)) \<rceil>) ]"
    proof (intro allI impI)
      fix x\<^sub>0 :: real
      assume close: "\<bar>r - x\<^sub>0\<bar> < \<delta>"
      have "H[True] fpm_aux(f, x\<^sub>0, tol, (1 - \<epsilon>))
              [ \<bar>x - r\<bar> \<le> (((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) ^ (2 ^ iter - 1)) * \<bar>x\<^sub>0 - r\<bar> ^ (2 ^ iter)
                \<and> \<bar>x_new - x\<bar> < tol
                \<and> iter \<le> Suc (nat \<lceil> ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol)) / ln (1 / (1 - \<epsilon>)) \<rceil>) ]"
        using Haux close
        by blast
      thus "H[True] fpm(f, x\<^sub>0, tol)
              [ \<bar>x - r\<bar> \<le> (((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) ^ (2 ^ iter - 1)) * \<bar>x\<^sub>0 - r\<bar> ^ (2 ^ iter)
                \<and> \<bar>x_new - x\<bar> < tol
                \<and> iter \<le> Suc (nat \<lceil> ln (max 1 (\<bar>f x\<^sub>0 - x\<^sub>0\<bar> / tol)) / ln (1 / (1 - \<epsilon>)) \<rceil>) ]"
        by (metis fpm_aux_is_fpm)
    qed
    show ?thesis
      using aux fpm_aux_is_fpm by auto
  qed
qed

section \<open>Paradigm B: Lammich's Refinement Framework (\<open>nres\<close>)\<close>

text \<open>The same fixed-point loop, expressed in Lammich's Refinement Framework as a
  single tail-recursive \<open>WHILET\<close> over the state \<open>(xc, xn, k)\<close> --- the current
  iterate \<open>xc\<close>, the next iterate \<open>xn = f xc\<close>, and the step counter \<open>k\<close>.  (We avoid
  the names \<open>x\<close>, \<open>x_new\<close>, \<open>iter\<close> here because those are field selectors of the
  \<open>st\<close> alphabet used by Paradigm A.)  Correctness is a \<open>\<le> SPEC\<close> statement
  discharged by \<open>WHILET_rule\<close>; the loop invariant, variant and \<^emph>\<open>all\<close> of the
  underlying contraction mathematics are exactly those used on the VCG side ---
  only the loop glue differs.\<close>

subsection \<open>Algorithm (\<open>nres\<close>)\<close>

definition R_fpm :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real \<times> real \<times> nat) nres" where
  "R_fpm f x0 tol \<equiv>
     WHILET (\<lambda>(xc, xn, k). tol \<le> \<bar>xn - xc\<bar>)
            (\<lambda>(xc, xn, k). RETURN (xn, f xn, k + 1))
            (x0, f x0, 0)"

text \<open>The exit iteration budget, identical to the one used by the VCG variant.\<close>

definition fpm_bound :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat" where
  "fpm_bound f x0 tol c = nat \<lceil> ln (max 1 (\<bar>f x0 - x0\<bar> / tol)) / ln (1 / c) \<rceil>"

text \<open>The loop invariant: \<open>xc\<close> is the \<open>k\<close>-th iterate, \<open>xn\<close> its image, the current
  step is geometrically small, and the counter is within budget.  It mirrors the
  \<open>invariant\<close> annotation of the VCG program \<^term>\<open>fpm_aux\<close> and is independent of
  the fixed point \<open>r\<close>, so it serves all three convergence regimes.\<close>

definition fpm_invar :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real \<times> real \<times> nat) \<Rightarrow> bool" where
  "fpm_invar f x0 tol c \<equiv> \<lambda>(xc, xn, k).
       xc = (f ^^ k) x0
     \<and> xn = f xc
     \<and> \<bar>xn - xc\<bar> \<le> c ^ k * \<bar>f x0 - x0\<bar>
     \<and> k \<le> Suc (fpm_bound f x0 tol c)"

subsection \<open>Loop bookkeeping (no contraction needed)\<close>

lemma fpm_invar_init: "fpm_invar f x0 tol c (x0, f x0, 0)"
  by (simp add: fpm_invar_def)

lemma fpm_exit:
  assumes "fpm_invar f x0 tol c (xc, xn, k)" and "\<not> tol \<le> \<bar>xn - xc\<bar>"
  shows "xc = (f ^^ k) x0 \<and> xn = f xc \<and> \<bar>xn - xc\<bar> < tol \<and> k \<le> Suc (fpm_bound f x0 tol c)"
  using assms by (auto simp: fpm_invar_def)

text \<open>While the guard holds, the counter is strictly within budget --- the same
  geometric argument (\<open>fpm_step_lt_tol_at_bound\<close>) the VCG variant uses to
  prove termination.\<close>

lemma fpm_iter_le_bound:
  assumes c_nonneg: "0 \<le> c" and c_strict: "c < 1" and tol_pos: "0 < tol"
    and inv: "fpm_invar f x0 tol c (xc, xn, k)"
    and looping: "tol \<le> \<bar>xn - xc\<bar>"
  shows "k \<le> fpm_bound f x0 tol c"
proof (rule ccontr)
  let ?B = "fpm_bound f x0 tol c"
  assume "\<not> k \<le> ?B"
  with inv have k_eq: "k = Suc ?B" by (auto simp: fpm_invar_def)
  from inv have step_bnd: "\<bar>xn - xc\<bar> \<le> c ^ k * \<bar>f x0 - x0\<bar>" by (auto simp: fpm_invar_def)
  have geom: "(c ^ Suc ?B) * \<bar>f x0 - x0\<bar> < tol"
  proof -
    have "(c ^ Suc (nat \<lceil>ln (max 1 (\<bar>f x0 - x0\<bar> / tol)) / ln (1 / c)\<rceil>)) * \<bar>f x0 - x0\<bar> < tol"
      by (rule fpm_step_lt_tol_at_bound[OF abs_ge_zero c_nonneg c_strict tol_pos])
    thus ?thesis by (simp only: fpm_bound_def)
  qed
  from step_bnd k_eq have "\<bar>xn - xc\<bar> \<le> (c ^ Suc ?B) * \<bar>f x0 - x0\<bar>" by simp
  with geom looping show False by linarith
qed

subsection \<open>Loop correctness under a closed-ball local contraction (Lammich glue)\<close>

text \<open>The Lammich loop glue for the closed-ball regime: one step preserves the
  invariant and decreases the variant, and the \<open>WHILET\<close> meets its exit \<open>SPEC\<close>.  The
  per-iteration decay it relies on (\<open>fpm_step_decay\<close>) is proved once above and only
  cited here --- this is exactly the math the VCG core cites too.\<close>

context
  fixes f :: "real \<Rightarrow> real" and r x0 tol c \<delta> :: real
  assumes c_nonneg: "0 \<le> c" and c_strict: "c < 1" and tol_pos: "0 < tol"
    and \<delta>_pos: "0 < \<delta>" and r_fixed: "f r = r" and x0_in: "\<bar>x0 - r\<bar> \<le> \<delta>"
    and contractive: "\<forall>s t. \<bar>s - r\<bar> \<le> \<delta> \<and> \<bar>t - r\<bar> \<le> \<delta> \<longrightarrow> \<bar>f s - f t\<bar> \<le> c * \<bar>s - t\<bar>"
begin

lemma fpm_invar_step:
  assumes inv: "fpm_invar f x0 tol c (xc, xn, k)" and looping: "tol \<le> \<bar>xn - xc\<bar>"
  shows "fpm_invar f x0 tol c (xn, f xn, k + 1)
       \<and> ((xn, f xn, k + 1), (xc, xn, k))
           \<in> Wellfounded.measure (\<lambda>(xc, xn, k). Suc (fpm_bound f x0 tol c) - k)"
proof -
  let ?B = "fpm_bound f x0 tol c"
  from inv have xc_eq: "xc = (f ^^ k) x0" and xn_eq: "xn = f xc"
    by (auto simp: fpm_invar_def)
  have k_le: "k \<le> ?B" using fpm_iter_le_bound[OF c_nonneg c_strict tol_pos inv looping] .
  have xn_eq': "xn = (f ^^ (k + 1)) x0" using xc_eq xn_eq by simp
  have step3: "\<bar>f xn - xn\<bar> \<le> c ^ (k + 1) * \<bar>f x0 - x0\<bar>"
    using fpm_step_decay[OF c_nonneg c_strict tol_pos \<delta>_pos r_fixed x0_in contractive, of "k + 1"]
          xn_eq' by simp
  have inv': "fpm_invar f x0 tol c (xn, f xn, k + 1)"
    using xn_eq' step3 k_le by (simp add: fpm_invar_def)
  have var: "((xn, f xn, k + 1), (xc, xn, k)) \<in> Wellfounded.measure (\<lambda>(xc, xn, k). Suc ?B - k)"
    using k_le by (simp add: in_measure)
  show ?thesis using inv' var by blast
qed

text \<open>Generic loop correctness: the program computes the \<open>k\<close>-th iterate, stops with
  a sub-tolerance step, and within budget.  Each convergence theorem below merely
  post-composes a (universal) error bound onto this via \<open>weaken_SPEC\<close>.\<close>

lemma R_fpm_loop:
  "R_fpm f x0 tol \<le> SPEC (\<lambda>(xc, xn, k). xc = (f ^^ k) x0 \<and> xn = f xc
        \<and> \<bar>xn - xc\<bar> < tol \<and> k \<le> Suc (fpm_bound f x0 tol c))"
  unfolding R_fpm_def
  apply (refine_vcg WHILET_rule[where I = "fpm_invar f x0 tol c"
            and R = "Wellfounded.measure (\<lambda>(xc, xn, k). Suc (fpm_bound f x0 tol c) - k)"])
  subgoal by simp
  subgoal by (simp add: fpm_invar_def)
  subgoal for s using fpm_invar_step by (cases s) (auto simp: in_measure)
  subgoal for s using fpm_invar_step by (cases s) (auto simp: in_measure)
  subgoal for s using fpm_exit by (cases s) auto
  subgoal for s using fpm_exit by (cases s) auto
  subgoal for s using fpm_exit by (cases s) auto
  subgoal for s using fpm_exit by (cases s) auto
  done

end

subsection \<open>Loop correctness under an open-ball local contraction (Lammich glue)\<close>

text \<open>The strict / open-ball analogue of the previous block (used for the quadratic
  regime), citing the shared \<open>fpm_step_decay_lt\<close>.\<close>

context
  fixes f :: "real \<Rightarrow> real" and r x0 tol c \<delta> :: real
  assumes c_nonneg: "0 \<le> c" and c_strict: "c < 1" and tol_pos: "0 < tol"
    and \<delta>_pos: "0 < \<delta>" and r_fixed: "f r = r" and x0_in: "\<bar>x0 - r\<bar> < \<delta>"
    and contractive: "\<forall>s t. \<bar>s - r\<bar> < \<delta> \<and> \<bar>t - r\<bar> < \<delta> \<longrightarrow> \<bar>f s - f t\<bar> \<le> c * \<bar>s - t\<bar>"
begin

lemma fpm_invar_step_lt:
  assumes inv: "fpm_invar f x0 tol c (xc, xn, k)" and looping: "tol \<le> \<bar>xn - xc\<bar>"
  shows "fpm_invar f x0 tol c (xn, f xn, k + 1)
       \<and> ((xn, f xn, k + 1), (xc, xn, k))
           \<in> Wellfounded.measure (\<lambda>(xc, xn, k). Suc (fpm_bound f x0 tol c) - k)"
proof -
  let ?B = "fpm_bound f x0 tol c"
  from inv have xc_eq: "xc = (f ^^ k) x0" and xn_eq: "xn = f xc"
    by (auto simp: fpm_invar_def)
  have k_le: "k \<le> ?B" using fpm_iter_le_bound[OF c_nonneg c_strict tol_pos inv looping] .
  have xn_eq': "xn = (f ^^ (k + 1)) x0" using xc_eq xn_eq by simp
  have step3: "\<bar>f xn - xn\<bar> \<le> c ^ (k + 1) * \<bar>f x0 - x0\<bar>"
    using fpm_step_decay_lt[OF c_nonneg c_strict tol_pos \<delta>_pos r_fixed x0_in contractive, of "k + 1"]
          xn_eq' by simp
  have inv': "fpm_invar f x0 tol c (xn, f xn, k + 1)"
    using xn_eq' step3 k_le by (simp add: fpm_invar_def)
  have var: "((xn, f xn, k + 1), (xc, xn, k)) \<in> Wellfounded.measure (\<lambda>(xc, xn, k). Suc ?B - k)"
    using k_le by (simp add: in_measure)
  show ?thesis using inv' var by blast
qed

lemma R_fpm_loop_lt:
  "R_fpm f x0 tol \<le> SPEC (\<lambda>(xc, xn, k). xc = (f ^^ k) x0 \<and> xn = f xc
        \<and> \<bar>xn - xc\<bar> < tol \<and> k \<le> Suc (fpm_bound f x0 tol c))"
  unfolding R_fpm_def
  apply (refine_vcg WHILET_rule[where I = "fpm_invar f x0 tol c"
            and R = "Wellfounded.measure (\<lambda>(xc, xn, k). Suc (fpm_bound f x0 tol c) - k)"])
  subgoal by simp
  subgoal by (simp add: fpm_invar_def)
  subgoal for s using fpm_invar_step_lt by (cases s) (auto simp: in_measure)
  subgoal for s using fpm_invar_step_lt by (cases s) (auto simp: in_measure)
  subgoal for s using fpm_exit by (cases s) auto
  subgoal for s using fpm_exit by (cases s) auto
  subgoal for s using fpm_exit by (cases s) auto
  subgoal for s using fpm_exit by (cases s) auto
  done

end

subsection \<open>Local linear contraction (mirrors \<open>fpm_iter_bnd_local_leq\<close>)\<close>

theorem R_fpm_iter_bnd_local_leq:
  fixes f :: "real \<Rightarrow> real" and r x0 tol c \<delta> :: real
  assumes c_nonneg: "0 \<le> c" and c_strict: "c < 1" and tol_pos: "0 < tol"
    and \<delta>_pos: "0 < \<delta>" and r_fixed: "f r = r" and x0_in: "\<bar>x0 - r\<bar> \<le> \<delta>"
    and contractive: "\<forall>s t. \<bar>s - r\<bar> \<le> \<delta> \<and> \<bar>t - r\<bar> \<le> \<delta> \<longrightarrow> \<bar>f s - f t\<bar> \<le> c * \<bar>s - t\<bar>"
  shows "R_fpm f x0 tol \<le> SPEC (\<lambda>(xc, xn, k). \<bar>xc - r\<bar> \<le> c ^ k * \<bar>x0 - r\<bar> \<and> \<bar>xn - xc\<bar> < tol
            \<and> k \<le> Suc (nat \<lceil> ln (max 1 (\<bar>f x0 - x0\<bar> / tol)) / ln (1 / c) \<rceil>))"
proof -
  have loop: "R_fpm f x0 tol \<le> SPEC (\<lambda>(xc, xn, k). xc = (f ^^ k) x0 \<and> xn = f xc
        \<and> \<bar>xn - xc\<bar> < tol \<and> k \<le> Suc (fpm_bound f x0 tol c))"
    using R_fpm_loop[OF c_nonneg c_strict tol_pos \<delta>_pos r_fixed x0_in contractive] .
  show ?thesis
  proof (rule weaken_SPEC[OF loop])
    fix s :: "real \<times> real \<times> nat"
    obtain xc xn k where s_eq: "s = (xc, xn, k)" by (cases s)
    assume "case s of (xc, xn, k) \<Rightarrow> xc = (f ^^ k) x0 \<and> xn = f xc \<and> \<bar>xn - xc\<bar> < tol
              \<and> k \<le> Suc (fpm_bound f x0 tol c)"
    then have A: "xc = (f ^^ k) x0" "\<bar>xn - xc\<bar> < tol" "k \<le> Suc (fpm_bound f x0 tol c)"
      by (auto simp: s_eq)
    have err: "\<bar>xc - r\<bar> \<le> c ^ k * \<bar>x0 - r\<bar>"
      using A(1) fpm_err_decay[OF c_nonneg c_strict tol_pos \<delta>_pos r_fixed x0_in contractive, of k]
      by simp
    show "case s of (xc, xn, k) \<Rightarrow> \<bar>xc - r\<bar> \<le> c ^ k * \<bar>x0 - r\<bar> \<and> \<bar>xn - xc\<bar> < tol
            \<and> k \<le> Suc (nat \<lceil> ln (max 1 (\<bar>f x0 - x0\<bar> / tol)) / ln (1 / c) \<rceil>)"
      using err A(2) A(3) by (simp add: s_eq fpm_bound_def)
  qed
qed

subsection \<open>C1 corollary (mirrors \<open>fpm_known_iter_bnd_C1_leq\<close>)\<close>

theorem R_fpm_known_iter_bnd_C1_leq:
  fixes f :: "real \<Rightarrow> real" and r tol :: real
  assumes r_fixed: "f r = r" and r_in_U: "r \<in> U" and C1_on_U: "C_k_on 1 f U"
    and deriv_strict: "\<bar>deriv f r\<bar> < 1" and tol_pos: "0 < tol"
  shows "\<exists>\<delta>>0. \<exists>\<epsilon>>0. (\<forall>x0. \<bar>r - x0\<bar> \<le> \<delta> \<longrightarrow>
      R_fpm f x0 tol \<le> SPEC (\<lambda>(xc, xn, k). \<bar>xc - r\<bar> \<le> (1 - \<epsilon>) ^ k * \<bar>x0 - r\<bar> \<and> \<bar>xn - xc\<bar> < tol
        \<and> k \<le> Suc (nat \<lceil> ln (max 1 (\<bar>f x0 - x0\<bar> / tol)) / ln (1 / (1 - \<epsilon>)) \<rceil>)))"
proof -
  obtain \<epsilon> \<delta> where
      \<epsilon>_pos: "0 < \<epsilon>" and \<epsilon>_lt1: "\<epsilon> < 1" and \<delta>_pos: "\<delta> > 0"
    and subset: "{r - \<delta> .. r + \<delta>} \<subseteq> U"
    and lip_ord: "\<forall>x y. x \<in> {r - \<delta> .. r + \<delta>} \<longrightarrow> y \<in> {x .. r + \<delta>} \<longrightarrow> \<bar>f x - f y\<bar> \<le> (1 - \<epsilon>) * \<bar>x - y\<bar>"
    by (meson C1_on_U r_in_U deriv_strict contractive_deriv_imp_contra_closed[of f U r 1])
  have main: "\<forall>x0. \<bar>r - x0\<bar> \<le> \<delta> \<longrightarrow>
      R_fpm f x0 tol \<le> SPEC (\<lambda>(xc, xn, k). \<bar>xc - r\<bar> \<le> (1 - \<epsilon>) ^ k * \<bar>x0 - r\<bar> \<and> \<bar>xn - xc\<bar> < tol
        \<and> k \<le> Suc (nat \<lceil> ln (max 1 (\<bar>f x0 - x0\<bar> / tol)) / ln (1 / (1 - \<epsilon>)) \<rceil>))"
  proof (intro allI impI)
    fix x0 :: real assume close: "\<bar>r - x0\<bar> \<le> \<delta>"
    have contr_sym: "\<forall>s t. \<bar>s - r\<bar> \<le> \<delta> \<and> \<bar>t - r\<bar> \<le> \<delta> \<longrightarrow> \<bar>f s - f t\<bar> \<le> (1 - \<epsilon>) * \<bar>s - t\<bar>"
    proof (intro allI impI)
      fix s t assume "\<bar>s - r\<bar> \<le> \<delta> \<and> \<bar>t - r\<bar> \<le> \<delta>"
      then have s_near: "\<bar>s - r\<bar> \<le> \<delta>" and t_near: "\<bar>t - r\<bar> \<le> \<delta>" by auto
      have s_mem: "s \<in> {r - \<delta> .. r + \<delta>}" using s_near by force
      have t_mem: "t \<in> {r - \<delta> .. r + \<delta>}" using t_near by force
      show "\<bar>f s - f t\<bar> \<le> (1 - \<epsilon>) * \<bar>s - t\<bar>"
      proof (cases "s \<le> t")
        case True
        have "t \<in> {s .. r + \<delta>}" using True t_mem by simp
        thus ?thesis using lip_ord s_mem by blast
      next
        case False
        then have "s \<in> {t .. r + \<delta>}" using s_mem by simp
        then have "\<bar>f t - f s\<bar> \<le> (1 - \<epsilon>) * \<bar>t - s\<bar>" using lip_ord t_mem by blast
        thus ?thesis by (simp add: abs_minus_commute)
      qed
    qed
    have x0_in: "\<bar>x0 - r\<bar> \<le> \<delta>" using close by (simp add: abs_minus_commute)
    show "R_fpm f x0 tol \<le> SPEC (\<lambda>(xc, xn, k). \<bar>xc - r\<bar> \<le> (1 - \<epsilon>) ^ k * \<bar>x0 - r\<bar> \<and> \<bar>xn - xc\<bar> < tol
          \<and> k \<le> Suc (nat \<lceil> ln (max 1 (\<bar>f x0 - x0\<bar> / tol)) / ln (1 / (1 - \<epsilon>)) \<rceil>))"
      by (rule R_fpm_iter_bnd_local_leq[where \<delta> = \<delta>])
         (use \<epsilon>_pos \<epsilon>_lt1 tol_pos \<delta>_pos r_fixed x0_in contr_sym in auto)
  qed
  show ?thesis using \<delta>_pos \<epsilon>_pos main by blast
qed

subsection \<open>Quadratic convergence (mirrors \<open>fpm_iter_quadratic_convergence\<close>)\<close>

text \<open>When \<open>f'(r) = 0\<close> (and \<open>f\<close> is twice differentiable at \<open>r\<close>) the iteration
  converges quadratically.  The Taylor-with-Peano-remainder argument that yields
  the per-step bound \<open>\<bar>f x - r\<bar> \<le> ((\<bar>f''(r)\<bar> + \<epsilon>)/2) \<bar>x - r\<bar>\<^sup>2\<close> and the squaring
  induction are exactly those of the VCG proof; only the loop is now discharged by
  \<open>R_fpm_loop_lt\<close> and \<open>weaken_SPEC\<close> instead of \<open>vcg\<close>.\<close>

theorem R_fpm_iter_quadratic_convergence:
  fixes f :: "real \<Rightarrow> real" and r tol :: real
  assumes r_fixed: "f r = r" and r_in_U: "r \<in> U" and cont_deriv: "C_k_on 1 f U"
    and der0: "deriv f r = 0" and twice_dff: "k_times_Fr_differentiable_at 2 f r" and tol_pos: "0 < tol"
  shows "\<exists>(\<delta>::real)>0. \<exists>(\<epsilon>::real)>0. (\<forall>x0. \<bar>r - x0\<bar> < \<delta> \<longrightarrow>
      R_fpm f x0 tol \<le> SPEC (\<lambda>(xc, xn, k).
            \<bar>xc - r\<bar> \<le> ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) ^ (2 ^ k - 1) * \<bar>x0 - r\<bar> ^ (2 ^ k)
          \<and> \<bar>xn - xc\<bar> < tol
          \<and> k \<le> Suc (nat \<lceil> ln (max 1 (\<bar>f x0 - x0\<bar> / tol)) / ln (1 / (1 - \<epsilon>)) \<rceil>)))"
proof -
  obtain \<epsilon> \<delta>0 where
      \<epsilon>_pos: "0 < \<epsilon>" and \<epsilon>_lt: "\<epsilon> < 1" and \<delta>0_pos: "\<delta>0 > 0"
    and subset: "{r - \<delta>0<..<r + \<delta>0} \<subseteq> U"
    and lip: "\<forall>x y. x \<in> {r-\<delta>0<..<r+\<delta>0} \<longrightarrow> y \<in> {x<..<r+\<delta>0} \<longrightarrow> \<bar>f x - f y\<bar> < (1 - \<epsilon>) * \<bar>x - y\<bar>"
    by (metis abs_0 r_in_U der0 cont_deriv contractive_deriv_imp_contra zero_less_one)
  have "(\<lambda>x. peano_remainder (1+1) f r x / (x - r) ^ (1+1)) \<midarrow>r\<rightarrow> 0"
      using Suc_1 twice_dff by (subst Taylor_Peano_remainder, argo, simp)
  then have "(\<lambda>x. (f x - (\<Sum>i\<le>2. (deriv^^i) f r / fact i * (x - r) ^ i)) / (x - r) ^ 2) \<midarrow>r\<rightarrow> 0"
    unfolding peano_remainder_def taylor_poly_def
    by (metis (no_types, lifting) ext Suc_1 Suc_eq_plus1)
  then have "(\<forall>\<epsilon>>0. \<exists>\<delta>>0. \<forall>y. y \<noteq> r \<and> \<bar>y - r\<bar> < \<delta> \<longrightarrow>
  \<bar>(\<lambda>x. (f x - (\<Sum>m\<le>2. (deriv^^m) f r / fact m * (x - r) ^ m)) / (x - r) ^ 2) y - 0\<bar> < \<epsilon>)"
    by (simp add: Limits_Higher_Order_Derivatives.tendsto_at_x_epsilon_def)
  then obtain \<delta>1 where \<delta>1_pos: "\<delta>1 > 0"
    and r0_prop:
    "\<And>x. x \<noteq> r \<Longrightarrow> \<bar>x - r\<bar> < \<delta>1 \<longrightarrow>
         \<bar>(f x - (\<Sum>m\<le>2. (deriv^^m) f r / fact m * (x - r)^m)) / (x - r)^2\<bar> < \<epsilon> / 2"
    using \<epsilon>_pos by (smt (verit, del_insts) half_gt_zero)
  then obtain h :: "real \<Rightarrow> real"
    where h_def: "h = (\<lambda> x. (f x - (\<Sum>m\<le>2. (deriv^^m) f r / fact m * (x - r)^m)) / (x - r)^2)"
    and h_bound: "\<And>x. x \<noteq> r \<Longrightarrow> \<bar>x - r\<bar> < \<delta>1 \<longrightarrow> \<bar>h x\<bar> < \<epsilon> / 2"
    by presburger
  obtain \<delta> where \<delta>_def: "\<delta> = min \<delta>0 \<delta>1"
    by blast
  then have \<delta>_pos: "0 < \<delta>" and \<delta>_leq_\<delta>0: "\<delta> \<le> \<delta>0" and \<delta>_leq_\<delta>1: "\<delta> \<le> \<delta>1"
    using \<delta>0_pos \<delta>1_pos by linarith+
  from lip have contraction: "\<forall>s t. s \<noteq> t \<longrightarrow> \<bar>s-r\<bar> < \<delta> \<longrightarrow> \<bar>t-r\<bar> < \<delta> \<longrightarrow> \<bar>f s - f t\<bar> < (1-\<epsilon>)*\<bar>s-t\<bar>"
    by (rule contraction_ball_closure', (simp add: \<epsilon>_pos \<delta>_pos \<delta>_leq_\<delta>0)+)
  have c_nonneg: "0 \<le> 1 - \<epsilon>" using \<epsilon>_lt by simp
  have c_lt1: "1 - \<epsilon> < 1" using \<epsilon>_pos by simp
  have contr_le: "\<forall>s t. \<bar>s - r\<bar> < \<delta> \<and> \<bar>t - r\<bar> < \<delta> \<longrightarrow> \<bar>f s - f t\<bar> \<le> (1 - \<epsilon>) * \<bar>s - t\<bar>"
  proof (intro allI impI)
    fix s t assume H: "\<bar>s - r\<bar> < \<delta> \<and> \<bar>t - r\<bar> < \<delta>"
    show "\<bar>f s - f t\<bar> \<le> (1 - \<epsilon>) * \<bar>s - t\<bar>"
    proof (cases "s = t")
      case True thus ?thesis by simp
    next
      case False
      with H contraction have "\<bar>f s - f t\<bar> < (1 - \<epsilon>) * \<bar>s - t\<bar>" by blast
      thus ?thesis by simp
    qed
  qed
  have one_step: "\<forall>(x::real). \<bar>x-r\<bar> < \<delta> \<longrightarrow> \<bar>f(x)-r\<bar> \<le> ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>)/ 2)*\<bar>x-r\<bar>^2"
  proof(clarify)
    fix x :: real
    assume delta_close: "\<bar>x - r\<bar> < \<delta>"
    then have h_bnd:"\<bar>h x\<bar> < \<epsilon> / 2"
       by (smt (verit, del_insts) h_bound \<delta>_leq_\<delta>1 \<epsilon>_pos division_ring_divide_zero
           h_def half_gt_zero mult_cancel_left2 power2_eq_square)
    show "\<bar>f x - r\<bar> \<le> (\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2 * \<bar>x - r\<bar>\<^sup>2"
    proof(cases "x = r")
      show " \<lbrakk>x = r\<rbrakk> \<Longrightarrow> \<bar>f x - r\<bar> \<le> (\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2 * \<bar>x - r\<bar>\<^sup>2"
         by (simp add: r_fixed)
    next
      assume x_neq_r: "x \<noteq> r"
      then have pos_dist: "0 < \<bar>x - r\<bar>"
       by auto
      have "f = (\<lambda>x. f r + ((deriv (deriv f) r) / 2) * (x - r)^2 +(x - r)^2 * h x)"
      proof -
        have f_eq: "f = (\<lambda>x. (\<Sum> m \<le> 2. (deriv^^m) f r / fact m * (x-r)^m) + (x-r)^2 *h x)"
          by (auto simp: h_def fun_eq_iff)
        then have "f  =  (\<lambda> x.(\<Sum> m \<le> 1. (deriv^^m) f r / fact m * (x - r)^m)
                             + ((deriv^^2) f r / fact 2 * (x - r)^2)
                             + (x - r)^2 * h x)"
           by (metis (no_types, lifting) Suc_1 sum.atMost_Suc)
        also have "... = (\<lambda> x. ((deriv^^0) f r / fact 0 * (x - r)^0)
                              + ((deriv^^1) f r / fact 1 * (x - r)^1)
                              + ((deriv^^2) f r / fact 2 * (x - r)^2)
                              + (x - r)^2 * h x)"
          by simp
        also have "... = (\<lambda> x.  (f r) + (deriv f r  * (x - r))
                              + ((deriv (deriv f) r) /  2 * (x - r)^2)
                              + (x - r)^2 * h x)"
           by (simp add: fun_eq_iff One_nat_def numeral_2_eq_2)
        also have "... =(\<lambda> x. (f r)+((deriv (deriv f) r) /  2 * (x - r)^2) + (x - r)^2 * h x)"
           by (simp add: der0)
        finally show ?thesis.
      qed
      then have "f x - r = ((deriv (deriv f) r) / 2 + h x) * (x - r)^2"
        by (smt (verit, best) Groups.mult_ac(2) r_fixed right_diff_distrib')
      then have abs_fx: "\<bar>f x - r\<bar> = \<bar>(deriv (deriv f) r) / 2 + h x\<bar> * \<bar>x - r\<bar>^2"
        by (simp add: abs_mult)
      also have "... \<le> (\<bar>deriv (deriv f) r\<bar> / 2 + \<bar>h x\<bar>)  * \<bar>x - r\<bar>^2"
        by (simp add: mult_right_mono)
      also have "... \<le> (\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2 * \<bar>x - r\<bar>\<^sup>2"
        using h_bnd pos_dist by auto
      finally show ?thesis.
   qed
  qed
  have main: "\<forall>x0. \<bar>r - x0\<bar> < \<delta> \<longrightarrow>
      R_fpm f x0 tol \<le> SPEC (\<lambda>(xc, xn, k).
            \<bar>xc - r\<bar> \<le> ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) ^ (2 ^ k - 1) * \<bar>x0 - r\<bar> ^ (2 ^ k)
          \<and> \<bar>xn - xc\<bar> < tol
          \<and> k \<le> Suc (nat \<lceil> ln (max 1 (\<bar>f x0 - x0\<bar> / tol)) / ln (1 / (1 - \<epsilon>)) \<rceil>))"
  proof (intro allI impI)
    fix x0 :: real assume sufficiently_close: "\<bar>r - x0\<bar> < \<delta>"
    have x0_in: "\<bar>x0 - r\<bar> < \<delta>" using sufficiently_close by (simp add: abs_minus_commute)
    have contractive_iters: "\<forall>Itr. \<bar>(f ^^ Itr) x0 - r\<bar> < \<delta>"
      using fpm_iters_in_ball[OF c_nonneg c_lt1 tol_pos \<delta>_pos r_fixed x0_in contr_le] by blast
    have Inductive_Step: "\<forall> (Itr :: nat). \<bar>(f ^^ Itr) x0 - r\<bar>
            \<le> ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) ^ (2 ^ Itr - Suc 0) * \<bar>x0 - r\<bar> ^ 2 ^ Itr"
    proof(clarify)
      fix Itr :: nat
      show "\<bar>(f ^^ Itr) x0 -r\<bar> \<le> ((\<bar>deriv (deriv f) r\<bar>+\<epsilon>)/2)^(2^Itr - Suc 0)*\<bar>x0 -r\<bar>^2^ Itr"
      proof(induct Itr)
        show "\<bar>(f ^^ 0) x0 - r\<bar> \<le> ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>)/2)^(2^0 - Suc 0)* \<bar>x0 - r\<bar> ^ 2 ^ 0"
          by simp
      next
        fix Itr
        assume IH:  "\<bar>(f ^^ Itr) x0 - r\<bar>
                      \<le> ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2)^ (2 ^ Itr - Suc 0) * \<bar>x0 - r\<bar> ^ 2 ^ Itr"
        have step_eq: "\<bar>(f ^^ Suc Itr) x0 - r\<bar> = \<bar>f ((f ^^ Itr) x0) - r\<bar>"
          by simp
        also have "\<dots> \<le> ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) * \<bar>(f ^^ Itr) x0 - r\<bar>^2"
          using one_step contractive_iters
          by blast
        also have "\<dots> \<le> ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2)
                   * ( ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) ^ (2 ^ Itr - Suc 0)
                   * \<bar>x0 - r\<bar> ^ (2 ^ Itr) ) ^ 2"
          by (smt (z3) IH \<epsilon>_pos field_sum_of_halves mult_left_mono power_less_imp_less_base)
        also have "\<dots> = ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) ^ (1 + 2 * (2 ^ Itr - Suc 0))
                   * \<bar>x0 - r\<bar> ^ (2 * (2 ^ Itr))"
          by (simp add: power_even_eq power_mult_distrib)
        ultimately show "\<bar>(f ^^ Suc Itr) x0 - r\<bar>
             \<le> ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) ^ (2 ^ Suc Itr - Suc 0) * \<bar>x0 - r\<bar> ^ 2 ^ Suc Itr"
          by (smt (verit, ccfv_SIG) Suc_1 Suc_pred bot_nat_0.not_eq_extremum diff_diff_left
              nat.discI nat.simps(1) nat_power_eq_Suc_0_iff plus_1_eq_Suc power_Suc0_right
              power_add power_eq_0_iff power_eq_if right_diff_distrib')
      qed
    qed
    have loop: "R_fpm f x0 tol \<le> SPEC (\<lambda>(xc, xn, k). xc = (f ^^ k) x0 \<and> xn = f xc
          \<and> \<bar>xn - xc\<bar> < tol \<and> k \<le> Suc (fpm_bound f x0 tol (1 - \<epsilon>)))"
      using R_fpm_loop_lt[OF c_nonneg c_lt1 tol_pos \<delta>_pos r_fixed x0_in contr_le] .
    show "R_fpm f x0 tol \<le> SPEC (\<lambda>(xc, xn, k).
            \<bar>xc - r\<bar> \<le> ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) ^ (2 ^ k - 1) * \<bar>x0 - r\<bar> ^ (2 ^ k)
          \<and> \<bar>xn - xc\<bar> < tol
          \<and> k \<le> Suc (nat \<lceil> ln (max 1 (\<bar>f x0 - x0\<bar> / tol)) / ln (1 / (1 - \<epsilon>)) \<rceil>))"
    proof (rule weaken_SPEC[OF loop])
      fix s :: "real \<times> real \<times> nat"
      obtain xc xn k where s_eq: "s = (xc, xn, k)" by (cases s)
      assume "case s of (xc, xn, k) \<Rightarrow> xc = (f ^^ k) x0 \<and> xn = f xc \<and> \<bar>xn - xc\<bar> < tol
                \<and> k \<le> Suc (fpm_bound f x0 tol (1 - \<epsilon>))"
      then have A: "xc = (f ^^ k) x0" "\<bar>xn - xc\<bar> < tol" "k \<le> Suc (fpm_bound f x0 tol (1 - \<epsilon>))"
        by (auto simp: s_eq)
      have quad: "\<bar>xc - r\<bar> \<le> ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) ^ (2 ^ k - 1) * \<bar>x0 - r\<bar> ^ (2 ^ k)"
      proof -
        have "\<bar>(f ^^ k) x0 - r\<bar>
                \<le> ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) ^ (2 ^ k - Suc 0) * \<bar>x0 - r\<bar> ^ (2 ^ k)"
          using Inductive_Step by blast
        thus ?thesis using A(1) by simp
      qed
      have k_bound:
        "k \<le> Suc (nat \<lceil> ln (max 1 (\<bar>f x0 - x0\<bar> / tol)) / ln (1 / (1 - \<epsilon>)) \<rceil>)"
        using A(3) by (simp add: fpm_bound_def)

      show "case s of (xc, xn, k) \<Rightarrow>
              \<bar>xc - r\<bar> \<le> ((\<bar>deriv (deriv f) r\<bar> + \<epsilon>) / 2) ^ (2 ^ k - 1) * \<bar>x0 - r\<bar> ^ (2 ^ k)
            \<and> \<bar>xn - xc\<bar> < tol
            \<and> k \<le> Suc (nat \<lceil> ln (max 1 (\<bar>f x0 - x0\<bar> / tol)) / ln (1 / (1 - \<epsilon>)) \<rceil>)"
        using quad A(2) k_bound s_eq by fastforce
    qed
  qed
  show ?thesis using \<delta>_pos \<epsilon>_pos main by blast
qed



section \<open>Paradigm C: Floating-point fixed-point iteration (direct, VCG)\<close>

text \<open>
  \<^bold>\<open>Motivation.\<close> The companion floating-point bisection development
  (Paradigm C of theory \<open>Bisection\<close>) bounds the total error
  \<open>|valof l - x\<^sup>\<star>|\<close> \<^emph>\<open>directly\<close> --- with no real shadow iterate and no
  triangle inequality --- by carrying the genuine floating-point bracket in
  the loop invariant and folding all accumulated round-off into a single
  \<^emph>\<open>constant\<close> width envelope \<open>E\<close>. This theory does the same for the
  \<^bold>\<open>fixed-point iteration\<close> \<open>x\<^sub>k\<^sub>+\<^sub>1 = f(x\<^sub>k)\<close>.

  There is no shadow. The loop invariant speaks only about the \<^emph>\<open>actual\<close>
  floating-point iterate \<open>valof x\<close> and the genuine fixed point \<open>r\<close> of the
  real map \<open>f_R\<close> (\<open>f_R r = r\<close>):

  \<^enum> the iterate obeys the \<^emph>\<open>direct contraction bound\<close>
    \<open>|valof x - r| \<le> c ^ iter \<cdot> |valof x\<^sub>0 - r| + E\<close>.

  The contraction bound is the crux. Writing \<open>w\<^sub>k = |valof x\<^sub>k - r|\<close>, one
  rounding step satisfies the affine recurrence \<open>w\<^sub>k\<^sub>+\<^sub>1 \<le> c \<cdot> w\<^sub>k + \<delta>\<close>
  (a genuine contraction by \<open>c < 1\<close> plus one evaluation/rounding error
  \<open>\<delta>\<close>), whose attracting fixed point is the \<^emph>\<open>constant\<close> envelope
  \<open>\<delta>/(1 - c)\<close>. Provided \<open>\<delta> \<le> (1 - c) E\<close>, the affine bound
  \<open>c ^ iter \<cdot> w\<^sub>0 + E\<close> is preserved verbatim across an iteration:

  \[
     c\,\bigl(c^{\,iter} w_0 + E\bigr) + \delta
     \;=\; c^{\,iter+1} w_0 + (c\,E + \delta)
     \;\le\; c^{\,iter+1} w_0 + E .
  \]

  (For bisection \<open>c = 1/2\<close>, so \<open>(1 - c) = 1/2\<close> and the condition reads
  \<open>2\<delta> \<le> E\<close> --- exactly the bisection envelope condition.)

  At loop exit the float step is small, \<open>|x_new - x| \<le> tol\<close>, and a
  standard \<^emph>\<open>a-posteriori\<close> argument for a contraction gives the
  \<^emph>\<open>direct\<close> total-error bound

  \[
     |valof x - r| \;\le\; \frac{valof\,tol + E + \delta}{1 - c},
  \]

  with no growing \<open>iter \<cdot> \<delta>\<close> term: all accumulated round-off is absorbed
  once into the constants \<open>E\<close> and \<open>\<delta>\<close>.

  \<^bold>\<open>Preliminaries.\<close> The few primitives this direct proof needs are
  collected in the inlined preliminaries below.
\<close>


subsection \<open>Inlined preliminaries\<close>

text \<open>IEEE binary64.  The \<^class>\<open>default\<close> instance for floats (needed for
  every \<^theory_text>\<open>zstore\<close> field type) is shared via
  \<^theory>\<open>Numerical_Methods.Float_Default\<close>.\<close>

type_synonym float64 = "(11, 52) IEEE.float"

text \<open>\<^const>\<open>valof\<close> and finiteness commute with floating-point absolute
  value (\<open>abs_float\<close> just clears the sign bit).\<close>

lemma valof_abs_float:
  fixes a :: "('e, 'f) float"
  shows "valof (abs a) = \<bar>valof a\<bar>"
proof (cases rule: sign_cases[of a])
  case pos
  hence "abs a = a" by (simp add: abs_float_def)
  thus ?thesis using valof_nonneg[OF pos] by simp
next
  case neg
  hence "abs a = - a" by (simp add: abs_float_def)
  thus ?thesis using valof_nonpos[OF neg] by (simp add: valof_uminus, 
        simp add: float_defs(7) neg sign_minus_float)
qed

lemma is_finite_abs_float:
  fixes a :: "('e, 'f) float"
  shows "is_finite (abs a) = is_finite a"
  by (simp add: abs_float_def)


subsection \<open>Direct guard-to-step bridge oracles\<close>

text \<open>
  These round-off facts relate the \<^emph>\<open>float\<close> loop guard \<open>tol < |x_new - x|\<close>
  to the \<^emph>\<open>real\<close> step width \<open>|valof x_new - valof x|\<close>. With no shadow to
  drift from, the float subtraction error is the only gap. The user
  discharges the abstract oracle hypotheses of \<open>fpm_FD_direct_correct\<close>
  from these, with a uniform envelope \<open>E\<close> dominating the per-step
  subtraction error.
\<close>

lemma step_guard_oracle_direct:
  fixes x x_new tol :: "('e::len, 'f::len) float" and E \<epsilon> :: real
  assumes fin_tol: "is_finite tol" and fin_x: "is_finite x" and fin_xn: "is_finite x_new"
    and threshold: "\<bar>valof x_new - valof x\<bar> < threshold TYPE(('e, 'f) float)"
    and sub: "\<bar>error TYPE(('e, 'f) float) (valof x_new - valof x)\<bar> \<le> \<epsilon>"
    and env: "\<epsilon> \<le> E"
    and guard: "tol < \<bar>x_new - x\<bar>"
  shows "valof tol < \<bar>valof x_new - valof x\<bar> + E"
proof -
  have fin_sub: "is_finite (x_new - x)"
    using float_sub(1)[OF fin_xn fin_x threshold] .
  have fin_abs: "is_finite (abs (x_new - x))"
    by (simp add: is_finite_abs_float fin_sub)
  have vg: "valof tol < valof (abs (x_new - x))"
    using guard float_lt[OF fin_tol fin_abs] by simp
  have eq: "valof (x_new - x) = valof x_new - valof x + error TYPE(('e, 'f) float) (valof x_new - valof x)"
    using float_sub(2)[OF fin_xn fin_x threshold] .
  have "\<bar>valof (x_new - x)\<bar> \<le> \<bar>valof x_new - valof x\<bar> + \<epsilon>"
    using eq sub by (smt (verit))
  hence "valof (abs (x_new - x)) \<le> \<bar>valof x_new - valof x\<bar> + \<epsilon>"
    by (simp add: valof_abs_float)
  thus ?thesis using vg env by linarith
qed

lemma step_exit_oracle_direct:
  fixes x x_new tol :: "('e::len, 'f::len) float" and E \<epsilon> :: real
  assumes fin_tol: "is_finite tol" and fin_x: "is_finite x" and fin_xn: "is_finite x_new"
    and threshold: "\<bar>valof x_new - valof x\<bar> < threshold TYPE(('e, 'f) float)"
    and sub: "\<bar>error TYPE(('e, 'f) float) (valof x_new - valof x)\<bar> \<le> \<epsilon>"
    and env: "\<epsilon> \<le> E"
    and exit: "\<not> (tol < \<bar>x_new - x\<bar>)"
  shows "\<bar>valof x_new - valof x\<bar> \<le> valof tol + E"
proof -
  have fin_sub: "is_finite (x_new - x)"
    using float_sub(1)[OF fin_xn fin_x threshold] .
  have fin_abs: "is_finite (abs (x_new - x))"
    by (simp add: is_finite_abs_float fin_sub)
  have vle: "valof (abs (x_new - x)) \<le> valof tol"
    using exit float_le_neg[OF fin_tol fin_abs] float_le[OF fin_abs fin_tol] by simp
  have eq: "valof (x_new - x) = valof x_new - valof x + error TYPE(('e, 'f) float) (valof x_new - valof x)"
    using float_sub(2)[OF fin_xn fin_x threshold] .
  have "\<bar>valof x_new - valof x\<bar> \<le> \<bar>valof (x_new - x)\<bar> + \<epsilon>"
    using eq sub by (smt (verit))
  hence "\<bar>valof x_new - valof x\<bar> \<le> valof (abs (x_new - x)) + \<epsilon>"
    by (simp add: valof_abs_float)
  thus ?thesis using vle env by linarith
qed


subsection \<open>The contraction recurrence\<close>

text \<open>
  Pure arithmetic core: a width obeying the affine bound \<open>c ^ k \<cdot> D\<^sub>0 + E\<close>
  and contracting by \<open>w \<mapsto> c w + \<delta>\<close> still obeys the \<^emph>\<open>same\<close> affine bound
  one step later, as long as \<open>\<delta> \<le> (1 - c) E\<close>. The envelope \<open>E\<close> does not
  grow with the iteration count --- this is precisely why the final bound
  has no \<open>iter \<cdot> \<delta>\<close> term.
\<close>

lemma direct_contraction_recurrence:
  fixes Wold Wnew D0 c \<delta> E :: real and k :: nat
  assumes old: "Wold \<le> c ^ k * D0 + E"
    and new: "Wnew \<le> c * Wold + \<delta>"
    and cnn: "0 \<le> c"
    and env: "\<delta> \<le> (1 - c) * E"
  shows "Wnew \<le> c ^ Suc k * D0 + E"
proof -
  have e2: "\<delta> \<le> E - c * E" using env by (simp add: algebra_simps)
  have "Wnew \<le> c * Wold + \<delta>" by (rule new)
  also have "\<dots> \<le> c * (c ^ k * D0 + E) + \<delta>"
    using mult_left_mono[OF old cnn] by linarith
  also have "\<dots> = c ^ Suc k * D0 + (c * E + \<delta>)"
    by (simp add: algebra_simps)
  also have "\<dots> \<le> c ^ Suc k * D0 + E" using e2 by linarith
  finally show ?thesis .
qed


subsection \<open>State and program (no shadow)\<close>

text \<open>
  The state holds only the iteration counter and the float iterate
  \<open>x\<close> together with the freshly evaluated next iterate \<open>x_new = f_F x\<close>.
  There are \<^emph>\<open>no\<close> real ghost variables: every fact below is about
  \<^const>\<open>valof\<close> of the genuine float iterates. The real map \<open>f_R\<close> and the
  reals \<open>r, c, \<delta>, E\<close> are \<^emph>\<open>specification-only\<close> parameters.
\<close>

zstore stFP =
  iter  :: "nat"
  x     :: "float64"
  x_new :: "float64"

program fpm_FD
  "(f_F :: float64 \<Rightarrow> float64, x0 :: float64, tol :: float64,
    f_R :: real \<Rightarrow> real, r :: real, c :: real, \<delta> :: real, E :: real)" over stFP
 = "x := x0; x_new := f_F x; iter := 0;
    while \<bar>x_new - x\<bar> > tol
    invariant
        is_finite x \<and> is_finite x_new
      \<and> x_new = f_F x
      \<and> \<bar>valof x - r\<bar> \<le> c ^ iter * \<bar>valof x0 - r\<bar> + E
    variant nat \<lceil>log (1 / c) ((1 + c) * \<bar>valof x0 - r\<bar> / (valof tol - (2 + c) * E - \<delta>))\<rceil> - iter
    do x := x_new; x_new := f_F x; iter := iter + 1 od"


subsection \<open>Direct total-error correctness\<close>

text \<open>
  Hypotheses. \<open>c \<in> (0,1)\<close> is the local contraction factor; \<open>\<delta>\<close> dominates
  the per-step evaluation/rounding error; the envelope condition
  \<open>\<delta> \<le> (1 - c) E\<close> keeps the round-off envelope constant; the margin
  \<open>\<delta> + (2 + c) E < valof tol\<close> (two \<open>E\<close>'s: step envelope + guard bridge)
  makes the variant denominator positive; and the start is away from the
  fixed point, \<open>0 < |valof x\<^sub>0 - r|\<close>.

  The abstract round-off is captured by oracles on the reachable region
  \<open>|s - r| \<le> |valof x\<^sub>0 - r| + E\<close>:

  \<^item> \<open>round_oracle\<close>: \<open>\<delta>\<close> dominates the evaluation error
    \<open>|valof (f_F s) - f_R (valof s)|\<close>;
  \<^item> \<open>contraction\<close>: \<open>f_R\<close> contracts towards its fixed point,
    \<open>|f_R s - r| \<le> c |s - r|\<close>;
  \<^item> \<open>finite_oracle\<close>: \<open>f_F\<close> preserves finiteness (no overflow);
  \<^item> \<open>step_guard_oracle\<close> / \<open>step_exit_oracle\<close>: the float guard
    \<open>tol < |x_new - x|\<close> tracks the real step \<open>|valof x_new - valof x|\<close> to
    within \<open>E\<close> (discharge from \<open>step_guard_oracle_direct\<close> /
    \<open>step_exit_oracle_direct\<close>).
\<close>

theorem fpm_FD_direct_correct:
  fixes f_F :: "float64 \<Rightarrow> float64"
  fixes f_R :: "real \<Rightarrow> real"
  fixes x0 tol :: float64
  fixes r c \<delta> E :: real
  assumes c_pos: "0 < c"
  assumes c_lt1: "c < 1"
  assumes delta_nonneg: "0 \<le> \<delta>"
  assumes envelope: "\<delta> \<le> (1 - c) * E"
  assumes tol_margin: "\<delta> + (2 + c) * E < valof tol"
  assumes x0_far: "0 < \<bar>valof x0 - r\<bar>"
  assumes finite_x0: "is_finite x0"
  assumes round_oracle:
    "\<And>s :: float64. is_finite s \<Longrightarrow> \<bar>valof s - r\<bar> \<le> \<bar>valof x0 - r\<bar> + E
        \<Longrightarrow> \<bar>valof (f_F s) - f_R (valof s)\<bar> \<le> \<delta>"
  assumes contraction:
    "\<And>s :: real. \<bar>s - r\<bar> \<le> \<bar>valof x0 - r\<bar> + E \<Longrightarrow> \<bar>f_R s - r\<bar> \<le> c * \<bar>s - r\<bar>"
  assumes finite_oracle:
    "\<And>s :: float64. is_finite s \<Longrightarrow> \<bar>valof s - r\<bar> \<le> \<bar>valof x0 - r\<bar> + E
        \<Longrightarrow> is_finite (f_F s)"
  assumes step_guard_oracle:
    "\<And>x x_new :: float64. is_finite x \<Longrightarrow> is_finite x_new
        \<Longrightarrow> \<bar>valof x - r\<bar> \<le> \<bar>valof x0 - r\<bar> + E \<Longrightarrow> x_new = f_F x
        \<Longrightarrow> tol < \<bar>x_new - x\<bar> \<Longrightarrow> valof tol < \<bar>valof x_new - valof x\<bar> + E"
  assumes step_exit_oracle:
    "\<And>x x_new :: float64. is_finite x \<Longrightarrow> is_finite x_new
        \<Longrightarrow> \<bar>valof x - r\<bar> \<le> \<bar>valof x0 - r\<bar> + E \<Longrightarrow> x_new = f_F x
        \<Longrightarrow> \<not> (tol < \<bar>x_new - x\<bar>) \<Longrightarrow> \<bar>valof x_new - valof x\<bar> \<le> valof tol + E"
  shows "H[True] fpm_FD (f_F, x0, tol, f_R, r, c, \<delta>, E)
       [\<bar>valof x - r\<bar> \<le> c ^ iter * \<bar>valof x0 - r\<bar> + E
        \<and> \<bar>valof x - r\<bar> \<le> (valof tol + E + \<delta>) / (1 - c)]"
proof -
  have c_nonneg: "0 \<le> c" using c_pos by simp
  have onemc_pos: "0 < 1 - c" using c_lt1 by simp
  have E0: "0 \<le> E"
    using envelope delta_nonneg onemc_pos
    by (meson landau_o.R_trans not_less zero_le_mult_iff) 
  have D0_nonneg: "0 \<le> \<bar>valof x0 - r\<bar>" by simp

  \<comment> \<open>One rounding step contracts the distance to the fixed point.\<close>
  have stepbound:
    "\<And>s :: float64. is_finite s \<Longrightarrow> \<bar>valof s - r\<bar> \<le> \<bar>valof x0 - r\<bar> + E
        \<Longrightarrow> \<bar>valof (f_F s) - r\<bar> \<le> c * \<bar>valof s - r\<bar> + \<delta>"
  proof -
    fix s :: float64
    assume fs: "is_finite s" and reg: "\<bar>valof s - r\<bar> \<le> \<bar>valof x0 - r\<bar> + E"
    have "\<bar>valof (f_F s) - r\<bar> \<le> \<bar>valof (f_F s) - f_R (valof s)\<bar> + \<bar>f_R (valof s) - r\<bar>"
      by linarith
    also have "\<dots> \<le> \<delta> + c * \<bar>valof s - r\<bar>"
      using round_oracle[OF fs reg] contraction[OF reg] by linarith
    finally show "\<bar>valof (f_F s) - r\<bar> \<le> c * \<bar>valof s - r\<bar> + \<delta>" by linarith
  qed

  \<comment> \<open>The affine bound keeps every iterate inside the reachable region.\<close>
  have reg_of_inv:
    "\<And>w :: real. \<And>k :: nat. \<bar>w - r\<bar> \<le> c ^ k * \<bar>valof x0 - r\<bar> + E
        \<Longrightarrow> \<bar>w - r\<bar> \<le> \<bar>valof x0 - r\<bar> + E"
  proof -
    fix w :: real and k :: nat
    assume hw: "\<bar>w - r\<bar> \<le> c ^ k * \<bar>valof x0 - r\<bar> + E"
    have cpow_le1: "c ^ k \<le> 1" using c_nonneg c_lt1 by (simp add: power_le_one)
    have "c ^ k * \<bar>valof x0 - r\<bar> \<le> 1 * \<bar>valof x0 - r\<bar>"
      by (rule mult_right_mono[OF cpow_le1]) simp
    thus "\<bar>w - r\<bar> \<le> \<bar>valof x0 - r\<bar> + E" using hw by simp
  qed

  show ?thesis
    apply vcg
    \<comment> \<open>Goal 1: \<open>is_finite (f_F (f_F x))\<close> --- finiteness preserved.\<close>
    subgoal premises prems for it xc
    proof -
      have finx: "is_finite xc" and finfx: "is_finite (f_F xc)"
        and inv4: "\<bar>valof xc - r\<bar> \<le> c ^ it * \<bar>valof x0 - r\<bar> + E"
        using prems by auto
      have xreg: "\<bar>valof xc - r\<bar> \<le> \<bar>valof x0 - r\<bar> + E" by (rule reg_of_inv[OF inv4])
      have fxreg: "\<bar>valof (f_F xc) - r\<bar> \<le> \<bar>valof x0 - r\<bar> + E"
      proof -
        have "\<bar>valof (f_F xc) - r\<bar> \<le> c ^ Suc it * \<bar>valof x0 - r\<bar> + E"
          by (rule direct_contraction_recurrence[OF inv4 stepbound[OF finx xreg] c_nonneg envelope])
        thus ?thesis by (rule reg_of_inv)
      qed
      show "is_finite (f_F (f_F xc))" by (rule finite_oracle[OF finfx fxreg])
    qed
    \<comment> \<open>Goal 2: the affine contraction bound is preserved.\<close>
    subgoal premises prems for it xc
    proof -
      have finx: "is_finite xc"
        and inv4: "\<bar>valof xc - r\<bar> \<le> c ^ it * \<bar>valof x0 - r\<bar> + E"
        using prems by auto
      have xreg: "\<bar>valof xc - r\<bar> \<le> \<bar>valof x0 - r\<bar> + E" by (rule reg_of_inv[OF inv4])
      have "\<bar>valof (f_F xc) - r\<bar> \<le> c ^ Suc it * \<bar>valof x0 - r\<bar> + E"
        by (rule direct_contraction_recurrence[OF inv4 stepbound[OF finx xreg] c_nonneg envelope])
      thus "\<bar>valof (f_F xc) - r\<bar> \<le> c * c ^ it * \<bar>valof x0 - r\<bar> + E" by simp
    qed
    \<comment> \<open>Goal 3: the variant strictly decreases.\<close>
    subgoal premises prems for it xc
    proof -
      have finx: "is_finite xc" and finfx: "is_finite (f_F xc)"
        and inv4: "\<bar>valof xc - r\<bar> \<le> c ^ it * \<bar>valof x0 - r\<bar> + E"
        and guard: "tol < \<bar>f_F xc - xc\<bar>"
        using prems by auto
      have xreg: "\<bar>valof xc - r\<bar> \<le> \<bar>valof x0 - r\<bar> + E" by (rule reg_of_inv[OF inv4])
      have xn_r: "\<bar>valof (f_F xc) - r\<bar> \<le> c * \<bar>valof xc - r\<bar> + \<delta>"
        by (rule stepbound[OF finx xreg])
      have g: "valof tol < \<bar>valof (f_F xc) - valof xc\<bar> + E"
        by (rule step_guard_oracle[OF finx finfx xreg refl guard])
      have step_big: "valof tol < (1 + c) * \<bar>valof xc - r\<bar> + \<delta> + E"
      proof -
        have tri: "\<bar>valof (f_F xc) - valof xc\<bar> \<le> \<bar>valof (f_F xc) - r\<bar> + \<bar>valof xc - r\<bar>" by linarith
        have dist1: "(1 + c) * \<bar>valof xc - r\<bar> = \<bar>valof xc - r\<bar> + c * \<bar>valof xc - r\<bar>"
          by (simp add: algebra_simps)
        from g tri xn_r have "valof tol < c * \<bar>valof xc - r\<bar> + \<delta> + \<bar>valof xc - r\<bar> + E"
          by linarith
        thus ?thesis using dist1 by linarith
      qed
      have onec: "0 < 1 + c" using c_pos by simp
      have denpos: "0 < (1 + c) * \<bar>valof x0 - r\<bar>" by (rule mult_pos_pos[OF onec x0_far])
      have Bpos: "0 < valof tol - (2 + c) * E - \<delta>" using tol_margin by linarith
      have key: "valof tol - (2 + c) * E - \<delta> < (1 + c) * (c ^ it * \<bar>valof x0 - r\<bar>)"
      proof -
        have W_mul: "(1 + c) * \<bar>valof xc - r\<bar> \<le> (1 + c) * (c ^ it * \<bar>valof x0 - r\<bar> + E)"
          by (rule mult_left_mono[OF inv4]) (use onec in simp)
        have expand: "(1 + c) * (c ^ it * \<bar>valof x0 - r\<bar> + E)
                        = (1 + c) * (c ^ it * \<bar>valof x0 - r\<bar>) + (1 + c) * E"
          by (simp add: algebra_simps)
        have Ecollect: "(1 + c) * E + E = (2 + c) * E" by (simp add: algebra_simps)
        from step_big W_mul expand Ecollect show ?thesis by linarith
      qed
      have cpow_lb: "(valof tol - (2 + c) * E - \<delta>) / ((1 + c) * \<bar>valof x0 - r\<bar>) < c ^ it"
        using key by (simp add: pos_divide_less_eq[OF denpos], argo)
      have cpow_pos: "0 < c ^ it" using c_pos by simp
      have b_gt1: "1 < 1 / c" using c_pos c_lt1 by (simp add: field_simps)
      have recip: "(1 / c) ^ it < (1 + c) * \<bar>valof x0 - r\<bar> / (valof tol - (2 + c) * E - \<delta>)"
      proof -
        have "(1 / c) ^ it = 1 / c ^ it" by (simp add: power_one_over)
        also have "\<dots> < 1 / ((valof tol - (2 + c) * E - \<delta>) / ((1 + c) * \<bar>valof x0 - r\<bar>))"
          using cpow_lb cpow_pos Bpos denpos by (smt (verit) frac_less2 zero_less_divide_iff)
        also have "\<dots> = (1 + c) * \<bar>valof x0 - r\<bar> / (valof tol - (2 + c) * E - \<delta>)"
          using Bpos denpos by simp
        finally show ?thesis .
      qed
      have iter_lt: "it < log (1 / c) ((1 + c) * \<bar>valof x0 - r\<bar> / (valof tol - (2 + c) * E - \<delta>))"
        using less_log_of_power[OF recip b_gt1] .
      have iter_lt_nat:
        "it < nat \<lceil>log (1 / c) ((1 + c) * \<bar>valof x0 - r\<bar> / (valof tol - (2 + c) * E - \<delta>))\<rceil>"
        using iter_lt real_nat_ceiling_ge by linarith
      show "nat \<lceil>log (1 / c) ((1 + c) * \<bar>valof x0 - r\<bar> / (valof tol - (2 + c) * E - \<delta>))\<rceil> - Suc it
             < nat \<lceil>log (1 / c) ((1 + c) * \<bar>valof x0 - r\<bar> / (valof tol - (2 + c) * E - \<delta>))\<rceil> - it"
        using iter_lt_nat by (metis diff_less_mono2 lessI)
    qed
    \<comment> \<open>Goal 4: initial \<open>is_finite x0\<close>.\<close>
    subgoal by (rule finite_x0)
    \<comment> \<open>Goal 5: initial \<open>is_finite (f_F x0)\<close>.\<close>
    subgoal premises prems
    proof -
      have rx0: "\<bar>valof x0 - r\<bar> \<le> \<bar>valof x0 - r\<bar> + E" using E0 by simp
      show "is_finite (f_F x0)" by (rule finite_oracle[OF finite_x0 rx0])
    qed
    \<comment> \<open>Goal 6: initial width envelope \<open>0 \<le> E\<close>.\<close>
    subgoal by (rule E0)
    \<comment> \<open>Goal 7: post --- the a-posteriori direct error bound.\<close>
    subgoal premises prems for it xc
    proof -
      have finx: "is_finite xc" and finfx: "is_finite (f_F xc)"
        and inv4: "\<bar>valof xc - r\<bar> \<le> c ^ it * \<bar>valof x0 - r\<bar> + E"
        and nguard: "\<not> tol < \<bar>f_F xc - xc\<bar>"
        using prems by auto
      have xreg: "\<bar>valof xc - r\<bar> \<le> \<bar>valof x0 - r\<bar> + E" by (rule reg_of_inv[OF inv4])
      have xn_r: "\<bar>valof (f_F xc) - r\<bar> \<le> c * \<bar>valof xc - r\<bar> + \<delta>"
        by (rule stepbound[OF finx xreg])
      have step: "\<bar>valof (f_F xc) - valof xc\<bar> \<le> valof tol + E"
        by (rule step_exit_oracle[OF finx finfx xreg refl nguard])
      have ineq: "\<bar>valof xc - r\<bar> \<le> (valof tol + E) + (c * \<bar>valof xc - r\<bar> + \<delta>)"
      proof -
        have "\<bar>valof xc - r\<bar> \<le> \<bar>valof xc - valof (f_F xc)\<bar> + \<bar>valof (f_F xc) - r\<bar>" by linarith
        thus ?thesis using step xn_r by (smt (verit))
      qed
      have collect: "(1 - c) * \<bar>valof xc - r\<bar> = \<bar>valof xc - r\<bar> - c * \<bar>valof xc - r\<bar>"
        by (simp add: algebra_simps)
      have "(1 - c) * \<bar>valof xc - r\<bar> \<le> valof tol + E + \<delta>" using ineq collect by linarith
      thus "\<bar>valof xc - r\<bar> \<le> (valof tol + E + \<delta>) / (1 - c)"
        using onemc_pos by (simp add: pos_le_divide_eq mult.commute)
    qed
    done
qed

text \<open>
  \<^bold>\<open>What was achieved.\<close> The postcondition bounds the distance from the
  \<^emph>\<open>actual\<close> floating-point iterate \<open>valof x\<close> to the genuine fixed point
  \<open>r\<close> \<^emph>\<open>directly\<close>: an affine \<open>c ^ iter \<cdot> |valof x\<^sub>0 - r| + E\<close> bound that
  holds throughout, and the a-posteriori bound
  \<open>(valof tol + E + \<delta>)/(1 - c)\<close> at exit. The proof never introduces a real
  shadow iterate and never appeals to the triangle inequality between a
  method error and a round-off error: the single affine invariant carries
  the whole argument, and \<open>direct_contraction_recurrence\<close> keeps the
  round-off envelope \<open>E\<close> constant across iterations, so no \<open>iter \<cdot> \<delta>\<close>
  drift term ever appears.
\<close>

end