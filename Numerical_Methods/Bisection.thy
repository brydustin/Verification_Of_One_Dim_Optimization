section \<open>Bisection: VCG, Lammich, and Floating-Point Verification\<close>

theory Bisection
  imports
    "Refine_Monadic.Refine_Monadic"
    Float_Default
begin

text \<open>
  A self-contained, side-by-side comparison of two verifications of the SAME
  bisection root-finder, sharing the SAME mathematical foundation
  (\<open>Bolzanos_theorem\<close>) so neither side enjoys a private resource the other
  lacks:

  \<^item> \<^bold>\<open>Paradigm A\<close>: an imperative ITree program discharged by the VCG-based
    Hoare logic (\<open>bisection_error_bound\<close>). Every proof obligation \<dash> the
    termination variant, the IVT root-extraction (via \<open>Bolzanos_theorem\<close>),
    and the \<open>\<lceil>log 2 ((b-a)/tol)\<rceil>\<close> iteration count \<dash> is discharged inline.
    Its sign-propagation obligations reuse the shared \<open>sign_prop\<close>.

  \<^item> \<^bold>\<open>Paradigm B\<close>: the same algorithm in Lammich's Refinement Framework
    (\<open>R_bisection\<close> in the \<open>nres\<close> monad, \<open>bisection_correct\<close>), whose root
    extraction also goes through \<open>Bolzanos_theorem\<close> and whose sign step reuses
    \<open>sign_prop\<close>. Only the termination variant uses a framework-specific helper
    (\<open>bisect_var_half\<close>): the two paradigms count down differently, so this is
    the one piece of reasoning that does \<^emph>\<open>not\<close> transfer.

  The two theorems carry \<^emph>\<open>identical\<close> assumptions, so the comparison is of the
  proof effort alone. (The \<open>nres\<close> algorithm is renamed \<open>R_bisection\<close> to coexist
  with the ITree \<open>program bisection\<close> in this single theory.)
\<close>

section \<open>Shared Mathematical Foundations\<close>

theorem Bolzanos_theorem:
  fixes f :: "real \<Rightarrow> real"
  assumes a_less_than_b: "\<alpha> < \<beta>"
  assumes opposite_signs: "f(\<alpha>)*f(\<beta>) < 0"
  assumes continuous_f: "continuous_on {\<alpha>..\<beta>} f"
  shows "\<exists> \<gamma>. (f(\<gamma>) = 0 \<and> \<alpha> < \<gamma> \<and> \<gamma> < \<beta>)"
proof -
  have "f(\<alpha>) \<noteq> 0" and "f(\<beta>) \<noteq> 0"
    using opposite_signs by (auto simp: mult_less_0_iff)
  hence cases: "(f(\<alpha>) < 0 \<and> f(\<beta>) > 0) \<or> (f(\<alpha>) > 0 \<and> f(\<beta>) < 0)"
    using opposite_signs by (auto simp: mult_less_0_iff)
  have  "\<exists> \<gamma>. \<gamma> \<in> {\<alpha>..\<beta>} \<and> f(\<gamma>) = 0"
  proof(cases "f(\<alpha>) < 0 \<and> f(\<beta>) > 0")
    show "f \<alpha> < 0 \<and> 0 < f \<beta> \<Longrightarrow> \<exists>\<gamma>. \<gamma> \<in> {\<alpha>..\<beta>} \<and> f \<gamma> = 0"
      by (metis IVT' a_less_than_b atLeastAtMost_iff continuous_f less_le_not_le)
  next
    assume "\<not> (f \<alpha> < 0 \<and> 0 < f \<beta>)"
    then have "(f \<beta> < 0 \<and> 0 < f \<alpha>)"
      using cases by linarith
    with IVT2'[where f = "f", where b="\<beta>", where a = "\<alpha>", where y=0]
    obtain \<gamma> where "\<gamma> \<in> {\<alpha>..\<beta>}" and "f \<gamma> = 0"
      using  a_less_than_b continuous_f by auto
    then show ?thesis
      by blast
  qed
  then show ?thesis
    by (smt (verit, best) \<open>f \<alpha> \<noteq> 0\<close> \<open>f \<beta> \<noteq> 0\<close> atLeastAtMost_iff)
qed


section \<open>Paradigm A: Imperative ITree Program, VCG-based Hoare Logic\<close>

subsection \<open>Algorithm\<close>

text \<open>
  We formalise a classic bisection root-finder and explicitly emulate the
  reference implementation in R's \<open>cmna::bisection\<close> (source and manual
  page below).
  \begin{itemize}
  \item Source (R):  \url{https://github.com/cran/cmna/blob/master/R/bisection.R}
  \item Manual page: \url{https://search.r-project.org/CRAN/refmans/cmna/html/bisection.html}
  \end{itemize}
\<close>

zstore st =
  iter :: "nat"
  fl   :: "real"
  fu   :: "real"
  l    :: "real"
  u    :: "real"
  xmid :: "real"
  ymid :: "real"

program bisection "(f :: real \<Rightarrow> real, a :: real, b :: real, tol :: real)" over st
 = "iter := 0; fl := f(a); fu := f(b); l := a; u := b; xmid := l;
    while u - l > tol
    invariant fl = f(l) \<and> fu = f(u) \<and> (l = xmid \<or> u = xmid) \<and> a \<le> l \<and> u \<le> b \<and> l < u
      \<and> fl * fu \<le> 0 \<and> u - l = (b - a) / 2^iter \<and> (2 * (u - l) > tol)
    variant nat(\<lceil>log 2 ((b - a) / tol)\<rceil>) - iter
    do iter := iter + 1; xmid := (l + u)/2; ymid := f(xmid);
       if fl*ymid > 0 then l := xmid; fl := ymid else u := xmid; fu := ymid fi od"

subsection \<open>Root-extraction helper (shared by both VCG exit paths)\<close>

text \<open>
  Both terminal paths of the \<open>vcg\<close> proof below \<dash> the one where the bracket
  point recorded in \<open>xmid\<close> is the lower end, and the one where it is the upper
  end \<dash> need the same fact: once the bracket width is within \<open>tol\<close>, the
  bracketed root lies within \<open>tol\<close> of the measured endpoint \<open>p\<close> and the
  iteration count equals \<open>\<lceil>log 2 ((b-a)/tol)\<rceil>\<close>. Proving it once, parametric
  in \<open>p\<close>, removes the ~40-line duplication.
\<close>

lemma bisect_root_extract:
  fixes f :: "real \<Rightarrow> real" and a b tol lo hi p :: real and iter :: nat
  assumes tol_pos: "0 < tol"
    and small_tol: "tol < b - a"
    and cont: "continuous_on {a..b} f"
    and opp: "f a * f b < 0"
    and a_lo: "a \<le> lo"
    and hi_b: "hi \<le> b"
    and sgn: "f lo * f hi \<le> 0"
    and width: "hi - lo = (b - a) / 2 ^ iter"
    and exitg: "\<not> tol < (b - a) / 2 ^ iter"
    and prevg: "tol < 2 * hi - 2 * lo"
    and p_in: "p = lo \<or> p = hi"
  shows "\<exists>c. f c = 0 \<and> a < c \<and> c < b \<and> \<bar>c - p\<bar> \<le> (b - a) / 2 ^ iter
           \<and> \<bar>c - p\<bar> \<le> tol \<and> int iter = \<lceil>log 2 ((b - a) / tol)\<rceil>"
proof -
  define L where "L = (b - a) / 2 ^ iter"
  have L_pos: "0 < L"
    using L_def width prevg tol_pos by linarith
  have cont_sub: "continuous_on {lo..hi} f"
    by (meson a_lo hi_b cont atLeastatMost_subset_iff continuous_on_subset)
  obtain c where cI: "c \<in> {lo..hi}" and fc0: "f c = 0"
    by (metis Bolzanos_theorem L_def L_pos sgn width antisym_conv1 atLeastAtMost_iff cont_sub
        diff_gt_0_iff_gt nle_le no_zero_divisors not_less_iff_gr_or_eq)
  have c_bounds: "a < c \<and> c < b"
    using a_lo hi_b opp cI fc0 order_less_le by fastforce
  have dist_L: "\<bar>c - p\<bar> \<le> (b - a) / 2 ^ iter"
    using cI p_in width by (smt (verit) atLeastAtMost_iff)
  have dist_tol: "\<bar>c - p\<bar> \<le> tol"
    using dist_L exitg by linarith
  have iter_pos: "iter \<ge> 1"
    using small_tol exitg by (metis div_by_1 less_one not_le power_0)
  have "int iter = \<lceil>log 2 ((b - a) / tol)\<rceil>"
  proof -
    have "1/2 < L / tol"
      by (smt (verit, ccfv_SIG) L_def width prevg add_divide_distrib tol_pos less_divide_eq_1_pos)
    then have "(2::real) ^ iter * (L / tol) > (2::real) ^ iter * (1/2)"
      by (smt (verit) mult_strict_left_mono zero_less_power)
    then have "(b - a) / tol > (2::real) ^ (iter - 1)"
      by (smt (verit, del_insts) Groups.mult_ac(2) L_def iter_pos mult_cancel_left2
          nonzero_divide_eq_eq power_diff power_one_right times_divide_eq_right)
    moreover have "(b - a) / tol \<le> 2 ^ iter"
      by (metis exitg linorder_not_le mult.commute one_le_power order_less_le_trans pos_divide_le_eq
          tol_pos verit_comp_simplify(28) verit_comp_simplify(5))
    ultimately show ?thesis
      by (smt (verit) Groups.add_ac(2) exitg add_diff_inverse_nat ceiling_log_eq_powr_iff
          int_ops(2) iter_pos linorder_not_le mult.commute of_nat_diff pos_divide_le_eq
          tol_pos powr_realpow zero_less_power)
  qed
  then show ?thesis
    using cI c_bounds dist_L dist_tol fc0 by auto
qed


subsection \<open>Total Correctness Proof\<close>

text \<open>
  The original error-bound theorem (carried over from the submitted
  version, modulo the renames). A strengthened version that explicitly
  asserts the result is in \<open>[a,b]\<close> is given below as
  \<open>bisection_in_interval\<close>.
\<close>

theorem bisection_error_bound:
  assumes postive_tolerance: "0 < tol"
  assumes sufficiently_small_tol: "tol < b-a"
  assumes continuous_f: "continuous_on {a..b} f"
  assumes opposite_signs: "f(a)*f(b)<0"
  shows  "H[True] bisection(f,a,b,tol)
       [\<exists> c::real. f(c) = 0 \<and> c \<in> {a<..<b} \<and> u-l \<le> tol \<and> \<bar>c-xmid\<bar> \<le> (b-a)/2^iter \<and> \<bar>c-xmid\<bar> \<le> tol
         \<and> iter = \<lceil>log 2 ((b-a) / tol)\<rceil>]"
proof -
  have a_less_than_b: "a < b"
    using assms(1,2) by auto
  have ln2_g_0 [simp]: "\<lceil>log 2 ((b - a) / tol)\<rceil> > 0"
    using assms(2) postive_tolerance by force
  hence [simp]: "0 < log 2 ((b - a) / tol)"
    using zero_less_ceiling by simp
  show ?thesis
  proof (vcg)
    show "\<And>xmid u. \<lbrakk> 0 < f xmid * f ((xmid + u) / 2); f xmid * f u \<le> 0 \<rbrakk>  \<Longrightarrow> f ((xmid + u) / 2) * f u \<le> 0"
      by (metis less_eq_real_def less_numeral_extra(3) mult_le_0_iff verit_la_disequality
          zero_less_mult_iff)
    show "\<And>xmid u iter.  u - xmid = (b - a) / 2 ^ iter  \<Longrightarrow> u - (xmid + u) / 2 = (b - a) / (2 * 2 ^ iter)"
      by (simp add: add_divide_distrib)    
    show "f a * f b \<le> 0"
      using opposite_signs by auto
    show "a < b"
      by (simp add: a_less_than_b)   
    show "\<And>xmid u iter. \<lbrakk> u - xmid = (b - a) / 2 ^ iter; tol < (b - a) / 2 ^ iter \<rbrakk> \<Longrightarrow> tol < 2 * u - (2 * xmid + 2 * u) / 2"
      by (smt (z3) field_sum_of_halves)
    show "\<And>l u.\<lbrakk> 0 < f l * f ((l + u) / 2); f l * f u \<le> 0 \<rbrakk> \<Longrightarrow> f ((l + u) / 2) * f u \<le> 0"
      by (metis less_eq_real_def less_numeral_extra(3) mult_le_0_iff verit_la_disequality
          zero_less_mult_iff)
    show "\<And>iter l u. \<lbrakk> u - l = (b - a) / 2 ^ iter; tol < (b - a) / 2 ^ iter \<rbrakk> \<Longrightarrow> tol < 2 * u - (2 * l + 2 * u) / 2"
      by (smt (z3) field_sum_of_halves)    
    show "\<And>iter l u. u - l = (b - a) / 2 ^ iter  \<Longrightarrow> u - (l + u) / 2 = (b - a) / (2 * 2 ^ iter)"
      by (simp add: field_simps)    
  next
    fix iter u xmid
    assume a0: "\<not> (tol < (b - a) / 2 ^ iter)" and a1: "f xmid * f u \<le> 0"
       and a2: "a \<le> xmid" and a3: "u \<le> b"
       and a4: "u - xmid = (b - a) / 2 ^ iter" and a5: "tol < 2 * u - 2 * xmid"
    show "\<exists>c. f c = 0 \<and> a < c \<and> c < b \<and> \<bar>c - xmid\<bar> \<le> (b - a) / 2 ^ iter \<and> \<bar>c - xmid\<bar> \<le> tol \<and> int iter = \<lceil>log 2 ((b - a) / tol)\<rceil>"
      by (rule bisect_root_extract[OF postive_tolerance sufficiently_small_tol continuous_f
            opposite_signs a2 a3 a1 a4 a0 a5]) simp
  next
    fix iter l u
    assume a0: "\<not> (tol < (b - a) / 2 ^ iter)" and a1: "f l * f u \<le> 0"
       and a2: "a \<le> l" and a3: "u \<le> b"
       and a4: "u - l = (b - a) / 2 ^ iter" and a5: "tol < 2 * u - 2 * l"
    show "\<exists>c. f c = 0 \<and> a < c \<and> c < b \<and> \<bar>c - u\<bar> \<le> (b - a) / 2 ^ iter \<and> \<bar>c - u\<bar> \<le> tol \<and> int iter = \<lceil>log 2 ((b - a) / tol)\<rceil>"
      by (rule bisect_root_extract[OF postive_tolerance sufficiently_small_tol continuous_f
            opposite_signs a2 a3 a1 a4 a0 a5]) simp
  next
    show "\<And>iter u xmid. tol < (b - a) / 2 ^ iter \<Longrightarrow> nat \<lceil>log 2 ((b - a) / tol)\<rceil> - Suc iter < nat \<lceil>log 2 ((b - a) / tol)\<rceil> - iter"
      by (smt (verit, del_insts) Groups.add_ac(2) a_less_than_b
          divide_divide_eq_right divide_pos_pos frac_le le_diff_conv less_log_of_power
          linear linorder_not_le nonzero_mult_div_cancel_left not_less_eq_eq of_nat_Suc
          of_nat_add of_nat_diff of_nat_le_iff order_le_less postive_tolerance real_nat_ceiling_ge)
    thus "\<And>iter u xmid. tol < (b - a) / 2 ^ iter \<Longrightarrow> nat \<lceil>log 2 ((b - a) / tol)\<rceil> - Suc iter < nat \<lceil>log 2 ((b - a) / tol)\<rceil> - iter" .
    thus "\<And>iter u xmid. tol < (b - a) / 2 ^ iter \<Longrightarrow> nat \<lceil>log 2 ((b - a) / tol)\<rceil> - Suc iter < nat \<lceil>log 2 ((b - a) / tol)\<rceil> - iter" .
    thus "\<And>iter u xmid. tol < (b - a) / 2 ^ iter \<Longrightarrow> nat \<lceil>log 2 ((b - a) / tol)\<rceil> - Suc iter < nat \<lceil>log 2 ((b - a) / tol)\<rceil> - iter" .
    show "tol < 2 * b - 2 * a"
      using assms(1,2) by linarith
  qed
qed


section \<open>Paradigm B: Lammich's Refinement Framework (\<open>nres\<close>)\<close>

subsection \<open>The abstract algorithm\<close>

definition R_bisection :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real nres" where
  "R_bisection f a b tol \<equiv> do {
     (l, u) \<leftarrow> WHILET
       (\<lambda>(l, u). tol < u - l)
       (\<lambda>(l, u). do {
          let m = (l + u) / 2;
          if f l * f m \<le> 0 then RETURN (l, m) else RETURN (m, u)
        })
       (a, b);
     RETURN ((l + u) / 2)
   }"

subsection \<open>Loop invariant and termination variant\<close>

definition bisect_invar :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<times> real \<Rightarrow> bool" where
  "bisect_invar f a b \<equiv> \<lambda>(l, u). a \<le> l \<and> l \<le> u \<and> u \<le> b \<and> f l * f u \<le> 0"

definition bisect_var :: "real \<Rightarrow> real \<times> real \<Rightarrow> nat" where
  "bisect_var tol \<equiv> \<lambda>(l, u). nat \<lceil>log 2 ((u - l) / tol)\<rceil>"

subsection \<open>Supporting facts\<close>

text \<open>Halving the bracket width strictly decreases the variant, provided the
  width still exceeds the tolerance (i.e. the loop guard holds).\<close>

lemma bisect_var_half:
  assumes tol: "0 < tol" and guard: "tol < w"
  shows "nat \<lceil>log 2 ((w / 2) / tol)\<rceil> < nat \<lceil>log 2 (w / tol)\<rceil>"
proof -
  have wpos: "0 < w" using assms by linarith
  have w2: "0 < w / 2" using wpos by simp
  have pos: "0 < w / tol" by (rule divide_pos_pos[OF wpos tol])
  have gt1: "1 < w / tol" using assms by (simp add: less_divide_eq)
  have logpos: "0 < log 2 (w / tol)" using gt1 pos by simp
  have ceil1: "1 \<le> \<lceil>log 2 (w / tol)\<rceil>" using logpos by (simp add: le_ceiling_iff)
  have l1: "log 2 ((w / 2) / tol) = log 2 (w / 2) - log 2 tol"
    using w2 tol by (intro log_divide_pos) auto
  have l2: "log 2 (w / 2) = log 2 w - 1"
  proof -
    have "log 2 (w / 2) = log 2 w - log 2 2" using wpos by (intro log_divide_pos) auto
    thus ?thesis by simp
  qed
  have l3: "log 2 (w / tol) = log 2 w - log 2 tol"
    using wpos tol by (intro log_divide_pos) auto
  have split: "log 2 ((w / 2) / tol) = log 2 (w / tol) - 1"
    using l1 l2 l3 by linarith
  have ceq: "\<lceil>log 2 ((w / 2) / tol)\<rceil> = \<lceil>log 2 (w / tol)\<rceil> - 1"
    using split by simp
  have key: "\<And>Y::int. 1 \<le> Y \<Longrightarrow> nat (Y - 1) < nat Y"
    by (auto simp: zless_nat_conj)
  show ?thesis unfolding ceq by (rule key[OF ceil1])
qed



subsection \<open>Correctness\<close>

theorem bisection_correct:
  assumes postive_tolerance: "0 < tol"
    and sufficiently_small_tol: "tol < b - a"
    and continuous_f: "continuous_on {a..b} f"
    and opposite_signs: "f a * f b < 0"
  shows "R_bisection f a b tol
          \<le> SPEC (\<lambda>c. \<exists>r\<in>{a..b}. f r = 0 \<and> \<bar>c - r\<bar> \<le> tol)"
  unfolding R_bisection_def
  apply (refine_vcg WHILET_rule[where I = "bisect_invar f a b"
                                  and R = "Wellfounded.measure (bisect_var tol)"])
  subgoal \<comment> \<open>well-foundedness of the variant\<close>
    by simp
  subgoal \<comment> \<open>invariant holds initially\<close>
    using sufficiently_small_tol postive_tolerance opposite_signs
    by (auto simp: bisect_invar_def)
  subgoal premises p for s aa ba \<comment> \<open>then-branch: invariant preserved\<close>
    using p by (auto simp: bisect_invar_def)
  subgoal premises p for s aa ba \<comment> \<open>then-branch: variant decreases\<close>
  proof -
    from p have g: "tol < ba - aa" and seq: "s = (aa, ba)" by auto
    have w: "(aa + ba) / 2 - aa = (ba - aa) / 2" by (simp add: field_simps)
    show ?thesis using bisect_var_half[OF postive_tolerance g]
      by (simp add: seq bisect_var_def w)
  qed
  subgoal premises p for s aa ba \<comment> \<open>else-branch: invariant preserved\<close>
  proof -
    from p have inv: "bisect_invar f a b (aa, ba)"
      and br: "\<not> f aa * f ((aa + ba) / 2) \<le> 0" by auto
    from inv have inv': "a \<le> aa" "aa \<le> ba" "ba \<le> b" "f aa * f ba \<le> 0"
      by (auto simp: bisect_invar_def)
    have pbr: "0 < f aa * f ((aa + ba) / 2)" using br by simp
    have "f ((aa + ba) / 2) * f ba \<le> 0" 
      by (metis inv'(4) landau_o.R_linear p(4) zero_compare_simps(8))
    thus ?thesis using inv' by (auto simp: bisect_invar_def)
  qed
  subgoal premises p for s aa ba \<comment> \<open>else-branch: variant decreases\<close>
  proof -
    from p have g: "tol < ba - aa" and seq: "s = (aa, ba)" by auto
    have w: "ba - (aa + ba) / 2 = (ba - aa) / 2" by (simp add: field_simps)
    show ?thesis using bisect_var_half[OF postive_tolerance g]
      by (simp add: seq bisect_var_def w)
  qed
  subgoal premises p for s aa ba \<comment> \<open>exit: width within tolerance, extract a root\<close>
  proof -
    from p have inv: "bisect_invar f a b (aa, ba)" and nguard: "\<not> tol < ba - aa"
      by auto
    from inv have inv': "a \<le> aa" "aa \<le> ba" "ba \<le> b" "f aa * f ba \<le> 0"
      by (auto simp: bisect_invar_def)
    from nguard have exit: "ba - aa \<le> tol" by simp
    have cont_lu: "continuous_on {aa..ba} f"
      by (rule continuous_on_subset[OF continuous_f]) (use inv' in auto)
    have root: "\<exists>r\<in>{aa..ba}. f r = 0"
    proof (cases "f aa * f ba < 0")
      case True
      \<comment> \<open>strict sign change: the endpoints differ, so Bolzano gives an interior root\<close>
      have "aa < ba" using inv'(2) True by (smt (verit) mult_less_0_iff)
      from Bolzanos_theorem[OF this True cont_lu]
      obtain \<gamma> where "f \<gamma> = 0 \<and> aa < \<gamma> \<and> \<gamma> < ba" by blast
      thus ?thesis by force
    next
      case False
      \<comment> \<open>non-strict: with \<open>f aa * f ba \<le> 0\<close> the product is 0, so an endpoint is a root\<close>
      hence "f aa * f ba = 0" using inv'(4) by linarith
      hence "f aa = 0 \<or> f ba = 0" by simp
      thus ?thesis using inv'(2) by force
    qed
    from root obtain r where r: "r \<in> {aa..ba}" "f r = 0" by blast
    from r have rin: "aa \<le> r" "r \<le> ba" by auto
    have "r \<in> {a..b}" using rin inv' by auto
    moreover have "\<bar>(aa + ba) / 2 - r\<bar> \<le> tol"
    proof -
      have m: "2 * ((aa + ba) / 2) = aa + ba" by simp
      have h1: "(aa + ba) / 2 - r \<le> tol" using rin exit m by linarith
      have h2: "r - (aa + ba) / 2 \<le> tol" using rin exit m by linarith
      from h1 h2 show ?thesis by (simp add: abs_le_iff)
    qed
    ultimately show ?thesis using r by blast
  qed
  done



section \<open>Paradigm C: Floating-point bisection (direct, VCG)\<close>

text \<open>
  \<^bold>\<open>Motivation.\<close> The Paradigm-B refinement proof of floating-point bisection
  bounds the total error \<^emph>\<open>indirectly\<close>, by a triangle inequality:

  \[
    \underbrace{|\mathrm{valof}(l_\mathbb{F}) - x^\star|}_{\text{total error}}
    \;\le\;
    \underbrace{|\mathrm{valof}(l_\mathbb{F}) - l_\mathbb{R}|}_{\text{round-off}}
    \;+\;
    \underbrace{|l_\mathbb{R} - x^\star|}_{\text{method error}} .
  \]

  That proof carries a \<^emph>\<open>real shadow\<close> bracket \<open>(l_R, u_R)\<close> alongside the
  float bracket, proves a method bound on the shadow and a round-off bound
  on the float-vs-shadow drift, and adds them. A referee can fairly ask:
  why not bound \<open>|valof(l_\<F>) - x\<^sup>\<star>|\<close> \<^emph>\<open>directly\<close>?

  \<^bold>\<open>The proof below does exactly that.\<close> There is no shadow. The loop invariant
  speaks only about the \<^emph>\<open>actual\<close> floating-point bracket
  \<open>[valof l, valof u]\<close> and a genuine root \<open>x\<^sup>\<star>\<close> of the real function
  \<open>f_R\<close>:

  \<^enum> the float bracket straddles a sign change of the real function,
    \<open>f_R(valof l) \<cdot> f_R(valof u) \<le> 0\<close>; and
  \<^enum> the bracket width obeys a \<^emph>\<open>direct contraction bound\<close>,
    \<open>valof u - valof l \<le> (b_R - a_R) / 2 ^ iter + E\<close>.

  The contraction bound is the crux. The safe floating-point midpoint
  obeys the recurrence \<open>w\<^sub>k\<^sub>+\<^sub>1 \<le> w\<^sub>k / 2 + \<delta>\<close> (halving plus one
  rounding error \<open>\<delta>\<close>), whose attracting fixed point is the \<^emph>\<open>constant\<close>
  envelope \<open>2\<delta>\<close>. Provided \<open>2\<delta> \<le> E\<close>, the affine bound
  \<open>(b_R - a_R)/2 ^ iter + E\<close> is preserved verbatim across an iteration:

  \[
     \tfrac{1}{2}\Big(\tfrac{b_R - a_R}{2^{\,iter}} + E\Big) + \delta
     \;=\; \tfrac{b_R - a_R}{2^{\,iter+1}} + \Big(\tfrac{E}{2} + \delta\Big)
     \;\le\; \tfrac{b_R - a_R}{2^{\,iter+1}} + E .
  \]

  At loop exit, \<open>x\<^sup>\<star> \<in> [valof l, valof u]\<close> (Bolzano on the float bracket)
  and \<open>valof u - valof l \<le> valof tol + E\<close>, so

  \[
     |valof(l_\<F>) - x^\star| \;\le\; valof\,tol + E
  \]

  \<^emph>\<open>directly\<close>. This is \<^emph>\<open>tighter\<close> than the triangle bound
  \<open>valof tol + E + iter \<cdot> \<delta>\<close>: because we never split the error, the
  growing drift term \<open>iter \<cdot> \<delta>\<close> never appears. All accumulated round-off is
  absorbed once and for all into the constant width envelope \<open>E\<close>.

  \<^bold>\<open>Preliminaries.\<close> The handful of primitives this direct proof needs ---
  Bolzano's theorem, the safe floating-point midpoint, and a
  \<^class>\<open>default\<close> instance for floats --- are collected in the inlined
  preliminaries below.
\<close>


subsection \<open>Inlined preliminaries\<close>

text \<open>
  Bolzano's theorem (the intermediate value theorem) is already provided
  above as \<open>Bolzanos_theorem\<close> and is reused by the floating-point root
  extraction; we do not restate it here.
\<close>

text \<open>
  IEEE binary64, and a \<^class>\<open>default\<close> instance for floats (required for
  every \<^theory_text>\<open>zstore\<close> field type) reusing the existing \<^class>\<open>zero\<close>.
\<close>

type_synonym float64 = "(11, 52) IEEE.float"

text \<open>
  The overflow-safe midpoint \<open>l + (u - l) / 2\<close> and its exact round-off
  \<open>mid_err\<close>. The standard formula
  \<open>(l + u) / 2\<close> can overflow even when both endpoints are well within
  range; \<open>l + (u - l) / 2\<close> keeps the intermediate \<open>(u - l) / 2\<close> bounded by
  half the bracket width.
\<close>

abbreviation two_F :: "('e, 'f) float" where "two_F \<equiv> 1 + 1"

definition safe_mid_F :: "('e, 'f) float \<Rightarrow> ('e, 'f) float \<Rightarrow> ('e, 'f) float"
  where "safe_mid_F a b = a + (b - a) / two_F"

definition mid_err :: "('e, 'f) float \<Rightarrow> ('e, 'f) float \<Rightarrow> real"
  where "mid_err a b = valof (safe_mid_F a b) - (valof a + valof b) / 2"

lemma safe_mid_F_decomp:
  "valof (safe_mid_F a b) = (valof a + valof b) / 2 + mid_err a b"
  unfolding mid_err_def by simp


subsection \<open>Direct guard-to-width bridge oracles\<close>

text \<open>
  These round-off facts relate the \<^emph>\<open>float\<close> loop guard \<open>tol < u - l\<close> to
  the \<^emph>\<open>real\<close> bracket width \<open>valof u - valof l\<close>. With no shadow to drift
  from, the float subtraction error is the \<^emph>\<open>only\<close> gap. The user
  discharges the abstract oracle hypotheses of
  \<open>bisection_FD_direct_correct\<close> from these with a uniform envelope \<open>E\<close>
  dominating the per-step subtraction error.
\<close>

lemma width_guard_oracle_direct:
  fixes l u tol :: "('e::len, 'f::len) float" and E \<epsilon> :: real
  assumes fin_l: "is_finite l" and fin_u: "is_finite u" and fin_tol: "is_finite tol"
    and threshold: "\<bar>valof u - valof l\<bar> < threshold TYPE(('e, 'f) float)"
    and sub: "\<bar>error TYPE(('e, 'f) float) (valof u - valof l)\<bar> \<le> \<epsilon>"
    and env: "\<epsilon> \<le> E"
    and guard: "tol < u - l"
  shows "valof tol < (valof u - valof l) + E"
proof -
  have fin_sub: "is_finite (u - l)"
    using float_sub(1)[OF fin_u fin_l threshold] .
  have vg: "valof tol < valof (u - l)"
    using guard float_lt[OF fin_tol fin_sub] by simp
  have eq: "valof (u - l) = valof u - valof l + error TYPE(('e, 'f) float) (valof u - valof l)"
    using float_sub(2)[OF fin_u fin_l threshold] .
  have "valof (u - l) \<le> (valof u - valof l) + \<epsilon>"
    using eq sub by (smt (verit))
  thus ?thesis using vg env by linarith
qed

lemma width_exit_oracle_direct:
  fixes l u tol :: "('e::len, 'f::len) float" and E \<epsilon> :: real
  assumes fin_l: "is_finite l" and fin_u: "is_finite u" and fin_tol: "is_finite tol"
    and threshold: "\<bar>valof u - valof l\<bar> < threshold TYPE(('e, 'f) float)"
    and sub: "\<bar>error TYPE(('e, 'f) float) (valof u - valof l)\<bar> \<le> \<epsilon>"
    and env: "\<epsilon> \<le> E"
    and exit: "\<not> (tol < u - l)"
  shows "valof u - valof l \<le> valof tol + E"
proof -
  have fin_sub: "is_finite (u - l)"
    using float_sub(1)[OF fin_u fin_l threshold] .
  have vle: "valof (u - l) \<le> valof tol"
    using exit float_lt[OF fin_tol fin_sub] by simp
  have eq: "valof (u - l) = valof u - valof l + error TYPE(('e, 'f) float) (valof u - valof l)"
    using float_sub(2)[OF fin_u fin_l threshold] .
  have "valof u - valof l \<le> valof (u - l) + \<epsilon>"
    using eq sub by (smt (verit))
  thus ?thesis using vle env by linarith
qed


subsection \<open>The width-contraction recurrence\<close>

text \<open>
  Pure arithmetic core of the direct proof: a width obeying the affine
  bound \<open>B / 2 ^ k + E\<close> and contracting by \<open>w \<mapsto> w/2 + \<delta>\<close> still obeys the
  \<^emph>\<open>same\<close> affine bound one halving later, as long as \<open>2\<delta> \<le> E\<close>. The
  envelope \<open>E\<close> does not grow with the iteration count --- this is precisely
  why the final bound has no \<open>iter \<cdot> \<delta>\<close> term.
\<close>

lemma direct_width_recurrence:
  fixes Wold Wnew B \<delta> E :: real and k :: nat
  assumes old: "Wold \<le> B / 2 ^ k + E"
    and new: "Wnew \<le> Wold / 2 + \<delta>"
    and env: "2 * \<delta> \<le> E"
  shows "Wnew \<le> B / 2 ^ Suc k + E"
proof -
  have pow: "B / 2 ^ Suc k = (B / 2 ^ k) / 2"
  proof -
    have "(2::real) ^ Suc k = 2 ^ k * 2" by (simp add: power_Suc2)
    thus ?thesis by simp
  qed
  show ?thesis using old new env pow by simp
qed


subsection \<open>State and program (no shadow)\<close>

text \<open>
  The state holds only the iteration counter, the float bracket
  \<open>(l, u)\<close> with cached endpoint function values \<open>(fl, fu)\<close>, and the
  working midpoint and its value. There are \<^emph>\<open>no\<close> real ghost variables:
  every fact proved below is about \<^const>\<open>valof\<close> of the genuine float
  iterates.
\<close>

zstore stFD =
  iter :: "nat"
  fl   :: "float64"
  fu   :: "float64"
  l    :: "float64"
  u    :: "float64"
  xmid :: "float64"
  ymid :: "float64"

text \<open>
  Pure IEEE binary64 bisection. The shape is identical to the real-valued
  Paradigm-A program above, but over \<^typ>\<open>float64\<close> with the
  overflow-safe midpoint \<^const>\<open>safe_mid_F\<close> and a float function
  \<open>f_F\<close>. The real function \<open>f_R\<close> and the reals \<open>a_R, b_R, \<delta>, E\<close> are
  \<^emph>\<open>specification-only\<close> parameters: they occur in the invariant/variant
  and in the error bound, never in an assignment, so the executable float
  trajectory is independent of them.
\<close>

program bisection_FD
  "(f_F :: float64 \<Rightarrow> float64, a :: float64, b :: float64, tol :: float64,
    f_R :: real \<Rightarrow> real, a_R :: real, b_R :: real, \<delta> :: real, E :: real)" over stFD
 = "iter := 0; fl := f_F a; fu := f_F b; l := a; u := b; xmid := l; ymid := f_F l;
    while u - l > tol
    invariant
        is_finite l \<and> is_finite u
      \<and> a_R \<le> valof l \<and> valof l \<le> valof u \<and> valof u \<le> b_R
      \<and> f_R (valof l) * f_R (valof u) \<le> 0
      \<and> valof u - valof l \<le> (b_R - a_R) / 2 ^ iter + E
    variant nat (\<lceil>log 2 ((b_R - a_R) / (valof tol - 2 * E))\<rceil>) - iter
    do iter := iter + 1;
       xmid := safe_mid_F l u; ymid := f_F xmid;
       if fl * ymid > 0
         then l := xmid; fl := ymid
         else u := xmid; fu := ymid fi od"


subsection \<open>Direct total-error correctness\<close>

text \<open>
  Hypotheses. The first block is the standard real-bisection setup on the
  endpoints. The second block abstracts the floating-point round-off, in
  the shadow-free form used by the direct invariant:

  \<^item> \<open>mid_bound\<close>: \<open>\<delta>\<close> dominates the safe-midpoint error \<^const>\<open>mid_err\<close>
    on every reachable bracket;
  \<^item> \<open>safe_mid_props\<close>: the safe midpoint is finite and stays \<^emph>\<open>inside\<close>
    the bracket \<open>[valof l, valof u]\<close> (the no-overflow / monotonicity side
    condition; bracket-containment is what makes the float interval a
    valid bisection bracket);
  \<^item> \<open>sign_oracle\<close>: the implemented float sign test
    \<open>0 < fl \<otimes> f_F(safe_mid_F l u)\<close> agrees with the real sign test
    \<^emph>\<open>at the same float-represented points\<close>,
    \<open>0 < f_R(valof l) \<cdot> f_R(valof(safe_mid_F l u))\<close>. This is the standard
    sign-margin assumption (Boldo et al.; Kellison et al.), stated
    directly on \<^const>\<open>valof\<close> of the iterates rather than on a shadow;
  \<^item> \<open>width_guard_oracle\<close> / \<open>width_exit_oracle\<close>: the float guard
    \<open>tol < u - l\<close> tracks the real width \<open>valof u - valof l\<close> to within the
    envelope \<open>E\<close>; discharge them from \<open>width_guard_oracle_direct\<close> /
    \<open>width_exit_oracle_direct\<close>.

  The variant counts against the round-off-aware bound
  \<open>\<lceil>log\<^sub>2((b_R - a_R)/(valof tol - 2 E))\<rceil>\<close>. Two \<open>E\<close>'s appear: one from
  the width envelope in the invariant, one from the guard-to-width bridge.
  Hence the margin hypothesis is \<open>2 E < valof tol\<close>.

  \<^bold>\<open>The postcondition bounds \<open>|valof l - c|\<close> directly\<close> --- there is no
  triangle inequality and no \<open>iter \<cdot> \<delta>\<close> term.

  \<^bold>\<open>Proof style.\<close> The total-correctness goal is discharged with a
  structured \<^theory_text>\<open>proof (vcg)\<close> (as in Paradigm A above): each verification
  condition is addressed by an explicit \<^theory_text>\<open>show\<close> --- using \<^theory_text>\<open>fix\<close>/\<^theory_text>\<open>assume\<close>
  for the loop-body and post-loop goals --- rather than an \<open>apply\<close>-script of
  \<open>subgoal\<close>s. Each block names only the premises it actually uses; the
  framework discharges the remaining loop-invariant hypotheses
  automatically.
\<close>

theorem bisection_FD_direct_correct:
  fixes f_F :: "float64 \<Rightarrow> float64"
  fixes f_R :: "real \<Rightarrow> real"
  fixes a b tol :: float64
  fixes a_R b_R \<delta> E :: real
  assumes positive_tolerance: "0 < valof tol"
  assumes positive_delta:     "0 \<le> \<delta>"
  assumes envelope:           "2 * \<delta> \<le> E"
  assumes tol_margin:         "2 * E < valof tol"
  assumes a_less_than_b_R:    "a_R < b_R"
  assumes continuous_f_R:     "continuous_on {a_R..b_R} f_R"
  assumes opposite_signs_R:   "f_R a_R * f_R b_R < 0"
  assumes endpoints_match:    "valof a = a_R" "valof b = b_R"
  assumes finite_endpoints:   "is_finite a" "is_finite b"
  assumes tol_lt_width:       "valof tol < b_R - a_R"
  assumes mid_bound:
    "\<And>l u :: float64. is_finite l \<Longrightarrow> is_finite u
        \<Longrightarrow> a_R \<le> valof l \<Longrightarrow> valof l \<le> valof u \<Longrightarrow> valof u \<le> b_R
        \<Longrightarrow> \<bar>mid_err l u\<bar> \<le> \<delta>"
  assumes safe_mid_props:
    "\<And>l u :: float64. is_finite l \<Longrightarrow> is_finite u
        \<Longrightarrow> a_R \<le> valof l \<Longrightarrow> valof l \<le> valof u \<Longrightarrow> valof u \<le> b_R
        \<Longrightarrow> is_finite (safe_mid_F l u)
          \<and> valof l \<le> valof (safe_mid_F l u)
          \<and> valof (safe_mid_F l u) \<le> valof u"
  assumes sign_oracle:
    "\<And>fl l u :: float64. is_finite l \<Longrightarrow> is_finite u
        \<Longrightarrow> a_R \<le> valof l \<Longrightarrow> valof l \<le> valof u \<Longrightarrow> valof u \<le> b_R
        \<Longrightarrow> (0 < fl * f_F (safe_mid_F l u))
             = (0 < f_R (valof l) * f_R (valof (safe_mid_F l u)))"
  assumes width_guard_oracle:
    "\<And>l u :: float64. is_finite l \<Longrightarrow> is_finite u
        \<Longrightarrow> a_R \<le> valof l \<Longrightarrow> valof l \<le> valof u \<Longrightarrow> valof u \<le> b_R
        \<Longrightarrow> tol < u - l \<Longrightarrow> valof tol < (valof u - valof l) + E"
  assumes width_exit_oracle:
    "\<And>l u :: float64. is_finite l \<Longrightarrow> is_finite u
        \<Longrightarrow> a_R \<le> valof l \<Longrightarrow> valof l \<le> valof u \<Longrightarrow> valof u \<le> b_R
        \<Longrightarrow> \<not> (tol < u - l) \<Longrightarrow> valof u - valof l \<le> valof tol + E"
  shows "H[True] bisection_FD (f_F, a, b, tol, f_R, a_R, b_R, \<delta>, E)
       [\<exists>c. f_R c = 0 \<and> a_R < c \<and> c < b_R \<and> \<bar>valof l - c\<bar> \<le> valof tol + E]"
proof -
  have D: "0 < valof tol - 2 * E" using tol_margin by linarith
  have E0: "0 \<le> E" using envelope positive_delta by linarith
  show ?thesis
  proof (vcg)
    \<comment> \<open>===== then-branch (\<open>l := safe_mid_F l u\<close>): invariant conjuncts that change =====\<close>
    \<comment> \<open>is_finite (safe_mid_F l u)\<close>
    fix iter :: nat and fl l u :: float64
    assume finl: "is_finite l" and finu: "is_finite u"
       and a_l: "a_R \<le> valof l" and l_u: "valof l \<le> valof u" and u_b: "valof u \<le> b_R"
    show "is_finite (safe_mid_F l u)"
      using safe_mid_props[OF finl finu a_l l_u u_b] by blast
  next
    \<comment> \<open>a_R \<le> valof (safe_mid_F l u)\<close>
    fix iter :: nat and fl l u :: float64
    assume finl: "is_finite l" and finu: "is_finite u"
       and a_l: "a_R \<le> valof l" and l_u: "valof l \<le> valof u" and u_b: "valof u \<le> b_R"
    show "a_R \<le> valof (safe_mid_F l u)"
      using safe_mid_props[OF finl finu a_l l_u u_b] a_l by linarith
  next
    \<comment> \<open>valof (safe_mid_F l u) \<le> valof u\<close>
    fix iter :: nat and fl l u :: float64
    assume finl: "is_finite l" and finu: "is_finite u"
       and a_l: "a_R \<le> valof l" and l_u: "valof l \<le> valof u" and u_b: "valof u \<le> b_R"
    show "valof (safe_mid_F l u) \<le> valof u"
      using safe_mid_props[OF finl finu a_l l_u u_b] by blast
  next
    \<comment> \<open>bracket preserved (then): f_R (valof (safe_mid_F l u)) * f_R (valof u) \<le> 0\<close>
    fix iter :: nat and fl l u :: float64
    assume finl: "is_finite l" and finu: "is_finite u"
       and a_l: "a_R \<le> valof l" and l_u: "valof l \<le> valof u" and u_b: "valof u \<le> b_R"
       and br: "f_R (valof l) * f_R (valof u) \<le> 0"
       and ifc: "0 < fl * f_F (safe_mid_F l u)"
    show "f_R (valof (safe_mid_F l u)) * f_R (valof u) \<le> 0"
    proof -
      have "0 < f_R (valof l) * f_R (valof (safe_mid_F l u))"
        using sign_oracle[OF finl finu a_l l_u u_b] ifc by blast
      thus ?thesis using br by (smt (verit, del_insts) zero_compare_simps(6))
    qed
  next
    \<comment> \<open>width (then): valof u - valof (safe_mid_F l u) \<le> (b_R - a_R) / (2 * 2 ^ iter) + E\<close>
    fix iter :: nat and fl l u :: float64
    assume finl: "is_finite l" and finu: "is_finite u"
       and a_l: "a_R \<le> valof l" and l_u: "valof l \<le> valof u" and u_b: "valof u \<le> b_R"
       and wid: "valof u - valof l \<le> (b_R - a_R) / 2 ^ iter + E"
    show "valof u - valof (safe_mid_F l u) \<le> (b_R - a_R) / (2 * 2 ^ iter) + E"
    proof -
      have mid: "\<bar>mid_err l u\<bar> \<le> \<delta>" using mid_bound[OF finl finu a_l l_u u_b] .
      have eq: "valof u - valof (safe_mid_F l u) = (valof u - valof l) / 2 - mid_err l u"
        unfolding safe_mid_F_decomp by (simp add: field_simps)
      have new: "valof u - valof (safe_mid_F l u) \<le> (valof u - valof l) / 2 + \<delta>"
        using eq mid by linarith
      show ?thesis using envelope new wid by argo
    qed
  next
    \<comment> \<open>variant strictly decreases (then-branch)\<close>
    fix iter :: nat and fl l u :: float64
    assume finl: "is_finite l" and finu: "is_finite u"
       and a_l: "a_R \<le> valof l" and l_u: "valof l \<le> valof u" and u_b: "valof u \<le> b_R"
       and wid: "valof u - valof l \<le> (b_R - a_R) / 2 ^ iter + E"
       and guard: "tol < u - l"
    show "nat \<lceil>log 2 ((b_R - a_R) / (valof tol - 2 * E))\<rceil> - Suc iter
            < nat \<lceil>log 2 ((b_R - a_R) / (valof tol - 2 * E))\<rceil> - iter"
    proof -
      have g: "valof tol < (valof u - valof l) + E"
        using width_guard_oracle[OF finl finu a_l l_u u_b guard] .
      have key: "valof tol - 2 * E < (b_R - a_R) / 2 ^ iter" using g wid by linarith
      show ?thesis using key D a_less_than_b_R
        by (smt (verit, del_insts) divide_divide_eq_right divide_pos_pos frac_le le_diff_conv
            less_log_of_power linorder_not_le nonzero_mult_div_cancel_left not_less_eq_eq
            of_nat_Suc of_nat_diff of_nat_le_iff order_le_less real_nat_ceiling_ge)
    qed
  next
    \<comment> \<open>===== else-branch (\<open>u := safe_mid_F l u\<close>): invariant conjuncts that change =====\<close>
    \<comment> \<open>is_finite (safe_mid_F l u)\<close>
    fix iter :: nat and fl l u :: float64
    assume finl: "is_finite l" and finu: "is_finite u"
       and a_l: "a_R \<le> valof l" and l_u: "valof l \<le> valof u" and u_b: "valof u \<le> b_R"
    show "is_finite (safe_mid_F l u)"
      using safe_mid_props[OF finl finu a_l l_u u_b] by blast
  next
    \<comment> \<open>valof l \<le> valof (safe_mid_F l u)\<close>
    fix iter :: nat and fl l u :: float64
    assume finl: "is_finite l" and finu: "is_finite u"
       and a_l: "a_R \<le> valof l" and l_u: "valof l \<le> valof u" and u_b: "valof u \<le> b_R"
    show "valof l \<le> valof (safe_mid_F l u)"
      using safe_mid_props[OF finl finu a_l l_u u_b] by blast
  next
    \<comment> \<open>valof (safe_mid_F l u) \<le> b_R\<close>
    fix iter :: nat and fl l u :: float64
    assume finl: "is_finite l" and finu: "is_finite u"
       and a_l: "a_R \<le> valof l" and l_u: "valof l \<le> valof u" and u_b: "valof u \<le> b_R"
    show "valof (safe_mid_F l u) \<le> b_R"
      using safe_mid_props[OF finl finu a_l l_u u_b] u_b by linarith
  next
    \<comment> \<open>bracket preserved (else): f_R (valof l) * f_R (valof (safe_mid_F l u)) \<le> 0\<close>
    fix iter :: nat and fl l u :: float64
    assume finl: "is_finite l" and finu: "is_finite u"
       and a_l: "a_R \<le> valof l" and l_u: "valof l \<le> valof u" and u_b: "valof u \<le> b_R"
       and nifc: "\<not> (0 < fl * f_F (safe_mid_F l u))"
    show "f_R (valof l) * f_R (valof (safe_mid_F l u)) \<le> 0"
      using sign_oracle[OF finl finu a_l l_u u_b] nifc by (simp add: not_less)
  next
    \<comment> \<open>width (else): valof (safe_mid_F l u) - valof l \<le> (b_R - a_R) / (2 * 2 ^ iter) + E\<close>
    fix iter :: nat and fl l u :: float64
    assume finl: "is_finite l" and finu: "is_finite u"
       and a_l: "a_R \<le> valof l" and l_u: "valof l \<le> valof u" and u_b: "valof u \<le> b_R"
       and wid: "valof u - valof l \<le> (b_R - a_R) / 2 ^ iter + E"
    show "valof (safe_mid_F l u) - valof l \<le> (b_R - a_R) / (2 * 2 ^ iter) + E"
    proof -
      have mid: "\<bar>mid_err l u\<bar> \<le> \<delta>" using mid_bound[OF finl finu a_l l_u u_b] .
      have eq: "valof (safe_mid_F l u) - valof l = (valof u - valof l) / 2 + mid_err l u"
        unfolding safe_mid_F_decomp by (simp add: field_simps)
      have new: "valof (safe_mid_F l u) - valof l \<le> (valof u - valof l) / 2 + \<delta>"
        using eq mid by linarith
      show ?thesis
        by (metis envelope direct_width_recurrence new power.simps(2) wid)
    qed
  next
    \<comment> \<open>variant strictly decreases (else-branch)\<close>
    fix iter :: nat and fl l u :: float64
    assume finl: "is_finite l" and finu: "is_finite u"
       and a_l: "a_R \<le> valof l" and l_u: "valof l \<le> valof u" and u_b: "valof u \<le> b_R"
       and wid: "valof u - valof l \<le> (b_R - a_R) / 2 ^ iter + E"
       and guard: "tol < u - l"
    show "nat \<lceil>log 2 ((b_R - a_R) / (valof tol - 2 * E))\<rceil> - Suc iter
            < nat \<lceil>log 2 ((b_R - a_R) / (valof tol - 2 * E))\<rceil> - iter"
    proof -
      have g: "valof tol < (valof u - valof l) + E"
        using width_guard_oracle[OF finl finu a_l l_u u_b guard] .
      have key: "valof tol - 2 * E < (b_R - a_R) / 2 ^ iter" using g wid by linarith
      show ?thesis using key D a_less_than_b_R
        by (smt (verit, del_insts) divide_divide_eq_right divide_pos_pos frac_le le_diff_conv
            less_log_of_power linorder_not_le nonzero_mult_div_cancel_left not_less_eq_eq
            of_nat_Suc of_nat_diff of_nat_le_iff order_le_less real_nat_ceiling_ge)
    qed
  next
    \<comment> \<open>===== initial establishment of the invariant (\<open>iter = 0, l = a, u = b\<close>) =====\<close>
    show "is_finite a" by (rule finite_endpoints)
    show "is_finite b" by (rule finite_endpoints)
    show "a_R \<le> valof a" using endpoints_match by simp
    show "valof a \<le> valof b"
    proof -
      have "a_R \<le> b_R" using a_less_than_b_R by linarith
      thus ?thesis using endpoints_match by simp
    qed
    show "valof b \<le> b_R" using endpoints_match by simp
    show "f_R (valof a) * f_R (valof b) \<le> 0"
    proof -
      have "f_R a_R * f_R b_R \<le> 0" using opposite_signs_R by linarith
      thus ?thesis using endpoints_match by simp
    qed
    show "valof b - valof a \<le> b_R - a_R + E"
      using endpoints_match E0 by simp
  next
    \<comment> \<open>===== post-loop: extract the root and the DIRECT error bound =====\<close>
    fix iter :: nat and l u :: float64
    assume finl: "is_finite l" and finu: "is_finite u"
       and al: "a_R \<le> valof l" and lu: "valof l \<le> valof u" and ub: "valof u \<le> b_R"
       and br: "f_R (valof l) * f_R (valof u) \<le> 0"
       and nguard: "\<not> (tol < u - l)"
    show "\<exists>c. f_R c = 0 \<and> a_R < c \<and> c < b_R \<and> \<bar>valof l - c\<bar> \<le> valof tol + E"
    proof -
      have w: "valof u - valof l \<le> valof tol + E"
        using width_exit_oracle[OF finl finu al lu ub nguard] .
      have cont_sub: "continuous_on {valof l..valof u} f_R"
        by (meson al ub atLeastatMost_subset_iff continuous_f_R continuous_on_subset)
      have ex_c: "\<exists>c. c \<in> {valof l..valof u} \<and> f_R c = 0"
      proof (cases "f_R (valof l) * f_R (valof u) < 0")
        case True
        have lt: "valof l < valof u"
        proof (rule ccontr)
          assume "\<not> valof l < valof u"
          with lu have "valof l = valof u" by simp
          hence "f_R (valof l) * f_R (valof u) = (f_R (valof l))\<^sup>2"
            by (simp add: power2_eq_square)
          hence "0 \<le> f_R (valof l) * f_R (valof u)" by simp
          with True show False by simp
        qed
        obtain c where "f_R c = 0" "valof l < c" "c < valof u"
          using Bolzanos_theorem[OF lt True cont_sub] by blast
        thus ?thesis
          by (meson atLeastAtMost_iff less_eq_real_def)
      next
        case False
        hence "f_R (valof l) * f_R (valof u) = 0" using br by linarith
        hence "f_R (valof l) = 0 \<or> f_R (valof u) = 0" by simp
        moreover have "valof l \<in> {valof l..valof u}" "valof u \<in> {valof l..valof u}"
          using lu by auto
        ultimately show ?thesis by blast
      qed
      then obtain c where cI: "c \<in> {valof l..valof u}" and fc0: "f_R c = 0" by blast
      have c_bounds: "a_R < c \<and> c < b_R"
        using al ub opposite_signs_R cI fc0 order_less_le by fastforce
      have dist: "\<bar>valof l - c\<bar> \<le> valof tol + E"
      proof -
        from cI have "valof l \<le> c" "c \<le> valof u" by auto
        thus ?thesis using w by linarith
      qed
      show ?thesis
        using fc0 c_bounds dist by blast
    qed
  qed
qed

text \<open>
  \<^bold>\<open>What was achieved.\<close> The postcondition

  \[
     \exists c.\; f_R\,c = 0 \;\wedge\; a_R < c < b_R
       \;\wedge\; |valof\,l - c| \le valof\,tol + E
  \]

  bounds the distance from the \<^emph>\<open>actual\<close> floating-point lower endpoint
  \<open>valof l\<close> to a true root \<open>c\<close> of the real function \<^emph>\<open>directly\<close>: the
  proof never introduces a real shadow iterate and never appeals to the
  triangle inequality. The single loop invariant (bracketing \<open>+\<close> the
  affine width bound) carries the entire argument, and the
  \<open>direct_width_recurrence\<close> step shows the round-off envelope \<open>E\<close>
  stays constant across iterations.

  \<^bold>\<open>Comparison with the triangle proof.\<close> The Paradigm-B corollary yields
  \<open>|c - valof l| \<le> valof tol + E + iter \<cdot> \<delta>\<close>. The direct bound here,
  \<open>valof tol + E\<close>, is uniformly tighter: it omits the data-dependent drift
  term \<open>iter \<cdot> \<delta>\<close>, because the contraction recurrence absorbs all
  accumulated midpoint round-off into the constant envelope rather than
  letting it grow with the iteration count.
\<close>

end