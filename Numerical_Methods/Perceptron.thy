section \<open>Perceptron: VCG, Lammich, and Floating-Point Verification\<close>

theory Perceptron
  imports
    "Refine_Monadic.Refine_Monadic"
    Float_Vector
    Float_Default
begin

text \<open>
  Two verifications of the SAME perceptron learning algorithm. Paradigm A is the
  imperative ITree program discharged by the VCG-based Hoare logic. Paradigm B
  replays it in Lammich's Refinement Framework:
  the bounded inner pass over the data is a pure \<open>foldl\<close>, and the outer
  ``while changed'' loop is a \<open>WHILET\<close> whose termination is the Novikoff
  mistake bound. The per-update mathematics is factored into shared lemmas used
  by both paradigms.
\<close>

section \<open>Shared per-update mathematics\<close>

text \<open>
  The three facts that drive the convergence argument, stated independently of
  any program so that both paradigms can invoke them. \<open>perc_margin_step\<close> and
  \<open>perc_norm_step\<close> are the two \<open>next\<close> blocks of the VCG proof; \<open>perc_mistake_bound\<close>
  is the Cauchy--Schwarz mistake bound (Novikoff). Variables: \<open>\<theta>, b\<close> the
  separating hyperplane; \<open>w, c\<close> the current weights/bias; \<open>xt, yt\<close> a data point;
  \<open>u\<close> the update count.
\<close>

lemma perc_margin_step:
  fixes \<theta> w xt :: "real vec['n]" and b c yt \<gamma> :: real and u :: nat
  assumes lab: "yt \<in> {-1, 1}"
    and marg: "\<gamma> \<le> yt *\<^sub>R (xt \<bullet> \<theta> + b)"
    and inv: "real u * \<gamma> \<le> \<theta> \<bullet> w + b * c"
  shows "(1 + real u) * \<gamma> \<le> \<theta> \<bullet> (w + yt *\<^sub>R xt) + b * (c + yt)"
proof -
  have "\<theta> \<bullet> (w + yt *\<^sub>R xt) + b * (c + yt) = \<theta> \<bullet> w + \<theta> \<bullet> (yt *\<^sub>R xt) + b * c + b * yt"
    using cross3_simps(35)
    by (smt (verit, ccfv_SIG) inner_real_def insert_iff real_inner_1_right singletonD)
  also have "... = \<theta> \<bullet> w + b * c + \<theta> \<bullet> (yt *\<^sub>R xt) + b * yt"
    by (clarsimp simp: field_simps)
  also have "... = \<theta> \<bullet> w + b * c + yt *\<^sub>R (xt \<bullet> \<theta> + b)"
    using lab by (simp add: cross3_simps(24,7) inner_commute)
  also have "... \<ge> \<theta> \<bullet> w + b * c + \<gamma>"
    using marg by linarith
  also have "\<theta> \<bullet> w + b * c + \<gamma> \<ge> real u * \<gamma> + \<gamma>"
    using inv by linarith
  finally show "(1 + real u) * \<gamma> \<le> \<theta> \<bullet> (w + yt *\<^sub>R xt) + b * (c + yt)"
    by (simp add: cross3_simps(11,24))
qed

lemma perc_norm_step:
  fixes w xt :: "real vec['n]" and c yt R :: real and u :: nat
  assumes lab: "yt \<in> {-1, 1}"
    and bnd: "\<parallel>xt\<parallel>\<^sup>2 + 1 \<le> R\<^sup>2"
    and mistake: "yt * (xt \<bullet> w + c) \<le> 0"
    and inv: "\<parallel>w\<parallel>\<^sup>2 + c\<^sup>2 \<le> real u * R\<^sup>2"
  shows "\<parallel>w + yt *\<^sub>R xt\<parallel>\<^sup>2 + (c + yt)\<^sup>2 \<le> (1 + real u) * R\<^sup>2"
proof -
  have "\<parallel>w + yt *\<^sub>R xt\<parallel>\<^sup>2 + (c + yt)\<^sup>2 =
        \<parallel>w\<parallel>\<^sup>2 + \<parallel>yt *\<^sub>R xt\<parallel>\<^sup>2 + 2 * (w \<bullet> (yt *\<^sub>R xt)) + c\<^sup>2 + yt\<^sup>2 + 2 * c * yt"
    using dot_norm[of w "yt *\<^sub>R xt"] power2_sum[of c yt] by (clarsimp simp: field_simps)
  also have "... = \<parallel>w\<parallel>\<^sup>2 + \<parallel>yt *\<^sub>R xt\<parallel>\<^sup>2 + 2 * (yt *\<^sub>R (xt \<bullet> w)) + c\<^sup>2 + yt\<^sup>2 + 2 * c * yt"
    using inner_commute lab by (smt (verit, ccfv_SIG) inner_scaleR_right real_scaleR_def)
  also have "... \<le> \<parallel>w\<parallel>\<^sup>2 + R\<^sup>2 + c\<^sup>2"
    using mistake lab bnd by fastforce
  also have "... \<le> real u * R\<^sup>2 + R\<^sup>2"
    using inv by linarith
  finally show "\<parallel>w + yt *\<^sub>R xt\<parallel>\<^sup>2 + (c + yt)\<^sup>2 \<le> (1 + real u) * R\<^sup>2"
    by argo
qed

lemma perc_mistake_bound:
  fixes \<theta> w :: "real vec['n]" and b c \<gamma> R :: real and u :: nat
  assumes sep_norm: "\<parallel>\<theta>\<parallel>\<^sup>2 + b\<^sup>2 = 1"
    and \<gamma>pos: "\<gamma> > 0"
    and inv1: "real u * \<gamma> \<le> \<theta> \<bullet> w + b * c"
    and inv2: "\<parallel>w\<parallel>\<^sup>2 + c\<^sup>2 \<le> real u * R\<^sup>2"
  shows "real u \<le> (R / \<gamma>)\<^sup>2"
proof -
  have u0: "(0::nat) \<le> u" by blast
  have "\<theta> \<bullet> w + b * c \<le> norm (w, c) * norm (\<theta>, b)"
    using norm_cauchy_schwarz[of "(\<theta>, b)" "(w, c)"] by (simp add: cross3_simps(11))
  also have "... = sqrt (\<parallel>w\<parallel>\<^sup>2 + c\<^sup>2)"
    using sep_norm by (simp add: norm_Pair)
  finally have "\<theta> \<bullet> w + b * c \<le> sqrt (\<parallel>w\<parallel>\<^sup>2 + c\<^sup>2)" .
  hence key: "(real u * \<gamma>)\<^sup>2 \<le> real u * R\<^sup>2"
    using inv2 by (smt (verit) Num.of_nat_simps(1) \<gamma>pos of_nat_0_less_iff
        bot_nat_0.not_eq_extremum inv1 real_less_lsqrt zero_compare_simps(4))
  have key_div: "u \<noteq> 0 \<Longrightarrow> real u * \<gamma>\<^sup>2 > 0"
    using \<gamma>pos u0 by (clarsimp simp: field_simps)
  hence "u \<noteq> 0 \<Longrightarrow> (real u * \<gamma>)\<^sup>2 / (real u * \<gamma>\<^sup>2) \<le> (real u * R\<^sup>2) / (real u * \<gamma>\<^sup>2)"
    using key by (metis divide_right_mono less_eq_real_def)
  hence "u \<noteq> 0 \<Longrightarrow> real u \<le> (R / \<gamma>)\<^sup>2"
    using \<gamma>pos by (simp add: power2_eq_square power_divide)
  thus "real u \<le> (R / \<gamma>)\<^sup>2"
    by force
qed

section \<open>Paradigm A: Imperative ITree Program, VCG-based Hoare Logic\<close>

alphabet 'n st =
   theta                   :: "real vec['n]"
   bias                    :: real
   updates                 :: nat
   x_i                     :: "real vec['n]"
   y_i                     :: real
   i                       :: nat
   changed                 :: bool

instantiation st_ext :: (finite, default) default
begin

definition default_st_ext :: "('a,'b) st_scheme" 
  where
  "default_st_ext =
     \<lparr> theta\<^sub>v   = 0,
       bias\<^sub>v    = 0,
       updates\<^sub>v = 0,
       x_i\<^sub>v     = 0,
       y_i\<^sub>v     = 0,
       i\<^sub>v       = 0,
       changed\<^sub>v = False,
       \<dots>         = default \<rparr>"

instance ..

end

(*Below, D denotes the data which comes as a list of pairs, D = {(xi,yi)}.*)

program pass_through "D :: ((real vec['n]) \<times> real) list" over "('n :: finite) st"
 = "changed := False; i := 0; 
    while i < length D 
    do x_i := fst(D!i); y_i := snd(D!i);
      if y_i * (x_i \<bullet> theta + bias) \<le> 0 then 
        theta := theta + y_i *\<^sub>R x_i; bias := bias + y_i; updates := updates + 1; changed := True
      fi; i := i + 1 
    od"

program perceptron "D :: ((real vec['n]) \<times> real) list" over "('n :: finite) st"
 = "theta := 0; bias := 0; changed := True; updates := 0; while changed do pass_through D od"
(*Terminates: \<lparr>theta\<^sub>v = \<^bold>[1, 1\<^bold>], bias\<^sub>v = - 1, updates\<^sub>v = 1, x_i\<^sub>v = \<^bold>[1, 1\<^bold>], y_i\<^sub>v = 1, i\<^sub>v = 4, changed\<^sub>v = False\<rparr> *)

execute "perceptron [(Vector[-1,-1], -1), (Vector[-1,1], -1), (Vector[1,-1], -1), (Vector[1,1], 1)]"

program pass_through_aux "(
    D :: ((real vec['n]) \<times> real) list, 
    \<theta> :: real vec['n], 
    b :: real,
    \<gamma> :: real,
    R :: real
  )" over "('n :: finite) st"
 = "changed := False;
    i := 0;
    while i < length D
    invariant updates * \<gamma> \<le> \<theta> \<bullet> theta + b * bias
      \<and> \<parallel>theta\<parallel>\<^sup>2 + bias\<^sup>2 \<le> updates * R\<^sup>2
      \<and> (changed \<longrightarrow> old[updates] < updates)
      \<and> (\<not> changed \<longrightarrow> updates = old[updates])
      \<and> (\<not> changed \<longrightarrow> (\<forall>j < i. (snd (D ! j)) * ((fst (D ! j)) \<bullet> theta + bias) > 0))
    variant length D - i
    do x_i := fst (D ! i); y_i := snd (D ! i);
      if y_i * (x_i \<bullet> theta + bias) \<le> 0 then 
        theta := theta + y_i *\<^sub>R x_i; bias := bias + y_i; updates := updates + 1; changed := True
      fi; i := i + 1
    od"

program perceptron_aux "(
    D :: ((real vec['n]) \<times> real) list, 
    \<theta> :: real vec['n], 
    b :: real,
    \<gamma> :: real,
    R :: real
  )" over "('n :: finite) st"
  = "theta := 0; bias := 0; changed := True; updates := 0;
    while changed
    invariant updates*\<gamma> \<le> \<theta>\<bullet>theta + b*bias \<and> \<parallel>theta\<parallel>\<^sup>2+bias\<^sup>2 \<le> updates*R\<^sup>2 \<and> updates \<le> nat \<lceil>(R/\<gamma>)\<^sup>2\<rceil>
      \<and> (\<not> changed \<longrightarrow> (\<forall>j < length D. (snd(D!j))*((fst(D!j))\<bullet>theta + bias) > 0))
    variant nat \<lceil>(R / \<gamma>)\<^sup>2\<rceil> - updates + (if changed then 1 else 0)
    do pass_through_aux (D, \<theta>, b, \<gamma>, R) od"

lemma perceptron_aux_is_perceptron: "perceptron_aux(D, R, \<gamma>, \<theta>, b) = perceptron(D)"
  by (simp add: perceptron_aux_def perceptron_def   
                pass_through_def pass_through_aux_def while_inv_var_def)

theorem perceptron_aux_convergence:
  assumes bounded:  "\<And>t. t < length D \<Longrightarrow>\<parallel>fst (D ! t)\<parallel>\<^sup>2 + 1 \<le> R\<^sup>2" 
    and labels:     "\<And>t. t < length D \<Longrightarrow> snd (D ! t) \<in> {-1, 1}"
    and sep_norm:   "\<parallel>\<theta>\<parallel>\<^sup>2 + b\<^sup>2 = 1" 
    and sep_margin: "\<forall>t < length D. snd (D ! t) *\<^sub>R ((fst (D ! t)) \<bullet> \<theta> + b) \<ge> \<gamma>"
    and \<gamma>pos:       "\<gamma> > 0"
  shows "H[True] perceptron_aux (D, \<theta>, b, \<gamma>, R)
     [updates \<le> (R/\<gamma>)^2 \<and> (\<forall>i < length D. sgn(fst(D!i)\<bullet>theta + bias) = snd (D!i))]"
proof(vcg)
  show "\<And> theta bias updates t changed i. \<lbrakk>\<not> snd (D ! t) * (fst (D ! t) \<bullet> theta + bias) \<le> 0;
                              \<forall>i<t. 0 < snd (D ! i) * (fst (D ! i) \<bullet> theta + bias); i < Suc t\<rbrakk>
         \<Longrightarrow> 0 < snd (D ! i) * (fst (D ! i) \<bullet> theta + bias)"
    using less_Suc_eq by fastforce
  show "\<And> theta bias i. \<lbrakk>\<forall>i<length D. 0 < snd (D ! i) * (fst (D ! i) \<bullet> theta + bias); i < length D\<rbrakk>
          \<Longrightarrow> sgn (fst (D ! i) \<bullet> theta + bias) = snd (D ! i)"
    using labels by fastforce
next
  fix theta bias updates t
  assume hyp: "snd (D ! t) * (fst (D ! t) \<bullet> theta + bias) \<le> 0"
    and inv: "(real updates) * \<gamma> \<le> \<theta> \<bullet> theta + b * bias"
    and tlen: "t < length D"
  let ?theta' = "theta + snd (D ! t) *\<^sub>R fst (D ! t)" and ?bias' = "bias + snd (D ! t)"
  \<comment> \<open>The margin step is the shared @{thm perc_margin_step}.\<close>
  show "(1 + real updates) * \<gamma> \<le> \<theta> \<bullet> ?theta' + b * ?bias'"
    using perc_margin_step[OF labels[OF tlen] sep_margin[rule_format, OF tlen] inv] .
  then show "(1 + real updates) * \<gamma> \<le> \<theta> \<bullet> ?theta' + b * ?bias'" .
  then show "(1 + real updates) * \<gamma> \<le> \<theta> \<bullet> ?theta' + b * ?bias'" .
next
  fix theta bias updates t
  assume check: "snd (D ! t) * (fst (D ! t) \<bullet> theta + bias) \<le> 0"
    and inv: "\<parallel>theta\<parallel>\<^sup>2 + bias\<^sup>2 \<le> (real updates) * R\<^sup>2"
    and tlen: "t < length D"
  let ?theta' = "theta + snd (D ! t) *\<^sub>R fst (D ! t)" and ?bias' = "bias + snd (D ! t)"
  \<comment> \<open>The norm step is the shared @{thm perc_norm_step}.\<close>
  show "\<parallel>?theta'\<parallel>\<^sup>2 + ?bias'\<^sup>2 \<le> (1 + real updates) * R\<^sup>2"
    using perc_norm_step[OF labels[OF tlen] bounded[OF tlen] check inv] .
  then show "\<parallel>?theta'\<parallel>\<^sup>2 + ?bias'\<^sup>2 \<le> (1 + real updates) * R\<^sup>2" .
  then show "\<parallel>?theta'\<parallel>\<^sup>2 + ?bias'\<^sup>2 \<le> (1 + real updates) * R\<^sup>2" .
next
  fix theta bias updates
  assume hyp1: "real updates * \<gamma> \<le> \<theta> \<bullet> theta + b * bias"
     and hyp2: "\<parallel>theta\<parallel>\<^sup>2 + bias\<^sup>2 \<le> real updates * R\<^sup>2"
  \<comment> \<open>The Novikoff mistake bound is the shared @{thm perc_mistake_bound}.\<close>
  show "real updates \<le> (R / \<gamma>)\<^sup>2"
    using perc_mistake_bound[OF sep_norm \<gamma>pos hyp1 hyp2] .
  thus "updates \<le> nat \<lceil>(R / \<gamma>)\<^sup>2\<rceil>"
    by linarith
  fix old_updates :: "\<nat>"
  assume "old_updates \<le> nat \<lceil>(R / \<gamma>)\<^sup>2\<rceil>" and "old_updates < updates"
  thus "nat \<lceil>(R / \<gamma>)\<^sup>2\<rceil> - updates < nat \<lceil>(R / \<gamma>)\<^sup>2\<rceil> - old_updates"
    using \<open>updates \<le> nat \<lceil>(R / \<gamma>)\<^sup>2\<rceil>\<close> by (metis diff_less_mono2 linorder_neqE_nat not_le)
qed

theorem perceptron_convergence_theorem:
  assumes "\<parallel>\<theta>\<parallel>\<^sup>2 + b\<^sup>2 = 1" "\<gamma> > 0" 
  and "\<And>t. t < length D \<Longrightarrow> \<parallel>fst(D!t)\<parallel>\<^sup>2 + 1 \<le> R\<^sup>2 \<and> snd(D!t)\<in>{-1,1} \<and> snd(D!t)*(fst(D!t)\<bullet>\<theta> + b) \<ge> \<gamma>"
  shows "H[True] perceptron (D)
    [real updates \<le> (R/\<gamma>)^2 \<and> (\<forall>i < length D. sgn(fst(D!i) \<bullet> theta + bias) = snd (D!i))]"
  using assms perceptron_aux_convergence[of D R \<theta> b \<gamma>] by (simp add: perceptron_aux_is_perceptron)


section \<open>Paradigm B: Lammich's Refinement Framework (\<open>nres\<close>)\<close>

text \<open>
  The same algorithm in the \<open>nres\<close> monad. Design choice: the bounded inner pass
  over \<open>D\<close> is a pure \<open>foldl\<close> (its termination is structural and automatic),
  while the outer ``while changed'' loop is a \<open>WHILET\<close> whose termination is the
  Novikoff mistake bound \<open>u \<le> \<lceil>(R/\<gamma>)\<^sup>2\<rceil>\<close> \<dash> exactly the variant annotated in
  the VCG \<open>perceptron_aux\<close>. State: \<open>(w, c, u, ch)\<close> = weights, bias, updates,
  changed-this-pass. Correctness reuses the shared \<open>perc_*\<close> lemmas.
\<close>

definition pstep ::
  "(real vec['n] \<times> real \<times> nat \<times> bool) \<Rightarrow> (real vec['n] \<times> real)
     \<Rightarrow> (real vec['n] \<times> real \<times> nat \<times> bool)" where
  "pstep s d = (case s of (w, c, u, ch) \<Rightarrow>
     (if snd d * (fst d \<bullet> w + c) \<le> 0
      then (w + snd d *\<^sub>R fst d, c + snd d, u + 1, True)
      else (w, c, u, ch)))"

definition one_pass ::
  "(real vec['n] \<times> real) list \<Rightarrow> (real vec['n] \<times> real \<times> nat)
     \<Rightarrow> (real vec['n] \<times> real \<times> nat \<times> bool)" where
  "one_pass D s = (case s of (w, c, u) \<Rightarrow> foldl pstep (w, c, u, False) D)"

definition R_perceptron ::
  "(real vec['n] \<times> real) list \<Rightarrow> (real vec['n] \<times> real \<times> nat) nres" where
  "R_perceptron D \<equiv> do {
     (w, c, u, ch) \<leftarrow> WHILET (\<lambda>(w, c, u, ch). ch)
                            (\<lambda>(w, c, u, ch). RETURN (one_pass D (w, c, u)))
                            (0, 0, 0, True);
     RETURN (w, c, u)
   }"

text \<open>A pass preserves the two Novikoff bounds (per-step via the shared lemmas).\<close>

lemma foldl_pstep_bounds:
  fixes \<theta> :: "real vec['n]" and b \<gamma> R :: real
  assumes data: "\<forall>d\<in>set D. snd d \<in> {-1, 1} \<and> \<gamma> \<le> snd d *\<^sub>R (fst d \<bullet> \<theta> + b) \<and> \<parallel>fst d\<parallel>\<^sup>2 + 1 \<le> R\<^sup>2"
    and i1: "real u * \<gamma> \<le> \<theta> \<bullet> w + b * c"
    and i2: "\<parallel>w\<parallel>\<^sup>2 + c\<^sup>2 \<le> real u * R\<^sup>2"
    and res: "foldl pstep (w, c, u, ch) D = (w', c', u', ch')"
  shows "real u' * \<gamma> \<le> \<theta> \<bullet> w' + b * c' \<and> \<parallel>w'\<parallel>\<^sup>2 + c'\<^sup>2 \<le> real u' * R\<^sup>2"
  using assms
proof (induction D arbitrary: w c u ch w' c' u' ch')
  case Nil
  then show ?case by simp
next
  case (Cons d D)
  obtain xt yt where d: "d = (xt, yt)" by (cases d)
  have hd: "yt \<in> {-1, 1}" "\<gamma> \<le> yt *\<^sub>R (xt \<bullet> \<theta> + b)" "\<parallel>xt\<parallel>\<^sup>2 + 1 \<le> R\<^sup>2"
    using Cons.prems(1) d by auto
  have dataD: "\<forall>d\<in>set D. snd d \<in> {-1, 1} \<and> \<gamma> \<le> snd d *\<^sub>R (fst d \<bullet> \<theta> + b) \<and> \<parallel>fst d\<parallel>\<^sup>2 + 1 \<le> R\<^sup>2"
    using Cons.prems(1) by simp
  show ?case
  proof (cases "yt * (xt \<bullet> w + c) \<le> 0")
    case True
    have step: "pstep (w, c, u, ch) d = (w + yt *\<^sub>R xt, c + yt, u + 1, True)"
      using d True by (simp add: pstep_def)
    have m1: "real (u + 1) * \<gamma> \<le> \<theta> \<bullet> (w + yt *\<^sub>R xt) + b * (c + yt)"
      using perc_margin_step[OF hd(1) hd(2) Cons.prems(2)] by (simp add: algebra_simps)
    have m2: "\<parallel>w + yt *\<^sub>R xt\<parallel>\<^sup>2 + (c + yt)\<^sup>2 \<le> real (u + 1) * R\<^sup>2"
      using perc_norm_step[OF hd(1) hd(3) True Cons.prems(3)] by (simp add: algebra_simps)
    have "foldl pstep (w + yt *\<^sub>R xt, c + yt, u + 1, True) D = (w', c', u', ch')"
      using Cons.prems(4) step by simp
    from Cons.IH[OF dataD m1 m2 this] show ?thesis .
  next
    case False
    have step: "pstep (w, c, u, ch) d = (w, c, u, ch)"
      using d False by (simp add: pstep_def)
    have "foldl pstep (w, c, u, ch) D = (w', c', u', ch')"
      using Cons.prems(4) step by simp
    from Cons.IH[OF dataD Cons.prems(2) Cons.prems(3) this] show ?thesis .
  qed
qed

text \<open>A pass: updates never decrease, the flag is monotone, an unchanged pass
  leaves the state fixed and certifies every point, and a changed pass strictly
  increases the update count (this last fact drives termination).\<close>

lemma foldl_pstep_props:
  "foldl pstep (w, c, u, ch) D = (w', c', u', ch') \<Longrightarrow>
      u \<le> u' \<and> (ch \<longrightarrow> ch')
    \<and> (\<not> ch \<and> \<not> ch' \<longrightarrow> w' = w \<and> c' = c \<and> u' = u \<and> (\<forall>d\<in>set D. 0 < snd d * (fst d \<bullet> w + c)))
    \<and> (\<not> ch \<and> ch' \<longrightarrow> u < u')"
proof (induction D arbitrary: w c u ch w' c' u' ch')
  case Nil
  then show ?case by simp
next
  case (Cons d D)
  obtain xt yt where d: "d = (xt, yt)" by (cases d)
  show ?case
  proof (cases "yt * (xt \<bullet> w + c) \<le> 0")
    case True
    have step: "pstep (w, c, u, ch) d = (w + yt *\<^sub>R xt, c + yt, u + 1, True)"
      using d True by (simp add: pstep_def)
    have "foldl pstep (w + yt *\<^sub>R xt, c + yt, u + 1, True) D = (w', c', u', ch')"
      using Cons.prems step by simp
    from Cons.IH[OF this] have "u + 1 \<le> u' \<and> ch'" by simp
    then show ?thesis using True d by auto
  next
    case False
    have step: "pstep (w, c, u, ch) d = (w, c, u, ch)"
      using d False by (simp add: pstep_def)
    have "foldl pstep (w, c, u, ch) D = (w', c', u', ch')"
      using Cons.prems step by simp
    from Cons.IH[OF this]
    have ih: "u \<le> u' \<and> (ch \<longrightarrow> ch')
            \<and> (\<not> ch \<and> \<not> ch' \<longrightarrow> w' = w \<and> c' = c \<and> u' = u \<and> (\<forall>d\<in>set D. 0 < snd d * (fst d \<bullet> w + c)))
            \<and> (\<not> ch \<and> ch' \<longrightarrow> u < u')" .
    have hdpos: "0 < yt * (xt \<bullet> w + c)" using False by simp
    show ?thesis using ih hdpos d by auto
  qed
qed

text \<open>From a positive margin and a \<open>\<plusminus>1\<close> label, the prediction is correct.\<close>

lemma sgn_from_margin:
  fixes y z :: real
  assumes "y \<in> {-1, 1}" and "0 < y * z"
  shows "sgn z = y"
  using assms by (auto simp: sgn_real_def zero_less_mult_iff)

definition perc_invar ::
  "(real vec['n] \<times> real) list \<Rightarrow> real vec['n] \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real
     \<Rightarrow> (real vec['n] \<times> real \<times> nat \<times> bool) \<Rightarrow> bool" where
  "perc_invar D \<theta> b \<gamma> R \<equiv> \<lambda>(w, c, u, ch).
       real u * \<gamma> \<le> \<theta> \<bullet> w + b * c
     \<and> \<parallel>w\<parallel>\<^sup>2 + c\<^sup>2 \<le> real u * R\<^sup>2
     \<and> u \<le> nat \<lceil>(R / \<gamma>)\<^sup>2\<rceil>
     \<and> (\<not> ch \<longrightarrow> (\<forall>d \<in> set D. 0 < snd d * (fst d \<bullet> w + c)))"

text \<open>One pass preserves the invariant and strictly decreases the Novikoff variant.\<close>

lemma one_pass_invar_step:
  fixes D :: "(real vec['n] \<times> real) list" and \<theta> :: "real vec['n]" and b \<gamma> R :: real
  assumes bounded: "\<forall>d\<in>set D. \<parallel>fst d\<parallel>\<^sup>2 + 1 \<le> R\<^sup>2"
    and labels: "\<forall>d\<in>set D. snd d \<in> {-1, 1}"
    and sep_norm: "\<parallel>\<theta>\<parallel>\<^sup>2 + b\<^sup>2 = 1"
    and sep_margin: "\<forall>d\<in>set D. \<gamma> \<le> snd d *\<^sub>R (fst d \<bullet> \<theta> + b)"
    and \<gamma>pos: "\<gamma> > 0"
    and inv: "perc_invar D \<theta> b \<gamma> R (w, c, u, ch)"
    and guard: "ch"
  shows "perc_invar D \<theta> b \<gamma> R (one_pass D (w, c, u))
       \<and> (one_pass D (w, c, u), (w, c, u, ch))
           \<in> Wellfounded.measure (\<lambda>(w, c, u, ch). nat \<lceil>(R / \<gamma>)\<^sup>2\<rceil> - u + (if ch then 1 else 0))"
proof -
  have data: "\<forall>d\<in>set D. snd d \<in> {-1, 1} \<and> \<gamma> \<le> snd d *\<^sub>R (fst d \<bullet> \<theta> + b) \<and> \<parallel>fst d\<parallel>\<^sup>2 + 1 \<le> R\<^sup>2"
    using bounded labels sep_margin by blast
  from inv have inv1: "real u * \<gamma> \<le> \<theta> \<bullet> w + b * c"
    and inv2: "\<parallel>w\<parallel>\<^sup>2 + c\<^sup>2 \<le> real u * R\<^sup>2"
    and invu: "u \<le> nat \<lceil>(R / \<gamma>)\<^sup>2\<rceil>"
    by (auto simp: perc_invar_def)
  obtain w' c' u' ch' where res: "foldl pstep (w, c, u, False) D = (w', c', u', ch')"
    by (cases "foldl pstep (w, c, u, False) D")
  have op: "one_pass D (w, c, u) = (w', c', u', ch')"
    using res by (simp add: one_pass_def)
  have bnds: "real u' * \<gamma> \<le> \<theta> \<bullet> w' + b * c'" "\<parallel>w'\<parallel>\<^sup>2 + c'\<^sup>2 \<le> real u' * R\<^sup>2"
    using foldl_pstep_bounds[OF data inv1 inv2 res] by auto
  have u'le: "u' \<le> nat \<lceil>(R / \<gamma>)\<^sup>2\<rceil>"
    using perc_mistake_bound[OF sep_norm \<gamma>pos bnds(1) bnds(2)] by linarith
  have props: "u \<le> u'
             \<and> (\<not> ch' \<longrightarrow> w' = w \<and> c' = c \<and> u' = u \<and> (\<forall>d\<in>set D. 0 < snd d * (fst d \<bullet> w + c)))
             \<and> (ch' \<longrightarrow> u < u')"
    using foldl_pstep_props[OF res] by simp
  have inv': "perc_invar D \<theta> b \<gamma> R (w', c', u', ch')"
    unfolding perc_invar_def using bnds u'le props by auto
  have var: "(one_pass D (w, c, u), (w, c, u, ch))
               \<in> Wellfounded.measure (\<lambda>(w, c, u, ch). nat \<lceil>(R / \<gamma>)\<^sup>2\<rceil> - u + (if ch then 1 else 0))"
  proof (cases ch')
    case True
    hence "u < u'" using props by simp
    hence "nat \<lceil>(R / \<gamma>)\<^sup>2\<rceil> - u' + 1 < nat \<lceil>(R / \<gamma>)\<^sup>2\<rceil> - u + 1"
      using u'le by linarith
    thus ?thesis using op guard True by (simp add: in_measure)
  next
    case False
    hence "u' = u" using props by simp
    thus ?thesis using op guard False by (simp add: in_measure)
  qed
  show ?thesis using op inv' var by simp
qed

text \<open>On loop exit (\<open>\<not> changed\<close>) the mistake count is bounded and every point is
  correctly classified.\<close>

lemma perc_exit_classify:
  fixes D :: "(real vec['n] \<times> real) list" and \<theta> :: "real vec['n]" and b \<gamma> R :: real
  assumes labels: "\<forall>d\<in>set D. snd d \<in> {-1, 1}"
    and sep_norm: "\<parallel>\<theta>\<parallel>\<^sup>2 + b\<^sup>2 = 1"
    and \<gamma>pos: "\<gamma> > 0"
    and inv: "perc_invar D \<theta> b \<gamma> R (w, c, u, ch)"
    and ng: "\<not> ch"
  shows "real u \<le> (R / \<gamma>)\<^sup>2 \<and> (\<forall>i < length D. sgn (fst (D ! i) \<bullet> w + c) = snd (D ! i))"
proof -
  from inv have inv1: "real u * \<gamma> \<le> \<theta> \<bullet> w + b * c"
    and inv2: "\<parallel>w\<parallel>\<^sup>2 + c\<^sup>2 \<le> real u * R\<^sup>2"
    and invc: "\<not> ch \<longrightarrow> (\<forall>d\<in>set D. 0 < snd d * (fst d \<bullet> w + c))"
    by (auto simp: perc_invar_def)
  have ub: "real u \<le> (R / \<gamma>)\<^sup>2"
    using perc_mistake_bound[OF sep_norm \<gamma>pos inv1 inv2] .
  have cls: "\<forall>i < length D. sgn (fst (D ! i) \<bullet> w + c) = snd (D ! i)"
  proof (intro allI impI)
    fix i assume "i < length D"
    hence din: "D ! i \<in> set D" by simp
    have "0 < snd (D ! i) * (fst (D ! i) \<bullet> w + c)" using invc ng din by blast
    thus "sgn (fst (D ! i) \<bullet> w + c) = snd (D ! i)"
      using sgn_from_margin labels din by blast
  qed
  show ?thesis using ub cls by blast
qed

text \<open>Total correctness in the Refinement Framework: the mistake count is bounded
  by \<open>(R/\<gamma>)\<^sup>2\<close> and every point is correctly classified (termination is the
  \<open>WHILET\<close> variant). Assumptions match \<open>perceptron_aux_convergence\<close>, in set form.\<close>

theorem R_perceptron_correct:
  fixes D :: "(real vec['n] \<times> real) list" and \<theta> :: "real vec['n]" and b \<gamma> R :: real
  assumes bounded: "\<forall>d\<in>set D. \<parallel>fst d\<parallel>\<^sup>2 + 1 \<le> R\<^sup>2"
    and labels: "\<forall>d\<in>set D. snd d \<in> {-1, 1}"
    and sep_norm: "\<parallel>\<theta>\<parallel>\<^sup>2 + b\<^sup>2 = 1"
    and sep_margin: "\<forall>d\<in>set D. \<gamma> \<le> snd d *\<^sub>R (fst d \<bullet> \<theta> + b)"
    and \<gamma>pos: "\<gamma> > 0"
  shows "R_perceptron D \<le> SPEC (\<lambda>(w, c, u). real u \<le> (R / \<gamma>)\<^sup>2
            \<and> (\<forall>i < length D. sgn (fst (D ! i) \<bullet> w + c) = snd (D ! i)))"
  unfolding R_perceptron_def
  apply (refine_vcg WHILET_rule[where I = "perc_invar D \<theta> b \<gamma> R"
            and R = "Wellfounded.measure (\<lambda>(w, c, u, ch). nat \<lceil>(R / \<gamma>)\<^sup>2\<rceil> - u + (if ch then 1 else 0))"])
  subgoal by simp
  subgoal by (simp add: perc_invar_def)
  subgoal for s
    using one_pass_invar_step[OF bounded labels sep_norm sep_margin \<gamma>pos]
    by (cases s) (auto simp: in_measure)
  subgoal for s
    using one_pass_invar_step[OF bounded labels sep_norm sep_margin \<gamma>pos]
    by (cases s) (auto simp: in_measure)
  subgoal for s
    using perc_mistake_bound[OF sep_norm \<gamma>pos]
    by (cases s) (auto simp: perc_invar_def)
  subgoal for s
    using labels
    by (cases s) (auto simp: perc_invar_def intro: sgn_from_margin dest: nth_mem)
  done



section \<open>Paradigm C: Floating-point perceptron (direct, VCG)\<close>

text \<open>
  The direct-float counterpart of the real-valued development above. The weight vector
  \<open>theta\<close> is a genuine float vector (\<^typ>\<open>float64 list\<close>); the data points
  are genuine float vectors; the misclassification test uses the genuine
  floating-point inner product \<^const>\<open>fdot\<close> (its real value), and the
  weight update \<open>theta \<oplus> (y \<odot> x)\<close> uses the genuine float operations
  \<^const>\<open>fvadd\<close> / \<^const>\<open>fscaleR\<close>.

  The convergence bound \<open>updates \<le> (R/\<gamma>)\<^sup>2\<close> is the classical
  mistake-counting (Cauchy--Schwarz) argument: the margin functional \<open>MRG\<close>
  grows by at least \<open>\<gamma>\<close> per update while the squared norm \<open>NRM\<close> grows by
  at most \<open>R\<^sup>2\<close>; Cauchy--Schwarz then forces \<open>updates \<cdot> \<gamma> \<le> \<surd>(updates) R\<close>.
  In the direct-float setting the round-off of the genuine float update is
  folded into the constants \<open>\<gamma>\<close> (a slightly smaller guaranteed margin gain)
  and \<open>R\<close> (a slightly larger norm growth); \<open>MRG\<close>, \<open>NRM\<close> and the
  per-update geometry are abstract hypotheses over the real shadow, exactly
  as the real development proves them over \<^typ>\<open>real^'n\<close>.
\<close>

text \<open>The \<^class>\<open>default\<close> instance for floats (needed for the scalar float
  fields of the \<^theory_text>\<open>zstore\<close>) is shared via \<^theory>\<open>Numerical_Methods.Float_Default\<close>.\<close>


subsection \<open>State and programs\<close>

zstore stP =
  theta   :: "float64 list"
  bias    :: "float64"
  updates :: "nat"
  x_i     :: "float64 list"
  y_i     :: "float64"
  i       :: "nat"
  changed :: "bool"

text \<open>
  One pass over the data. The misclassification test and the running
  ``already classified'' assertion compare the \<^emph>\<open>real value\<close>
  \<open>valof (snd (D ! j)) * (valof (fdot (fst (D ! j)) theta) + valof bias)\<close>
  of the genuine float inner product against zero. \<open>MRG\<close>/\<open>NRM\<close> are the
  (real) margin and squared-norm functionals of the float weight vector.
\<close>

program pass_through_aux_F
  "(D :: (float64 list \<times> float64) list,
    MRG :: float64 list \<Rightarrow> float64 \<Rightarrow> real, NRM :: float64 list \<Rightarrow> float64 \<Rightarrow> real,
    \<gamma> :: real, R :: real)" over stP
 = "changed := False; i := 0;
    while i < length D
    invariant real updates * \<gamma> \<le> MRG theta bias
      \<and> NRM theta bias \<le> real updates * R\<^sup>2
      \<and> (changed \<longrightarrow> old[updates] < updates)
      \<and> (\<not> changed \<longrightarrow> updates = old[updates])
      \<and> (\<not> changed \<longrightarrow>
           (\<forall>j < i. 0 < valof (snd (D ! j)) * (valof (fdot (fst (D ! j)) theta) + valof bias)))
    variant length D - i
    do x_i := fst (D ! i); y_i := snd (D ! i);
       if valof y_i * (valof (fdot x_i theta) + valof bias) \<le> 0 then
         theta := fvadd theta (fscaleR y_i x_i); bias := bias + y_i;
         updates := updates + 1; changed := True
       fi; i := i + 1
    od"

program perceptron_aux_F
  "(D :: (float64 list \<times> float64) list,
    MRG :: float64 list \<Rightarrow> float64 \<Rightarrow> real, NRM :: float64 list \<Rightarrow> float64 \<Rightarrow> real,
    \<gamma> :: real, R :: real, z0 :: float64 list)" over stP
 = "theta := z0; bias := 0; changed := True; updates := 0;
    while changed
    invariant real updates * \<gamma> \<le> MRG theta bias
      \<and> NRM theta bias \<le> real updates * R\<^sup>2
      \<and> real updates \<le> (R / \<gamma>)\<^sup>2
      \<and> (\<not> changed \<longrightarrow>
           (\<forall>j < length D. 0 < valof (snd (D ! j)) * (valof (fdot (fst (D ! j)) theta) + valof bias)))
    variant nat \<lceil>(R / \<gamma>)\<^sup>2\<rceil> - updates + (if changed then 1 else 0)
    do pass_through_aux_F (D, MRG, NRM, \<gamma>, R) od"


subsection \<open>The mistake-counting (Cauchy--Schwarz) bound\<close>

text \<open>
  Pure arithmetic core of the convergence argument: if the margin
  functional \<open>m\<close> grows like \<open>u \<cdot> G\<close> while the squared norm \<open>n\<close> is at most
  \<open>u \<cdot> R\<^sup>2\<close>, then Cauchy--Schwarz (\<open>m \<le> \<surd>n\<close>) caps the mistake count at
  \<open>(R/G)\<^sup>2\<close>.
\<close>

lemma perc_count:
  fixes u :: nat and m n G R :: real
  assumes mlb: "real u * G \<le> m" and nub: "n \<le> real u * R\<^sup>2"
    and cs: "m \<le> sqrt n" and nn: "0 \<le> n" and Gpos: "0 < G"
  shows "real u \<le> (R / G)\<^sup>2"
proof (cases "u = 0")
  case True thus ?thesis by simp
next
  case False
  hence upos: "0 < real u" by simp
  have rg_nn: "0 \<le> real u * G" using upos Gpos by simp
  have m_nn: "0 \<le> m" using mlb rg_nn by linarith
  have "(real u * G)\<^sup>2 \<le> m\<^sup>2" using power_mono[OF mlb rg_nn] .
  also have "m\<^sup>2 \<le> n" by (metis power_mono[OF cs m_nn] real_sqrt_pow2[OF nn])
  also have "n \<le> real u * R\<^sup>2" by (rule nub)
  finally have key: "(real u * G)\<^sup>2 \<le> real u * R\<^sup>2" .
  have key2: "real u * (real u * G\<^sup>2) \<le> real u * R\<^sup>2"
    using key by (simp add: power_mult_distrib power2_eq_square mult.assoc mult.left_commute)
  have "real u * G\<^sup>2 \<le> R\<^sup>2" using mult_left_le_imp_le[OF key2 upos] .
  thus ?thesis using Gpos by (simp add: power_divide pos_le_divide_eq mult.commute)
qed


text \<open>Two affine-step combiners (one per inequality direction): they carry
  the distributive law \<open>(1 + u) G = u G + G\<close> that linear arithmetic alone
  will not expand.\<close>

lemma affine_step:
  fixes A G b :: real and u :: nat
  assumes g: "A + G \<le> b" and inv: "real u * G \<le> A"
  shows "(1 + real u) * G \<le> b"
proof -
  have "(1 + real u) * G = real u * G + G" by (simp add: algebra_simps)
  thus ?thesis using g inv by linarith
qed

lemma affine_step_le:
  fixes A G b :: real and u :: nat
  assumes g: "b \<le> A + G" and inv: "A \<le> real u * G"
  shows "b \<le> (1 + real u) * G"
proof -
  have "(1 + real u) * G = real u * G + G" by (simp add: algebra_simps)
  thus ?thesis using g inv by linarith
qed


subsection \<open>Direct convergence correctness\<close>

theorem perceptron_aux_F_convergence:
  fixes D :: "(float64 list \<times> float64) list"
  fixes MRG NRM :: "float64 list \<Rightarrow> float64 \<Rightarrow> real"
  fixes \<gamma> R :: real and z0 :: "float64 list"
  assumes \<gamma>_pos: "0 < \<gamma>"
  assumes labels: "\<And>t. t < length D \<Longrightarrow> valof (snd (D ! t)) = 1 \<or> valof (snd (D ! t)) = -1"
  assumes mrg0: "MRG z0 0 = 0"
  assumes nrm0: "NRM z0 0 = 0"
  assumes margin_gain:
    "\<And>th bs t. t < length D
        \<Longrightarrow> MRG th bs + \<gamma>
              \<le> MRG (fvadd th (fscaleR (snd (D ! t)) (fst (D ! t)))) (bs + snd (D ! t))"
  assumes norm_gain:
    "\<And>th bs t. t < length D
        \<Longrightarrow> valof (snd (D ! t)) * (valof (fdot (fst (D ! t)) th) + valof bs) \<le> 0
        \<Longrightarrow> NRM (fvadd th (fscaleR (snd (D ! t)) (fst (D ! t)))) (bs + snd (D ! t))
              \<le> NRM th bs + R\<^sup>2"
  assumes cs_oracle: "\<And>th bs. MRG th bs \<le> sqrt (NRM th bs)"
  assumes nrm_nonneg: "\<And>th bs. 0 \<le> NRM th bs"
  shows "H[True] perceptron_aux_F (D, MRG, NRM, \<gamma>, R, z0)
       [real updates \<le> (R / \<gamma>)\<^sup>2
        \<and> (\<forall>i < length D.
             sgn (valof (fdot (fst (D ! i)) theta) + valof bias) = valof (snd (D ! i)))]"
  apply vcg
  \<comment> \<open>Goals 1--6: margin growth / bounded norm growth on a misclassified update.\<close>
  subgoal premises prems for dum th0 bs0 up0 ch0 th bs iv
  proof -
    have g: "MRG th bs + \<gamma> \<le> MRG (fvadd th (fscaleR (snd (D ! iv)) (fst (D ! iv)))) (bs + snd (D ! iv))"
      using margin_gain prems by blast
    have inv: "real up0 * \<gamma> \<le> MRG th bs" using prems by blast
    show "(1 + real up0) * \<gamma> \<le> MRG (fvadd th (fscaleR (snd (D ! iv)) (fst (D ! iv)))) (bs + snd (D ! iv))"
      using g inv by (blast intro: affine_step affine_step_le)
  qed
  subgoal premises prems for dum th0 bs0 up0 ch0 th bs iv
  proof -
    have g: "NRM (fvadd th (fscaleR (snd (D ! iv)) (fst (D ! iv)))) (bs + snd (D ! iv)) \<le> NRM th bs + R\<^sup>2"
      using norm_gain prems by blast
    have inv: "NRM th bs \<le> real up0 * R\<^sup>2" using prems by blast
    show "NRM (fvadd th (fscaleR (snd (D ! iv)) (fst (D ! iv)))) (bs + snd (D ! iv)) \<le> (1 + real up0) * R\<^sup>2"
      using g inv by (blast intro: affine_step affine_step_le)
  qed
  subgoal premises prems for dum th0 bs0 up0 ch0 th bs upw iv
  proof -
    have g: "MRG th bs + \<gamma> \<le> MRG (fvadd th (fscaleR (snd (D ! iv)) (fst (D ! iv)))) (bs + snd (D ! iv))"
      using margin_gain prems by blast
    have inv: "real upw * \<gamma> \<le> MRG th bs" using prems by blast
    show "(1 + real upw) * \<gamma> \<le> MRG (fvadd th (fscaleR (snd (D ! iv)) (fst (D ! iv)))) (bs + snd (D ! iv))"
      using g inv by (blast intro: affine_step affine_step_le)
  qed
  subgoal premises prems for dum th0 bs0 up0 ch0 th bs upw iv
  proof -
    have g: "NRM (fvadd th (fscaleR (snd (D ! iv)) (fst (D ! iv)))) (bs + snd (D ! iv)) \<le> NRM th bs + R\<^sup>2"
      using norm_gain prems by blast
    have inv: "NRM th bs \<le> real upw * R\<^sup>2" using prems by blast
    show "NRM (fvadd th (fscaleR (snd (D ! iv)) (fst (D ! iv)))) (bs + snd (D ! iv)) \<le> (1 + real upw) * R\<^sup>2"
      using g inv by (blast intro: affine_step affine_step_le)
  qed
  subgoal premises prems for dum th0 bs0 up0 ch0 th bs upw iv
  proof -
    have g: "MRG th bs + \<gamma> \<le> MRG (fvadd th (fscaleR (snd (D ! iv)) (fst (D ! iv)))) (bs + snd (D ! iv))"
      using margin_gain prems by blast
    have inv: "real upw * \<gamma> \<le> MRG th bs" using prems by blast
    show "(1 + real upw) * \<gamma> \<le> MRG (fvadd th (fscaleR (snd (D ! iv)) (fst (D ! iv)))) (bs + snd (D ! iv))"
      using g inv by (blast intro: affine_step affine_step_le)
  qed
  subgoal premises prems for dum th0 bs0 up0 ch0 th bs upw iv
  proof -
    have g: "NRM (fvadd th (fscaleR (snd (D ! iv)) (fst (D ! iv)))) (bs + snd (D ! iv)) \<le> NRM th bs + R\<^sup>2"
      using norm_gain prems by blast
    have inv: "NRM th bs \<le> real upw * R\<^sup>2" using prems by blast
    show "NRM (fvadd th (fscaleR (snd (D ! iv)) (fst (D ! iv)))) (bs + snd (D ! iv)) \<le> (1 + real upw) * R\<^sup>2"
      using g inv by (blast intro: affine_step affine_step_le)
  qed
  \<comment> \<open>Goal 7: a correctly-classified point stays classified through the pass.\<close>
  subgoal premises prems using prems by (smt (verit) less_Suc_eq)
  \<comment> \<open>Goal 8: the Cauchy--Schwarz mistake bound.\<close>
  subgoal premises prems for dum thv bsv upv chv th bs upw iv cv
  proof -
    have a: "real upw * \<gamma> \<le> MRG th bs" using prems by auto
    have b: "NRM th bs \<le> real upw * R\<^sup>2" using prems by auto
    show "real upw \<le> (R / \<gamma>)\<^sup>2"
      by (rule perc_count[OF a b cs_oracle nrm_nonneg \<gamma>_pos])
  qed
  \<comment> \<open>Goal 9: the outer variant strictly decreases.\<close>
  subgoal premises prems for dum thv bsv upv chv th bs upw iv cv
  proof -
    have a: "real upw * \<gamma> \<le> MRG th bs" using prems by auto
    have b: "NRM th bs \<le> real upw * R\<^sup>2" using prems by auto
    have lt: "upv < upw" using prems by auto
    have bnd: "real upw \<le> (R / \<gamma>)\<^sup>2"
      by (rule perc_count[OF a b cs_oracle nrm_nonneg \<gamma>_pos])
    hence "upw \<le> nat \<lceil>(R / \<gamma>)\<^sup>2\<rceil>"
      using real_nat_ceiling_ge by (meson of_nat_le_iff order_trans)
    thus "nat \<lceil>(R / \<gamma>)\<^sup>2\<rceil> - upw < nat \<lceil>(R / \<gamma>)\<^sup>2\<rceil> - upv"
      using lt by simp 
  qed
  \<comment> \<open>Goals 10,11: the invariant holds initially.\<close>
  subgoal by (simp add: mrg0)
  subgoal by (simp add: nrm0)
  \<comment> \<open>Goal 12: at exit every point is correctly classified.\<close>
  subgoal premises prems for th bs up ch iv
  proof -
    have cls: "0 < valof (snd (D ! iv)) * (valof (fdot (fst (D ! iv)) th) + valof bs)"
      using prems by auto
    have lab: "valof (snd (D ! iv)) = 1 \<or> valof (snd (D ! iv)) = -1"
      using labels prems by auto
    show "sgn (valof (fdot (fst (D ! iv)) th) + valof bs) = valof (snd (D ! iv))"
      using cls lab by fastforce 
  qed
  done

end