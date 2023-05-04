theory Euler
  imports "ITree_VCG.ITree_VCG"   "HOL-Analysis.Analysis" "HOL.Topological_Spaces" "HOL-Library.Log_Nat"  "HOL-Number_Theory.Fib" HOL.Orderings
begin

instantiation rat :: default
begin          
definition "default_rat = (0::rat)"
instance ..
end





instantiation real :: default
begin          
definition "default_real = (0::real)"
instance ..
end

zstore state = 
  xs :: "rat list"
  c :: "real"
  error :: "rat list"
  func_vals :: "rat list"
  lower :: "real"
  upper :: "real"
  iter :: "nat"
  fa :: "real"
  fb :: "real"
  fx :: "real"
  xmid :: "real"
  ymid :: "real"
  app_root :: "real"
  phi :: "real"
  aStar :: "real"
  bStar :: "real"
  A :: "rat"
  B :: "rat"
  x_min :: "real"
  f_min :: "real"
  oldx :: "real"
  oldfx :: "real"
  newx :: "real"
  X :: "real"
  

term "\<lambda> x. 5 - 0.1 * x"

procedure euler "(f :: rat \<Rightarrow> rat, x\<^sub>0 :: rat, t :: rat, steps :: nat)" over state
  = "xs := [x\<^sub>0];
     for i in [0..<steps-1]
     do 
       xs := xs @ [xs!i + t * f(xs!i)]
     od"

execute "euler (\<lambda> x. - 0.1 * x, 0.1, 1, 10)"

(*Log base 2 of 2 is 1*)
lemma  "log 2 2 = 1"
  by simp


lemma "sgn(-3 ::real) = -1"
  by simp



(*Some documentation*)
(*https://github.com/cran/cmna/blob/master/R/bisection.R*)
(*https://search.r-project.org/CRAN/refmans/cmna/html/bisection.html*)

(*Below: m stands for the maximum iterations allowed*)
(*Note:  Whenever possible I try to emulate the style of the R source code*)


procedure bisection "(f :: real \<Rightarrow> real, a :: real, b :: real, tol :: real)" over state
 = "iter := 0;
    fa:= f(a);
    fb:= f(b);
    lower:= a;
    upper:= b;
    xmid:= lower;
    ymid:= f(xmid);
    
     
    while (upper - lower > tol) 

    inv (fa * fb \<le> 0) 
                                    \<and> ((lower = xmid) \<or> (xmid = upper))
                                    \<and> (ymid = f(xmid))
                                    \<and> (fa = f(lower))
                                    \<and> (fb = f(upper))
                                    \<and> ((a \<le> lower) & (upper \<le> b))
                                    \<and> (fa = f(lower))
                                    \<and> (fb = f(upper))
                                    \<and> ((lower < upper))
                                    \<and> ((upper - lower) = (b - a) / 2^iter)

    do
      iter:= iter + 1;
      
      xmid:= (lower + upper)/2;      
      ymid:= f(xmid);

      if (fa*ymid >0) then (lower:= xmid; fa:= ymid) else (upper:= xmid; fb:= ymid) fi
    od;
    app_root:= (lower+upper)/2
"







procedure bisection_with_root_check "(f :: real \<Rightarrow> real, a :: real, b :: real, tol :: real)" over state
 = "iter := 0;
    fa:= f(a);
    fb:= f(b);
    lower:= a;
    upper:= b;
    xmid:= lower;
    ymid:= f(xmid);
    
     
    while (upper - lower > tol) \<and> ymid \<noteq> 0  

    inv (fa * fb \<le> 0) 
                                    \<and> ((lower = xmid) \<or> (xmid = upper))
                                    \<and> (ymid = f(xmid))
                                    \<and> (fa = f(lower))
                                    \<and> (fb = f(upper))
                                    \<and> ((a \<le> lower) & (upper \<le> b))
                                    \<and> (fa = f(lower))
                                    \<and> (fb = f(upper))
                                    \<and> ((lower < upper))
                                    \<and> ((upper - lower) = (b - a) / 2^iter)

    do
      iter:= iter + 1;
      
      xmid:= (lower + upper)/2;      
      ymid:= f(xmid);

      if (fa*ymid >0) then (lower:= xmid; fa:= ymid) else (upper:= xmid; fb:= ymid) fi
    od;
    app_root:= (lower+upper)/2
"

value "(2::nat)^(2::nat)"


execute "bisection (\<lambda> x. (x*x*x) -2*x*x - 159 , 0, 10, 0.0001)"  (*This has a root of 6.17 as desired!*)

execute "bisection (\<lambda> x.  (x*x), -1, 1, 0.0001)"  (*This has a root of 6.17 as desired!*)


lemma Bolzanos_IVT:
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
    from IVT2'[where f = "f", where b="\<beta>", where a = "\<alpha>", where y=0]
    obtain \<gamma> where "\<gamma> \<in> {\<alpha>..\<beta>}" and "f \<gamma> = 0"
      using \<open>f \<beta> < 0 \<and> 0 < f \<alpha>\<close> \<open>f \<beta> < 0 \<and> 0 < f \<alpha>\<close> a_less_than_b continuous_f by auto
    then show ?thesis
      by blast
  qed
  then show ?thesis
    by (smt (verit, best) \<open>f \<alpha> \<noteq> 0\<close> \<open>f \<beta> \<noteq> 0\<close> atLeastAtMost_iff)
qed


(*Some questions to ask: 

(1) How do we incorporate m into the procedure and proof?
(2) Is it appropriate to have a check for ymid = 0 if this is not the official version for R?
(3) Supposing it is appropriate to check for ymid = 0, are we correctly returning the root for that special case or merely the nearby "root" defined in the procedure?
(4) Are there any good lemmas we can state about the output "root".... and is "root" just the same as xmid?*)




lemma bisection_error_bound:   
  assumes a_less_than_b: "(a::real) < (b::real)"
  assumes continuous_f: "continuous_on {a..b} f"
  assumes opposite_signs: "f(a)*f(b)<0"
  assumes postive_tolerance: "tol > 0"
  shows "H{True} bisection(f,a,b,tol) {\<exists> (c::real). (f(c) = 0 \<and> a < c \<and> c < b \<and>  (abs(c - xmid) \<le> (b - a)/(2^(iter))))}"
  unfolding continuous_on_def
proof(vcg)
  show "\<And>upper iter xmid.
       0 < f xmid * f ((xmid + upper) / 2) \<Longrightarrow>
       f xmid * f upper \<le> 0 \<Longrightarrow>
       a \<le> xmid \<Longrightarrow> upper \<le> b \<Longrightarrow> xmid < upper \<Longrightarrow> upper - xmid = (b - a) / 2 ^ iter \<Longrightarrow> tol < (b - a) / 2 ^ iter \<Longrightarrow> f ((xmid + upper) / 2) * f upper \<le> 0"
    by (smt (verit, del_insts) zero_less_mult_iff)
next
  fix upper iter xmid
  assume "upper - xmid = (b - a) / 2 ^ iter"
  then have "(upper - xmid) / 2 = (b - a) / (2 * 2 ^ iter)"
    by auto
  then show "upper - (xmid + upper) / 2 = (b - a) / (2 * 2 ^ iter)"
    by (smt (z3) field_sum_of_halves)
next
  show "\<And>lower upper iter.
       0 < f lower * f ((lower + upper) / 2) \<Longrightarrow>
       f lower * f upper \<le> 0 \<Longrightarrow> a \<le> lower \<Longrightarrow> upper \<le> b \<Longrightarrow> lower < upper \<Longrightarrow> upper - lower = (b - a) / 2 ^ iter \<Longrightarrow> tol < (b - a) / 2 ^ iter \<Longrightarrow> f ((lower + upper) / 2) * f upper \<le> 0"
    by (smt (verit) zero_less_mult_iff)
next
  show "\<And>lower upper iter.
       0 < f lower * f ((lower + upper) / 2) \<Longrightarrow>
       f lower * f upper \<le> 0 \<Longrightarrow> a \<le> lower \<Longrightarrow> upper \<le> b \<Longrightarrow> lower < upper \<Longrightarrow> upper - lower = (b - a) / 2 ^ iter \<Longrightarrow> tol < (b - a) / 2 ^ iter \<Longrightarrow> upper - (lower + upper) / 2 = (b - a) / (2 * 2 ^ iter)"
  proof -
    fix lower :: "\<real>" and upper :: "\<real>" and iter :: "\<nat>"
    assume a1: "upper - lower = (b - a) / 2 ^ iter"
    have f2: "\<forall>r ra. (r::\<real>) + - ra = r - ra"
      using add_uminus_conv_diff by blast
    have "\<forall>r ra rb. (r::\<real>) / ra / rb = r / (ra * rb)"
      using divide_divide_eq_left by blast
    then show "upper - (lower + upper) / 2 = (b - a) / (2 * 2 ^ iter)"
      using f2 a1 by (metis (no_types) add_diff_cancel_right' diff_minus_eq_add div_0 mult_2 mult_2_right real_average_minus_second right_minus_eq times_divide_eq_right uminus_add_conv_diff)
  qed
next
  show "f a * f b \<le> 0"
    using opposite_signs by auto
next
  show "a < b"
    by (simp add: a_less_than_b)
next
   fix upper iter xmid
    assume a1: "f xmid * f upper \<le> 0"
    assume a2: "a \<le> xmid"
    assume a3: "upper \<le> b"
    assume a4: "xmid < upper"
    assume a5: "upper - xmid = (b - a) / 2 ^ iter"
    assume a6: "\<not> tol < (b - a) / 2 ^ iter"

    then have "upper - xmid \<le> tol"
      by (simp add: a5)

    show "\<exists>c. f c = 0 \<and> a < c \<and> c < b \<and> \<bar>c - xmid\<bar> \<le> (b - a) / 2 ^ iter"
    proof(cases "f(xmid) = 0")
      show "f xmid = 0 \<Longrightarrow> \<exists>c. f c = 0 \<and> a < c \<and> c < b \<and> \<bar>c - xmid\<bar> \<le> (b - a) / 2 ^ iter"
        by (smt (verit, ccfv_SIG) a2 a3 a4 a5 mult_eq_0_iff opposite_signs)
    next
      assume "f xmid \<noteq> 0"
      show "\<exists>c. f c = 0 \<and> a < c \<and> c < b \<and> \<bar>c - xmid\<bar> \<le> (b - a) / 2 ^ iter"
      proof(cases "f  upper = 0")
        show "f upper = 0 \<Longrightarrow> \<exists>c. f c = 0 \<and> a < c \<and> c < b \<and> \<bar>c - xmid\<bar> \<le> (b - a) / 2 ^ iter"
          by (smt (verit, del_insts) a2 a3 a4 a5 mult_eq_0_iff opposite_signs)
      next
        assume "f upper \<noteq> 0"
        then have "f(xmid) * f(upper) < 0"
          using \<open>f xmid \<noteq> 0\<close> a1 mult_eq_0_iff by fastforce
        have "{xmid..upper} \<subseteq> {a..b}"
          by (simp add: a2 a3)          
        then have f_continuous: "continuous_on {xmid..upper} f"
          by (meson continuous_f continuous_on_subset)
        then show "\<exists>c. f c = 0 \<and> a < c \<and> c < b \<and> \<bar>c - xmid\<bar> \<le> (b - a) / 2 ^ iter"
          using Bolzanos_IVT \<open>f xmid * f upper < 0\<close> a2 a3 a4 a5 by fastforce
      qed
    qed
next
    fix lower upper iter
    assume a1: "f lower * f upper \<le> 0"
    assume a2: "a \<le> lower"
    assume a3: "upper \<le> b"
    assume a4: "lower < upper"
    assume a5: "upper - lower = (b - a) / 2 ^ iter"
    assume a6: "\<not> tol < (b - a) / 2 ^ iter"

    then have "upper - lower \<le> tol"
      by (simp add: a5)

    show "\<exists>c. f c = 0 \<and> a < c \<and> c < b \<and> \<bar>c - upper\<bar> \<le> (b - a) / 2 ^ iter"
    proof(cases "f(upper) = 0")
      show "f upper = 0 \<Longrightarrow> \<exists>c. f c = 0 \<and> a < c \<and> c < b \<and> \<bar>c - upper\<bar> \<le> (b - a) / 2 ^ iter"
        by (smt (verit, ccfv_SIG) a2 a3 a4 a5 mult_eq_0_iff opposite_signs)
    next
      assume "f upper \<noteq> 0"
      show "\<exists>c. f c = 0 \<and> a < c \<and> c < b \<and> \<bar>c - upper\<bar> \<le> (b - a) / 2 ^ iter"
      proof(cases "f  lower = 0")
        show "f lower = 0 \<Longrightarrow> \<exists>c. f c = 0 \<and> a < c \<and> c < b \<and> \<bar>c - upper\<bar> \<le> (b - a) / 2 ^ iter"
          by (smt (verit, del_insts) a2 a3 a4 a5 mult_eq_0_iff opposite_signs)
      next
        assume "f lower \<noteq> 0"
        then  have "f(lower) * f(upper) < 0"
          by (meson \<open>f upper \<noteq> 0\<close> a1 less_eq_real_def mult_eq_0_iff)


        have "{lower..upper} \<subseteq> {a..b}"
          by (simp add: a2 a3)          
        then have f_continuous: "continuous_on {lower..upper} f"
          by (meson continuous_f continuous_on_subset)
        then show "\<exists>c. f c = 0 \<and> a < c \<and> c < b \<and> \<bar>c - upper\<bar> \<le> (b - a) / 2 ^ iter"
          using Bolzanos_IVT \<open>f lower * f upper < 0\<close> a2 a3 a4 a5 by fastforce
    qed
  qed
qed






lemma bisection_with_root_check_error_bound:   
  assumes a_less_than_b: "(a::real) < (b::real)"
  assumes continuous_f: "continuous_on {a..b} f"
  assumes opposite_signs: "f(a)*f(b)<0"
  assumes postive_tolerance: "tol > 0"
  shows "H{True} bisection_with_root_check(f,a,b,tol) {\<exists> (c::real). (f(c) = 0 \<and> a < c \<and> c < b \<and>  (abs(c - xmid) \<le> (b - a)/(2^(iter))))}"
  unfolding continuous_on_def
proof(vcg)
  show "\<And>upper iter xmid.
       0 < f xmid * f ((xmid + upper) / 2) \<Longrightarrow>
       f xmid * f upper \<le> 0 \<Longrightarrow> a \<le> xmid \<Longrightarrow> upper \<le> b \<Longrightarrow> xmid < upper \<Longrightarrow> upper - xmid = (b - a) / 2 ^ iter \<Longrightarrow> tol < (b - a) / 2 ^ iter \<Longrightarrow> f xmid \<noteq> 0 \<Longrightarrow> f ((xmid + upper) / 2) * f upper \<le> 0"
    by (smt (verit, best) zero_less_mult_iff)
next
  fix upper iter xmid
  assume "upper - xmid = (b - a) / 2 ^ iter"
  then have "(upper - xmid) / 2 = (b - a) / (2 * 2 ^ iter)"
    by auto
  then show "upper - (xmid + upper) / 2 = (b - a) / (2 * 2 ^ iter)"
    by (smt (z3) field_sum_of_halves)
next
  show "\<And>lower upper iter.
       0 < f lower * f ((lower + upper) / 2) \<Longrightarrow>
       f lower * f upper \<le> 0 \<Longrightarrow> a \<le> lower \<Longrightarrow> upper \<le> b \<Longrightarrow> lower < upper \<Longrightarrow> upper - lower = (b - a) / 2 ^ iter \<Longrightarrow> tol < (b - a) / 2 ^ iter \<Longrightarrow> f upper \<noteq> 0 \<Longrightarrow> f ((lower + upper) / 2) * f upper \<le> 0"
    by (smt (verit) zero_less_mult_iff)
next
  show "\<And>lower upper iter.
       0 < f lower * f ((lower + upper) / 2) \<Longrightarrow>
       f lower * f upper \<le> 0 \<Longrightarrow>
       a \<le> lower \<Longrightarrow> upper \<le> b \<Longrightarrow> lower < upper \<Longrightarrow> upper - lower = (b - a) / 2 ^ iter \<Longrightarrow> tol < (b - a) / 2 ^ iter \<Longrightarrow> f upper \<noteq> 0 \<Longrightarrow> upper - (lower + upper) / 2 = (b - a) / (2 * 2 ^ iter)"
  proof -
    fix lower :: "\<real>" and upper :: "\<real>" and iter :: "\<nat>"
    assume a1: "upper - lower = (b - a) / 2 ^ iter"
    have f2: "\<forall>r ra. (r::\<real>) + - ra = r - ra"
      using add_uminus_conv_diff by blast
    have "\<forall>r ra rb. (r::\<real>) / ra / rb = r / (ra * rb)"
      using divide_divide_eq_left by blast
    then show "upper - (lower + upper) / 2 = (b - a) / (2 * 2 ^ iter)"
      using f2 a1 by (metis (no_types) add_diff_cancel_right' diff_minus_eq_add div_0 mult_2 mult_2_right real_average_minus_second right_minus_eq times_divide_eq_right uminus_add_conv_diff)
  qed
next
  show "f a * f b \<le> 0"
    using opposite_signs by auto
next
  show "a < b"
    by (simp add: a_less_than_b)
next
    fix upper iter xmid
    assume a1: "f xmid * f upper \<le> 0"
    assume a2: "a \<le> xmid"
    assume a3: "upper \<le> b"
    assume a4: "xmid < upper"
    assume a5: "upper - xmid = (b - a) / 2 ^ iter"
    assume a6: "\<not> tol < (b - a) / 2 ^ iter"

    then have "upper - xmid \<le> tol"
      by (simp add: a5)

    show "\<exists>c. f c = 0 \<and> a < c \<and> c < b \<and> \<bar>c - xmid\<bar> \<le> (b - a) / 2 ^ iter"
    proof(cases "f(xmid) = 0")
      show "f xmid = 0 \<Longrightarrow> \<exists>c. f c = 0 \<and> a < c \<and> c < b \<and> \<bar>c - xmid\<bar> \<le> (b - a) / 2 ^ iter"
        by (smt (verit, ccfv_SIG) a2 a3 a4 a5 mult_eq_0_iff opposite_signs)
    next
      assume "f xmid \<noteq> 0"
      show "\<exists>c. f c = 0 \<and> a < c \<and> c < b \<and> \<bar>c - xmid\<bar> \<le> (b - a) / 2 ^ iter"
      proof(cases "f  upper = 0")
        show "f upper = 0 \<Longrightarrow> \<exists>c. f c = 0 \<and> a < c \<and> c < b \<and> \<bar>c - xmid\<bar> \<le> (b - a) / 2 ^ iter"
          by (smt (verit, del_insts) a2 a3 a4 a5 mult_eq_0_iff opposite_signs)
      next
        assume "f upper \<noteq> 0"
        then have "f(xmid) * f(upper) < 0"
          using \<open>f xmid \<noteq> 0\<close> a1 mult_eq_0_iff by fastforce
        have "{xmid..upper} \<subseteq> {a..b}"
          by (simp add: a2 a3)          
        then have f_continuous: "continuous_on {xmid..upper} f"
          by (meson continuous_f continuous_on_subset)
        then show "\<exists>c. f c = 0 \<and> a < c \<and> c < b \<and> \<bar>c - xmid\<bar> \<le> (b - a) / 2 ^ iter"
          using Bolzanos_IVT \<open>f xmid * f upper < 0\<close> a2 a3 a4 a5 by fastforce
      qed
    qed
next
  show "\<And>upper iter xmid. a \<le> xmid \<Longrightarrow> upper \<le> b \<Longrightarrow> xmid < upper \<Longrightarrow> upper - xmid = (b - a) / 2 ^ iter \<Longrightarrow> f xmid = 0 \<Longrightarrow> \<exists>c. f c = 0 \<and> a < c \<and> c < b \<and> \<bar>c - xmid\<bar> \<le> (b - a) / 2 ^ iter"
    by (smt (verit, best) mult_eq_0_iff opposite_signs)
next
    fix lower upper iter
    assume a1: "f lower * f upper \<le> 0"
    assume a2: "a \<le> lower"
    assume a3: "upper \<le> b"
    assume a4: "lower < upper"
    assume a5: "upper - lower = (b - a) / 2 ^ iter"
    assume a6: "\<not> tol < (b - a) / 2 ^ iter"

    then have "upper - lower \<le> tol"
      by (simp add: a5)

    show "\<exists>c. f c = 0 \<and> a < c \<and> c < b \<and> \<bar>c - upper\<bar> \<le> (b - a) / 2 ^ iter"
    proof(cases "f(upper) = 0")
      show "f upper = 0 \<Longrightarrow> \<exists>c. f c = 0 \<and> a < c \<and> c < b \<and> \<bar>c - upper\<bar> \<le> (b - a) / 2 ^ iter"
        by (smt (verit, ccfv_SIG) a2 a3 a4 a5 mult_eq_0_iff opposite_signs)
    next
      assume "f upper \<noteq> 0"
      show "\<exists>c. f c = 0 \<and> a < c \<and> c < b \<and> \<bar>c - upper\<bar> \<le> (b - a) / 2 ^ iter"
      proof(cases "f  lower = 0")
        show "f lower = 0 \<Longrightarrow> \<exists>c. f c = 0 \<and> a < c \<and> c < b \<and> \<bar>c - upper\<bar> \<le> (b - a) / 2 ^ iter"
          by (smt (verit, del_insts) a2 a3 a4 a5 mult_eq_0_iff opposite_signs)
      next
        assume "f lower \<noteq> 0"
        then  have "f(lower) * f(upper) < 0"
          by (meson \<open>f upper \<noteq> 0\<close> a1 less_eq_real_def mult_eq_0_iff)


        have "{lower..upper} \<subseteq> {a..b}"
          by (simp add: a2 a3)          
        then have f_continuous: "continuous_on {lower..upper} f"
          by (meson continuous_f continuous_on_subset)
        then show "\<exists>c. f c = 0 \<and> a < c \<and> c < b \<and> \<bar>c - upper\<bar> \<le> (b - a) / 2 ^ iter"
          using Bolzanos_IVT \<open>f lower * f upper < 0\<close> a2 a3 a4 a5 by fastforce
      qed
    qed
  next 
    show "\<And>lower upper iter. a \<le> lower \<Longrightarrow> upper \<le> b \<Longrightarrow> lower < upper \<Longrightarrow> upper - lower = (b - a) / 2 ^ iter \<Longrightarrow> f upper = 0 \<Longrightarrow> \<exists>c. f c = 0 \<and> a < c \<and> c < b \<and> \<bar>c - upper\<bar> \<le> (b - a) / 2 ^ iter"
      using less_eq_real_def opposite_signs by auto
qed



 

  





































  

(*Caution:  A terrible rational approximation of phi = (sqrt(5) - 1) / 2  is used below! !*)

(*https://github.com/cran/cmna/blob/master/R/goldsect.R*)


(*return the \code{x} value of the minimum found*)



(*
procedure goldensectmin "(f :: real \<Rightarrow> real, a :: real, b :: real, tol :: real, m :: nat)" over state 
  = "iter:= 0;
    phi:= 0.6;  
    A:= a;
    B:= b;
    

    aStar:= b - phi * abs(b - a);
    bStar:= a + phi * abs(b - a);
    
    while (abs(B-A) > tol)
    do
      iter:= iter + 1;
      if (iter > m) then Stop fi;
      if (f(aStar) < f(bStar)) then
        B:= bStar;
        bStar:= aStar;
        aStar:= B - (phi * abs(B - A))
      else
        A:= aStar;
        aStar:= bStar;
        bStar:= A + (phi * abs(B - A))
      fi
    od;
    x_min:= (A+B)/2;
    f_min:= f(x_min)"
     
execute "goldensectmin (\<lambda> x. x^2 - 3 * x + 3 , 0, 5, 0.1, 100)"
*)

(*https://github.com/cran/cmna/blob/master/R/newton.R*)


procedure newton "(f :: real \<Rightarrow> real, fp :: real \<Rightarrow> real, x\<^sub>0 :: real, tol :: real, m :: nat)" over state 
  = "iter:= 0;

    oldx:= x\<^sub>0;
    X:= oldx + 10*tol;
    
    while (abs(X - oldx) > tol)
        
                             
    do
      iter:= iter + 1;
      if (iter > m) then Stop fi;
      oldx:= X;
      X:= X - f(X)/fp(X)
    od"


execute "newton (\<lambda> x.(x^3 - 2 * x^2 - 159 * x - 540) , \<lambda> x. (3 * x^2 - 4 * x - 159), 1, 0.001, 100)"


execute "newton (\<lambda> x.(x^3) , \<lambda> x. (3*x^2), 1, 0.001, 100)"


(*I would like to work on newton method and gradient
 descent in higher dimensions but that would require me to have a way to calculate vector norms.  
is there a vector equivalent to the "abs" function?*)


(* A Deep Dive Into How R Fits a Linear Model: 
http://madrury.github.io/jekyll/update/statistics/2016/07/20/lm-in-R.html*)


procedure secant "(f :: real \<Rightarrow> real, x\<^sub>0 :: real, tol :: real, m :: nat)" over state 
  = "iter:= 0;

    oldx:= x\<^sub>0;
    oldfx := f(x\<^sub>0);
    X:= oldx + 10*tol;
    
    while (abs(X - oldx) > tol)
    do
      iter:= iter + 1;
      
      fx:= X;
      newx := X - fx*((X-oldx)/(fx-oldfx));
      oldx := X;
      oldfx:= fx;
      X:= newx
    od
"


(*
procedure fibonacci "(n :: nat)" over state
 = "fibonacci <- function(n) {
    if(n == 0)
        return(0)
    if(n == 1)
        return(1)
    return(fibonacci(n - 1) + fibonacci(n - 2))
"

lemma fibonnacci_verified:   
  "H{True} fibonacci(n) {\<exists> (c::real). (f(c) = 0 \<and> a < c \<and> c < b \<and>  (abs(c - xmid) \<le> (b - a)/(2^(iter))))}"
  unfolding continuous_on_def
proof(vcg)
*)




end
