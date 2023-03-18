theory Euler
  imports "ITree_VCG.ITree_VCG"   "HOL-Analysis.Analysis" "HOL.Topological_Spaces"
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
  xmid :: "real"
  ymid :: "real"
  root :: "real"
  phi :: "rat"
  aStar :: "rat"
  bStar :: "rat"
  A :: "rat"
  B :: "rat"
  x_min :: "real"
  f_min :: "real"
  oldx :: "rat"
  X :: "rat"
  

term "\<lambda> x. 5 - 0.1 * x"

procedure euler "(f :: rat \<Rightarrow> rat, x\<^sub>0 :: rat, t :: rat, steps :: nat)" over state
  = "xs := [x\<^sub>0];
     for i in [0..<steps-1]
     do 
       xs := xs @ [xs!i + t * f(xs!i)]
     od"

execute "euler (\<lambda> x. - 0.1 * x, 0.1, 1, 10)"

lemma "real_of_rat(9581 / 1000) = 9.581" 
  oops



lemma "abs((2::int) -3) =1"
  by simp

(*Some documentation*)
(*https://github.com/cran/cmna/blob/master/R/bisection.R*)
(*https://search.r-project.org/CRAN/refmans/cmna/html/bisection.html*)

(*Below: m stands for the maximum iterations allowed*)
(*Note:  Whenever possible I try to emulate the style of the R source code*)


procedure bisection "(f :: real \<Rightarrow> real, a :: real, b :: real, tol :: real, m :: nat)" over state 
 = "iter := 0;
    fa:= f(a);
    fb:= f(b);
    lower:= a;
    upper:= b;
    xmid:= (lower + upper)/2;
    
     
    while (abs((upper - lower)) > tol) inv (fa * fb \<le> 0) \<and> (lower < xmid \<and> xmid < upper)

    
    do
      iter:= iter + 1;
      
       xmid:= (lower + upper)/2;      
       ymid:= f(xmid)
      ;
      if (fa*ymid >0) then (lower:= xmid; fa:= ymid) else (upper:= xmid; fb:= ymid) fi
    od;
    root:= (lower+upper)/2
"
(*if (iter > m) then Stop else xmid: .... fi*) (*I'm not sure how to handle this in the lemmas, so I'm removing for now!*)

(*Might want an invariant like inv (abs(xmid - c) \<le> (upper-lower)/(2^iter)) but it's unclear what c would mean here!  
  Can I just plug it in as:
inv \<exists>  c. (f(c) = 0 \<and> a < c \<and> c < b \<and>  (abs(xmid - c) \<le> (upper-lower)/(2^iter))) ?*)


(*Clearly above c_1 = (a+b)/2 *)

execute "bisection (\<lambda> x. (x*x*x) -2*x*x - 159 , 0, 10, 0.0001, 100)"  (*This has a root of 6.17 as desired!*)

value "real_of_int(32::nat)"  (*Converts ints and nats to reals*)

value "abs((3::real) - 2)"

term bisection

term "\<lambda> a1 b1 c1. H{a1}b1{c1}"

(*\<and> (\<exists>c.(f(c) = 0 \<and> lower < c \<and> c < upper))   An invariant?*)


lemma helpful_fact:
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
    then have "\<exists> \<gamma>. \<gamma> \<in> {\<alpha>..\<beta>} \<and> f \<gamma> = 0"
      using IVT'[OF continuous_f, of 0 \<beta> \<alpha>] a_less_than_b by auto
     (*Chat gpt proof*)
    oops
qed






(*

lemma bisection_error_bound:   
  assumes a_less_than_b: "(a::real) < (b::real)"
  assumes continuous_f: "continuous_on {a..b} f"
  assumes opposite_signs: "f(a)*f(b)<0"
  assumes postive_tolerance: "tol > 0"
  shows "H{True} bisection(f,a,b,tol,m) {\<exists> (c::real). (f(c) = 0 \<and> a < c \<and> c < b \<and>  (abs(xmid - c) \<le> (b-a)/(2^iter)))  }"
  unfolding continuous_on_def
proof(vcg)

  oops

*)
  
(*

  show "\<And>lower upper fa fb c.
       0 < fa * real_of_int (f ((lower + upper) / 2)) \<Longrightarrow>
       0 \<le> fa * fb \<Longrightarrow> tol < upper - lower \<Longrightarrow> f c = 0 \<Longrightarrow> lower < c \<Longrightarrow> c < upper \<Longrightarrow> 0 \<le> real_of_int (f ((lower + upper) / 2)) * fb"
    by (smt (verit, del_insts) zero_le_mult_iff zero_less_mult_iff)
  show "\<And>lower upper fa fb c.
       0 < fa * real_of_int (f ((lower + upper) / 2)) \<Longrightarrow>
       0 \<le> fa * fb \<Longrightarrow> tol < upper - lower \<Longrightarrow> f c = 0 \<Longrightarrow> lower < c \<Longrightarrow> c < upper \<Longrightarrow> \<exists>c. f c = 0 \<and> lower + upper < c * 2 \<and> c < upper"
    sorry
  show "\<And>lower upper iter fa fb xmid c.
       \<not> tol < upper - lower \<Longrightarrow>
       0 \<le> fa * fb \<Longrightarrow> f c = 0 \<Longrightarrow> lower < c \<Longrightarrow> c < upper \<Longrightarrow> \<exists>c. f c = 0 \<and> real_of_int a < c \<and> c < real_of_int b \<and> \<bar>xmid - c\<bar> \<le> (real_of_int b - real_of_int a) / 2 ^ iter"


*)




(*

(*   When we ONLY used (fa * fb \<ge> 0) for the invariance *)
  show "\<And>lower upper fa fb. 0 < fa * real_of_int (f ((lower + upper) / 2)) \<Longrightarrow> 0 \<le> fa * fb \<Longrightarrow> tol < \<bar>upper - lower\<bar> \<Longrightarrow> 0 \<le> real_of_int (f ((lower + upper) / 2)) * fb"
    by (smt (verit) zero_le_mult_iff zero_less_mult_iff)
  show "\<And>lower upper fa fb. \<not> 0 < fa * real_of_int (f ((lower + upper) / 2)) \<Longrightarrow> 0 \<le> fa * fb \<Longrightarrow> tol < \<bar>upper - lower\<bar> \<Longrightarrow> f ((lower + upper) / 2) \<noteq> 0 \<Longrightarrow> fa = 0"
  proof - 
    fix lower upper fa fb
    assume new_value_not_op_sign: "\<not> 0 < fa * real_of_int (f ((lower + upper) / 2))"
    assume opposite_signs: "0 \<le> fa * fb"
    assume not_converged: "tol < \<bar>upper - lower\<bar>"
    assume mid_not_root: "f ((lower + upper) / 2) \<noteq> 0"
    (*show "fa = 0"*)

    have new_value_not_op_sign2: "0 \<ge> fa * real_of_int (f ((lower + upper) / 2))"
      using new_value_not_op_sign by linarith

    show "fa = 0"
      sorry




    
  qed
  show "\<And>xmid. xmid * 2 = real_of_int a + real_of_int b \<Longrightarrow> 0 \<le> real_of_int (f (real_of_int a)) * real_of_int (f (real_of_int b))"
  proof - 
    fix xmid
    assume xmid_def: "xmid * 2 = real_of_int a + real_of_int b"
    show "0 \<le> real_of_int (f (real_of_int a)) * real_of_int (f (real_of_int b))"
      sorry
  qed
  then show "\<And>lower upper iter fa fb xmid.
       \<not> tol < \<bar>upper - lower\<bar> \<Longrightarrow> 0 \<le> fa * fb \<Longrightarrow> \<exists>c. f c = 0 \<and> real_of_int a < c \<and> c < real_of_int b \<and> \<bar>xmid - c\<bar> \<le> (real_of_int b - real_of_int a) / 2 ^ iter"
    by (metis divide_eq_eq_numeral1(1) not_le of_int_less_0_iff of_int_mult opposite_signs zero_neq_numeral)
qed

*)




  

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


procedure newton "(f :: rat \<Rightarrow> rat, fp :: rat \<Rightarrow> rat, x\<^sub>0 :: rat, tol :: rat, m :: nat)" over state 
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




end
