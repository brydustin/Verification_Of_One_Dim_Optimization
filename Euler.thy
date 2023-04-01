theory Euler
  imports "ITree_VCG.ITree_VCG"   "HOL-Analysis.Analysis" "HOL.Topological_Spaces" "HOL-Library.Log_Nat"
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






(*I removed the following: 
                                    \<and> (iter = 0) \<or> (iter > 0 \<and> (upper - lower) = (b - a) / 2^iter)

and replaced it with:  \<and> ((upper - lower) \<le> (b - a) / 2^iter)

They seem very similar but give different goals....

Going to experiment with this.... \<and> ((lower = xmid \<and> fa = ymid) \<or> (upper = xmid \<and> fb = ymid))


Isn't
((iter = 0 \<and> fa \<noteq> 0 \<and> fb \<noteq> 0) \<or> (iter > 0)) just equivalent to f(a) \<noteq> 0  and f(b) \<noteq> 0 ?!
Why not use the latter as an invariant... it's more clear. Or even better.... (f(a)*f(b) <  0).... or even better just remove it all together because that's an assumption!




Try without: \<and> (\<exists> \<gamma>. (f(\<gamma>) = 0 \<and> lower \<le> \<gamma> \<and> \<gamma> \<le> upper)) and instead try to derive it!
Likewise with "                                     \<and> ((lower \<le> xmid) \<and> (xmid \<le> upper)) "

I wonder if it is better to assume fewer invariants if you can always dervie the others or assume more invariants (assuming they can be proven from the more basic list!?)
*)



procedure bisection "(f :: real \<Rightarrow> real, a :: real, b :: real, tol :: real)" over state
 = "iter := 0;
    fa:= f(a);
    fb:= f(b);
    lower:= a;
    upper:= b;
    xmid:= (lower + upper)/2;
    ymid:= f(xmid);
    
     
    while (upper - lower > tol) \<and> ymid \<noteq> 0  


                                    inv (fa * fb \<le> 0)   
                                    \<and> ((lower \<le> xmid) \<and> (xmid \<le> upper))
                                    \<and> (\<exists> \<gamma>. (f(\<gamma>) = 0 \<and> lower \<le> \<gamma> \<and> \<gamma> \<le> upper))          
                                    \<and> xmid = (lower + upper)/2
                                    \<and> ymid = f(xmid)
                                    \<and> fa = f(lower)
                                    \<and> fb = f(upper)
                                    \<and> ((a \<le> lower) \<and> (upper \<le> b))
                                    \<and> (lower < upper)
                                    \<and> ((upper - lower) = (b - a) / 2^iter)
                                   
                                    
    do
      iter:= iter + 1;
      
      xmid:= (lower + upper)/2;      
      ymid:= f(xmid)
      ;
      if (fa*ymid >0) then (lower:= xmid; fa:= ymid) else (upper:= xmid; fb:= ymid) fi
    od;
    root:= (lower+upper)/2
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











lemma bisection_error_bound:   
  assumes a_less_than_b: "(a::real) < (b::real)"
  assumes continuous_f: "continuous_on {a..b} f"
  assumes opposite_signs: "f(a)*f(b)<0"
  assumes postive_tolerance: "tol > 0"
  shows "H{True} bisection(f,a,b,tol) {\<exists> (c::real). (f(c) = 0 \<and> a < c \<and> c < b \<and>  (abs(c - xmid) \<le> (b - a)/(2^(iter+1))))}"
  unfolding continuous_on_def
proof(vcg)
 






    
 








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
