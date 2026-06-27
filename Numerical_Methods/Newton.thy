section \<open>Newton's Method (imperative ITree program)\<close>

theory Newton
  imports "ITree_Numeric_VCG.ITree_Numeric_VCG"
begin

text \<open>Newton's root-finding iteration \<open>x \<mapsto> x - f x / f' x\<close> as an imperative
  ITree program over a small state record. The quadratic-convergence statement
  is recorded but its proof is left open.\<close>

zstore state =
  iter :: "nat"
  fx :: "real"
  f'x :: "real"
  x :: "real"
  x_new :: "real"

program newton "(f :: real \<Rightarrow> real, f' :: real \<Rightarrow> real, x\<^sub>0 :: real, tol :: real, max_iter :: nat)" over state 
  = "iter := 0;
    x := x\<^sub>0;
              
    while (iter < max_iter)
    do
      fx := f(x); 
      f'x := f'(x);   
      x_new := x - (fx/f'x);
      if \<bar>x_new - x\<bar> < tol
      then iter := max_iter
      fi;
      x := x_new
    od
"

execute "newton (\<lambda> x.(x^3 - 3 * x^2 - 1) , \<lambda> x. (3 * x^2 - 6 * x), 3, 0.1, 500)"

(*https://github.com/cran/cmna/blob/master/R/newton.R*)


lemma newton_quadratic_convergence:   
  assumes a_less_than_b: "(a::real) < (b::real)"
  assumes continuous_f: "continuous_on {a..b} f"
  assumes convex: "convex_on {a..b} f"
  assumes opposite_signs: "f(a)*f(b)<0"
  assumes postive_tolerance: "tol > 0"
  shows "H{a< x\<^sub>0 \<and> x\<^sub>0 < b} newton (f,f',x\<^sub>0, tol, m){\<bar>x_new - x\<bar> < tol}"
  unfolding continuous_def convex_on_def
proof(vcg)

  oops








end