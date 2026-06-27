section \<open>Euler's Method (with assorted root-finding sketches)\<close>

theory Euler
  imports "ITree_VCG.ITree_VCG"
begin

text \<open>Euler's method for the ODE \<open>x' = f x\<close> as an imperative ITree program,
  together with an unverified secant-method sketch and some commented-out
  experiments. This is exploratory material kept outside the verified
  sessions.\<close>

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
