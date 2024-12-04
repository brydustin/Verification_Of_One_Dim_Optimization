theory Sigmoid
  imports "HOL-Analysis.Analysis" Complex_Main  "HOL-Combinatorics.Stirling"
begin

definition sigmoid :: "real \<Rightarrow> real" where 
"sigmoid = (\<lambda> x::real. exp(x) / (1 + exp(x)))"



lemma sigmoid_alt_def: "sigmoid x = inverse (1 + exp(-x))"
proof -
  have "sigmoid x = (exp(x) * exp(-x)) / ((1 + exp(x))* exp(-x))"
    unfolding sigmoid_def by simp
  also have "... = 1 / (1*exp(-x) + exp(x)*exp(-x))"
    by (simp add: distrib_right exp_minus_inverse)
  also have "... = inverse (exp(-x) + 1)"
    by (simp add: divide_inverse_commute exp_minus)
  finally show ?thesis
    by simp
qed

(* Bounds *)

lemma sigmoid_pos: "sigmoid x > 0"
  apply (smt (verit) divide_le_0_1_iff exp_gt_zero inverse_eq_divide sigmoid_alt_def)
  done

(* Prove that sigmoid(x) is strictly less than 1 for all x *)
lemma sigmoid_less_1: "sigmoid x < 1"
  apply (smt (verit) le_divide_eq_1_pos not_exp_le_zero sigmoid_def)
  done

(* Theorem: The sigmoid function takes values between 0 and 1 for all real x *)
theorem sigmoid_range: "0 < sigmoid x \<and> sigmoid x < 1"
  apply (simp add: sigmoid_less_1 sigmoid_pos)
  done






(* Symmetry (Odd Function)
The sigmoid function is symmetric about the origin in a certain sense:
\<sigma>(−x) = 1−\<sigma>(x). This property reflects the fact that as the input x becomes
negative, the sigmoid shifts its output towards 0, while positive inputs
shift the output towards 1. *)

theorem sigmoid_symmetry: "sigmoid (-x) = 1 - sigmoid x"
  apply (smt (verit, ccfv_SIG) add_divide_distrib divide_self_if exp_ge_zero inverse_eq_divide sigmoid_alt_def sigmoid_def)
  done


(* Sum Identity
The sigmoid function has an interesting identity when considering the sum of
sigmoid outputs for x and −x : \<sigma>(x) + \<sigma>(−x) = 1 This follows directly from
the symmetry property. *)

theorem "sigmoid(x) + sigmoid(-x) = 1"
  by (simp add: sigmoid_symmetry)

(* Increasing
The sigmoid function is strictly increasing. *)

theorem sigmoid_strictly_increasing: "x1 < x2 \<Longrightarrow> sigmoid x1 < sigmoid x2"
  apply (unfold sigmoid_alt_def)
  apply (smt (verit) add_strict_left_mono divide_eq_0_iff exp_gt_zero exp_less_cancel_iff inverse_less_iff_less le_divide_eq_1_pos neg_0_le_iff_le neg_le_iff_le order_less_trans real_add_le_0_iff)
  done


lemma sigmoid_left_dom_range:
  assumes "x < 0"
  shows "sigmoid x < 1/2"
  by (metis assms exp_zero one_add_one sigmoid_def sigmoid_strictly_increasing)

lemma sigmoid_right_dom_range:
  assumes "x \<ge> 0"
  shows "sigmoid x \<ge> 1/2"
  using assms less_eq_real_def sigmoid_alt_def sigmoid_strictly_increasing by fastforce













(* Derivative
The derivative of the sigmoid function can be expressed in terms of the function
itself: \<sigma>\<Zprime>(x) = \<sigma>(x ) \<^emph> (1 − \<sigma>(x )). This is a key identity used in
backpropagation for updating weights in neural networks. It shows that the
derivative depends on the value of the function itself, simplifying calculations
in optimisation problems. *)

lemma uminus_derive_minus_one: "(uminus has_derivative (*) (-1 :: real)) (at a within A)"
  apply (rule has_derivative_eq_rhs)
   apply (rule derivative_intros)
   apply (rule derivative_intros)
  apply fastforce
  done




term "(^^)"



lemma sigmoid_differentiable: 
  "(\<lambda>x. sigmoid x) differentiable_on UNIV"
proof -
  have "\<forall>x. sigmoid differentiable (at x)"
  proof 
    fix x :: real
    have num_diff: "(\<lambda>x. exp x) differentiable (at x)"
      by (simp add: field_differentiable_imp_differentiable field_differentiable_within_exp)
    have denom_diff: "(\<lambda>x. 1 + exp x) differentiable (at x)"
      by (simp add: num_diff)
    hence "(\<lambda>x. exp x / (1 + exp x)) differentiable (at x)"
      by (metis add_le_same_cancel2 num_diff differentiable_divide exp_ge_zero not_one_le_zero)    
    thus "sigmoid differentiable (at x)"
      by (simp add: sigmoid_def)
  qed
  thus ?thesis
    by (simp add: differentiable_on_def)
qed

lemma sigmoid_differentiable':
 "sigmoid field_differentiable at x"
  by (meson UNIV_I differentiable_on_def field_differentiable_def real_differentiableE sigmoid_differentiable)

(* has_derivative*)
(*frechet_derivative*)
  (*Geautux derivative*)


(* x is real, f : real \<longrightarrow> real, therefore f(x) is real*)


lemma sigmoid_derivative:
  shows "deriv sigmoid x = sigmoid x * (1 - sigmoid x)"
proof(unfold sigmoid_def)
  have "deriv (\<lambda>x. exp x / (1 + exp x)) x = deriv (\<lambda>w. (\<lambda>x. exp x) w  / (\<lambda>x. 1 + exp x)w) x"
    by simp
  also have "... = (deriv (\<lambda>x. exp x) x * (\<lambda>x. 1 + exp x) x - (\<lambda>x. exp x) x * deriv (\<lambda>x. 1 + exp x) x) / ((\<lambda>x. 1 + exp x) x)\<^sup>2"
    apply(rule deriv_divide)
       apply(simp add: field_differentiable_within_exp)
       apply(simp add: Derivative.field_differentiable_add field_differentiable_within_exp)
       apply(smt (verit, ccfv_threshold) exp_gt_zero)
    done
  also have "... = ((exp x) * (1 + exp x) - (exp x)  * (deriv (\<lambda>w. ((\<lambda>v. 1)w + (\<lambda> u. exp u)w)) x)     ) / (1 + exp x)\<^sup>2"
    by (simp add: DERIV_imp_deriv)
  also have "... = ((exp x) * (1 + exp x) - (exp x)  * (deriv (\<lambda>v. 1) x  + deriv (\<lambda> u. exp u) x)     ) / (1 + exp x)\<^sup>2"
    by (subst deriv_add, simp, simp add: field_differentiable_within_exp, auto)
  also have "... = ((exp x) * (1 + exp x) - (exp x)  * (exp x)) / (1 + exp x)\<^sup>2"
    by (simp add: DERIV_imp_deriv)
  also have "... = (exp x + (exp x)\<^sup>2 - (exp x)\<^sup>2) / (1 + exp x)\<^sup>2"
    by (simp add: ring_class.ring_distribs(1))  
  also have "... = (exp x / (1 + exp x)) * (1 / (1 + exp x))"
    by (simp add: power2_eq_square)
  also have "... = exp x / (1 + exp x) * (1 - exp x / (1 + exp x))"
    by (metis add.inverse_inverse inverse_eq_divide sigmoid_alt_def sigmoid_def sigmoid_symmetry)
  then show "deriv (\<lambda>x. exp x / (1 + exp x)) x = exp x / (1 + exp x) * (1 - exp x / (1 + exp x))"
    using \<open>(deriv exp x * (1 + exp x) - exp x * deriv (\<lambda>x. 1 + exp x) x) / (1 + exp x)\<^sup>2 = (exp x * (1 + exp x) - exp x * deriv (\<lambda>w. 1 + exp w) x) / (1 + exp x)\<^sup>2\<close>
 \<open>(exp x * (1 + exp x) - exp x * (deriv (\<lambda>v. 1) x + deriv exp x)) / (1 + exp x)\<^sup>2 = (exp x * (1 + exp x) - exp x * exp x) / (1 + exp x)\<^sup>2\<close> \<open>(exp x * (1 + exp x) - exp x * deriv (\<lambda>w. 1 + exp w) x) / (1 + exp x)\<^sup>2 = (exp x * (1 + exp x) - exp x * (deriv (\<lambda>v. 1) x + deriv exp x)) / (1 + exp x)\<^sup>2\<close>
 \<open>(exp x * (1 + exp x) - exp x * exp x) / (1 + exp x)\<^sup>2 = (exp x + (exp x)\<^sup>2 - (exp x)\<^sup>2) / (1 + exp x)\<^sup>2\<close> \<open>(exp x + (exp x)\<^sup>2 - (exp x)\<^sup>2) / (1 + exp x)\<^sup>2 = exp x / (1 + exp x) * (1 / (1 + exp x))\<close> \<open>deriv (\<lambda>w. exp w / (1 + exp w)) x = (deriv exp x * (1 + exp x) - exp x * deriv (\<lambda>x. 1 + exp x) x) / (1 + exp x)\<^sup>2\<close>
    by presburger
qed
  
(*Might be good to show that 0 < \<sigma>'(x) < 1/4*)

(*Old proof  This one is so much shorter but which is preferred?
lemma sigmod_derivative':
  "DERIV sigmoid x :> sigmoid(x) * (1 - sigmoid(x))"
  apply (unfold sigmoid_alt_def)
  apply (unfold has_field_derivative_def)
  apply (rule has_derivative_eq_rhs)
  apply (rule derivative_intros)
   apply (metis add.right_neutral le_minus_one_simps(1) minus_add_cancel not_exp_le_zero)
  apply (rule derivative_intros)
   apply (rule derivative_intros)
  apply (rule derivative_intros)
   apply (rule uminus_derive_minus_one)
  apply (auto simp add: fun_eq_iff)
  using division_ring_inverse_diff by force
*)







(*This is simply helpful to have, but we can eliminate it if needed!*)
lemma deriv_one_minus_sigmoid:
  "deriv (\<lambda>y. 1 - sigmoid y) x = sigmoid x * (sigmoid x - 1)"
  apply (subst deriv_diff)
  apply simp
  using field_differentiable_def
  apply (metis UNIV_I differentiable_on_def real_differentiableE sigmoid_differentiable)
  by (metis deriv_const diff_0 minus_diff_eq mult_minus_right sigmoid_derivative)  





fun Nth_derivative :: "nat \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real" where
  "Nth_derivative 0 f x = f x" |
  "Nth_derivative (Suc n) f x = deriv (Nth_derivative n f) x"


lemma first_derivative_alt_def:
 "Nth_derivative 1 f x = deriv f x"
proof -
  have "deriv (Nth_derivative 0 f) x = deriv f x"
    using Nth_derivative.simps(1) by presburger
  then show ?thesis
    by simp
qed

lemma second_derivative_alt_def:
"Nth_derivative 2 f x  = deriv (deriv f) x"
  using Nth_derivative.simps(1,2) numeral_2_eq_2 by presburger


definition C_k_on :: "nat \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real set \<Rightarrow> bool" where
  "C_k_on k f U \<equiv> (\<forall>n \<le> k. \<forall>x \<in> U. continuous_on U (Nth_derivative n f))"

 
definition smooth :: "(real \<Rightarrow> real) \<Rightarrow> bool" where
  "smooth f \<equiv> (\<forall>k. \<exists>U. open U \<and> (\<forall>x\<in>U. C_k_on k f U))"







(* Second Derivative
The second derivative of the sigmoid function can also be expressed in terms of
the function itself: \<sigma>\<Zprime>\<Zprime>(x) = \<sigma>(x)\<^emph>(1−\<sigma>(x))\<^emph>(1−2\<^emph>\<sigma>(x)). This identity is useful
when analysing the curvature of the sigmoid function, particularly in
optimisation problems. *)

thm deriv_mult

lemma sigmoid_second_derivative:
  shows "Nth_derivative 2 sigmoid x = sigmoid x * (1 - sigmoid x) * (1 - 2 * sigmoid x)"
proof - 
  have "Nth_derivative 2 sigmoid x =  deriv ((\<lambda>w. deriv sigmoid w)) x"
    by (simp add: second_derivative_alt_def)
  also have "... = deriv ((\<lambda>w. (\<lambda>a. sigmoid a) w * (((\<lambda>u.1) - (\<lambda>v. sigmoid v)) w ))) x"
    by (simp add: sigmoid_derivative)
  also have "... = sigmoid x * (deriv ((\<lambda>u.1) - (\<lambda>v. sigmoid v)) x) + deriv (\<lambda>a. sigmoid a) x * ((\<lambda>u.1) - (\<lambda>v. sigmoid v)) x"
    by (rule deriv_mult,
        simp add: sigmoid_differentiable',
        simp add: Derivative.field_differentiable_diff sigmoid_differentiable')
  also have "... = sigmoid x * (deriv (\<lambda>y. 1 - sigmoid y) x) + deriv (\<lambda>a. sigmoid a) x * ((\<lambda>u.1) - (\<lambda>v. sigmoid v)) x"
    by (meson minus_apply)
  also have "... = sigmoid x * (deriv (\<lambda>y. 1 - sigmoid y) x) + deriv (\<lambda>a. sigmoid a) x * (\<lambda>y. 1 - sigmoid y) x"
    by simp
  also have "... = sigmoid x * sigmoid x * (sigmoid x -1) + sigmoid x * (1 - sigmoid x) * (1 - sigmoid x)"
    by (simp add: deriv_one_minus_sigmoid sigmoid_derivative)
  also have "... = sigmoid x * (1 - sigmoid x) * (1 - 2 * sigmoid x)"
    by (simp add: right_diff_distrib)
  finally show ?thesis.
qed



(*
NOTE:
has_real_derivative is a special case for has_field derivative is a special case for has_derivative

We need to know how to use the computed derivatives to show that "has_derivative" is true.

lemma test_lemma:
  "\<exists>f'. (Nth_derivative 2 sigmoid has_derivative f') (at y)"
proof -


  have "(Nth_derivative 2 sigmoid has_real_derivative (Nth_derivative 3 sigmoid) y) (at y)"

*)




(*Reference: https://eecs.ceas.uc.edu/~minaiaa/papers/minai_sigmoids_NN93.pdf *)
(*           https://analyticphysics.com/Mathematical%20Methods/Multiple%20Derivatives%20of%20the%20Sigmoid%20Function.htm *)




(*Higher Order Derivatives*)


(*Stirling refers to Stirling numbers of the 2nd kind!*)

theorem nth_derivative_sigmoid:
  "\<And>x. Nth_derivative n sigmoid x = 
    (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (sigmoid x)^k)"
proof (induct n)
  case 0
  show ?case
    by simp
next
  fix n x
  assume induction_hypothesis: 
    "\<And>x. Nth_derivative n sigmoid x = 
         (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (sigmoid x)^k)"
  show "Nth_derivative (Suc n) sigmoid x = 
          (\<Sum>k = 1..(Suc n)+1. (-1)^(k+1) * fact (k - 1) * Stirling ((Suc n)+1) k * (sigmoid x)^k)"
  proof -
  

    
    (*Auxillary facts: *)

    have sigmoid_pwr_rule: "\<And>k. deriv (\<lambda>v. (sigmoid v)^k) x = k * (sigmoid x)^(k - 1) * deriv (\<lambda>u. sigmoid u) x"
        by (subst deriv_pow, simp add: sigmoid_differentiable', simp)
    have index_shift: "(\<Sum>j = 1..n+1. ((-1)^(j+1+1) * fact (j - 1) * Stirling (n+1) j * j * ((sigmoid x)^(j+1)))) = 
                          (\<Sum>j = 2..n+2. (-1)^(j+1) * fact (j - 2) * Stirling (n+1) (j - 1) * (j - 1) * (sigmoid x)^j)"
      by (rule sum.reindex_bij_witness[of _ "\<lambda>j. j -1" "\<lambda>j. j + 1"], simp+,  auto)



    have simplified_terms: "(\<Sum>k = 1..n+1. ((-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * k * (sigmoid x)^k) +
                                           ((-1)^(k+1) * fact (k - 2) * Stirling (n+1) (k-1) * (k-1) * (sigmoid x)^k)) = 
                            (\<Sum>k = 1..n+1. ((-1)^(k+1) * fact (k - 1) * Stirling (n+2) k *  (sigmoid x)^k))"
    proof - 
      have equal_terms: "\<forall> (k::nat) \<ge> 1.
       ((-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * k * (sigmoid x)^k) +
       ((-1)^(k+1) * fact (k - 2) * Stirling (n+1) (k-1) * (k-1) * (sigmoid x)^k) = 
       ((-1)^(k+1) * fact (k - 1) * Stirling (n+2) k * (sigmoid x)^k)"

      proof(clarify)
        fix k::nat
        assume "1 \<le> k"

        have "real_of_int ((- 1) ^ (k + 1) * fact (k - 1) * int (Stirling (n + 1) k) * int k) * sigmoid x ^ k +
              real_of_int ((- 1) ^ (k + 1) * fact (k - 2) * int (Stirling (n + 1) (k - 1)) * int (k - 1)) * sigmoid x ^ k =
              real_of_int (((- 1) ^ (k + 1) * ((fact (k - 1) * int (Stirling (n + 1) k) * int k) +
                                       (fact (k - 2) * int (Stirling (n + 1) (k - 1)) * int (k - 1))))) * sigmoid x ^ k"
          by (metis (mono_tags, opaque_lifting) ab_semigroup_mult_class.mult_ac(1) distrib_left mult.commute of_int_add)
        also have "... = real_of_int (((- 1) ^ (k + 1) * ((fact (k - 1) * int (Stirling (n + 1) k) * int k) +
                                                  ((int (k - 1) * fact (k - 2)) * int (Stirling (n + 1) (k - 1)))))) * sigmoid x ^ k"
              by (simp add: ring_class.ring_distribs(1))
        also have "... = real_of_int (((- 1) ^ (k + 1) * ((fact (k - 1) * int (Stirling (n + 1) k) * int k) +
                                                  (fact (k - 1) * int (Stirling (n + 1) (k - 1)))))) * sigmoid x ^ k"
          by (smt (verit, ccfv_threshold) Stirling.simps(3) add.commute diff_diff_left fact_num_eq_if mult_eq_0_iff of_nat_eq_0_iff one_add_one plus_1_eq_Suc)
        also have "... = real_of_int (((- 1) ^ (k + 1) * fact (k - 1)*
                              ( Stirling (n + 1) k *  k +    Stirling (n + 1) (k - 1)  )  )) * sigmoid x ^ k"
          by (simp add: distrib_left)
        also have "... = real_of_int ((- 1) ^ (k + 1) * fact (k - 1) * int (Stirling (n + 2) k)) * sigmoid x ^ k"
          by (smt (z3) Stirling.simps(4) Suc_eq_plus1 \<open>1 \<le> k\<close> add.commute le_add_diff_inverse mult.commute nat_1_add_1 plus_nat.simps(2))
        finally show "real_of_int ((- 1) ^ (k + 1) * fact (k - 1) * int (Stirling (n + 1) k) * int k) * sigmoid x ^ k +
         real_of_int ((- 1) ^ (k + 1) * fact (k - 2) * int (Stirling (n + 1) (k - 1)) * int (k - 1)) * sigmoid x ^ k =
         real_of_int ((- 1) ^ (k + 1) * fact (k - 1) * int (Stirling (n + 2) k)) * sigmoid x ^ k".
      qed     
      from equal_terms show ?thesis
        by simp
    qed



    (*Main Goal: *)

    have "Nth_derivative (Suc n) sigmoid x = deriv (\<lambda> w. Nth_derivative n sigmoid w) x"
      by simp    
    also have "... = deriv (\<lambda> w.\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (sigmoid w)^k) x"
      using induction_hypothesis by presburger
    also have "... = (\<Sum>k = 1..n+1. deriv (\<lambda>w. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (sigmoid w)^k) x)"
      by (rule deriv_sum, metis(mono_tags) DERIV_chain2 DERIV_cmult_Id field_differentiable_def field_differentiable_power sigmoid_differentiable')
    also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * deriv (\<lambda>w. (sigmoid w)^k) x)"
      by(subst deriv_cmult, auto, simp add: field_differentiable_power sigmoid_differentiable')
    also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^(k - 1) * deriv (\<lambda>u. sigmoid u) x))"
      using sigmoid_pwr_rule by presburger
    also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^(k - 1) * (sigmoid x * (1 - sigmoid x))))"
      using sigmoid_derivative by presburger
    also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * ((sigmoid x)^(k - 1) * (sigmoid x)^1) * (1 - sigmoid x)))"
      by (simp add: mult.assoc)
    also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^(k-1+1) * (1 - sigmoid x)))"
      by (metis (no_types, lifting) power_add)
    also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^k * (1 + -sigmoid x)))"
      by fastforce
    also have "... = (\<Sum>k = 1..n+1. (    (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^k)) * (1 + -sigmoid x)   )"
      by (simp add: ab_semigroup_mult_class.mult_ac(1))
    also have "... = (\<Sum>k = 1..n+1. (    (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^k)) *1 +
                                    ((    (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^k)) * (-sigmoid x))   )"
      by (meson vector_space_over_itself.scale_right_distrib)
    also have "... = (\<Sum>k = 1..n+1. (    (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^k))  +
                                    (    (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^k)) * (-sigmoid x))"
      by simp
    also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^k))  +
                     (\<Sum>k = 1..n+1. ((-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^k)) * (-sigmoid x))"
      by (metis (no_types) sum.distrib)
    also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^k))  +
                     (\<Sum>k = 1..n+1. ((-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * k * ((sigmoid x)^k * (-sigmoid x)     )   ))"
      by (simp add: mult.commute mult.left_commute)
    also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^k))  +
                     (\<Sum>j = 1..n+1. ((-1)^(j+1+1) * fact (j - 1) * Stirling (n+1) j * j * ((sigmoid x)^(j+1)     )   ))"
      by (simp add: mult.commute)
    also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (k * (sigmoid x)^k)) +
                     (\<Sum>j = 2..n+2. (-1)^(j+1) * fact (j - 2) * Stirling (n+1) (j - 1) * (j - 1) * (sigmoid x)^j)"
      using index_shift by presburger
    also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * k * (sigmoid x)^k) +
                      0 +
                     (\<Sum>j = 2..n+2. (-1)^(j+1) * fact (j - 2) * Stirling (n+1) (j - 1) * (j - 1) * (sigmoid x)^j)"
      by (smt (verit, ccfv_SIG) ab_semigroup_mult_class.mult_ac(1) of_int_mult of_int_of_nat_eq sum.cong)
    also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * k * (sigmoid x)^k)  +
                                   ((-1)^(1+1) * fact (1 - 2) * Stirling (n+1) (1 - 1) * (1 - 1) * (sigmoid x)^1 ) +
                     (\<Sum>k = 2..n+2. (-1)^(k+1) * fact (k - 2) * Stirling (n+1) (k - 1) * (k  -1) * (sigmoid x)^k )"
      by simp
    also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * k * (sigmoid x)^k)  +
                     (\<Sum>k = 1..n+2. (-1)^(k+1) * fact (k - 2) * Stirling (n+1) (k-1) * (k-1) * (sigmoid x)^k        )"
      by (smt (verit) Suc_eq_plus1 Suc_leI add_Suc_shift add_cancel_left_left cancel_comm_monoid_add_class.diff_cancel nat_1_add_1 of_nat_0 sum.atLeast_Suc_atMost zero_less_Suc)
   also have "... = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * k * (sigmoid x)^k) +
                     (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 2) * Stirling (n+1) (k-1) * (k-1) * (sigmoid x)^k) +
               ((-1)^((n+2)+1) * fact ((n+2) - 2) * Stirling (n+1) ((n+2)-1) * ((n+2)-1) * (sigmoid x)^(n+2))"
      by simp
    also have "... = (\<Sum>k = 1..n+1. ((-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * k * (sigmoid x)^k) +
                                    ((-1)^(k+1) * fact (k - 2) * Stirling (n+1) (k-1) * (k-1) * (sigmoid x)^k)) +
                   ((-1)^((n+2)+1) * fact ((n+2) - 2) * Stirling (n+1) ((n+2)-1) * ((n+2)-1) * (sigmoid x)^(n+2))"
      by (metis (no_types) sum.distrib)
    also have "... = (\<Sum>k = 1..n+1. ((-1)^(k+1) * fact (k - 1) * Stirling (n+2) k *  (sigmoid x)^k)) +
                                    ((-1)^((n+2)+1) * fact ((n+2) - 2) * Stirling (n+1) ((n+2)-1) * ((n+2)-1) * (sigmoid x)^(n+2))"
      using simplified_terms by presburger   
    also have "... = (\<Sum>k = 1..n+1. ((-1)^(k+1) * fact (k - 1) * Stirling ((Suc n) + 1) k *  (sigmoid x)^k)) +
        (\<Sum>k = Suc n + 1..Suc n + 1.((-1)^(k+1) * fact (k - 1) * Stirling ((Suc n) + 1) k  * (sigmoid x)^(k)))"
      by(subst atLeastAtMost_singleton,  simp)   
    also have "... = (\<Sum>k = 1..(Suc n)+1. (-1)^(k+1) * fact (k - 1) * Stirling ((Suc n)+1) k * (sigmoid x)^k)"
      by (subst sum.cong[where B="{1..n + 1}", where h = "\<lambda>k. ((-1)^(k+1) * fact (k - 1) * Stirling ((Suc n) + 1) k  * (sigmoid x)^(k))"], simp+)
    finally show ?thesis.
  qed
qed

(*Differentiable vs field differentiable*)

lemma second_deriv_sigmoid_differentiable:
  "(\<lambda>x. Nth_derivative 2 sigmoid x) differentiable (at x)"   
proof -
  have second_derivative_diff:
    "(\<lambda>x. sigmoid x * (1 - sigmoid x) * (1 - 2 * sigmoid x)) differentiable (at x)"
    by (simp add: field_differentiable_imp_differentiable sigmoid_differentiable')
  then show ?thesis
    using sigmoid_second_derivative by presburger
qed




lemma smooth_sigmoid:
  "smooth sigmoid"
  unfolding smooth_def
proof (clarify)
  fix k :: nat
  let ?U = UNIV  (* Use the entire real number line *)
  have "open ?U" by simp
  have C_k: "\<forall>x\<in>?U. C_k_on k sigmoid ?U"
    unfolding C_k_on_def
  proof (clarify)
    fix x::real
    fix n 
    fix a::real
    assume "x \<in> UNIV"
    assume "n \<le> k"
    assume "a \<in> UNIV"
    have nth_deriv: "Nth_derivative n sigmoid x = (\<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (sigmoid x)^k)"
      using nth_derivative_sigmoid by presburger    
    have "\<And>k. k \<in> {1..n + 1} \<Longrightarrow> continuous_on UNIV (\<lambda>x.((-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (sigmoid x)^k))"
    proof - 
      fix k
      have cont_const: "continuous_on UNIV (\<lambda>x. (\<lambda>y. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k) x)"
        using continuous_on_const by blast
      have cont_sigmoid: "continuous_on UNIV (\<lambda>x.((sigmoid x)^k))"
        by (simp add: continuous_on_power differentiable_imp_continuous_on sigmoid_differentiable)
      show cont_prod: "continuous_on UNIV (\<lambda>x. (\<lambda>x. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k) x * (\<lambda>x. (sigmoid x)^k) x)"
        using continuous_on_const by (rule continuous_intros, simp add: cont_sigmoid)
    qed
    then have "continuous_on UNIV (\<lambda>x. \<Sum>k = 1..n+1. (-1)^(k+1) * fact (k - 1) * Stirling (n+1) k * (sigmoid x)^k)"
      by(rule continuous_on_sum, simp)
    then show "continuous_on UNIV (Nth_derivative n sigmoid)"
      using nth_derivative_sigmoid by presburger
  qed
  then show "\<exists>U. open U \<and> (\<forall>x\<in>U. C_k_on k sigmoid U)"
    by(rule_tac x=UNIV in exI, simp)
qed








    
   

















(* Logit (Inverse of Sigmoid)
The inverse of the sigmoid function, often referred to as the logit function, is
given by: \<sigma>−1(y) = ln(y/1−y), for 0 < y < 1. This transformation converts a
probability (sigmoid output) back into the corresponding log-odds. *)


definition logit :: "real \<Rightarrow> real" where
  "logit p = (if 0 < p \<and> p < 1 then ln (p / (1 - p)) else undefined)"


(*undefined = (SOME x. False)    Eps = name of constant SOME *)


(* 'a => 'b option
'b option = None | Some 'b  *)

(*
f : [0,infty) \<rightarrow> R

f x = (if x >= 0 then Some x else None)

*)


lemma sigmoid_logit_comp:
  "0 < p \<and> p < (1::real) \<Longrightarrow> sigmoid (logit p ) = p"
proof -
  assume "0 < p \<and> p < 1"
  then show "sigmoid (logit p ) = p"
    by (smt (verit, del_insts) divide_pos_pos exp_ln_iff logit_def real_shrink_Galois sigmoid_def)
qed


lemma logit_sigmoid_comp:
  "logit (sigmoid p ) = (p ::real)"
  by (smt (verit, best) sigmoid_less_1 sigmoid_logit_comp sigmoid_pos sigmoid_strictly_increasing)



 

definition softmax :: "real^'k \<Rightarrow> real^'k" where 
"softmax z = (\<chi> i. exp (z $ i) / (\<Sum> j\<in>UNIV. exp (z $ j)))"  






term tendsto 
term at_top

term eventually
thm open_real
thm at_top_le_at_infinity
term at_infinity


find_theorems norm

thm minus_divide_right



lemma tanh_sigmoid_relationship:
  "2 * sigmoid (2 * x) - 1 = tanh x"
proof -
  have "2 * sigmoid (2 * x) - 1 = 2 * (1 / (1 + exp (- (2 * x)))) - 1"
    by (simp add: inverse_eq_divide sigmoid_alt_def)
  also have "... = (2 / (1 + exp (- (2 * x)))) - 1"
    by simp
  also have "... = (2 - (1 + exp (- (2 * x)))) / (1 + exp (- (2 * x)))"
    by (smt (verit, ccfv_SIG) diff_divide_distrib div_self exp_gt_zero)
  also have "... = (exp x * (exp x - exp (-x))) / (exp x * (exp x + exp (-x)))"
    by (smt (z3) exp_not_eq_zero mult_divide_mult_cancel_left_if tanh_altdef tanh_real_altdef)
  also have "... = (exp x - exp (-x)) / (exp x + exp (-x))"
    using exp_gt_zero by simp
  also have "... = tanh x"
    by (simp add: tanh_altdef)
  finally show ?thesis.
qed

thm Limits.LIMSEQ_iff[where X = "f \<circ> real", where L = c]
thm sym[OF real_norm_def] (*For real numbers their norm is the abs func*)
thm real_norm_def




lemma tendsto_at_top_epsilon_def:
  "((\<lambda>x. f x) \<longlongrightarrow> c) at_top = (\<forall>(\<epsilon>::real) > 0. \<exists>N. \<forall>x \<ge> N. \<bar>f (x::real) - c\<bar> < \<epsilon>)"
  by (simp add: Zfun_def tendsto_Zfun_iff eventually_at_top_linorder)

lemma tendsto_at_bot_epsilon_def:
  "((\<lambda>x. f x) \<longlongrightarrow> c) at_bot = (\<forall>(\<epsilon>::real) > 0. \<exists>N. \<forall>x \<le> N. \<bar>f (x::real) - c\<bar> < \<epsilon>)"
    by (simp add: Zfun_def tendsto_Zfun_iff eventually_at_bot_linorder)




lemma tendsto_inf_at_top_epsilon_def:
  "((\<lambda>x. g (x:: real)) \<longlongrightarrow> \<infinity>) at_top = (\<forall> (\<epsilon> :: real) > 0. \<exists>N. \<forall>x \<ge> N. g x > \<epsilon>)"
  by (subst tendsto_PInfty', subst Filter.eventually_at_top_linorder, auto)
  
lemma tendsto_inf_at_bot_epsilon_def:
  "((\<lambda>x. g (x:: real)) \<longlongrightarrow> \<infinity>) at_bot = (\<forall> (\<epsilon> :: real) > 0. \<exists>N. \<forall>x \<le> N. g x > \<epsilon>)"
  by (subst tendsto_PInfty', subst Filter.eventually_at_bot_linorder, auto)



term "LIM f x. P f z :> at_top"


find_theorems "eventually ?P ?f = ?Q"

(*
thm tendsto_PInfty'[where F=at_top] Filter.eventually_at_top_linorder
*)

declare [[show_types]]



lemma tendsto_exp_neg_at_infinity: "((\<lambda>(x :: real). exp (-x)) \<longlongrightarrow> 0) at_top"
  by(subst tendsto_at_top_epsilon_def, metis abs_exp_cancel abs_minus_cancel abs_minus_commute 
     diff_0 exp_less_mono exp_ln_iff gt_ex minus_le_iff minus_less_iff order_le_less_trans)



thm filterlim_at_bot_mirror
thm exp_at_bot
thm tendsto_Zfun_iff  



lemma tendsto_divide_approaches_const:
  fixes f g :: "real \<Rightarrow> real"
  assumes f_lim:"((\<lambda>x. f (x::real)) \<longlongrightarrow> c) at_top"
      and g_lim: "((\<lambda>x. g (x::real)) \<longlongrightarrow> \<infinity>) at_top"
    shows "((\<lambda>x. f (x::real) / g x) \<longlongrightarrow> 0) at_top"
proof(subst tendsto_at_top_epsilon_def, clarify)
  fix \<epsilon> :: real
  assume \<epsilon>_pos: "0 < \<epsilon>"

  obtain M where M_def: "M = abs c + 1" and M_gt_0: "M > 0"
    by simp

  obtain N1 where N1_def: "\<forall>x\<ge>N1. abs (f x - c) < 1"
    using f_lim tendsto_at_top_epsilon_def zero_less_one by blast 

  have f_bound: "\<forall>x\<ge>N1. abs (f x) < M"
    using M_def N1_def by fastforce

  have M_over_\<epsilon>_gt_0: "M / \<epsilon> > 0"
    by (simp add: M_gt_0 \<epsilon>_pos)

  then obtain N2 where N2_def: "\<forall>x\<ge>N2. g x > M / \<epsilon>"
    using g_lim tendsto_inf_at_top_epsilon_def by blast

  obtain N where "N = max N1 N2" and N_ge_N1: "N \<ge> N1" and N_ge_N2: "N \<ge> N2"
    by auto 
    
  show "\<exists>N::real. \<forall>x\<ge>N. \<bar>f x / g x - 0\<bar> < \<epsilon>"
  proof(intro exI [where x=N], clarify)
    fix x :: real
    assume x_ge_N: " N \<le> x"

    have f_bound_x: "\<bar>f x\<bar> < M"
      using N_ge_N1 f_bound x_ge_N by auto

    have g_bound_x: "g x > M / \<epsilon>"
      using N2_def N_ge_N2 x_ge_N by auto 

    have "\<bar>f x / g x\<bar> = \<bar>f x\<bar> / \<bar>g x\<bar>"
      using abs_divide by blast
    also have "... < M /  \<bar>g x\<bar>"
      using M_over_\<epsilon>_gt_0 divide_strict_right_mono f_bound_x g_bound_x by force
    also have  "... < \<epsilon>"
      by (metis  M_over_\<epsilon>_gt_0 \<epsilon>_pos abs_real_def g_bound_x mult.commute order_less_irrefl order_less_trans pos_divide_less_eq)
    finally show "\<bar>f x / g x - 0\<bar> < \<epsilon>"
      by linarith
  qed      
qed

lemma tendsto_divide_approaches_const_at_bot:
  fixes f g :: "real \<Rightarrow> real"
  assumes f_lim: "((\<lambda>x. f (x::real)) \<longlongrightarrow> c) at_bot"
      and g_lim: "((\<lambda>x. g (x::real)) \<longlongrightarrow> \<infinity>) at_bot"
    shows "((\<lambda>x. f (x::real) / g x) \<longlongrightarrow> 0) at_bot"
proof(subst tendsto_at_bot_epsilon_def, clarify)
  fix \<epsilon> :: real
  assume \<epsilon>_pos: "0 < \<epsilon>"

  obtain M where M_def: "M = abs c + 1" and M_gt_0: "M > 0"
    by simp

  obtain N1 where N1_def: "\<forall>x\<le>N1. abs (f x - c) < 1"
    using f_lim tendsto_at_bot_epsilon_def zero_less_one by blast 

  have f_bound: "\<forall>x\<le>N1. abs (f x) < M"
    using M_def N1_def by fastforce

  have M_over_\<epsilon>_gt_0: "M / \<epsilon> > 0"
    by (simp add: M_gt_0 \<epsilon>_pos)

  then obtain N2 where N2_def: "\<forall>x\<le>N2. g x > M / \<epsilon>"
    using g_lim tendsto_inf_at_bot_epsilon_def by blast

  obtain N where "N = min N1 N2" and N_le_N1: "N \<le> N1" and N_le_N2: "N \<le> N2"
    by auto 
    
  show "\<exists>N::real. \<forall>x\<le>N. \<bar>f x / g x - 0\<bar> < \<epsilon>"
  proof(intro exI [where x=N], clarify)
    fix x :: real
    assume x_le_N: "x \<le> N"

    have f_bound_x: "\<bar>f x\<bar> < M"
      using N_le_N1 f_bound x_le_N by auto

    have g_bound_x: "g x > M / \<epsilon>"
      using N2_def N_le_N2 x_le_N by auto 

    have "\<bar>f x / g x\<bar> = \<bar>f x\<bar> / \<bar>g x\<bar>"
      using abs_divide by blast
    also have "... < M /  \<bar>g x\<bar>"
      using M_over_\<epsilon>_gt_0 divide_strict_right_mono f_bound_x g_bound_x by force
    also have  "... < \<epsilon>"
      by (metis  M_over_\<epsilon>_gt_0 \<epsilon>_pos abs_real_def g_bound_x mult.commute order_less_irrefl order_less_trans pos_divide_less_eq)
    finally show "\<bar>f x / g x - 0\<bar> < \<epsilon>"
      by linarith
  qed      
qed






(* Asymptotic Behaviour
As x \<rightarrow> +\<infinity>, the sigmoid function tends towards 1: lim_{x\<rightarrow>+\<infinity>} \<sigma>(x) = 1.
As x \<rightarrow> −\<infinity>, the sigmoid function tends towards 0: lim_{x\<rightarrow>-\<infinity>} \<sigma>(x) = 0. *)

(* Proof that the limit of the sigmoid function as x \<rightarrow> +\<infinity> is 1 *)
lemma lim_sigmoid_infinity: "((\<lambda>x. sigmoid x) \<longlongrightarrow> 1) at_top"
proof(subst tendsto_at_top_epsilon_def, clarify)
  fix \<epsilon> :: real
  assume \<epsilon>_pos: "0 < \<epsilon>"

  then obtain N where N_def: "\<forall>x \<ge> N. exp (- x) < \<epsilon>"
    by (metis dual_order.trans exp_le_cancel_iff exp_ln gt_ex le_minus_iff linorder_not_less)
    
  have "\<forall>x \<ge> N. \<bar>sigmoid x - 1\<bar> \<le> exp (-x)"
    by (smt(verit, best) divide_inverse exp_gt_zero exp_minus_inverse mult_le_cancel_left_pos sigmoid_alt_def sigmoid_def sigmoid_symmetry)

  then have "\<forall>x \<ge> N. \<bar>sigmoid x - 1\<bar> < \<epsilon>"
    by (meson N_def order_le_less_trans)
  then show "\<exists>N. \<forall>x \<ge> N. \<bar>sigmoid x - 1\<bar> < \<epsilon>"
    by blast
qed



(* Proof that the limit of the sigmoid function as x \<rightarrow> -\<infinity> is 0 *)
lemma lim_sigmoid_minus_infinity: "((\<lambda>x. sigmoid x) \<longlongrightarrow> 0) at_bot"
proof (subst tendsto_at_bot_epsilon_def, clarify)
  fix \<epsilon> :: real
  assume \<epsilon>_pos: "0 < \<epsilon>"
  
  have "\<forall>x \<le> ln \<epsilon>. \<bar>sigmoid x - 0\<bar> < \<epsilon>"
  proof(clarify)
    fix x :: real
    assume "x \<le> ln \<epsilon>"
    then have "-x \<ge> - ln \<epsilon>"
      by simp
    then have f1: "exp (- x) \<ge> exp (- ln \<epsilon>)"
      by simp
    have "exp (- ln \<epsilon>) = 1 / \<epsilon>"
      by (simp add: \<epsilon>_pos exp_minus inverse_eq_divide)
    then have "1 + exp (- x) \<ge>  1 / \<epsilon>"
      using f1 by auto
    then have "sigmoid x \<le> \<epsilon>"
       using \<epsilon>_pos le_imp_inverse_le sigmoid_alt_def by fastforce 
    then show "\<bar>sigmoid x - 0\<bar> < \<epsilon>"
      by (smt (verit, best) exp_ln exp_minus f1 inverse_inverse_eq sigmoid_alt_def sigmoid_pos)
  qed
  then show "\<exists>N::real. \<forall>x\<le>N. \<bar>sigmoid x - (0::real)\<bar> < \<epsilon>"
    by (rule exI[where x="ln \<epsilon>"])
qed



(* f''(x) > 0 on D then for all x and y in D \<longrightarrow> f'(x) < f'(y)*)




(*Values of Derivative*)

lemma sigmoid_positive_derivative:
"deriv sigmoid x > 0"
  by (simp add: sigmoid_derivative sigmoid_range)

lemma sigmoid_deriv_0:
"deriv sigmoid 0 = 1/4"
proof -
  have f1: "1 / (1 + 1) = sigmoid 0"
    by (simp add: sigmoid_def)
  then have f2: "\<forall>r. sigmoid 0 * (r + r) = r"
    by simp
  then have f3: "\<forall>n. sigmoid 0 * numeral (num.Bit0 n) = numeral n"
    by (metis (no_types) numeral_Bit0)
  have f4: "\<forall>r. sigmoid r * sigmoid (- r) = deriv sigmoid r"
    using sigmoid_derivative sigmoid_symmetry by presburger
  have "sigmoid 0 = 0 \<longrightarrow> deriv sigmoid 0 = 1 / 4"
    using f1 by force
  then show ?thesis
    using f4 f3 f2 by (metis (no_types) add.inverse_neutral divide_divide_eq_right nonzero_mult_div_cancel_left one_add_one zero_neq_numeral)
qed



(*Limits of Derivative *)


lemma sig_deriv_lim_at_top: "((\<lambda>x. deriv sigmoid x) \<longlongrightarrow> 0) at_top"
proof (subst tendsto_at_top_epsilon_def, clarify)
  fix \<epsilon> :: real
  assume \<epsilon>_pos: "0 < \<epsilon>"

  (* Using the fact that sigmoid(x) \<longrightarrow> 1 as x \<longrightarrow> \<infinity> *)
  obtain N where N_def: "\<forall>x \<ge> N. \<bar>sigmoid x - 1\<bar> < \<epsilon> / 2"
    using lim_sigmoid_infinity[unfolded tendsto_at_top_epsilon_def] \<epsilon>_pos
    by (metis  half_gt_zero)



  have deriv_bound: "\<forall>x \<ge> N. \<bar>deriv sigmoid x\<bar> \<le> \<bar>sigmoid x - 1\<bar>"
  proof (clarify)
    fix x
    assume "x \<ge> N"
    hence "\<bar>deriv sigmoid x\<bar> = \<bar>sigmoid x - 1 + 1\<bar> * \<bar>1 - sigmoid x\<bar>"
      by (simp add: abs_mult sigmoid_derivative)

    also have "... \<le> \<bar>sigmoid x - 1\<bar>"
      by (smt (verit) mult_cancel_right1 mult_right_mono sigmoid_range)
    finally show "\<bar>deriv sigmoid x\<bar> \<le> \<bar>sigmoid x - 1\<bar>".      
  qed

  have "\<forall>x \<ge> N. \<bar>deriv sigmoid x\<bar> < \<epsilon>"
  proof (clarify)
    fix x
    assume "x \<ge> N"
    hence "\<bar>deriv sigmoid x\<bar> \<le> \<bar>sigmoid x - 1\<bar>"
      using deriv_bound by simp
    also have "... < \<epsilon> / 2"
      using `x \<ge> N` N_def by simp
    also have "... < \<epsilon>"
      using \<epsilon>_pos by simp
    finally show "\<bar>deriv sigmoid x\<bar> < \<epsilon>" .
  qed

  then show "\<exists>N::real. \<forall>x\<ge>N. \<bar>deriv sigmoid x - (0::real)\<bar> < \<epsilon>"
    by (metis diff_zero)
qed

lemma sig_deriv_lim_at_bot: "((\<lambda>x. deriv sigmoid x) \<longlongrightarrow> 0) at_bot"
proof (subst tendsto_at_bot_epsilon_def, clarify)
  fix \<epsilon> :: real
  assume \<epsilon>_pos: "0 < \<epsilon>"

  (* Using the fact that sigmoid(x) \<longrightarrow> 0 as x \<longrightarrow> -\<infinity> *)
  obtain N where N_def: "\<forall>x \<le> N. \<bar>sigmoid x - 0\<bar> < \<epsilon> / 2"
    using lim_sigmoid_minus_infinity[unfolded tendsto_at_bot_epsilon_def] \<epsilon>_pos
    by (meson half_gt_zero)

  have deriv_bound: "\<forall>x \<le> N. \<bar>deriv sigmoid x\<bar> \<le> \<bar>sigmoid x - 0\<bar>"
  proof (clarify)
    fix x
    assume "x \<le> N"
    hence "\<bar>deriv sigmoid x\<bar> = \<bar>sigmoid x - 0 + 0\<bar> * \<bar>1 - sigmoid x\<bar>"
      by (simp add: abs_mult sigmoid_derivative)
    also have "... \<le> \<bar>sigmoid x - 0\<bar>"
      by (smt (verit, del_insts) mult_cancel_left2 mult_left_mono sigmoid_range)
    finally show "\<bar>deriv sigmoid x\<bar> \<le> \<bar>sigmoid x - 0\<bar>".
  qed

  have "\<forall>x \<le> N. \<bar>deriv sigmoid x\<bar> < \<epsilon>"
  proof (clarify)
    fix x
    assume "x \<le> N"
    hence "\<bar>deriv sigmoid x\<bar> \<le> \<bar>sigmoid x - 0\<bar>"
      using deriv_bound by simp
    also have "... < \<epsilon> / 2"
      using `x \<le> N` N_def by simp
    also have "... < \<epsilon>"
      using \<epsilon>_pos by simp
    finally show "\<bar>deriv sigmoid x\<bar> < \<epsilon>" .
  qed

  then show "\<exists>N::real. \<forall>x \<le> N. \<bar>deriv sigmoid x - (0::real)\<bar> < \<epsilon>"
    by (metis diff_zero)
qed











(*Values of second derivative *)

lemma second_derivative_positive_on:
  assumes "x < 0"
  shows "Nth_derivative 2 sigmoid x > 0"
proof -
  have "1 - 2 * sigmoid x > 0"
    using assms sigmoid_left_dom_range by force
  then show "Nth_derivative 2 sigmoid x > 0"
    by (simp add: sigmoid_range sigmoid_second_derivative)
qed


lemma second_derivative_negative_on:
  assumes "x > 0"
  shows "Nth_derivative 2 sigmoid x < 0"
proof -
  have "1 - 2 * sigmoid x < 0"
    by (smt (verit) assms sigmoid_strictly_increasing sigmoid_symmetry)
  then show "Nth_derivative 2 sigmoid x < 0"
    by (simp add: mult_pos_neg sigmoid_range sigmoid_second_derivative)
qed

lemma sigmoid_inflection_point:
  "Nth_derivative 2 sigmoid 0 = 0"
  by (simp add: sigmoid_alt_def sigmoid_second_derivative)


(*Monotonicity of derivative *)


(*
lemma deriv_sigmoid_monotonic_negatives:
  assumes "x1 < x2" "x2 < 0"
  shows "deriv sigmoid x1 < deriv sigmoid x2"
proof -
  have "deriv(deriv  sigmoid) x1 > 0"
    using assms second_derivative_alt_def second_derivative_positive_on by auto
  have "deriv(deriv  sigmoid) x2 > 0"
    using assms second_derivative_alt_def second_derivative_positive_on by auto
  show ?thesis



lemma deriv_sigmoid_monotonic_positives:
  assumes "x1 < x2" "0 < x1"
  shows "deriv sigmoid x1 > deriv sigmoid x2"

*)


thm continuous_on_eq_continuous_at[where s = "\<real>", where 'a1 = "real", where 'b = "real"]

thm continuous_on_eq_continuous_at
thm continuous_at_imp_continuous_on

(* Why can't I seem to show that (global) continuity implies local continuity?
lemma continuous_on_implies_isCont_real:
  "continuous_on \<real> f \<Longrightarrow> \<forall>(x::real). isCont f x"
*)


(*Continuity of Sigmoid and its Derivatives*)

(*
lemma sigmoid_is_continuous: "continuous_on \<real> sigmoid"
proof -
  have exp_contin: "continuous_on \<real> (\<lambda> (x::real). exp x)"
    by (rule continuous_on_exp, simp)
  then have exp_pls1_contin: "continuous_on \<real> (\<lambda> (x::real). 1 + exp x)"
    by (simp add: continuous_on_add)
  from exp_contin and exp_pls1_contin have "continuous_on \<real> (\<lambda> x::real. exp(x) / (1 + exp(x)))"
    by(rule continuous_on_divide, smt (verit, ccfv_threshold) not_exp_le_zero)
  then show ?thesis
    unfolding sigmoid_def by simp
qed
*)

(*Smooth : Every derivative exists and is continuous.
           Every derivative exists.  f^(n) is differentiable for every n
Analytic: A function is equal to its Taylor series about each point
*)

lemma sigmoid_is_continuous_at: "\<forall>x. isCont sigmoid x"
  by (simp add: field_differentiable_imp_continuous_at sigmoid_differentiable')

lemma sigmoid_is_continuous: "continuous_on \<real> sigmoid"
  by (simp add: continuous_at_imp_continuous_on sigmoid_is_continuous_at)


lemma deriv_sigmoid_continuous_at: "\<forall>x. isCont (\<lambda>y. sigmoid y * (1 - sigmoid y)) x"
  by (simp add: sigmoid_is_continuous_at)


(*  Is this what I want to state it as?  What about for the higher derivatives?
lemma sigmoid_is_contin_differentiable: "continuous_on \<real> (deriv sigmoid)"
*)





thm continuous_on_divide


(*Sigmoidal Definition and Properties of Such Functions*)

definition sigmoidal :: "(real \<Rightarrow> real) \<Rightarrow> bool" where
  "sigmoidal f \<equiv> ((\<lambda>x. f x) \<longlongrightarrow> 1) at_top \<and> ((\<lambda>x. f x) \<longlongrightarrow> 0) at_bot"


lemma sigmoid_is_sigmoidal: "sigmoidal sigmoid"
  unfolding sigmoidal_def
  by (simp add: lim_sigmoid_infinity lim_sigmoid_minus_infinity)




end