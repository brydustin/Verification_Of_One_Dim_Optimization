section \<open>Genuine Float Vectors: First-Principles Inner-Product Error Bounds\<close>

theory Float_Vector
  imports "IEEE_Floating_Point.IEEE_Properties"
begin

text \<open>
  Groundwork for the direct-float perceptron and gradient-descent
  developments. The IEEE AFP entry provides only the \<^emph>\<open>scalar\<close> type
  \<^typ>\<open>('e, 'f) float\<close>, and \<^typ>\<open>('e, 'f) float\<close> is not a real vector
  space, so \<open>inner\<close>, \<open>norm\<close> and \<open>(*\<^sub>R)\<close> are unavailable on float vectors.
  Here we model float vectors concretely as \<^emph>\<open>lists\<close> of floats and build
  the floating-point inner product as the genuine sequential accumulation
  of float \<open>+\<close> and \<open>\<times>\<close>.

  The error analysis is \<^emph>\<open>first-principles\<close>: each \<open>+\<close> and \<open>\<times>\<close>
  contributes one AFP rounding term \<^const>\<open>error\<close> (via \<open>float_add\<close> /
  \<open>float_mul\<close>), and we accumulate these by induction over the lists, in the
  style of Higham's running-error analysis of inner products. No single
  oracle hides the whole dot product; only the genuine per-operation IEEE
  rounding terms appear.
\<close>

type_synonym float64 = "(11, 52) IEEE.float"


subsection \<open>Sequential float summation\<close>

text \<open>Right-folded floating-point sum, \<open>x\<^sub>0 \<oplus> (x\<^sub>1 \<oplus> (\<dots> \<oplus> 0))\<close>.\<close>

fun fsum :: "('e, 'f) float list \<Rightarrow> ('e, 'f) float" where
  "fsum [] = 0"
| "fsum (a # as) = a + fsum as"

text \<open>
  No-overflow side condition for the whole fold: every partial sum is
  finite and every addition stays below the overflow threshold.
\<close>

fun fsum_ok :: "('e::len, 'f::len) float list \<Rightarrow> bool" where
  "fsum_ok [] = True"
| "fsum_ok (a # as) \<longleftrightarrow>
     is_finite a \<and> is_finite (fsum as)
     \<and> \<bar>valof a + valof (fsum as)\<bar> < threshold TYPE(('e, 'f) float)
     \<and> fsum_ok as"

text \<open>The running sum of per-addition rounding errors.\<close>

fun fsum_err :: "('e::len, 'f::len) float list \<Rightarrow> real" where
  "fsum_err [] = 0"
| "fsum_err (a # as) =
     \<bar>error TYPE(('e, 'f) float) (valof a + valof (fsum as))\<bar> + fsum_err as"

lemma fsum_err_nonneg: "0 \<le> fsum_err xs"
  by (induction xs) auto

lemma fsum_ok_finite: "fsum_ok xs \<Longrightarrow> is_finite (fsum xs)"
proof (induction xs)
  case Nil thus ?case by (simp add: is_finite_def)
next
  case (Cons a as) thus ?case by (auto simp: float_add(1))
qed

text \<open>
  \<^bold>\<open>First-principles summation error bound.\<close> Under the no-overflow side
  condition the floating-point sum differs from the exact real sum of the
  values by at most the accumulated per-addition rounding errors.
\<close>

lemma fsum_error:
  fixes xs :: "('e::len, 'f::len) float list"
  assumes "fsum_ok xs"
  shows "\<bar>valof (fsum xs) - (\<Sum>x\<leftarrow>xs. valof x)\<bar> \<le> fsum_err xs"
  using assms
proof (induction xs)
  case Nil
  show ?case by simp
next
  case (Cons a as)
  have fa: "is_finite a" and ffs: "is_finite (fsum as)"
    and thr: "\<bar>valof a + valof (fsum as)\<bar> < threshold TYPE(('e, 'f) float)"
    and ok: "fsum_ok as"
    using Cons.prems by auto
  have decomp: "valof (a + fsum as)
                  = valof a + valof (fsum as) + error TYPE(('e, 'f) float) (valof a + valof (fsum as))"
    using float_add(2)[OF fa ffs thr] .
  have IH: "\<bar>valof (fsum as) - (\<Sum>x\<leftarrow>as. valof x)\<bar> \<le> fsum_err as"
    using Cons.IH[OF ok] .
  have "\<bar>valof (fsum (a # as)) - (\<Sum>x\<leftarrow>(a # as). valof x)\<bar>
          = \<bar>(valof (fsum as) - (\<Sum>x\<leftarrow>as. valof x))
              + error TYPE(('e, 'f) float) (valof a + valof (fsum as))\<bar>"
    by (simp add: decomp)
  also have "\<dots> \<le> \<bar>valof (fsum as) - (\<Sum>x\<leftarrow>as. valof x)\<bar>
                  + \<bar>error TYPE(('e, 'f) float) (valof a + valof (fsum as))\<bar>"
    by (rule abs_triangle_ineq)
  also have "\<dots> \<le> fsum_err (a # as)" using IH by simp
  finally show ?case .
qed


subsection \<open>Sequential float inner product\<close>

text \<open>
  The float inner product multiplies componentwise (one rounded \<open>\<times>\<close> each)
  and accumulates sequentially (one rounded \<open>+\<close> each). \<open>fdot\<close> is the
  genuine floating-point value; \<open>rdot\<close> is the exact real inner product of
  the values. Defining them by mutual structural recursion keeps the error
  induction clean.
\<close>

fun fdot :: "('e, 'f) float list \<Rightarrow> ('e, 'f) float list \<Rightarrow> ('e, 'f) float" where
  "fdot [] ys = 0"
| "fdot (x # xs) [] = 0"
| "fdot (x # xs) (y # ys) = x * y + fdot xs ys"

fun rdot :: "('e, 'f) float list \<Rightarrow> ('e, 'f) float list \<Rightarrow> real" where
  "rdot [] ys = 0"
| "rdot (x # xs) [] = 0"
| "rdot (x # xs) (y # ys) = valof x * valof y + rdot xs ys"

text \<open>No-overflow side condition for the inner product.\<close>

fun fdot_ok :: "('e::len, 'f::len) float list \<Rightarrow> ('e, 'f) float list \<Rightarrow> bool" where
  "fdot_ok [] ys = True"
| "fdot_ok (x # xs) [] = True"
| "fdot_ok (x # xs) (y # ys) \<longleftrightarrow>
     is_finite x \<and> is_finite y
     \<and> \<bar>valof x * valof y\<bar> < threshold TYPE(('e, 'f) float)
     \<and> is_finite (fdot xs ys)
     \<and> \<bar>valof (x * y) + valof (fdot xs ys)\<bar> < threshold TYPE(('e, 'f) float)
     \<and> fdot_ok xs ys"

text \<open>Accumulated per-multiplication and per-addition rounding errors.\<close>

fun fdot_err :: "('e::len, 'f::len) float list \<Rightarrow> ('e, 'f) float list \<Rightarrow> real" where
  "fdot_err [] ys = 0"
| "fdot_err (x # xs) [] = 0"
| "fdot_err (x # xs) (y # ys) =
     \<bar>error TYPE(('e, 'f) float) (valof x * valof y)\<bar>
     + \<bar>error TYPE(('e, 'f) float) (valof (x * y) + valof (fdot xs ys))\<bar>
     + fdot_err xs ys"

lemma fdot_err_nonneg: "0 \<le> fdot_err xs ys"
  by (induction xs ys rule: fdot_err.induct) auto

lemma fdot_ok_finite:
  fixes xs ys :: "('e::len, 'f::len) float list"
  assumes "fdot_ok xs ys"
  shows "is_finite (fdot xs ys)"
  using assms
proof (induction xs ys rule: fdot.induct)
  case (1 ys) thus ?case by (simp add: is_finite_def)
next
  case (2 x xs) thus ?case by (simp add: is_finite_def)
next
  case (3 x xs y ys)
  have fx: "is_finite x" and fy: "is_finite y"
    and thr_mul: "\<bar>valof x * valof y\<bar> < threshold TYPE(('e, 'f) float)"
    and ffd: "is_finite (fdot xs ys)"
    and thr_add: "\<bar>valof (x * y) + valof (fdot xs ys)\<bar> < threshold TYPE(('e, 'f) float)"
    using "3.prems" by auto
  have fxy: "is_finite (x * y)" using float_mul(1)[OF fx fy thr_mul] .
  show ?case using float_add(1)[OF fxy ffd thr_add] by simp
qed

text \<open>
  \<^bold>\<open>First-principles inner-product error bound.\<close> Under the no-overflow side
  condition, the genuine floating-point inner product differs from the
  exact real inner product by at most the accumulated per-multiplication
  and per-addition rounding errors.
\<close>

theorem fdot_error:
  fixes xs ys :: "('e::len, 'f::len) float list"
  assumes "fdot_ok xs ys"
  shows "\<bar>valof (fdot xs ys) - rdot xs ys\<bar> \<le> fdot_err xs ys"
  using assms
proof (induction xs ys rule: fdot.induct)
  case (1 ys)
  show ?case by simp
next
  case (2 x xs)
  show ?case by simp
next
  case (3 x xs y ys)
  have fx: "is_finite x" and fy: "is_finite y"
    and thr_mul: "\<bar>valof x * valof y\<bar> < threshold TYPE(('e, 'f) float)"
    and ffd: "is_finite (fdot xs ys)"
    and thr_add: "\<bar>valof (x * y) + valof (fdot xs ys)\<bar> < threshold TYPE(('e, 'f) float)"
    and ok: "fdot_ok xs ys"
    using "3.prems" by auto
  have fxy: "is_finite (x * y)" using float_mul(1)[OF fx fy thr_mul] .
  have emul: "valof (x * y) = valof x * valof y + error TYPE(('e, 'f) float) (valof x * valof y)"
    using float_mul(2)[OF fx fy thr_mul] .
  have eadd: "valof ((x * y) + fdot xs ys)
                = valof (x * y) + valof (fdot xs ys)
                  + error TYPE(('e, 'f) float) (valof (x * y) + valof (fdot xs ys))"
    using float_add(2)[OF fxy ffd thr_add] .
  have IH: "\<bar>valof (fdot xs ys) - rdot xs ys\<bar> \<le> fdot_err xs ys"
    using "3.IH"[OF ok] .
  have val_eq: "valof (fdot (x # xs) (y # ys)) - rdot (x # xs) (y # ys)
        = (valof (fdot xs ys) - rdot xs ys)
          + error TYPE(('e, 'f) float) (valof x * valof y)
          + error TYPE(('e, 'f) float) (valof (x * y) + valof (fdot xs ys))"
    using emul eadd by (simp add: algebra_simps)
  have "\<bar>valof (fdot (x # xs) (y # ys)) - rdot (x # xs) (y # ys)\<bar>
          \<le> \<bar>valof (fdot xs ys) - rdot xs ys\<bar>
            + \<bar>error TYPE(('e, 'f) float) (valof x * valof y)\<bar>
            + \<bar>error TYPE(('e, 'f) float) (valof (x * y) + valof (fdot xs ys))\<bar>"
    using val_eq by (smt (verit))
  also have "\<dots> \<le> fdot_err (x # xs) (y # ys)" using IH by simp
  finally show ?case .
qed


subsection \<open>Componentwise float vector operations\<close>

text \<open>
  Scalar-times-vector and vector subtraction, used by the gradient-descent
  update \<open>x \<ominus> (\<alpha> \<odot> grad x)\<close>. \<open>valofL\<close> reads a float vector as its
  real-valued shadow (componentwise \<open>valof\<close>).
\<close>

definition valofL :: "('e, 'f) float list \<Rightarrow> real list" where
  "valofL xs = map valof xs"

definition fscaleR :: "('e, 'f) float \<Rightarrow> ('e, 'f) float list \<Rightarrow> ('e, 'f) float list" where
  "fscaleR a xs = map (\<lambda>x. a * x) xs"

fun fvsub :: "('e, 'f) float list \<Rightarrow> ('e, 'f) float list \<Rightarrow> ('e, 'f) float list" where
  "fvsub [] ys = []"
| "fvsub (x # xs) [] = []"
| "fvsub (x # xs) (y # ys) = (x - y) # fvsub xs ys"

fun fvadd :: "('e, 'f) float list \<Rightarrow> ('e, 'f) float list \<Rightarrow> ('e, 'f) float list" where
  "fvadd [] ys = []"
| "fvadd (x # xs) [] = []"
| "fvadd (x # xs) (y # ys) = (x + y) # fvadd xs ys"

lemma length_fscaleR [simp]: "length (fscaleR a xs) = length xs"
  by (simp add: fscaleR_def)

lemma length_fvsub [simp]: "length (fvsub xs ys) = min (length xs) (length ys)"
  by (induction xs ys rule: fvsub.induct) auto

lemma length_fvadd [simp]: "length (fvadd xs ys) = min (length xs) (length ys)"
  by (induction xs ys rule: fvadd.induct) auto

lemma length_valofL [simp]: "length (valofL xs) = length xs"
  by (simp add: valofL_def)

end
