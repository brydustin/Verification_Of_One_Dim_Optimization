section \<open>Cholesky factorisation of an SPD matrix: the classical \<open>A = L L\<^sup>T\<close> (VCG vs Lammich), and a square-root-free, executable \<open>A = L D L\<^sup>T\<close>\<close>

theory Cholesky_Comparison
  imports "ITree_Numeric_VCG.ITree_Numeric_VCG" "Refine_Monadic.Refine_Monadic"
begin

text \<open>This is the third comparison subject (after bisection/perceptron/gradient descent), chosen
  for its genuinely nested control flow: the column Cholesky algorithm has an outer loop over
  columns, an inner loop over the rows beneath the diagonal, and an innermost dot-product
  accumulation loop, with two structurally distinct inner bodies (the diagonal square-root branch
  and the below-diagonal division branch).  Matrices are modelled as nat-indexed functions
  \<^typ>\<open>nat \<Rightarrow> nat \<Rightarrow> real\<close> with an explicit dimension \<^term>\<open>n\<close>, so loops use ordinary nat
  counters and there is no \<open>mod_type\<close> indexing seam.\<close>

section \<open>Shared mathematics: the Cholesky correctness identity\<close>

definition symmetric_upto :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> bool" where
  "symmetric_upto n A \<longleftrightarrow> (\<forall>i<n. \<forall>j<n. A i j = A j i)"

definition lower_upto :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> bool" where
  "lower_upto n L \<longleftrightarrow> (\<forall>i<n. \<forall>j<n. i < j \<longrightarrow> L i j = 0)"

text \<open>\<open>chol_recur\<close> is the family of defining equations the algorithm establishes: for every
  entry on or below the diagonal, the dot product of rows \<open>i\<close> and \<open>j\<close> truncated at column \<open>j\<close>
  equals \<open>A i j\<close>.  (Diagonal \<open>i = j\<close>: \<open>\<Sum>k\<le>j. (L j k)\<^sup>2 = A j j\<close>; below-diagonal \<open>i > j\<close>:
  \<open>(\<Sum>k<j. L i k * L j k) + L i j * L j j = A i j\<close>.)\<close>

definition chol_recur :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> bool" where
  "chol_recur n A L \<longleftrightarrow> (\<forall>i<n. \<forall>j<n. j \<le> i \<longrightarrow> (\<Sum>k\<le>j. L i k * L j k) = A i j)"

text \<open>Correctness: if \<open>L\<close> is lower-triangular and satisfies the Cholesky defining equations for a
  symmetric \<open>A\<close>, then \<open>L L\<^sup>T = A\<close> entrywise.  The proof is a dropped-zero-terms sum split (the
  upper part of \<open>L\<close> vanishes) followed by symmetry for the entries above the diagonal --- no
  induction and no appeal to positivity (that is needed only to make the algorithm's divisions
  and square roots well defined).\<close>

lemma cholesky_LLt:
  assumes sym: "symmetric_upto n A" and low: "lower_upto n L" and rec: "chol_recur n A L"
    and i: "i < n" and j: "j < n"
  shows "(\<Sum>k<n. L i k * L j k) = A i j"
proof -
  have main: "\<And>a c. a < n \<Longrightarrow> c < n \<Longrightarrow> c \<le> a \<Longrightarrow> (\<Sum>k<n. L a k * L c k) = A a c"
  proof -
    fix a c assume a: "a < n" and c: "c < n" and ca: "c \<le> a"
    have "(\<Sum>k<n. L a k * L c k) = (\<Sum>k\<le>c. L a k * L c k)"
    proof (rule sum.mono_neutral_right)
      show "finite {..<n}" by simp
      show "{..c} \<subseteq> {..<n}" using c by auto
      show "\<forall>k\<in>{..<n} - {..c}. L a k * L c k = 0"
        using low c by (auto simp: lower_upto_def)
    qed
    also have "\<dots> = A a c" using rec a c ca by (simp add: chol_recur_def)
    finally show "(\<Sum>k<n. L a k * L c k) = A a c" .
  qed
  show ?thesis
  proof (cases "j \<le> i")
    case True
    show ?thesis using main[OF i j True] .
  next
    case False
    hence ij: "i \<le> j" by simp
    have "(\<Sum>k<n. L i k * L j k) = (\<Sum>k<n. L j k * L i k)" by (simp add: mult.commute)
    also have "\<dots> = A j i" using main[OF j i ij] .
    also have "\<dots> = A i j" using sym i j by (simp add: symmetric_upto_def)
    finally show ?thesis .
  qed
qed

section \<open>Shared computational spec: the Cholesky factor exists\<close>

text \<open>\<open>cholmat A m\<close> is the lower-triangular factor with its first \<open>m\<close> columns filled in by the
  column-Cholesky recurrence (columns \<open>\<ge> m\<close> are still zero).  It is primitive-recursive on the
  column count, so the dot-product sums refer to the already-built \<open>cholmat A m\<close> rather than to a
  self-call under the sum.  This is the reference both paradigms compute.\<close>

fun cholmat :: "(nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "cholmat A 0 = (\<lambda>i j. 0)"
| "cholmat A (Suc m) =
     (\<lambda>i j. if j = m
            then (if m < i
                  then (A i m - (\<Sum>k<m. cholmat A m i k * cholmat A m m k))
                        / sqrt (A m m - (\<Sum>k<m. (cholmat A m m k)\<^sup>2))
                  else if i = m
                  then sqrt (A m m - (\<Sum>k<m. (cholmat A m m k)\<^sup>2))
                  else 0)
            else cholmat A m i j)"

text \<open>The Cholesky-safety side condition: every radicand stays strictly positive (so each
  diagonal \<open>sqrt\<close> is real and nonzero).  Under SPD this holds; proving \<open>SPD A \<Longrightarrow> chol_safe A n\<close>
  (Sylvester / Schur-complement) is the remaining piece of mathematics.\<close>

definition chol_safe :: "(nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> bool" where
  "chol_safe A n \<longleftrightarrow> (\<forall>m<n. 0 < A m m - (\<Sum>k<m. (cholmat A m m k)\<^sup>2))"

text \<open>Columns below the current count are frozen once built.\<close>

lemma cholmat_mono: "k < m \<Longrightarrow> m \<le> m' \<Longrightarrow> cholmat A m' i k = cholmat A m i k"
proof (induction m')
  case 0 thus ?case by simp
next
  case (Suc m')
  show ?case
  proof (cases "m = Suc m'")
    case True thus ?thesis by simp
  next
    case False
    with Suc.prems have mm': "m \<le> m'" by simp
    with \<open>k < m\<close> have "k \<noteq> m'" by simp
    hence "cholmat A (Suc m') i k = cholmat A m' i k" by simp
    also have "\<dots> = cholmat A m i k" using Suc.IH \<open>k < m\<close> mm' by simp
    finally show ?thesis .
  qed
qed

lemma cholmat_lower: "lower_upto n (cholmat A n)"
proof -
  have "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow> i < j \<Longrightarrow> cholmat A n i j = 0"
  proof -
    fix i j assume "i < n" "j < n" "i < j"
    have "cholmat A n i j = cholmat A (Suc j) i j"
      using cholmat_mono[of j "Suc j" n A i] \<open>j < n\<close> by simp
    also have "\<dots> = 0" using \<open>i < j\<close> by simp
    finally show "cholmat A n i j = 0" .
  qed
  thus ?thesis by (simp add: lower_upto_def)
qed

text \<open>The factor satisfies the Cholesky defining equations.  The radicand at column \<open>j\<close> is
  positive by \<open>chol_safe\<close>, so the diagonal \<open>sqrt\<close> is nonzero and the divisions are exact; the
  diagonal and below-diagonal cases then each telescope to \<open>A i j\<close>.\<close>

lemma cholmat_recur:
  assumes safe: "chol_safe A n"
  shows "chol_recur n A (cholmat A n)"
proof -
  have "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow> j \<le> i
        \<Longrightarrow> (\<Sum>k\<le>j. cholmat A n i k * cholmat A n j k) = A i j"
  proof -
    fix i j assume i: "i < n" and j: "j < n" and ji: "j \<le> i"
    let ?r = "A j j - (\<Sum>k<j. (cholmat A j j k)\<^sup>2)"
    have rpos: "0 < ?r" using safe j by (auto simp: chol_safe_def)
    have rsq: "sqrt ?r * sqrt ?r = ?r" using rpos by (simp add: real_sqrt_mult_self)
    have rne: "sqrt ?r \<noteq> 0" using rpos by simp
    have stab: "\<And>a k. k \<le> j \<Longrightarrow> cholmat A n a k = cholmat A (Suc j) a k"
    proof -
      fix a k assume "k \<le> j" hence "k < Suc j" by simp
      thus "cholmat A n a k = cholmat A (Suc j) a k"
        using cholmat_mono[of k "Suc j" n A a] j by simp
    qed
    have colj: "\<And>a k. k < j \<Longrightarrow> cholmat A (Suc j) a k = cholmat A j a k" by simp
    have djj: "cholmat A (Suc j) j j = sqrt ?r" by simp
    have sum_eq: "(\<Sum>k\<le>j. cholmat A n i k * cholmat A n j k)
                = (\<Sum>k<j. cholmat A j i k * cholmat A j j k) + cholmat A (Suc j) i j * sqrt ?r"
    proof -
      have "(\<Sum>k\<le>j. cholmat A n i k * cholmat A n j k)
          = (\<Sum>k\<le>j. cholmat A (Suc j) i k * cholmat A (Suc j) j k)"
        by (rule sum.cong[OF refl]) (auto simp: stab)
      also have "\<dots> = (\<Sum>k<j. cholmat A (Suc j) i k * cholmat A (Suc j) j k)
                       + cholmat A (Suc j) i j * cholmat A (Suc j) j j"
        by (simp add: lessThan_Suc_atMost[symmetric] sum.lessThan_Suc)
      also have "\<dots> = (\<Sum>k<j. cholmat A j i k * cholmat A j j k) + cholmat A (Suc j) i j * sqrt ?r"
        by (simp add: colj djj)
      finally show ?thesis .
    qed
    show "(\<Sum>k\<le>j. cholmat A n i k * cholmat A n j k) = A i j"
    proof (cases "j < i")
      case True
      have "cholmat A (Suc j) i j
            = (A i j - (\<Sum>k<j. cholmat A j i k * cholmat A j j k)) / sqrt ?r"
        using True by simp
      hence "cholmat A (Suc j) i j * sqrt ?r = A i j - (\<Sum>k<j. cholmat A j i k * cholmat A j j k)"
        using rne by simp
      thus ?thesis using sum_eq by simp
    next
      case False
      hence eqij: "i = j" using ji by simp
      have "cholmat A (Suc j) i j * sqrt ?r = ?r" using eqij djj rsq by simp
      moreover have "(\<Sum>k<j. cholmat A j i k * cholmat A j j k) = (\<Sum>k<j. (cholmat A j j k)\<^sup>2)"
        using eqij by (simp add: power2_eq_square)
      ultimately show ?thesis using sum_eq eqij by simp
    qed
  qed
  thus ?thesis by (simp add: chol_recur_def)
qed

text \<open>Hence the reference factor really is a Cholesky factor: \<open>L L\<^sup>T = A\<close> entrywise.\<close>

theorem cholmat_factorises:
  assumes "symmetric_upto n A" "chol_safe A n" "i < n" "j < n"
  shows "(\<Sum>k<n. cholmat A n i k * cholmat A n j k) = A i j"
  by (rule cholesky_LLt[OF assms(1) cholmat_lower cholmat_recur[OF assms(2)] assms(3,4)])

section \<open>Paradigm B: Lammich's Refinement Framework (\<open>nres\<close>)\<close>

text \<open>How one column extends the factor (read straight off \<^const>\<open>cholmat\<close>'s recursion):
  columns other than \<open>j\<close> are untouched, and the new column \<open>j\<close> has the diagonal square root
  and the below-diagonal quotients.\<close>

lemma cholmat_Suc_other: "j' \<noteq> j \<Longrightarrow> cholmat A (Suc j) i' j' = cholmat A j i' j'" by simp

lemma cholmat_Suc_diag: "cholmat A (Suc j) j j = sqrt (A j j - (\<Sum>k<j. (cholmat A j j k)\<^sup>2))" by simp

lemma cholmat_Suc_offdiag:
  "j < i \<Longrightarrow> cholmat A (Suc j) i j
     = (A i j - (\<Sum>k<j. cholmat A j i k * cholmat A j j k))
        / sqrt (A j j - (\<Sum>k<j. (cholmat A j j k)\<^sup>2))" by simp

text \<open>Entries in a column at or beyond the current count are still zero.\<close>
lemma cholmat_col_ge: "m \<le> k \<Longrightarrow> cholmat A m i k = 0"
proof (induction m)
  case 0 thus ?case by simp
next
  case (Suc m)
  hence "m \<le> k" "k \<noteq> m" by auto
  thus ?case using Suc.IH by simp
qed

definition agree :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> bool" where
  "agree n L M \<longleftrightarrow> (\<forall>i<n. \<forall>j<n. L i j = M i j)"

text \<open>Inner loop: fill column \<open>j\<close> below the (already-set) diagonal, one row at a time.  This is the
  innermost of the two nested loops --- the feature missing from the earlier single-loop examples.\<close>

definition chol_column ::
  "(nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> real) nres" where
  "chol_column A n j d L \<equiv>
     do { (L', _) \<leftarrow> WHILET (\<lambda>(L, i). i < n)
                      (\<lambda>(L, i). RETURN (L(i := (L i)(j := (A i j - (\<Sum>k<j. L i k * L j k)) / d)), Suc i))
                      (L, Suc j);
          RETURN L' }"

text \<open>Outer loop: process the columns left to right.  The square root is guarded by an
  \<^const>\<open>ASSERT\<close>: the refinement-framework specification is ``returns a Cholesky factor, or fails'',
  and the \<^const>\<open>ASSERT\<close> is discharged exactly from \<^const>\<open>chol_safe\<close> (so under SPD it never
  fails).  This is the paradigm-distinguishing idiom: the partial \<open>sqrt\<close>'s domain condition is
  localised at the point of use, rather than threaded through the loop invariants.\<close>

text \<open>Inner-loop invariant preservation (pure): writing the recurrence value into row \<open>i\<close> of
  column \<open>j\<close> extends the ``matches \<^const>\<open>cholmat\<close>'' invariant by one row.\<close>

lemma chol_column_inv_step:
  assumes inv1: "\<And>i' j'. i'<n \<Longrightarrow> j'<n \<Longrightarrow> i'<i \<or> j'\<noteq>j \<Longrightarrow> L' i' j' = cholmat A (Suc j) i' j'"
    and inv2: "\<And>i'. i'<n \<Longrightarrow> i \<le> i' \<Longrightarrow> L' i' j = cholmat A j i' j"
    and ji: "Suc j \<le> i" and iin: "i < n" and jn: "Suc j \<le> n"
    and dd: "d = cholmat A (Suc j) j j"
  shows "(\<forall>i'<n. \<forall>j'<n. (i'<Suc i \<or> j'\<noteq>j) \<longrightarrow>
            (L'(i := (L' i)(j := (A i j - (\<Sum>k<j. L' i k * L' j k)) / d))) i' j' = cholmat A (Suc j) i' j')
       \<and> (\<forall>i'<n. Suc i \<le> i' \<longrightarrow>
            (L'(i := (L' i)(j := (A i j - (\<Sum>k<j. L' i k * L' j k)) / d))) i' j = cholmat A j i' j)"
proof -
  let ?v = "(A i j - (\<Sum>k<j. L' i k * L' j k)) / d"
  let ?L = "L'(i := (L' i)(j := ?v))"
  have ji': "j < i" using ji by simp
  have crux: "?v = cholmat A (Suc j) i j"
  proof -
    have "(\<Sum>k<j. L' i k * L' j k) = (\<Sum>k<j. cholmat A j i k * cholmat A j j k)"
    proof (rule sum.cong[OF refl])
      fix k assume "k \<in> {..<j}" hence kj: "k < j" by simp
      hence kn: "k < n" using jn by simp
      have "L' i k = cholmat A j i k"
        using inv1[OF iin kn] kj cholmat_Suc_other[of k j A i] by simp
      moreover have "L' j k = cholmat A j j k"
        using inv1[of j k] jn kn kj cholmat_Suc_other[of k j A j] by simp
      ultimately show "L' i k * L' j k = cholmat A j i k * cholmat A j j k" by simp
    qed
    thus ?thesis using dd ji' by simp
  qed
  have c1: "\<forall>i'<n. \<forall>j'<n. (i'<Suc i \<or> j'\<noteq>j) \<longrightarrow> ?L i' j' = cholmat A (Suc j) i' j'"
  proof (intro allI impI)
    fix i' j' assume i': "i'<n" and j': "j'<n" and ante: "i'<Suc i \<or> j'\<noteq>j"
    show "?L i' j' = cholmat A (Suc j) i' j'"
    proof (cases "i'=i \<and> j'=j")
      case True thus ?thesis using crux by simp
    next
      case False
      hence "?L i' j' = L' i' j'" by auto
      moreover have "i'<i \<or> j'\<noteq>j" using False ante by auto
      ultimately show ?thesis using inv1[OF i' j'] by simp
    qed
  qed
  have c2: "\<forall>i'<n. Suc i \<le> i' \<longrightarrow> ?L i' j = cholmat A j i' j"
  proof (intro allI impI)
    fix i' assume i': "i'<n" and "Suc i \<le> i'"
    hence "i' \<noteq> i" by simp
    hence "?L i' j = L' i' j" by simp
    also have "\<dots> = cholmat A j i' j" using inv2[OF i'] \<open>Suc i \<le> i'\<close> by simp
    finally show "?L i' j = cholmat A j i' j" .
  qed
  from c1 c2 show ?thesis by blast
qed

definition chol_inner_inv :: "(nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> real) \<times> nat \<Rightarrow> bool" where
  "chol_inner_inv A n j \<equiv> (\<lambda>(L', i). Suc j \<le> i \<and> i \<le> n
       \<and> (\<forall>i'<n. \<forall>j'<n. (i'<i \<or> j'\<noteq>j) \<longrightarrow> L' i' j' = cholmat A (Suc j) i' j')
       \<and> (\<forall>i'<n. i \<le> i' \<longrightarrow> L' i' j = cholmat A j i' j))"

text \<open>The inner loop computes column \<open>j\<close>: starting from a factor that already agrees with
  \<^term>\<open>cholmat A (Suc j)\<close> on the diagonal and earlier columns, it fills the rest of column \<open>j\<close>.\<close>

lemma chol_column_correct:
  assumes pre1: "\<And>i' j'. i'<n \<Longrightarrow> j'<n \<Longrightarrow> i' < Suc j \<or> j' \<noteq> j \<Longrightarrow> L i' j' = cholmat A (Suc j) i' j'"
    and pre2: "\<And>i'. i'<n \<Longrightarrow> Suc j \<le> i' \<Longrightarrow> L i' j = cholmat A j i' j"
    and jn: "Suc j \<le> n" and dd: "d = cholmat A (Suc j) j j"
  shows "chol_column A n j d L \<le> SPEC (\<lambda>L'. agree n L' (cholmat A (Suc j)))"
  unfolding chol_column_def
  apply (refine_vcg WHILET_rule[where I="chol_inner_inv A n j"
            and R="Wellfounded.measure (\<lambda>(L', i). n - i)"])
  subgoal by simp
  subgoal using jn pre1 pre2 by (auto simp: chol_inner_inv_def)
  \<comment> \<open>step: invariant preserved\<close>
  subgoal premises p for s a b
  proof -
    from p have cc: "chol_inner_inv A n j (a, b)" and guard: "b < n" by auto
    from cc have inv1: "\<And>i' j'. i'<n \<Longrightarrow> j'<n \<Longrightarrow> i'<b \<or> j'\<noteq>j \<Longrightarrow> a i' j' = cholmat A (Suc j) i' j'"
      and inv2: "\<And>i'. i'<n \<Longrightarrow> b \<le> i' \<Longrightarrow> a i' j = cholmat A j i' j"
      and Ib: "Suc j \<le> b" by (auto simp: chol_inner_inv_def)
    have "(\<forall>i'<n. \<forall>j'<n. (i'<Suc b \<or> j'\<noteq>j) \<longrightarrow>
            (a(b := (a b)(j := (A b j - (\<Sum>k<j. a b k * a j k)) / d))) i' j' = cholmat A (Suc j) i' j')
        \<and> (\<forall>i'<n. Suc b \<le> i' \<longrightarrow>
            (a(b := (a b)(j := (A b j - (\<Sum>k<j. a b k * a j k)) / d))) i' j = cholmat A j i' j)"
      using chol_column_inv_step[OF inv1 inv2 Ib guard jn dd] .
    thus "chol_inner_inv A n j
            (a(b := (a b)(j := (A b j - (\<Sum>k<j. a b k * a j k)) / d)), Suc b)"
      using Ib guard by (auto simp: chol_inner_inv_def)
  qed
  \<comment> \<open>step: measure decreases\<close>
  subgoal premises p for s a b using p by (auto simp: in_measure)
  \<comment> \<open>exit: invariant at \<open>i = n\<close> gives agreement\<close>
  subgoal premises p for s a b
  proof -
    from p have cc: "chol_inner_inv A n j (a, b)" and nb: "\<not> b < n" by auto
    from cc have inv1: "\<And>i' j'. i'<n \<Longrightarrow> j'<n \<Longrightarrow> i'<b \<or> j'\<noteq>j \<Longrightarrow> a i' j' = cholmat A (Suc j) i' j'"
      and bn: "b \<le> n" by (auto simp: chol_inner_inv_def)
    have "b = n" using bn nb by simp
    thus "agree n a (cholmat A (Suc j))" using inv1 by (auto simp: agree_def)
  qed
  done

definition R_cholesky ::
  "(nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> real) nres" where
  "R_cholesky A n \<equiv>
     do { (L, _) \<leftarrow> WHILET (\<lambda>(L, j). j < n)
                     (\<lambda>(L, j). do {
                        ASSERT (0 < A j j - (\<Sum>k<j. (L j k)\<^sup>2));
                        let d = sqrt (A j j - (\<Sum>k<j. (L j k)\<^sup>2));
                        let L = L(j := (L j)(j := d));
                        L \<leftarrow> chol_column A n j d L;
                        RETURN (L, Suc j)
                      })
                     ((\<lambda>i j. 0), 0);
          RETURN L }"

definition chol_outer_inv :: "(nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> real) \<times> nat \<Rightarrow> bool" where
  "chol_outer_inv A n \<equiv> (\<lambda>(L, j). j \<le> n \<and> agree n L (cholmat A j))"

theorem R_cholesky_correct:
  assumes safe: "chol_safe A n" and sym: "symmetric_upto n A"
  shows "R_cholesky A n \<le> SPEC (\<lambda>L. \<forall>i<n. \<forall>j<n. (\<Sum>k<n. L i k * L j k) = A i j)"
  unfolding R_cholesky_def
  apply (refine_vcg WHILET_rule[where I="chol_outer_inv A n"
            and R="Wellfounded.measure (\<lambda>(L, j). n - j)"]
         chol_column_correct)
  subgoal by simp
  subgoal by (simp add: chol_outer_inv_def agree_def)
  \<comment> \<open>ASSERT: the square-root argument is positive (from \<open>chol_safe\<close>)\<close>
  subgoal premises p for s a b
  proof -
    from p have cc: "agree n a (cholmat A b)" and guard: "b < n" by (auto simp: chol_outer_inv_def)
    have "(\<Sum>k<b. (a b k)\<^sup>2) = (\<Sum>k<b. (cholmat A b b k)\<^sup>2)"
      using cc guard by (intro sum.cong refl) (auto simp: agree_def)
    moreover have "0 < A b b - (\<Sum>k<b. (cholmat A b b k)\<^sup>2)"
      using safe guard by (auto simp: chol_safe_def)
    ultimately show "0 < A b b - (\<Sum>k<b. (a b k)\<^sup>2)" by simp
  qed
  \<comment> \<open>chol_column precondition pre1\<close>
  subgoal premises p for s a b i' j'
  proof -
    from p have cc: "agree n a (cholmat A b)" and guard: "b < n"
      and i'n: "i' < n" and j'n: "j' < n" and ante: "i' < Suc b \<or> j' \<noteq> b"
      by (auto simp: chol_outer_inv_def)
    have aval: "\<And>i k. i < n \<Longrightarrow> k < n \<Longrightarrow> a i k = cholmat A b i k"
      using cc by (auto simp: agree_def)
    have seq: "(\<Sum>k<b. (a b k)\<^sup>2) = (\<Sum>k<b. (cholmat A b b k)\<^sup>2)"
      using aval guard by (intro sum.cong refl) auto
    show "(a(b := (a b)(b := sqrt (A b b - (\<Sum>k<b. (a b k)\<^sup>2))))) i' j' = cholmat A (Suc b) i' j'"
    proof (cases "i' = b")
      case True
      then show ?thesis
      proof (cases "j' = b")
        case True with \<open>i' = b\<close> seq show ?thesis by (simp add: cholmat_Suc_diag)
      next
        case False with \<open>i' = b\<close> guard j'n aval show ?thesis by (simp add: cholmat_Suc_other)
      qed
    next
      case False
      then show ?thesis
      proof (cases "j' = b")
        case True
        have "i' < b" using ante \<open>i' \<noteq> b\<close> \<open>j' = b\<close> by simp
        with \<open>i' \<noteq> b\<close> \<open>j' = b\<close> i'n guard aval show ?thesis by (simp add: cholmat_col_ge)
      next
        case False with \<open>i' \<noteq> b\<close> i'n j'n aval show ?thesis by (simp add: cholmat_Suc_other)
      qed
    qed
  qed
  \<comment> \<open>chol_column precondition pre2\<close>
  subgoal premises p for s a b i'
  proof -
    from p have cc: "agree n a (cholmat A b)" and guard: "b < n"
      and i'n: "i' < n" and ge: "Suc b \<le> i'" by (auto simp: chol_outer_inv_def)
    have "a i' b = cholmat A b i' b" using cc i'n guard by (auto simp: agree_def)
    thus "(a(b := (a b)(b := sqrt (A b b - (\<Sum>k<b. (a b k)\<^sup>2))))) i' b = cholmat A b i' b"
      using ge by simp
  qed
  \<comment> \<open>chol_column precondition: \<open>Suc b \<le> n\<close>\<close>
  subgoal premises p for s a b using p by (auto simp: chol_outer_inv_def)
  \<comment> \<open>chol_column precondition: the diagonal value equals \<open>cholmat A (Suc b) b b\<close>\<close>
  subgoal premises p for s a b
  proof -
    from p have cc: "agree n a (cholmat A b)" and guard: "b < n" by (auto simp: chol_outer_inv_def)
    have "(\<Sum>k<b. (a b k)\<^sup>2) = (\<Sum>k<b. (cholmat A b b k)\<^sup>2)"
      using cc guard by (intro sum.cong refl) (auto simp: agree_def)
    thus "sqrt (A b b - (\<Sum>k<b. (a b k)\<^sup>2)) = cholmat A (Suc b) b b"
      by (simp add: cholmat_Suc_diag)
  qed
  \<comment> \<open>outer invariant preserved\<close>
  subgoal premises p for s a b x using p by (auto simp: chol_outer_inv_def)
  \<comment> \<open>outer measure decreases\<close>
  subgoal premises p for s a b x using p by (auto simp: in_measure)
  \<comment> \<open>exit: agreement with \<open>cholmat A n\<close> yields the factorisation\<close>
  subgoal premises p for s a b i j
  proof -
    from p have cc: "agree n a (cholmat A b)" and nb: "\<not> b < n" and bn: "b \<le> n"
      and iin: "i < n" and jjn: "j < n" by (auto simp: chol_outer_inv_def)
    have "b = n" using bn nb by simp
    hence ag: "agree n a (cholmat A n)" using cc by simp
    have "(\<Sum>k<n. a i k * a j k) = (\<Sum>k<n. cholmat A n i k * cholmat A n j k)"
      using ag iin jjn by (intro sum.cong refl) (auto simp: agree_def)
    also have "\<dots> = A i j" by (rule cholmat_factorises[OF sym safe iin jjn])
    finally show "(\<Sum>k<n. a i k * a j k) = A i j" .
  qed
  done


section \<open>Paradigm A: imperative ITree program via the VCG Hoare logic\<close>

text \<open>The same column-Cholesky algorithm written as an imperative ITree \<open>program\<close> and verified with
  the VCG-based Hoare logic \<open>H[_] _ [_]\<close>.  The inner column pass \<open>chol_col\<close> is kept as a
  separate program (mirroring \<^const>\<open>chol_column\<close>), but the numeric \<open>vcg\<close> inlines it and discharges
  the inner loop's invariant as part of the outer proof --- it offers no way to cite a separately
  proved triple for a sub-program, in contrast to the Lammich \<open>nres\<close> refinement where
  \<^const>\<open>chol_column\<close> is a standalone spec used inside \<^const>\<open>R_cholesky\<close>.  Also unlike the Lammich
  \<open>nres\<close> monad there is no \<open>ASSERT\<close>/failure construct, so positivity of the square-root argument is
  not localised: the factorisation is stated under \<^const>\<open>chol_safe\<close> as a precondition.\<close>

definition upd2 :: "(nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> real)" where
  "upd2 M r c v = M(r := (M r)(c := v))"

text \<open>A function-valued program variable (the matrix \<open>Lc\<close>) needs a \<^class>\<open>default\<close> instance for the
  \<open>zstore\<close> initial state; the pointwise default \<open>\<lambda>_. default\<close> serves.\<close>
instantiation "fun" :: (type, default) default
begin
  definition default_fun :: "'a \<Rightarrow> 'b" where "default_fun = (\<lambda>_. default)"
  instance ..
end

lemma cholmat_strict_upper: "p < q \<Longrightarrow> q < n \<Longrightarrow> cholmat A n p q = 0"
  using cholmat_lower[of n A] by (auto simp: lower_upto_def)

text \<open>Keep \<^const>\<open>cholmat\<close> folded during \<open>vcg\<close> (its \<open>fun\<close> equations would otherwise be unfolded by
  the tactic's simplifier, exposing the recursive case split); the inner-loop invariant is the
  opaque predicate \<open>chol_inner_pred\<close> so \<open>vcg\<close> does not crack open its quantifiers.\<close>
declare cholmat.simps [simp del]

definition chol_inner_pred :: "(nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> bool" where
  "chol_inner_pred A n j dg Lc i \<longleftrightarrow> Suc j \<le> i \<and> i \<le> n \<and> dg = cholmat A (Suc j) j j
     \<and> (\<forall>p<n. \<forall>q<n. (p < i \<or> q \<noteq> j) \<longrightarrow> Lc p q = cholmat A (Suc j) p q)
     \<and> (\<forall>p<n. i \<le> p \<longrightarrow> Lc p j = cholmat A j p j)"

definition chol_outer_pred :: "(nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> bool" where
  "chol_outer_pred A n Lc j \<longleftrightarrow> j \<le> n \<and> (\<forall>p<n. \<forall>q<n. Lc p q = cholmat A j p q)"

zstore chol_state =
  Lc :: "nat \<Rightarrow> nat \<Rightarrow> real"
  dg :: "real"
  i  :: "nat"
  j  :: "nat"

program chol_col "(A :: nat \<Rightarrow> nat \<Rightarrow> real, n :: nat)" over chol_state =
"i := j + 1;
 while i < n
 invariant chol_inner_pred A n j dg Lc i \<and> j = old[j]
 variant n - i
 do Lc := upd2 Lc i j ((A i j - (\<Sum>k<j. Lc i k * Lc j k)) / dg); i := i + 1 od"

text \<open>The clause \<open>j = old[j]\<close> in \<^const>\<open>chol_col\<close>'s invariant records that the inner loop leaves the
  outer counter \<open>j\<close> unchanged --- the outer termination measure \<open>n - j\<close> needs it once the inner loop
  sits inside the outer body.\<close>

program cholesky "(A :: nat \<Rightarrow> nat \<Rightarrow> real, n :: nat)" over chol_state =
"Lc := (\<lambda>r c. 0); j := 0;
 while j < n
 invariant chol_outer_pred A n Lc j
 variant n - j
 do dg := sqrt (A j j - (\<Sum>k<j. (Lc j k)\<^sup>2));
    Lc := upd2 Lc j j dg;
    chol_col (A, n);
    j := j + 1 od"

theorem cholesky_vcg_correct:
  assumes sym: "symmetric_upto n A" and safe: "chol_safe A n"
  shows "H[True] cholesky (A, n) [ \<forall>p<n. \<forall>q<n. (\<Sum>k<n. Lc p k * Lc q k) = A p q ]"
proof (vcg)
  \<comment> \<open>(1) inner loop body preserves the inner invariant (the \<^const>\<open>chol_column\<close> algebra)\<close>
  fix M0 M1 j Lc dg i
  assume "\<forall>x xa. M1 x xa = upd2 M0 j j (sqrt (A j j - (\<Sum>k<j. (M0 j k)\<^sup>2))) x xa"
     and "chol_outer_pred A n M0 j" and "j < n"
     and cc: "chol_inner_pred A n j dg Lc i" and guard: "i < n"
  from cc have inv1: "\<And>p' q'. p'<n \<Longrightarrow> q'<n \<Longrightarrow> p'<i \<or> q'\<noteq>j \<Longrightarrow> Lc p' q' = cholmat A (Suc j) p' q'"
    and inv2: "\<And>p'. p'<n \<Longrightarrow> i \<le> p' \<Longrightarrow> Lc p' j = cholmat A j p' j"
    and ji: "Suc j \<le> i" and iin: "i \<le> n" and dd: "dg = cholmat A (Suc j) j j"
    by (auto simp: chol_inner_pred_def)
  have jn: "Suc j \<le> n" using ji iin by simp
  show "chol_inner_pred A n j dg (upd2 Lc i j ((A i j - (\<Sum>k<j. Lc i k * Lc j k)) / dg)) (Suc i)"
    unfolding chol_inner_pred_def upd2_def
    using chol_column_inv_step[OF inv1 inv2 ji guard jn dd] ji guard dd by auto
next
  \<comment> \<open>(2) the outer body (set diagonal) establishes the inner invariant at \<open>i = Suc j\<close>\<close>
  fix M0 M1 M1' j
  assume "\<forall>x xa. M1' x xa = upd2 M0 j j (sqrt (A j j - (\<Sum>k<j. (M0 j k)\<^sup>2))) x xa"
     and co: "chol_outer_pred A n M0 j" and guard: "j < n"
     and "\<forall>x xa. M1 x xa = upd2 M0 j j (sqrt (A j j - (\<Sum>k<j. (M0 j k)\<^sup>2))) x xa"
  from co have agj: "\<And>p' q'. p'<n \<Longrightarrow> q'<n \<Longrightarrow> M0 p' q' = cholmat A j p' q'"
    by (auto simp: chol_outer_pred_def)
  have seq: "(\<Sum>k<j. (M0 j k)\<^sup>2) = (\<Sum>k<j. (cholmat A j j k)\<^sup>2)"
    using agj guard by (intro sum.cong refl) auto
  have dgd: "sqrt (A j j - (\<Sum>k<j. (M0 j k)\<^sup>2)) = cholmat A (Suc j) j j"
    using seq by (simp add: cholmat_Suc_diag)
  show "chol_inner_pred A n j (sqrt (A j j - (\<Sum>k<j. (M0 j k)\<^sup>2)))
          (upd2 M0 j j (sqrt (A j j - (\<Sum>k<j. (M0 j k)\<^sup>2)))) (Suc j)"
    unfolding chol_inner_pred_def
  proof (intro conjI)
    show "Suc j \<le> Suc j" by simp
    show "Suc j \<le> n" using guard by simp
    show "sqrt (A j j - (\<Sum>k<j. (M0 j k)\<^sup>2)) = cholmat A (Suc j) j j" by (rule dgd)
    show "\<forall>p<n. \<forall>q<n. (p < Suc j \<or> q \<noteq> j) \<longrightarrow>
            upd2 M0 j j (sqrt (A j j - (\<Sum>k<j. (M0 j k)\<^sup>2))) p q = cholmat A (Suc j) p q"
    proof (intro allI impI)
      fix p q assume pn: "p < n" and qn: "q < n" and ante: "p < Suc j \<or> q \<noteq> j"
      show "upd2 M0 j j (sqrt (A j j - (\<Sum>k<j. (M0 j k)\<^sup>2))) p q = cholmat A (Suc j) p q"
      proof (cases "p = j")
        case True
        show ?thesis
        proof (cases "q = j")
          case True with \<open>p = j\<close> dgd show ?thesis by (simp add: upd2_def)
        next
          case False with \<open>p = j\<close> guard qn agj show ?thesis by (simp add: upd2_def cholmat_Suc_other)
        qed
      next
        case False
        show ?thesis
        proof (cases "q = j")
          case True
          have "p < j" using ante \<open>p \<noteq> j\<close> \<open>q = j\<close> by simp
          with \<open>p \<noteq> j\<close> \<open>q = j\<close> pn guard agj show ?thesis
            by (simp add: upd2_def cholmat_col_ge cholmat_strict_upper)
        next
          case False with \<open>p \<noteq> j\<close> pn qn agj show ?thesis by (simp add: upd2_def cholmat_Suc_other)
        qed
      qed
    qed
    show "\<forall>p<n. Suc j \<le> p \<longrightarrow> upd2 M0 j j (sqrt (A j j - (\<Sum>k<j. (M0 j k)\<^sup>2))) p j = cholmat A j p j"
    proof (intro allI impI)
      fix p assume pn: "p < n" and ge: "Suc j \<le> p"
      have "M0 p j = cholmat A j p j" using agj pn guard by auto
      thus "upd2 M0 j j (sqrt (A j j - (\<Sum>k<j. (M0 j k)\<^sup>2))) p j = cholmat A j p j"
        using ge by (simp add: upd2_def)
    qed
  qed
next
  \<comment> \<open>(3) inner exit \<open>i = n\<close> re-establishes the outer invariant for the next column\<close>
  fix M0 M1 j Lc dg i
  assume "\<forall>x xa. M1 x xa = upd2 M0 j j (sqrt (A j j - (\<Sum>k<j. (M0 j k)\<^sup>2))) x xa"
     and "chol_outer_pred A n M0 j" and "j < n" and ni: "\<not> i < n" and cc: "chol_inner_pred A n j dg Lc i"
  from cc have iin: "i \<le> n" and ji: "Suc j \<le> i"
    and cl1: "\<And>p' q'. p'<n \<Longrightarrow> q'<n \<Longrightarrow> p'<i \<or> q'\<noteq>j \<Longrightarrow> Lc p' q' = cholmat A (Suc j) p' q'"
    by (auto simp: chol_inner_pred_def)
  have ieq: "i = n" using iin ni by simp
  show "chol_outer_pred A n Lc (Suc j)"
    unfolding chol_outer_pred_def
  proof (intro conjI allI impI)
    show "Suc j \<le> n" using ji ieq by simp
    fix p q assume pn: "p < n" and qn: "q < n"
    have "p < i" using pn ieq by simp
    thus "Lc p q = cholmat A (Suc j) p q" using cl1[OF pn qn] by simp
  qed
next
  \<comment> \<open>(4) initialisation: the zero matrix agrees with \<^term>\<open>cholmat A 0\<close>\<close>
  fix Lc
  assume "\<forall>x xa. Lc x xa = 0"
  show "chol_outer_pred A n (\<lambda>r c. 0) 0" by (simp add: chol_outer_pred_def cholmat.simps(1))
next
  \<comment> \<open>(5) outer exit \<open>j = n\<close>: agreement with \<^term>\<open>cholmat A n\<close> yields the factorisation\<close>
  fix Lc j p q
  assume nj: "\<not> j < n" and co: "chol_outer_pred A n Lc j" and pn: "p < n" and qn: "q < n"
  from co have jn: "j \<le> n" and ag: "\<And>p' q'. p'<n \<Longrightarrow> q'<n \<Longrightarrow> Lc p' q' = cholmat A j p' q'"
    by (auto simp: chol_outer_pred_def)
  have "j = n" using jn nj by simp
  hence ag': "\<And>p' q'. p'<n \<Longrightarrow> q'<n \<Longrightarrow> Lc p' q' = cholmat A n p' q'" using ag by simp
  have "(\<Sum>k<n. Lc p k * Lc q k) = (\<Sum>k<n. cholmat A n p k * cholmat A n q k)"
    using ag' pn qn by (intro sum.cong refl) auto
  also have "\<dots> = A p q" by (rule cholmat_factorises[OF sym safe pn qn])
  finally show "(\<Sum>k<n. Lc p k * Lc q k) = A p q" .
qed


section \<open>A concrete end-to-end run of the classical L L^T Cholesky\<close>

text \<open>The classic SPD example \<open>A = L L\<^sup>T\<close>, \<open>L = [[2,0,0],[6,1,0],[-8,5,3]]\<close>.  Square roots are not
  code-executable on \<^typ>\<open>real\<close>, so instead of \<open>execute\<close> we \<^emph>\<open>prove\<close> the computed factor equals a
  concrete matrix and let \<open>value\<close> display it.\<close>

definition A0 :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "A0 = (\<lambda>i j. [[4,12,-16],[12,37,-43],[-16,-43,98]] ! i ! j)"

definition L0 :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "L0 = (\<lambda>i j. [[2,0,0],[6,1,0],[-8,5,3]] ! i ! j)"

definition mat_to_list :: "(nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real list list" where
  "mat_to_list M n = map (\<lambda>i. map (M i) [0..<n]) [0..<n]"

lemma sqrt4: "sqrt 4 = 2" using real_sqrt_abs[of 2] by simp
lemma sqrt1: "sqrt 1 = 1" using real_sqrt_abs[of 1] by simp
lemma sqrt9: "sqrt 9 = 3" using real_sqrt_abs[of 3] by simp

value "mat_to_list A0 3"
value "mat_to_list L0 3"

\<comment> \<open>the algorithm's reference factor on \<open>A0\<close> equals \<open>L0\<close> (this is what the program computes)\<close>
lemma chol_factor_A0: "mat_to_list (cholmat A0 3) 3 = mat_to_list L0 3"
  by (simp add: mat_to_list_def L0_def A0_def cholmat.simps sqrt4 sqrt1 sqrt9
                numeral_2_eq_2 numeral_3_eq_3)

\<comment> \<open>\<open>L0\<close> is genuinely a Cholesky factor: \<open>L0 L0\<^sup>T = A0\<close> (pure arithmetic, no square roots)\<close>
lemma L0_factorises: "\<forall>i<3. \<forall>j<3. (\<Sum>k<3. L0 i k * L0 j k) = A0 i j"
  by (auto simp: L0_def A0_def numeral_3_eq_3 sum.lessThan_Suc less_Suc_eq)

\<comment> \<open>the two preconditions of \<open>cholesky_vcg_correct\<close> hold for \<open>A0\<close>\<close>
lemma A0_symmetric: "symmetric_upto 3 A0"
  by (auto simp: symmetric_upto_def A0_def numeral_3_eq_3 less_Suc_eq)

lemma A0_safe: "chol_safe A0 3"
  by (simp add: chol_safe_def A0_def cholmat.simps sqrt4 sqrt1 sqrt9
                numeral_2_eq_2 numeral_3_eq_3 sum.lessThan_Suc less_Suc_eq)

text \<open>End-to-end: instantiating the general correctness theorem on this concrete matrix, the
  imperative \<open>cholesky\<close> program run on \<open>A0\<close> is guaranteed to return a factor \<open>L\<close> with \<open>L L\<^sup>T = A0\<close>;
  by @{thm chol_factor_A0} that factor is exactly \<open>L0 = [[2,0,0],[6,1,0],[-8,5,3]]\<close>.\<close>
theorem cholesky_on_A0:
  "H[True] cholesky (A0, 3) [\<forall>p<3. \<forall>q<3. (\<Sum>k<3. Lc p k * Lc q k) = A0 p q]"
  by (rule cholesky_vcg_correct[OF A0_symmetric A0_safe])


section \<open>A square-root-free, executable variant: the L D L^T factorisation\<close>

text \<open>The development above verifies the \<^emph>\<open>classical\<close> Cholesky factorisation A = L L^T (Paradigm
  A via the VCG Hoare logic, Paradigm B via Lammich's refinement).  Its diagonal entries are square
  roots, and a square root of a rational is in general irrational, so that factorisation cannot be
  computed exactly; in particular the imperative program cannot be run with the \<open>execute\<close> command,
  as there is no code equation for \<open>sqrt\<close> on the reals.

  This section develops the closely related, \<^emph>\<open>square-root-free\<close> L D L^T factorisation: A = L D L^T
  with L unit lower-triangular and D diagonal, computed by a recurrence using only addition,
  subtraction, multiplication and division.  It therefore computes \<^emph>\<open>exactly\<close> over the rationals,
  it is \<^emph>\<open>literally runnable\<close> with \<open>value\<close> and the \<open>execute\<close> command (both appear at the end of
  the section), and it is proved to refine the verified Cholesky factor above by the theorem
  \<open>ldl_factorises\<close>: A = L D L^T for every symmetric, \<open>chol_safe\<close> matrix.  The classical Cholesky
  factor is recovered as L_chol = L * diag (sqrt D).\<close>

fun ldlmat :: "(nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "ldlmat A 0 = (\<lambda>i j. 0)"
| "ldlmat A (Suc m) =
     (\<lambda>i j. if j = m
            then (if m < i
                  then (A i m - (\<Sum>k<m. ldlmat A m i k * ldlmat A m m k * ldlmat A m k k))
                        / (A m m - (\<Sum>k<m. (ldlmat A m m k)\<^sup>2 * ldlmat A m k k))
                  else if i = m
                  then A m m - (\<Sum>k<m. (ldlmat A m m k)\<^sup>2 * ldlmat A m k k)
                  else 0)
            else ldlmat A m i j)"

text \<open>Unit-lower factor \<open>L\<close> and pivots \<open>D\<close> read off the packed result.\<close>

definition ldl_L :: "(nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "ldl_L A n r c = (if r = c then 1 else if c < r then ldlmat A n r c else 0)"

definition ldl_D :: "(nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "ldl_D A n c = ldlmat A n c c"

subsection \<open>It runs: matrix in, factor out (exact rationals, no square roots)\<close>

value "mat_to_list (ldlmat A0 3) 3"
value "mat_to_list (ldl_L A0 3) 3"
value "map (ldl_D A0 3) [0..<3]"

\<comment> \<open>reconstruct \<open>A\<close> from the factor: L D L^T -- should print \<open>A0\<close> again\<close>
value "mat_to_list (\<lambda>i j. \<Sum>k<3. ldl_L A0 3 i k * ldl_D A0 3 k * ldl_L A0 3 j k) 3"

subsection \<open>End-to-end correctness on the concrete matrix (decided by exact computation)\<close>

lemma A0_LDLt: "\<forall>i<3. \<forall>j<3. (\<Sum>k<3. ldl_L A0 3 i k * ldl_D A0 3 k * ldl_L A0 3 j k) = A0 i j"
  by eval

subsection \<open>General correctness: the sqrt-free factor refines the verified Cholesky factor\<close>

text \<open>Columns are frozen once built (as for \<^const>\<open>cholmat\<close>).\<close>
lemma ldlmat_mono: "k < m \<Longrightarrow> m \<le> m' \<Longrightarrow> ldlmat A m' a k = ldlmat A m a k"
proof (induction m')
  case 0 thus ?case by simp
next
  case (Suc m')
  show ?case
  proof (cases "m = Suc m'")
    case True thus ?thesis by simp
  next
    case False
    with Suc.prems have mm': "m \<le> m'" by simp
    with \<open>k < m\<close> have "k \<noteq> m'" by simp
    hence "ldlmat A (Suc m') a k = ldlmat A m' a k" by simp
    also have "\<dots> = ldlmat A m a k" using Suc.IH \<open>k < m\<close> mm' by simp
    finally show ?thesis .
  qed
qed

text \<open>Under \<open>chol_safe\<close> the Cholesky diagonal is strictly positive, so the divisions below are exact.\<close>
lemma cholmat_diag_pos:
  assumes "chol_safe A n" "k < n" shows "0 < cholmat A n k k"
proof -
  have "cholmat A n k k = cholmat A (Suc k) k k"
    using cholmat_mono[of k "Suc k" n A k] assms(2) by simp
  also have "\<dots> = sqrt (A k k - (\<Sum>j<k. (cholmat A k k j)\<^sup>2))" by (simp add: cholmat_Suc_diag)
  finally have eq: "cholmat A n k k = sqrt (A k k - (\<Sum>j<k. (cholmat A k k j)\<^sup>2))" .
  have "0 < A k k - (\<Sum>j<k. (cholmat A k k j)\<^sup>2)" using assms by (simp add: chol_safe_def)
  thus ?thesis using eq by simp
qed

text \<open>The one bit of square-root algebra: \<open>X / r \<cdot> \<surd>r = X / \<surd>r\<close> for \<open>r > 0\<close>.\<close>
lemma div_sqrt_aux:
  fixes X r :: real assumes r: "0 < r" shows "X / r * sqrt r = X / sqrt r"
proof -
  have s0: "sqrt r \<noteq> 0" using r by simp
  have rs: "sqrt r * sqrt r = r" using r by (simp add: real_sqrt_mult_self)
  show "X / r * sqrt r = X / sqrt r"
    by (metis rs s0 mult.commute nonzero_mult_divide_mult_cancel_left times_divide_eq_left)
qed

text \<open>The packed factor relates to the Cholesky factor: the stored diagonal is L_kk^2 (the pivot
  D_k) and each below-diagonal entry is L_ik / L_kk (the unit-triangular L~).\<close>
lemma ldl_chol_rel:
  assumes safe: "chol_safe A n"
  shows "k < n \<Longrightarrow> ldlmat A n k k = (cholmat A n k k)\<^sup>2
                  \<and> (\<forall>i. k < i \<longrightarrow> i < n \<longrightarrow> ldlmat A n i k * cholmat A n k k = cholmat A n i k)"
proof (induction k rule: less_induct)
  case (less k)
  {
    assume kn: "k < n"
    have IHd: "\<And>j. j < k \<Longrightarrow> ldlmat A n j j = (cholmat A n j j)\<^sup>2"
      using less.IH kn by force
    have IHl: "\<And>i j. j < k \<Longrightarrow> j < i \<Longrightarrow> i < n \<Longrightarrow> ldlmat A n i j * cholmat A n j j = cholmat A n i j"
      using less.IH kn by force
    have cpos: "\<And>j. j < n \<Longrightarrow> 0 < cholmat A n j j" using safe cholmat_diag_pos by blast
    \<comment> \<open>convert count-\<open>k\<close> / count-\<open>Suc k\<close> entries (columns \<open><k\<close>) to count \<open>n\<close>\<close>
    have sL: "\<And>a j. j < k \<Longrightarrow> ldlmat A k a j = ldlmat A n a j"
      using ldlmat_mono kn by (metis less_le_trans nat_less_le)
    have sC: "\<And>a j. j < k \<Longrightarrow> cholmat A k a j = cholmat A n a j"
      using cholmat_mono kn by (metis less_le_trans nat_less_le)
    \<comment> \<open>per-term identity used in both column-\<open>k\<close> sums\<close>
    have offterm: "\<And>a j. j < k \<Longrightarrow> a < n \<Longrightarrow> j < a
          \<Longrightarrow> ldlmat A k a j * ldlmat A k k j * ldlmat A k j j = cholmat A n a j * cholmat A n k j"
    proof -
      fix a j assume jk: "j < k" and an: "a < n" and ja: "j < a"
      have la: "ldlmat A n a j * cholmat A n j j = cholmat A n a j" using IHl jk ja an by simp
      have lk: "ldlmat A n k j * cholmat A n j j = cholmat A n k j" using IHl jk jk kn by simp
      have dj: "ldlmat A n j j = (cholmat A n j j)\<^sup>2" using IHd jk by simp
      have "ldlmat A k a j * ldlmat A k k j * ldlmat A k j j
          = (ldlmat A n a j * cholmat A n j j) * (ldlmat A n k j * cholmat A n j j)"
        using sL jk an dj by (simp add: power2_eq_square algebra_simps)
      thus "ldlmat A k a j * ldlmat A k k j * ldlmat A k j j = cholmat A n a j * cholmat A n k j"
        using la lk by simp
    qed
    have diagterm: "\<And>j. j < k \<Longrightarrow> (ldlmat A k k j)\<^sup>2 * ldlmat A k j j = (cholmat A n k j)\<^sup>2"
    proof -
      fix j assume jk: "j < k"
      have lk: "ldlmat A n k j * cholmat A n j j = cholmat A n k j" using IHl jk jk kn by simp
      have dj: "ldlmat A n j j = (cholmat A n j j)\<^sup>2" using IHd jk by simp
      have "(ldlmat A k k j)\<^sup>2 * ldlmat A k j j
          = (ldlmat A n k j * cholmat A n j j)\<^sup>2"
        using sL jk kn dj by (simp add: power2_eq_square algebra_simps)
      thus "(ldlmat A k k j)\<^sup>2 * ldlmat A k j j = (cholmat A n k j)\<^sup>2" using lk by simp
    qed
    \<comment> \<open>the LDLT pivot equals the Cholesky radicand at column \<open>k\<close>\<close>
    let ?r = "A k k - (\<Sum>j<k. (cholmat A k k j)\<^sup>2)"
    have rpos: "0 < ?r" using safe kn by (simp add: chol_safe_def)
    have rsq: "sqrt ?r * sqrt ?r = ?r" using rpos by (simp add: real_sqrt_mult_self)
    have rne: "sqrt ?r \<noteq> 0" using rpos by simp
    have dk_eq: "A k k - (\<Sum>j<k. (ldlmat A k k j)\<^sup>2 * ldlmat A k j j) = ?r"
    proof -
      have "(\<Sum>j<k. (ldlmat A k k j)\<^sup>2 * ldlmat A k j j) = (\<Sum>j<k. (cholmat A n k j)\<^sup>2)"
        by (rule sum.cong[OF refl]) (simp add: diagterm)
      also have "\<dots> = (\<Sum>j<k. (cholmat A k k j)\<^sup>2)" by (rule sum.cong[OF refl]) (simp add: sC)
      finally show ?thesis by simp
    qed
    have ckk: "cholmat A (Suc k) k k = sqrt ?r" by (simp add: cholmat_Suc_diag)
    \<comment> \<open>diagonal relation\<close>
    have D: "ldlmat A n k k = (cholmat A n k k)\<^sup>2"
    proof -
      have "ldlmat A n k k = ldlmat A (Suc k) k k" using ldlmat_mono[of k "Suc k" n A k] kn by simp
      also have "\<dots> = A k k - (\<Sum>j<k. (ldlmat A k k j)\<^sup>2 * ldlmat A k j j)" by simp
      also have "\<dots> = ?r" by (rule dk_eq)
      finally have "ldlmat A n k k = ?r" .
      moreover have "(cholmat A n k k)\<^sup>2 = ?r"
        using cholmat_mono[of k "Suc k" n A k] kn ckk rsq by (simp add: power2_eq_square)
      ultimately show ?thesis by simp
    qed
    \<comment> \<open>below-diagonal relation\<close>
    have L: "\<forall>i. k < i \<longrightarrow> i < n \<longrightarrow> ldlmat A n i k * cholmat A n k k = cholmat A n i k"
    proof (intro allI impI)
      fix i assume ki: "k < i" and iin: "i < n"
      have num_eq: "A i k - (\<Sum>j<k. ldlmat A k i j * ldlmat A k k j * ldlmat A k j j)
                  = A i k - (\<Sum>j<k. cholmat A k i j * cholmat A k k j)"
      proof -
        have "(\<Sum>j<k. ldlmat A k i j * ldlmat A k k j * ldlmat A k j j)
            = (\<Sum>j<k. cholmat A n i j * cholmat A n k j)"
        proof (rule sum.cong[OF refl])
          fix x assume "x \<in> {..<k}" hence xk: "x < k" by simp
          hence "x < i" using ki by simp
          thus "ldlmat A k i x * ldlmat A k k x * ldlmat A k x x = cholmat A n i x * cholmat A n k x"
            using offterm[OF xk iin] by simp
        qed
        also have "\<dots> = (\<Sum>j<k. cholmat A k i j * cholmat A k k j)"
          by (rule sum.cong[OF refl]) (simp add: sC)
        finally show ?thesis by simp
      qed
      have li: "ldlmat A n i k = (A i k - (\<Sum>j<k. cholmat A k i j * cholmat A k k j)) / ?r"
      proof -
        have "ldlmat A n i k = ldlmat A (Suc k) i k" using ldlmat_mono[of k "Suc k" n A i] kn by simp
        also have "\<dots> = (A i k - (\<Sum>j<k. ldlmat A k i j * ldlmat A k k j * ldlmat A k j j))
                          / (A k k - (\<Sum>j<k. (ldlmat A k k j)\<^sup>2 * ldlmat A k j j))"
          using ki by simp
        also have "\<dots> = (A i k - (\<Sum>j<k. cholmat A k i j * cholmat A k k j)) / ?r"
          by (simp add: num_eq dk_eq)
        finally show ?thesis .
      qed
      have ci: "cholmat A n i k = (A i k - (\<Sum>j<k. cholmat A k i j * cholmat A k k j)) / sqrt ?r"
      proof -
        have "cholmat A n i k = cholmat A (Suc k) i k" using cholmat_mono[of k "Suc k" n A i] kn by simp
        also have "\<dots> = (A i k - (\<Sum>j<k. cholmat A k i j * cholmat A k k j)) / sqrt ?r"
          using ki by (simp add: cholmat_Suc_offdiag)
        finally show ?thesis .
      qed
      have ck: "cholmat A n k k = sqrt ?r" using cholmat_mono[of k "Suc k" n A k] kn ckk by simp
      have "ldlmat A n i k * cholmat A n k k
          = (A i k - (\<Sum>j<k. cholmat A k i j * cholmat A k k j)) / ?r * sqrt ?r"
        using li ck by simp
      also have "\<dots> = (A i k - (\<Sum>j<k. cholmat A k i j * cholmat A k k j)) / sqrt ?r"
        using div_sqrt_aux[OF rpos] by simp
      also have "\<dots> = cholmat A n i k" using ci by simp
      finally show "ldlmat A n i k * cholmat A n k k = cholmat A n i k" .
    qed
    have "ldlmat A n k k = (cholmat A n k k)\<^sup>2
        \<and> (\<forall>i. k < i \<longrightarrow> i < n \<longrightarrow> ldlmat A n i k * cholmat A n k k = cholmat A n i k)"
      using D L by blast
  }
  thus ?case using less.prems by blast
qed

text \<open>Hence the executable factor reproduces \<open>A\<close>: A = L~ D L~^T for every symmetric, \<open>chol_safe\<close> matrix.\<close>
theorem ldl_factorises:
  assumes sym: "symmetric_upto n A" and safe: "chol_safe A n" and pn: "p < n" and qn: "q < n"
  shows "(\<Sum>k<n. ldl_L A n p k * ldl_D A n k * ldl_L A n q k) = A p q"
proof -
  have rel2: "\<And>r c. r < n \<Longrightarrow> c < n \<Longrightarrow> ldl_L A n r c * cholmat A n c c = cholmat A n r c"
  proof -
    fix r c assume rn: "r < n" and cn: "c < n"
    show "ldl_L A n r c * cholmat A n c c = cholmat A n r c"
    proof (cases "c < r")
      case True
      have "ldlmat A n r c * cholmat A n c c = cholmat A n r c"
        using ldl_chol_rel[OF safe cn] True rn by blast
      thus ?thesis using True by (simp add: ldl_L_def)
    next
      case False
      thus ?thesis
      proof (cases "r = c")
        case True thus ?thesis by (simp add: ldl_L_def)
      next
        case False with \<open>\<not> c < r\<close> have "r < c" by simp
        thus ?thesis using cholmat_strict_upper[of r c n A] cn by (simp add: ldl_L_def)
      qed
    qed
  qed
  have relD: "\<And>c. c < n \<Longrightarrow> ldl_D A n c = (cholmat A n c c)\<^sup>2"
  proof -
    fix c assume cn: "c < n"
    have "ldlmat A n c c = (cholmat A n c c)\<^sup>2" using ldl_chol_rel[OF safe cn] by blast
    thus "ldl_D A n c = (cholmat A n c c)\<^sup>2" by (simp add: ldl_D_def)
  qed
  have "(\<Sum>k<n. ldl_L A n p k * ldl_D A n k * ldl_L A n q k)
      = (\<Sum>k<n. cholmat A n p k * cholmat A n q k)"
  proof (rule sum.cong[OF refl])
    fix k assume "k \<in> {..<n}" hence kn: "k < n" by simp
    have "ldl_L A n p k * ldl_D A n k * ldl_L A n q k
        = (ldl_L A n p k * cholmat A n k k) * (ldl_L A n q k * cholmat A n k k)"
      using relD kn by (simp add: power2_eq_square algebra_simps)
    also have "\<dots> = cholmat A n p k * cholmat A n q k" using rel2 pn qn kn by simp
    finally show "ldl_L A n p k * ldl_D A n k * ldl_L A n q k = cholmat A n p k * cholmat A n q k" .
  qed
  also have "\<dots> = A p q" by (rule cholmat_factorises[OF sym safe pn qn])
  finally show ?thesis .
qed

subsection \<open>A literally executable imperative program\<close>

text \<open>To run the algorithm with the \<open>execute\<close> command the state must be a displayable type, so the
  matrix is stored as a \<^typ>\<open>real list list\<close> (rows) rather than a function, and \<open>\<surd>\<close> is avoided by
  computing the same packed \<open>L D L\<^sup>T\<close> as \<^const>\<open>ldlmat\<close> (pivots on the diagonal, \<open>L\<close> below).\<close>

definition A0_list :: "real list list" where
  "A0_list = [[4,12,-16],[12,37,-43],[-16,-43,98]]"

text \<open>State: \<open>Lm\<close> is the unit lower-triangular factor (the recognisable \<open>L\<close>), \<open>Dv\<close> the pivot vector
  \<open>D\<close>; on termination \<open>A = Lm \<cdot> diag Dv \<cdot> Lm\<^sup>T\<close> (the classical Cholesky factor is \<open>Lm \<cdot> diag(\<surd>Dv)\<close>,
  but \<open>\<surd>\<close> is not code-executable, which is exactly why we run the square-root-free \<open>L D L\<^sup>T\<close>).\<close>

zstore ldlt_state =
  Lm :: "real list list"
  Dv :: "real list"
  cc :: nat
  rr :: nat

program ldlt "(A :: real list list, n :: nat)" over ldlt_state =
"Lm := replicate n (replicate n (0::real));
 Dv := replicate n (0::real);
 cc := 0;
 while cc < n inv True do
   Dv := list_update Dv cc (A ! cc ! cc - (\<Sum>k<cc. (Lm ! cc ! k)\<^sup>2 * (Dv ! k)));
   Lm := list_update Lm cc (list_update (Lm ! cc) cc 1);
   rr := cc + 1;
   while rr < n inv True do
     Lm := list_update Lm rr (list_update (Lm ! rr) cc
              ((A ! rr ! cc - (\<Sum>k<cc. Lm ! rr ! k * Lm ! cc ! k * Dv ! k)) / (Dv ! cc)));
     rr := rr + 1
   od;
   cc := cc + 1
 od"

execute "ldlt ([[4,12,-16],[12,37,-43],[-16,-43,98]], 3)"


section \<open>Verifying the L D L^T algorithm under both paradigms\<close>

text \<open>Like \<^const>\<open>cholmat\<close>, the square-root-free factor \<^const>\<open>ldlmat\<close> is a packed lower-triangular
  matrix (pivots \<open>D\<close> on the diagonal, multipliers below), built column by column.  So the two
  verifications of the classical \<open>L L^T\<close> algorithm carry over with the diagonal square root dropped
  and each dot-product weighted by the pivot.  Both paradigms are shown to compute the verified
  packed factor \<^const>\<open>ldlmat\<close>; with @{thm ldl_factorises} that is the full \<open>A = L D L^T\<close>
  guarantee for an actual program.\<close>

lemma ldlmat_Suc_other: "b \<noteq> c \<Longrightarrow> ldlmat A (Suc c) a b = ldlmat A c a b" by simp

lemma ldl_diag_pos:
  assumes "chol_safe A n" "c < n" shows "0 < ldlmat A n c c"
proof -
  have e: "ldlmat A n c c = (cholmat A n c c)\<^sup>2" using ldl_chol_rel[OF assms(1)] assms(2) by blast
  have "0 < cholmat A n c c" using cholmat_diag_pos[OF assms] .
  hence "0 < (cholmat A n c c)\<^sup>2" by simp
  thus ?thesis using e by simp
qed

text \<open>Filling one entry of column \<open>c\<close> below the diagonal preserves agreement with \<^const>\<open>ldlmat\<close>
  (the shared inner-loop algebra, sqrt-free and pivot-weighted).\<close>
lemma ldl_column_inv_step:
  assumes inv1: "\<And>a b. a<n \<Longrightarrow> b<n \<Longrightarrow> a<r \<or> b\<noteq>c \<Longrightarrow> M a b = ldlmat A (Suc c) a b"
    and inv2: "\<And>a. a<n \<Longrightarrow> r \<le> a \<Longrightarrow> M a c = ldlmat A c a c"
    and ji: "Suc c \<le> r" and iin: "r < n" and jn: "Suc c \<le> n"
    and dd: "d = ldlmat A (Suc c) c c"
  shows "(\<forall>a<n. \<forall>b<n. (a<Suc r \<or> b\<noteq>c) \<longrightarrow>
            (M(r := (M r)(c := (A r c - (\<Sum>k<c. M r k * M c k * M k k)) / d))) a b = ldlmat A (Suc c) a b)
       \<and> (\<forall>a<n. Suc r \<le> a \<longrightarrow>
            (M(r := (M r)(c := (A r c - (\<Sum>k<c. M r k * M c k * M k k)) / d))) a c = ldlmat A c a c)"
proof -
  let ?v = "(A r c - (\<Sum>k<c. M r k * M c k * M k k)) / d"
  let ?M = "M(r := (M r)(c := ?v))"
  have ji': "c < r" using ji by simp
  have crux: "?v = ldlmat A (Suc c) r c"
  proof -
    have "(\<Sum>k<c. M r k * M c k * M k k) = (\<Sum>k<c. ldlmat A c r k * ldlmat A c c k * ldlmat A c k k)"
    proof (rule sum.cong[OF refl])
      fix k assume "k \<in> {..<c}" hence kj: "k < c" by simp
      hence kn: "k < n" using jn by simp
      have "M r k = ldlmat A c r k" using inv1[OF iin kn] kj ldlmat_Suc_other[of k c A r] by simp
      moreover have "M c k = ldlmat A c c k" using inv1[of c k] jn kn kj ldlmat_Suc_other[of k c A c] by simp
      moreover have "M k k = ldlmat A c k k" using inv1[of k k] kn kj ldlmat_Suc_other[of k c A k] by simp
      ultimately show "M r k * M c k * M k k = ldlmat A c r k * ldlmat A c c k * ldlmat A c k k" by simp
    qed
    thus ?thesis using dd ji' by simp
  qed
  have c1: "\<forall>a<n. \<forall>b<n. (a<Suc r \<or> b\<noteq>c) \<longrightarrow> ?M a b = ldlmat A (Suc c) a b"
  proof (intro allI impI)
    fix a b assume a': "a<n" and b': "b<n" and ante: "a<Suc r \<or> b\<noteq>c"
    show "?M a b = ldlmat A (Suc c) a b"
    proof (cases "a=r \<and> b=c")
      case True thus ?thesis using crux by simp
    next
      case False
      hence "?M a b = M a b" by auto
      moreover have "a<r \<or> b\<noteq>c" using False ante by auto
      ultimately show ?thesis using inv1[OF a' b'] by simp
    qed
  qed
  have c2: "\<forall>a<n. Suc r \<le> a \<longrightarrow> ?M a c = ldlmat A c a c"
  proof (intro allI impI)
    fix a assume a': "a<n" and "Suc r \<le> a"
    hence "a \<noteq> r" by simp
    hence "?M a c = M a c" by simp
    also have "\<dots> = ldlmat A c a c" using inv2[OF a'] \<open>Suc r \<le> a\<close> by simp
    finally show "?M a c = ldlmat A c a c" .
  qed
  from c1 c2 show ?thesis by blast
qed

lemma ldlmat_col_ge: "m \<le> k \<Longrightarrow> ldlmat A m a k = 0"
proof (induction m)
  case 0 thus ?case by simp
next
  case (Suc m)
  hence "m \<le> k" "k \<noteq> m" by auto
  thus ?case using Suc.IH by simp
qed

subsection \<open>Paradigm A for L D L^T: imperative ITree program via the VCG Hoare logic\<close>

definition ldl_inner_pred :: "(nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> bool" where
  "ldl_inner_pred A n c d M r \<longleftrightarrow> Suc c \<le> r \<and> r \<le> n \<and> d = ldlmat A (Suc c) c c
     \<and> (\<forall>a<n. \<forall>b<n. (a < r \<or> b \<noteq> c) \<longrightarrow> M a b = ldlmat A (Suc c) a b)
     \<and> (\<forall>a<n. r \<le> a \<longrightarrow> M a c = ldlmat A c a c)"

definition ldl_outer_pred :: "(nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> bool" where
  "ldl_outer_pred A n M c \<longleftrightarrow> c \<le> n \<and> (\<forall>a<n. \<forall>b<n. M a b = ldlmat A c a b)"

program ldl_col "(A :: nat \<Rightarrow> nat \<Rightarrow> real, n :: nat)" over chol_state =
"i := j + 1;
 while i < n
 invariant ldl_inner_pred A n j dg Lc i \<and> j = old[j]
 variant n - i
 do Lc := upd2 Lc i j ((A i j - (\<Sum>k<j. Lc i k * Lc j k * Lc k k)) / dg); i := i + 1 od"

program ldlt_chol "(A :: nat \<Rightarrow> nat \<Rightarrow> real, n :: nat)" over chol_state =
"Lc := (\<lambda>r c. 0); j := 0;
 while j < n
 invariant ldl_outer_pred A n Lc j
 variant n - j
 do dg := A j j - (\<Sum>k<j. (Lc j k)\<^sup>2 * Lc k k);
    Lc := upd2 Lc j j dg;
    ldl_col (A, n);
    j := j + 1 od"

text \<open>The program computes the verified packed factor \<^const>\<open>ldlmat\<close>; with @{thm ldl_factorises}
  that is the \<open>A = L D L^T\<close> guarantee.  No square root occurs, so (unlike \<^const>\<open>cholesky\<close>) the
  spec needs no precondition at all.\<close>
theorem ldlt_vcg_correct:
  "H[True] ldlt_chol (A, n) [ \<forall>p<n. \<forall>q<n. Lc p q = ldlmat A n p q ]"
proof (vcg)
  \<comment> \<open>(1) inner loop body preserves the inner invariant\<close>
  fix M0 M1 j Lc dg i
  assume "\<forall>x xa. M1 x xa = upd2 M0 j j (A j j - (\<Sum>k<j. (M0 j k)\<^sup>2 * M0 k k)) x xa"
     and "ldl_outer_pred A n M0 j" and "j < n"
     and cc: "ldl_inner_pred A n j dg Lc i" and guard: "i < n"
  from cc have inv1: "\<And>a b. a<n \<Longrightarrow> b<n \<Longrightarrow> a<i \<or> b\<noteq>j \<Longrightarrow> Lc a b = ldlmat A (Suc j) a b"
    and inv2: "\<And>a. a<n \<Longrightarrow> i \<le> a \<Longrightarrow> Lc a j = ldlmat A j a j"
    and ji: "Suc j \<le> i" and iin: "i \<le> n" and dd: "dg = ldlmat A (Suc j) j j"
    by (auto simp: ldl_inner_pred_def)
  have jn: "Suc j \<le> n" using ji iin by simp
  show "ldl_inner_pred A n j dg (upd2 Lc i j ((A i j - (\<Sum>k<j. Lc i k * Lc j k * Lc k k)) / dg)) (Suc i)"
    unfolding ldl_inner_pred_def upd2_def
    using ldl_column_inv_step[OF inv1 inv2 ji guard jn dd] ji guard dd by auto
next
  \<comment> \<open>(2) the outer body (compute pivot, set diagonal) establishes the inner invariant at \<open>i = Suc j\<close>\<close>
  fix M0 M1 M1' j
  assume "\<forall>x xa. M1' x xa = upd2 M0 j j (A j j - (\<Sum>k<j. (M0 j k)\<^sup>2 * M0 k k)) x xa"
     and co: "ldl_outer_pred A n M0 j" and guard: "j < n"
     and "\<forall>x xa. M1 x xa = upd2 M0 j j (A j j - (\<Sum>k<j. (M0 j k)\<^sup>2 * M0 k k)) x xa"
  from co have agj: "\<And>a b. a<n \<Longrightarrow> b<n \<Longrightarrow> M0 a b = ldlmat A j a b"
    by (auto simp: ldl_outer_pred_def)
  have seq: "(\<Sum>k<j. (M0 j k)\<^sup>2 * M0 k k) = (\<Sum>k<j. (ldlmat A j j k)\<^sup>2 * ldlmat A j k k)"
    using agj guard by (intro sum.cong refl) auto
  have dgd: "A j j - (\<Sum>k<j. (M0 j k)\<^sup>2 * M0 k k) = ldlmat A (Suc j) j j"
    using seq by simp
  show "ldl_inner_pred A n j (A j j - (\<Sum>k<j. (M0 j k)\<^sup>2 * M0 k k))
          (upd2 M0 j j (A j j - (\<Sum>k<j. (M0 j k)\<^sup>2 * M0 k k))) (Suc j)"
    unfolding ldl_inner_pred_def
  proof (intro conjI)
    show "Suc j \<le> Suc j" by simp
    show "Suc j \<le> n" using guard by simp
    show "A j j - (\<Sum>k<j. (M0 j k)\<^sup>2 * M0 k k) = ldlmat A (Suc j) j j" by (rule dgd)
    show "\<forall>p<n. \<forall>q<n. (p < Suc j \<or> q \<noteq> j) \<longrightarrow>
            upd2 M0 j j (A j j - (\<Sum>k<j. (M0 j k)\<^sup>2 * M0 k k)) p q = ldlmat A (Suc j) p q"
    proof (intro allI impI)
      fix p q assume pn: "p < n" and qn: "q < n" and ante: "p < Suc j \<or> q \<noteq> j"
      show "upd2 M0 j j (A j j - (\<Sum>k<j. (M0 j k)\<^sup>2 * M0 k k)) p q = ldlmat A (Suc j) p q"
      proof (cases "p = j")
        case True
        show ?thesis
        proof (cases "q = j")
          case True with \<open>p = j\<close> seq show ?thesis by (simp add: upd2_def)
        next
          case False with \<open>p = j\<close> guard qn agj show ?thesis by (simp add: upd2_def)
        qed
      next
        case False
        show ?thesis
        proof (cases "q = j")
          case True
          have "p < j" using ante \<open>p \<noteq> j\<close> \<open>q = j\<close> by simp
          with \<open>p \<noteq> j\<close> \<open>q = j\<close> pn guard agj show ?thesis by (simp add: upd2_def ldlmat_col_ge)
        next
          case False with \<open>p \<noteq> j\<close> pn qn agj show ?thesis by (simp add: upd2_def)
        qed
      qed
    qed
    show "\<forall>p<n. Suc j \<le> p \<longrightarrow> upd2 M0 j j (A j j - (\<Sum>k<j. (M0 j k)\<^sup>2 * M0 k k)) p j = ldlmat A j p j"
    proof (intro allI impI)
      fix p assume pn: "p < n" and ge: "Suc j \<le> p"
      have "M0 p j = ldlmat A j p j" using agj pn guard by auto
      thus "upd2 M0 j j (A j j - (\<Sum>k<j. (M0 j k)\<^sup>2 * M0 k k)) p j = ldlmat A j p j"
        using ge by (simp add: upd2_def)
    qed
  qed
next
  \<comment> \<open>(3) inner exit \<open>i = n\<close> re-establishes the outer invariant\<close>
  fix M0 M1 j Lc dg i
  assume "\<forall>x xa. M1 x xa = upd2 M0 j j (A j j - (\<Sum>k<j. (M0 j k)\<^sup>2 * M0 k k)) x xa"
     and "ldl_outer_pred A n M0 j" and "j < n" and ni: "\<not> i < n" and cc: "ldl_inner_pred A n j dg Lc i"
  from cc have iin: "i \<le> n" and ji: "Suc j \<le> i"
    and cl1: "\<And>a b. a<n \<Longrightarrow> b<n \<Longrightarrow> a<i \<or> b\<noteq>j \<Longrightarrow> Lc a b = ldlmat A (Suc j) a b"
    by (auto simp: ldl_inner_pred_def)
  have ieq: "i = n" using iin ni by simp
  show "ldl_outer_pred A n Lc (Suc j)"
    unfolding ldl_outer_pred_def
  proof (intro conjI allI impI)
    show "Suc j \<le> n" using ji ieq by simp
    fix p q assume pn: "p < n" and qn: "q < n"
    have "p < i" using pn ieq by simp
    thus "Lc p q = ldlmat A (Suc j) p q" using cl1[OF pn qn] by simp
  qed
next
  \<comment> \<open>(4) initialisation: the zero matrix agrees with \<^term>\<open>ldlmat A 0\<close>\<close>
  fix Lc
  assume "\<forall>x xa. Lc x xa = 0"
  show "ldl_outer_pred A n (\<lambda>r c. 0) 0" by (simp add: ldl_outer_pred_def)
next
  \<comment> \<open>(5) outer exit \<open>j = n\<close>: the state is the verified packed factor \<^const>\<open>ldlmat\<close>\<close>
  fix Lc j p q
  assume nj: "\<not> j < n" and co: "ldl_outer_pred A n Lc j" and pn: "p < n" and qn: "q < n"
  from co have jn: "j \<le> n" and ag: "\<And>a b. a<n \<Longrightarrow> b<n \<Longrightarrow> Lc a b = ldlmat A j a b"
    by (auto simp: ldl_outer_pred_def)
  have "j = n" using jn nj by simp
  thus "Lc p q = ldlmat A n p q" using ag pn qn by simp
qed

subsection \<open>Paradigm B for L D L^T: Lammich's refinement framework (\<open>nres\<close>)\<close>

definition ldl_column ::
  "(nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> real) nres" where
  "ldl_column A n c d M \<equiv>
     do { (M', _) \<leftarrow> WHILET (\<lambda>(M, r). r < n)
                      (\<lambda>(M, r). RETURN (M(r := (M r)(c := (A r c - (\<Sum>k<c. M r k * M c k * M k k)) / d)), Suc r))
                      (M, Suc c);
          RETURN M' }"

definition ldl_inner_inv :: "(nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> real) \<times> nat \<Rightarrow> bool" where
  "ldl_inner_inv A n c \<equiv> (\<lambda>(M, r). Suc c \<le> r \<and> r \<le> n
       \<and> (\<forall>i'<n. \<forall>j'<n. (i'<r \<or> j'\<noteq>c) \<longrightarrow> M i' j' = ldlmat A (Suc c) i' j')
       \<and> (\<forall>i'<n. r \<le> i' \<longrightarrow> M i' c = ldlmat A c i' c))"

lemma ldl_column_correct:
  assumes pre1: "\<And>i' j'. i'<n \<Longrightarrow> j'<n \<Longrightarrow> i' < Suc c \<or> j' \<noteq> c \<Longrightarrow> M i' j' = ldlmat A (Suc c) i' j'"
    and pre2: "\<And>i'. i'<n \<Longrightarrow> Suc c \<le> i' \<Longrightarrow> M i' c = ldlmat A c i' c"
    and jn: "Suc c \<le> n" and dd: "d = ldlmat A (Suc c) c c"
  shows "ldl_column A n c d M \<le> SPEC (\<lambda>M'. agree n M' (ldlmat A (Suc c)))"
  unfolding ldl_column_def
  apply (refine_vcg WHILET_rule[where I="ldl_inner_inv A n c"
            and R="Wellfounded.measure (\<lambda>(M, r). n - r)"])
  subgoal by simp
  subgoal using jn pre1 pre2 by (auto simp: ldl_inner_inv_def)
  subgoal premises p for s a b
  proof -
    from p have cc: "ldl_inner_inv A n c (a, b)" and guard: "b < n" by auto
    from cc have inv1: "\<And>i' j'. i'<n \<Longrightarrow> j'<n \<Longrightarrow> i'<b \<or> j'\<noteq>c \<Longrightarrow> a i' j' = ldlmat A (Suc c) i' j'"
      and inv2: "\<And>i'. i'<n \<Longrightarrow> b \<le> i' \<Longrightarrow> a i' c = ldlmat A c i' c"
      and Ib: "Suc c \<le> b" by (auto simp: ldl_inner_inv_def)
    have "(\<forall>i'<n. \<forall>j'<n. (i'<Suc b \<or> j'\<noteq>c) \<longrightarrow>
            (a(b := (a b)(c := (A b c - (\<Sum>k<c. a b k * a c k * a k k)) / d))) i' j' = ldlmat A (Suc c) i' j')
        \<and> (\<forall>i'<n. Suc b \<le> i' \<longrightarrow>
            (a(b := (a b)(c := (A b c - (\<Sum>k<c. a b k * a c k * a k k)) / d))) i' c = ldlmat A c i' c)"
      using ldl_column_inv_step[OF inv1 inv2 Ib guard jn dd] .
    thus "ldl_inner_inv A n c
            (a(b := (a b)(c := (A b c - (\<Sum>k<c. a b k * a c k * a k k)) / d)), Suc b)"
      using Ib guard by (auto simp: ldl_inner_inv_def)
  qed
  subgoal premises p for s a b using p by (auto simp: in_measure)
  subgoal premises p for s a b
  proof -
    from p have cc: "ldl_inner_inv A n c (a, b)" and nb: "\<not> b < n" by auto
    from cc have inv1: "\<And>i' j'. i'<n \<Longrightarrow> j'<n \<Longrightarrow> i'<b \<or> j'\<noteq>c \<Longrightarrow> a i' j' = ldlmat A (Suc c) i' j'"
      and bn: "b \<le> n" by (auto simp: ldl_inner_inv_def)
    have "b = n" using bn nb by simp
    thus "agree n a (ldlmat A (Suc c))" using inv1 by (auto simp: agree_def)
  qed
  done

definition R_ldlt ::
  "(nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> real) nres" where
  "R_ldlt A n \<equiv>
     do { (M, _) \<leftarrow> WHILET (\<lambda>(M, c). c < n)
                     (\<lambda>(M, c). do {
                        ASSERT (0 < A c c - (\<Sum>k<c. (M c k)\<^sup>2 * M k k));
                        let d = A c c - (\<Sum>k<c. (M c k)\<^sup>2 * M k k);
                        let M = M(c := (M c)(c := d));
                        M \<leftarrow> ldl_column A n c d M;
                        RETURN (M, Suc c) })
                     ((\<lambda>x y. 0), 0);
          RETURN M }"

definition ldl_outer_inv :: "(nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> real) \<times> nat \<Rightarrow> bool" where
  "ldl_outer_inv A n \<equiv> (\<lambda>(M, c). c \<le> n \<and> agree n M (ldlmat A c))"

text \<open>As on the \<open>L L^T\<close> side, the pivot positivity is an \<open>ASSERT\<close> discharged from \<^const>\<open>chol_safe\<close>
  (here via @{thm ldl_diag_pos}); the program computes the verified packed factor \<^const>\<open>ldlmat\<close>.\<close>
theorem R_ldlt_correct:
  assumes safe: "chol_safe A n"
  shows "R_ldlt A n \<le> SPEC (\<lambda>M. \<forall>u<n. \<forall>v<n. M u v = ldlmat A n u v)"
  unfolding R_ldlt_def
  apply (refine_vcg WHILET_rule[where I="ldl_outer_inv A n"
            and R="Wellfounded.measure (\<lambda>(M, c). n - c)"]
         ldl_column_correct)
  subgoal by simp
  subgoal by (simp add: ldl_outer_inv_def agree_def)
  \<comment> \<open>ASSERT: the pivot is positive (from \<open>chol_safe\<close>)\<close>
  subgoal premises p for s a b
  proof -
    from p have cc: "agree n a (ldlmat A b)" and guard: "b < n" by (auto simp: ldl_outer_inv_def)
    have seq: "(\<Sum>k<b. (a b k)\<^sup>2 * a k k) = (\<Sum>k<b. (ldlmat A b b k)\<^sup>2 * ldlmat A b k k)"
      using cc guard by (intro sum.cong refl) (auto simp: agree_def)
    have p1: "0 < ldlmat A n b b" using ldl_diag_pos[OF safe guard] .
    have p2: "ldlmat A n b b = A b b - (\<Sum>k<b. (ldlmat A b b k)\<^sup>2 * ldlmat A b k k)"
      using ldlmat_mono[of b "Suc b" n A b] guard by simp
    show "0 < A b b - (\<Sum>k<b. (a b k)\<^sup>2 * a k k)" using p1 p2 seq by simp
  qed
  \<comment> \<open>ldl_column precondition pre1\<close>
  subgoal premises p for s a b i' j'
  proof -
    from p have cc: "agree n a (ldlmat A b)" and guard: "b < n"
      and i'n: "i' < n" and j'n: "j' < n" and ante: "i' < Suc b \<or> j' \<noteq> b"
      by (auto simp: ldl_outer_inv_def)
    have aval: "\<And>i k. i < n \<Longrightarrow> k < n \<Longrightarrow> a i k = ldlmat A b i k" using cc by (auto simp: agree_def)
    have seq: "(\<Sum>k<b. (a b k)\<^sup>2 * a k k) = (\<Sum>k<b. (ldlmat A b b k)\<^sup>2 * ldlmat A b k k)"
      using aval guard by (intro sum.cong refl) auto
    show "(a(b := (a b)(b := A b b - (\<Sum>k<b. (a b k)\<^sup>2 * a k k)))) i' j' = ldlmat A (Suc b) i' j'"
    proof (cases "i' = b")
      case True
      then show ?thesis
      proof (cases "j' = b")
        case True with \<open>i' = b\<close> seq show ?thesis by simp
      next
        case False with \<open>i' = b\<close> guard j'n aval show ?thesis by simp
      qed
    next
      case False
      then show ?thesis
      proof (cases "j' = b")
        case True
        have "i' < b" using ante \<open>i' \<noteq> b\<close> \<open>j' = b\<close> by simp
        with \<open>i' \<noteq> b\<close> \<open>j' = b\<close> i'n guard aval show ?thesis by (simp add: ldlmat_col_ge)
      next
        case False with \<open>i' \<noteq> b\<close> i'n j'n aval show ?thesis by simp
      qed
    qed
  qed
  \<comment> \<open>ldl_column precondition pre2\<close>
  subgoal premises p for s a b i'
  proof -
    from p have cc: "agree n a (ldlmat A b)" and guard: "b < n"
      and i'n: "i' < n" and ge: "Suc b \<le> i'" by (auto simp: ldl_outer_inv_def)
    have "a i' b = ldlmat A b i' b" using cc i'n guard by (auto simp: agree_def)
    thus "(a(b := (a b)(b := A b b - (\<Sum>k<b. (a b k)\<^sup>2 * a k k)))) i' b = ldlmat A b i' b"
      using ge by simp
  qed
  \<comment> \<open>ldl_column precondition \<open>Suc b \<le> n\<close>\<close>
  subgoal premises p for s a b using p by (auto simp: ldl_outer_inv_def)
  \<comment> \<open>ldl_column precondition: the pivot equals \<open>ldlmat A (Suc b) b b\<close>\<close>
  subgoal premises p for s a b
  proof -
    from p have cc: "agree n a (ldlmat A b)" and guard: "b < n" by (auto simp: ldl_outer_inv_def)
    have "(\<Sum>k<b. (a b k)\<^sup>2 * a k k) = (\<Sum>k<b. (ldlmat A b b k)\<^sup>2 * ldlmat A b k k)"
      using cc guard by (intro sum.cong refl) (auto simp: agree_def)
    thus "A b b - (\<Sum>k<b. (a b k)\<^sup>2 * a k k) = ldlmat A (Suc b) b b" by simp
  qed
  \<comment> \<open>outer invariant preserved\<close>
  subgoal premises p for s a b x using p by (auto simp: ldl_outer_inv_def)
  \<comment> \<open>outer measure decreases\<close>
  subgoal premises p for s a b x using p by (auto simp: in_measure)
  \<comment> \<open>exit: the state is the verified packed factor \<^const>\<open>ldlmat\<close>\<close>
  subgoal premises p for s a b u v
  proof -
    from p have cc: "agree n a (ldlmat A b)" and nb: "\<not> b < n" and bn: "b \<le> n"
      and un: "u < n" and vn: "v < n" by (auto simp: ldl_outer_inv_def)
    have "b = n" using bn nb by simp
    thus "a u v = ldlmat A n u v" using cc un vn by (auto simp: agree_def)
  qed
  done

end
