import Mathlib

open Finset

namespace BernsteinWeierstrass

/-- `p n k x = (n choose k) x^k (1-x)^(n-k)`. -/
noncomputable def p (n k : ℕ) (x : ℝ) : ℝ :=
  (n.choose k : ℝ) * x ^ k * (1 - x) ^ (n - k)

/-- The Bernstein polynomial of `f` (as a function). -/
noncomputable def B (f : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range (n + 1), f ((k : ℝ) / n) * p n k x

/-! ### Basic facts about `p` -/

lemma p_eq (n k : ℕ) (x : ℝ) :
    p n k x = (bernsteinPolynomial ℝ n k).eval x := by
  simp [p, bernsteinPolynomial]

lemma p_nonneg {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (n k : ℕ) : 0 ≤ p n k x := by
  obtain ⟨h0, h1⟩ := hx
  unfold p
  exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg h0 _))
    (pow_nonneg (sub_nonneg.2 h1) _)

/-- Partition of unity: `∑ p_{k,n}(x) = 1`. -/
lemma sum_p (n : ℕ) (x : ℝ) : ∑ k ∈ range (n + 1), p n k x = 1 := by
  have h := congrArg (Polynomial.eval x) (bernsteinPolynomial.sum ℝ n)
  simpa [p_eq, Polynomial.eval_finsetSum] using h

/-- Variance identity: `∑ (n x - k)^2 p_{k,n}(x) = n x (1 - x)`. -/
lemma variance_p (n : ℕ) (x : ℝ) :
    ∑ k ∈ range (n + 1), ((n : ℝ) * x - k) ^ 2 * p n k x = n * x * (1 - x) := by
  have h := congrArg (Polynomial.eval x) (bernsteinPolynomial.variance ℝ n)
  simpa [p_eq, Polynomial.eval_finsetSum] using h

/-- Rescaled variance: `∑ (k/n - x)^2 p_{k,n}(x) = x (1 - x) / n`. -/
lemma variance_div {n : ℕ} (hn : 0 < n) (x : ℝ) :
    ∑ k ∈ range (n + 1), ((k : ℝ) / n - x) ^ 2 * p n k x = x * (1 - x) / n := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have h := variance_p n x
  have key : ∀ k ∈ range (n + 1),
      ((k : ℝ) / n - x) ^ 2 * p n k x
        = (1 / (n : ℝ) ^ 2) * (((n : ℝ) * x - k) ^ 2 * p n k x) := by
    intro k _
    first
      | (field_simp; ring)
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, h]
  field_simp

lemma div_mem_Icc {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    (k : ℝ) / n ∈ Set.Icc (0:ℝ) 1 := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  constructor
  · positivity
  · rw [div_le_one hn']
    exact_mod_cast hk

/-! ### Step 1: termwise estimate (near / far split) -/

/-- If `|y - x| < δ` use uniform continuity; otherwise use the bound `2C`
and `1 ≤ (y - x)^2 / δ^2`. -/
lemma pointwise_bound {f : ℝ → ℝ} {C ε δ : ℝ}
    (hC : ∀ y ∈ Set.Icc (0 : ℝ) 1, |f y| ≤ C)
    (hδ : 0 < δ)
    (hunif : ∀ y ∈ Set.Icc (0 : ℝ) 1, ∀ z ∈ Set.Icc (0 : ℝ) 1,
      |y - z| < δ → |f y - f z| < ε / 2)
    {y x : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |f y - f x| ≤ ε / 2 + 2 * C / δ ^ 2 * (y - x) ^ 2 := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0 ⟨le_rfl, zero_le_one⟩)
  have hnn : 0 ≤ 2 * C / δ ^ 2 * (y - x) ^ 2 :=
    mul_nonneg (div_nonneg (by linarith) (sq_nonneg δ)) (sq_nonneg _)
  by_cases h : |y - x| < δ
  · have := hunif y hy x hx h
    linarith
  · push Not at h
    have h1 : |f y - f x| ≤ 2 * C := by
      have := abs_add_le (f y) (-f x)
      simp only [abs_neg, ← sub_eq_add_neg] at this
      linarith [hC y hy, hC x hx]
    have h2 : δ ^ 2 ≤ (y - x) ^ 2 := by
      have : δ ^ 2 ≤ |y - x| ^ 2 := pow_le_pow_left₀ hδ.le h 2
      simpa [sq_abs] using this
    have h3 : 2 * C ≤ 2 * C / δ ^ 2 * (y - x) ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (sq_pos_of_pos hδ)]
      exact mul_le_mul_of_nonneg_left h2 (by linarith)
    have hε : 0 ≤ ε := by
      have h := hunif y hy y hy (by simpa using hδ)
      simp only [sub_self, abs_zero] at h
      linarith
    linarith

/-! ### Step 2: summing against the weights -/

lemma bernstein_error {f : ℝ → ℝ} {C ε δ : ℝ}
    (hC : ∀ y ∈ Set.Icc (0 : ℝ) 1, |f y| ≤ C)
    (hδ : 0 < δ)
    (hunif : ∀ y ∈ Set.Icc (0 : ℝ) 1, ∀ z ∈ Set.Icc (0 : ℝ) 1,
      |y - z| < δ → |f y - f z| < ε / 2)
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |B f n x - f x| ≤ ε / 2 + C / (2 * δ ^ 2 * n) := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0 ⟨le_rfl, zero_le_one⟩)
  have hsum := sum_p n x
  have hrepr : B f n x - f x
      = ∑ k ∈ range (n + 1), (f ((k : ℝ) / n) - f x) * p n k x := by
    simp only [B, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, mul_one]
  have hpos : 0 ≤ 2 * C / δ ^ 2 := div_nonneg (by linarith) (sq_nonneg δ)
  calc |B f n x - f x|
      = |∑ k ∈ range (n + 1), (f ((k : ℝ) / n) - f x) * p n k x| := by rw [hrepr]
    _ ≤ ∑ k ∈ range (n + 1), |(f ((k : ℝ) / n) - f x) * p n k x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range (n + 1),
          (ε / 2 + 2 * C / δ ^ 2 * ((k : ℝ) / n - x) ^ 2) * p n k x := by
        apply Finset.sum_le_sum
        intro k hk
        have hk' : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
        rw [abs_mul, abs_of_nonneg (p_nonneg hx n k)]
        exact mul_le_mul_of_nonneg_right
          (pointwise_bound hC hδ hunif (div_mem_Icc hn hk') hx) (p_nonneg hx n k)
    _ = ε / 2 * ∑ k ∈ range (n + 1), p n k x
          + 2 * C / δ ^ 2 * ∑ k ∈ range (n + 1), ((k : ℝ) / n - x) ^ 2 * p n k x := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
    _ = ε / 2 + 2 * C / δ ^ 2 * (x * (1 - x) / n) := by
        rw [hsum, variance_div hn x, mul_one]
    _ ≤ ε / 2 + 2 * C / δ ^ 2 * ((1 / 4) / n) := by
        have hxx : x * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg (x - 1 / 2)]
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        gcongr
    _ = ε / 2 + C / (2 * δ ^ 2 * n) := by
        have hδ0 : δ ≠ 0 := hδ.ne'
        have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
        first
          | (congr 1; field_simp; ring)

/-! ### Step 3: conclusion -/

/-- **Weierstrass via Bernstein polynomials**: `B_n f → f` uniformly on `[0,1]`. -/
theorem bernstein_uniform_convergence (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc 0 1)) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ Set.Icc (0:ℝ) 1, |B f n x - f x| < ε := by
  -- boundedness
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hC' : ∀ y ∈ Set.Icc (0:ℝ) 1, |f y| ≤ C := fun y hy => by
    simpa using hC y hy
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC' 0 ⟨le_rfl, zero_le_one⟩)
  -- uniform continuity
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous hf
  rw [Metric.uniformContinuousOn_iff] at hu
  obtain ⟨δ, hδ, hδ'⟩ := hu (ε / 2) (by positivity)
  have hunif : ∀ y ∈ Set.Icc (0:ℝ) 1, ∀ z ∈ Set.Icc (0:ℝ) 1,
      |y - z| < δ → |f y - f z| < ε / 2 := by
    intro y hy z hz h
    simpa [Real.dist_eq] using hδ' y hy z hz (by simpa [Real.dist_eq] using h)
  -- choose N
  obtain ⟨N, hN⟩ := exists_nat_gt (C / (δ ^ 2 * ε))
  refine ⟨N, fun n hn x hx => ?_⟩
  have hn' : C / (δ ^ 2 * ε) < n := lt_of_lt_of_le hN (by exact_mod_cast hn)
  have hnpos : (0 : ℝ) < n :=
    lt_of_le_of_lt (div_nonneg hC0 (by positivity)) hn'
  have hnN : 0 < n := Nat.cast_pos.1 hnpos
  have hlt : C / (2 * δ ^ 2 * n) < ε / 2 := by
    rw [div_lt_iff₀ (by positivity)]
    have h := (div_lt_iff₀ (by positivity : 0 < δ ^ 2 * ε)).1 hn'
    calc C < n * (δ ^ 2 * ε) := h
      _ = ε / 2 * (2 * δ ^ 2 * n) := by ring
  have := bernstein_error hC' hδ hunif hnN hx
  linarith

/-! ### Step 4: `B n f` really is a polynomial -/

lemma B_isPoly (f : ℝ → ℝ) (n : ℕ) :
    ∃ P : Polynomial ℝ, ∀ x, P.eval x = B f n x := by
  refine ⟨∑ k ∈ range (n + 1),
    Polynomial.C (f ((k : ℝ) / n)) * bernsteinPolynomial ℝ n k, fun x => ?_⟩
  simp [B, p_eq, Polynomial.eval_finsetSum]

/-- **Weierstrass Approximation Theorem** on `[0,1]`. -/
theorem weierstrass_unit_interval (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc 0 1)) (ε : ℝ) (hε : 0 < ε) :
    ∃ P : Polynomial ℝ, ∀ x ∈ Set.Icc (0:ℝ) 1, |P.eval x - f x| < ε := by
  obtain ⟨N, hN⟩ := bernstein_uniform_convergence f hf ε hε
  obtain ⟨P, hP⟩ := B_isPoly f (N + 1)
  exact ⟨P, fun x hx => by rw [hP]; exact hN (N + 1) (by omega) x hx⟩

end BernsteinWeierstrass

#print axioms BernsteinWeierstrass.weierstrass_unit_interval
