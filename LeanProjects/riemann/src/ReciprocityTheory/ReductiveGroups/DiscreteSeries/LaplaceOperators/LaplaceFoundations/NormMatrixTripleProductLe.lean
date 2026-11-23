import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.RaisingLoweringNormIdentities

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.ConjugationTaylorBound

open scoped Nat

section Abstract

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]

theorem norm_exp_sub_one_sub_le (x : 𝔸) :
    ‖NormedSpace.exp x - 1 - x‖ ≤ ‖x‖ ^ 2 * Real.exp ‖x‖ := by
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) x
  have h2 := (hasSum_nat_add_iff' 2).mpr h
  have e : ∑ i ∈ Finset.range 2, ((i !⁻¹ : ℂ) • x ^ i) = 1 + x := by
    simp [Finset.sum_range_succ]
  rw [e, ← sub_sub] at h2
  have hr := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖
  rw [← Real.exp_eq_exp_ℝ] at hr
  have hg := hr.mul_left (‖x‖ ^ 2)
  refine h2.norm_le_of_bounded hg ?_
  intro m
  rw [norm_smul, norm_inv, Complex.norm_natCast, smul_eq_mul]
  have hf : ((m + 2)! : ℝ)⁻¹ ≤ ((m ! : ℕ) : ℝ)⁻¹ := by
    apply inv_anti₀ (by exact_mod_cast Nat.factorial_pos m)
    exact_mod_cast Nat.factorial_le (by omega)
  have hp : ‖x ^ (m + 2)‖ ≤ ‖x‖ ^ (m + 2) := norm_pow_le' x (by omega)
  calc ((((m + 2)! : ℕ) : ℝ))⁻¹ * ‖x ^ (m + 2)‖ ≤ ((m ! : ℕ) : ℝ)⁻¹ * ‖x‖ ^ (m + 2) :=
        mul_le_mul hf hp (norm_nonneg _) (by positivity)
    _ = ‖x‖ ^ 2 * (((m ! : ℕ) : ℝ)⁻¹ * ‖x‖ ^ m) := by ring

theorem conj_identity (a b u M : 𝔸) :
    a * M * b - M - (u * M - M * u) =
      M * (b - 1 + u) - u * M * u + u * M * (b - 1 + u) + (a - 1 - u) * M -
        (a - 1 - u) * M * u + (a - 1 - u) * M * (b - 1 + u) := by
  noncomm_ring

theorem norm_six (a b c d e f : 𝔸) :
    ‖a - b + c + d - e + f‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ := by
  have h1 := norm_add_le (a - b + c + d - e) f
  have h2 := norm_sub_le (a - b + c + d) e
  have h3 := norm_add_le (a - b + c) d
  have h4 := norm_add_le (a - b) c
  have h5 := norm_sub_le a b
  linarith

theorem norm_matrix_triple_product_le (x y z : 𝔸) : ‖x * y * z‖ ≤ ‖x‖ * ‖y‖ * ‖z‖ :=
  (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))

theorem le3 {a b c A B C : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h1 : a ≤ A) (h2 : b ≤ B)
    (h3 : c ≤ C) : a * b * c ≤ A * B * C :=
  mul_le_mul (mul_le_mul h1 h2 hb (ha.trans h1)) h3 hc (mul_nonneg (ha.trans h1) (hb.trans h2))

theorem conj_taylor (Y M : 𝔸) (τ r m : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hY : ‖Y‖ ≤ r)
    (hM : ‖M‖ ≤ m) :
    ‖NormedSpace.exp ((τ : ℂ) • Y) * M * NormedSpace.exp (-((τ : ℂ) • Y)) - M -
        (τ : ℂ) • (Y * M - M * Y)‖ ≤
      m * (2 * r ^ 2 * Real.exp r + r ^ 2 + 2 * r ^ 3 * Real.exp r + r ^ 4 * Real.exp r ^ 2) *
        τ ^ 2 := by
  set u : 𝔸 := (τ : ℂ) • Y with hu
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hY
  have hm0 : 0 ≤ m := (norm_nonneg _).trans hM
  have hsm : (τ : ℂ) • (Y * M - M * Y) = u * M - M * u := by
    rw [hu, smul_sub, smul_mul_assoc, mul_smul_comm]
  rw [hsm, conj_identity]
  set p : ℝ := τ * r with hp
  set E : ℝ := Real.exp r with hE
  set q : ℝ := p ^ 2 * E with hq
  have hp0 : 0 ≤ p := mul_nonneg hτ0 hr0
  have hE0 : 0 ≤ E := (Real.exp_pos r).le
  have hq0 : 0 ≤ q := mul_nonneg (pow_nonneg hp0 2) hE0
  have hu' : ‖u‖ ≤ p := by
    rw [hu, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hτ0]
    exact mul_le_mul_of_nonneg_left hY hτ0
  have hexp : Real.exp ‖u‖ ≤ E := by
    apply Real.exp_le_exp.mpr
    calc ‖u‖ ≤ p := hu'
      _ ≤ r := by rw [hp]; nlinarith
  have hA : ‖NormedSpace.exp u - 1 - u‖ ≤ q := by
    refine (norm_exp_sub_one_sub_le u).trans ?_
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hu' 2) hexp (Real.exp_pos _).le
      (pow_nonneg hp0 2)
  have hB : ‖NormedSpace.exp (-u) - 1 + u‖ ≤ q := by
    have := norm_exp_sub_one_sub_le (-u)
    rw [sub_neg_eq_add, norm_neg] at this
    refine this.trans ?_
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hu' 2) hexp (Real.exp_pos _).le
      (pow_nonneg hp0 2)
  set A := NormedSpace.exp u - 1 - u
  set B := NormedSpace.exp (-u) - 1 + u
  have t1 : ‖M * B‖ ≤ m * q :=
    (norm_mul_le _ _).trans (mul_le_mul hM hB (norm_nonneg _) hm0)
  have t2 : ‖u * M * u‖ ≤ p * m * p :=
    (norm_matrix_triple_product_le _ _ _).trans (le3 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hu' hM hu')
  have t3 : ‖u * M * B‖ ≤ p * m * q :=
    (norm_matrix_triple_product_le _ _ _).trans (le3 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hu' hM hB)
  have t4 : ‖A * M‖ ≤ q * m :=
    (norm_mul_le _ _).trans (mul_le_mul hA hM (norm_nonneg _) hq0)
  have t5 : ‖A * M * u‖ ≤ q * m * p :=
    (norm_matrix_triple_product_le _ _ _).trans (le3 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hA hM hu')
  have t6 : ‖A * M * B‖ ≤ q * m * q :=
    (norm_matrix_triple_product_le _ _ _).trans (le3 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hA hM hB)
  refine (norm_six _ _ _ _ _ _).trans ?_
  have hτ3 : τ ^ 3 ≤ τ ^ 2 := pow_le_pow_of_le_one hτ0 hτ1 (by norm_num)
  have hτ4 : τ ^ 4 ≤ τ ^ 2 := pow_le_pow_of_le_one hτ0 hτ1 (by norm_num)
  have key : m * q + p * m * p + p * m * q + q * m + q * m * p + q * m * q =
      m * (2 * r ^ 2 * E * τ ^ 2 + r ^ 2 * τ ^ 2 + 2 * r ^ 3 * E * τ ^ 3 + r ^ 4 * E ^ 2 * τ ^ 4) := by
    rw [hq, hp]; ring
  have c3 : 2 * r ^ 3 * E * τ ^ 3 ≤ 2 * r ^ 3 * E * τ ^ 2 :=
    mul_le_mul_of_nonneg_left hτ3 (by positivity)
  have c4 : r ^ 4 * E ^ 2 * τ ^ 4 ≤ r ^ 4 * E ^ 2 * τ ^ 2 :=
    mul_le_mul_of_nonneg_left hτ4 (by positivity)
  have fin : m * q + p * m * p + p * m * q + q * m + q * m * p + q * m * q ≤
      m * (2 * r ^ 2 * E + r ^ 2 + 2 * r ^ 3 * E + r ^ 4 * E ^ 2) * τ ^ 2 := by
    rw [key]
    have := mul_le_mul_of_nonneg_left (add_le_add (add_le_add (le_refl
      (2 * r ^ 2 * E * τ ^ 2 + r ^ 2 * τ ^ 2)) c3) c4) hm0
    linarith
  linarith

end Abstract

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.ConjugationTaylorBound

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.ConjugationTaylorBound

section Op

open scoped NNReal

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}

theorem entry_le_op (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : ‖A i j‖ ≤ ‖A‖ := by
  have h : ‖A i j‖₊ ≤ ‖A‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    refine le_trans ?_ (Finset.le_sup (f := fun i : Fin n => ∑ j : Fin n, ‖A i j‖₊)
      (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j => ‖A i j‖₊) (fun _ _ => bot_le) (Finset.mem_univ j)
  exact_mod_cast h

theorem op_le_of_entry (A : Matrix (Fin n) (Fin n) ℂ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ i j, ‖A i j‖ ≤ c) : ‖A‖ ≤ n * c := by
  have h' : ‖A‖₊ ≤ (n : ℝ≥0) * c.toNNReal := by
    rw [Matrix.linfty_opNNNorm_def]
    apply Finset.sup_le
    intro i _
    calc ∑ j, ‖A i j‖₊ ≤ ∑ _j : Fin n, c.toNNReal :=
          Finset.sum_le_sum fun j _ => (by
            have := Real.toNNReal_le_toNNReal (h i j)
            rwa [norm_toNNReal] at this)
      _ = (n : ℝ≥0) * c.toNNReal := by simp
  have := NNReal.coe_le_coe.mpr h'
  push_cast [Real.coe_toNNReal _ hc] at this
  exact this

theorem conj_taylor_entry (R : ℝ) (hR : 0 ≤ R) (Y M : Matrix (Fin n) (Fin n) ℂ)
    (hY : ∀ i j, ‖Y i j‖ ≤ R) (hM : ∀ i j, ‖M i j‖ ≤ R) (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (i j : Fin n) :
    ‖(NormedSpace.exp ((τ : ℂ) • Y) * M * NormedSpace.exp (-((τ : ℂ) • Y)) - M -
        (τ : ℂ) • (Y * M - M * Y)) i j‖ ≤
      (n * R) * (2 * (n * R) ^ 2 * Real.exp (n * R) + (n * R) ^ 2 +
        2 * (n * R) ^ 3 * Real.exp (n * R) + (n * R) ^ 4 * Real.exp (n * R) ^ 2) * τ ^ 2 :=
  (entry_le_op _ i j).trans
    (conj_taylor Y M τ (n * R) (n * R) hτ0 hτ1 (op_le_of_entry Y R hR hY)
      (op_le_of_entry M R hR hM))

end Op

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.ConjugationTaylorBound

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

open ConjugationTaylorBound in
theorem b3c : ConjugationSecondOrderBound := by
  intro n R
  have hR : (0 : ℝ) ≤ max R 0 := le_max_right _ _
  refine ⟨(n * max R 0) * (2 * (n * max R 0) ^ 2 * Real.exp (n * max R 0) + (n * max R 0) ^ 2 +
        2 * (n * max R 0) ^ 3 * Real.exp (n * max R 0) +
        (n * max R 0) ^ 4 * Real.exp (n * max R 0) ^ 2), by positivity, ?_⟩
  intro Y M hY hM τ h0 h1
  have hY' : ∀ i j, ‖Y i j‖ ≤ max R 0 := fun i j =>
    (Matrix.norm_entry_le_entrywise_sup_norm Y).trans (hY.trans (le_max_left _ _))
  have hM' : ∀ i j, ‖M i j‖ ≤ max R 0 := fun i j =>
    (Matrix.norm_entry_le_entrywise_sup_norm M).trans (hM.trans (le_max_left _ _))
  exact (Matrix.norm_le_iff (by positivity)).2
    (fun i j => conj_taylor_entry (max R 0) hR Y M hY' hM' τ h0 h1 i j)

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
