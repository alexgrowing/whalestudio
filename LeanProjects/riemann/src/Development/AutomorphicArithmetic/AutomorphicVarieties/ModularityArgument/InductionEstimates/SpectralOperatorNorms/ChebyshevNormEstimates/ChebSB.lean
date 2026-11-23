import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.KillExempt

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem chebyshev_image_norm_le {A B : Type} [CommRing A] [Algebra ℂ A] [NormedRing B] (φ : A →+* B)
    (h1 : ‖(1 : B)‖ ≤ 1) (y : A) (r : ℝ) (hr : ‖φ y‖ ≤ r) (m : ℕ) :
    ‖φ (Polynomial.aeval y (Polynomial.Chebyshev.T ℂ (m : ℤ)))‖ ≤ (2 * r + 1) ^ m := by
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hr
  induction m using Nat.twoStepInduction with
  | zero => simpa using h1
  | one =>
    have : ‖φ y‖ ≤ 2 * r + 1 := by linarith
    simpa using this
  | more m ih0 ih1 =>
    have e : Polynomial.Chebyshev.T ℂ ((m + 2 : ℕ) : ℤ) =
        Polynomial.X * Polynomial.Chebyshev.T ℂ ((m + 1 : ℕ) : ℤ) +
          Polynomial.X * Polynomial.Chebyshev.T ℂ ((m + 1 : ℕ) : ℤ) - Polynomial.Chebyshev.T ℂ (m : ℤ) := by
      push_cast
      rw [Polynomial.Chebyshev.T_add_two]
      ring
    rw [e, map_sub, map_add, map_mul, Polynomial.aeval_X, map_sub, map_add, map_mul]
    set u := φ (Polynomial.aeval y (Polynomial.Chebyshev.T ℂ ((m + 1 : ℕ) : ℤ)))
    set v := φ (Polynomial.aeval y (Polynomial.Chebyshev.T ℂ (m : ℤ)))
    have hp : ‖φ y * u‖ ≤ r * (2 * r + 1) ^ (m + 1) :=
      (norm_mul_le _ _).trans (mul_le_mul hr ih1 (norm_nonneg _) hr0)
    have hq : (2 * r + 1) ^ m ≤ (2 * r + 1) ^ (m + 1) :=
      pow_le_pow_right₀ (by linarith) (Nat.le_succ m)
    have h2 := norm_sub_le (φ y * u + φ y * u) v
    have h3 := norm_add_le (φ y * u) (φ y * u)
    have h4 : (2 * r + 1) ^ (m + 2) = (2 * r + 1) * (2 * r + 1) ^ (m + 1) := by ring
    rw [h4]
    linarith

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.chebSB :
    ∀ {K : Type} [Field K] [NumberField K] {n d : ℕ} (evz : ℂ → PR K n →+* (Eu d →L[ℂ] Eu d)), (∀ z (c : ℂ), evz z (C (C c)) = c • 1) → ∀ M₀, SB (fun z => evz z (C (X none))) M₀ →
      ∃ M₁ : ℝ, 4 ≤ M₁ ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ m : ℕ, SB (fun z => evz z (chebP η m)) ((M₁ / η) ^ m) := by
  intro K _ _ n d evz hc M₀ hM
  have hM0 : 0 ≤ M₀ := (norm_nonneg _).trans (hM 0 (by simp))
  refine ⟨4 * M₀ + 4, by linarith, fun η hη hη1 m z hz => ?_⟩
  have h1 : ‖(1 : Eu d →L[ℂ] Eu d)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hX : ‖evz z (C (X none))‖ ≤ M₀ := hM z hz
  have h2η : 0 ≤ 2 / η := by positivity
  have hy : ‖((evz z).comp C) (C ((2 / η : ℝ) : ℂ) * X none - 1 : MvPolynomial (Option (Ix K n)) ℂ)‖
      ≤ 2 / η * M₀ + 1 := by
    rw [map_sub, map_mul, map_one, RingHom.comp_apply, RingHom.comp_apply, hc, smul_mul_assoc, one_mul]
    refine (norm_sub_le _ _).trans (add_le_add ?_ h1)
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg h2η]
    exact mul_le_mul_of_nonneg_left hX h2η
  have := chebyshev_image_norm_le ((evz z).comp C) h1 _ _ hy m
  refine this.trans (pow_le_pow_left₀ (by positivity) ?_ m)
  have h4 : 4 ≤ 4 / η := by rw [le_div_iff₀ hη]; linarith
  have e : (4 * M₀ + 4) / η = 2 * (2 / η * M₀) + 4 / η := by ring
  rw [e]
  linarith
