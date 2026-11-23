import Mathlib

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.TB.Mink

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory ENNReal Module
open scoped nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

theorem exists_small_mem_ideal (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    ∃ a : 𝓞 K, a ∈ I ∧ a ≠ 0 ∧ ∀ w : InfinitePlace K,
      w (a : K) < 3 * ((Ideal.absNorm I : ℝ) * Real.sqrt |(discr K : ℝ)|) ^ ((finrank ℚ K : ℝ)⁻¹) := by
  classical
  set n := finrank ℚ K with hn_def
  have hn : 0 < n := finrank_pos
  have hN : 0 < (Ideal.absNorm I : ℝ) := Nat.cast_pos.2 (Ideal.absNorm_pos_iff_mem_nonZeroDivisors.2
    (mem_nonZeroDivisors_of_ne_zero (by simpa using hI)))
  have hD : 0 < Real.sqrt |(discr K : ℝ)| :=
    Real.sqrt_pos.2 (abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K)))
  set X : ℝ := (Ideal.absNorm I : ℝ) * Real.sqrt |(discr K : ℝ)| with hX_def
  have hX : 0 < X := mul_pos hN hD
  set R : ℝ := 3 * X ^ ((n : ℝ)⁻¹) with hR_def
  have hR : 0 < R := by positivity
  have hRn : R ^ n = 3 ^ n * X := by
    rw [hR_def, mul_pow, ← Real.rpow_natCast (X ^ ((n : ℝ)⁻¹)), ← Real.rpow_mul hX.le,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn.ne'), Real.rpow_one]
  let J : (FractionalIdeal (𝓞 K)⁰ K)ˣ := Units.mk0 (I : FractionalIdeal (𝓞 K)⁰ K) (FractionalIdeal.coeIdeal_ne_zero.2 hI)
  let f : InfinitePlace K → NNReal := fun _ => ⟨R, hR.le⟩
  have hL : (minkowskiBound K J).toReal =
      (Ideal.absNorm I : ℝ) * (2 : ℝ)⁻¹ ^ nrComplexPlaces K * Real.sqrt |(discr K : ℝ)| * 2 ^ n := by
    simp_rw [minkowskiBound, volume_fundamentalDomain_fractionalIdealLatticeBasis,
      volume_fundamentalDomain_latticeBasis, toReal_mul, toReal_pow, toReal_inv, coe_toReal, toReal_ofNat,
      mixedEmbedding.finrank]
    rw [ENNReal.toReal_ofReal (Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg _))]
    simp only [J, Units.val_mk0, FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast, Real.coe_sqrt, coe_nnnorm,
      Int.norm_eq_abs]
    ring
  have hV : volume (convexBodyLT K f) ≠ ⊤ := by
    rw [convexBodyLT_volume]; exact mul_ne_top coe_ne_top coe_ne_top
  have hR' : (volume (convexBodyLT K f)).toReal = (convexBodyLTFactor K : ℝ) * R ^ n := by
    rw [convexBodyLT_volume, toReal_mul, coe_toReal, coe_toReal]
    congr 1
    rw [NNReal.coe_prod]
    have e : ∀ x : InfinitePlace K, ((f x ^ x.mult : NNReal) : ℝ) = R ^ x.mult := fun x => by
      rw [NNReal.coe_pow]; rfl
    rw [Finset.prod_congr rfl fun x _ => e x, Finset.prod_pow_eq_pow_sum, sum_mult_eq]
  have h : minkowskiBound K J < volume (convexBodyLT K f) := by
    rw [← ENNReal.toReal_lt_toReal (minkowskiBound_lt_top K J).ne hV, hL, hR', hRn]
    have h1 : (1 : ℝ) ≤ convexBodyLTFactor K := by exact_mod_cast one_le_convexBodyLTFactor K
    have h2 : (2 : ℝ)⁻¹ ^ nrComplexPlaces K ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have h3 : (2 : ℝ) ^ n < 3 ^ n := pow_lt_pow_left₀ (by norm_num) (by norm_num) hn.ne'
    calc (Ideal.absNorm I : ℝ) * (2 : ℝ)⁻¹ ^ nrComplexPlaces K * Real.sqrt |(discr K : ℝ)| * 2 ^ n
        = (X * 2 ^ n) * (2 : ℝ)⁻¹ ^ nrComplexPlaces K := by rw [hX_def]; ring
      _ ≤ (X * 2 ^ n) * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = X * 2 ^ n := by ring
      _ < X * 3 ^ n := mul_lt_mul_of_pos_left h3 hX
      _ = 1 * (3 ^ n * X) := by ring
      _ ≤ (convexBodyLTFactor K : ℝ) * (3 ^ n * X) := mul_le_mul_of_nonneg_right h1 (by positivity)
  obtain ⟨a, ha, hne, hlt⟩ := exists_ne_zero_mem_ideal_lt K J h
  rw [Units.val_mk0, FractionalIdeal.mem_coeIdeal] at ha
  obtain ⟨x, hx, rfl⟩ := ha
  refine ⟨x, hx, fun h0 => hne (by rw [h0, map_zero]), fun w => ?_⟩
  exact hlt w

theorem exists_small_mem_ideal' (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    ∃ a : 𝓞 K, a ∈ I ∧ a ≠ 0 ∧ ∀ σ : K →+* ℂ,
      ‖σ (a : K)‖ < 3 * ((Ideal.absNorm I : ℝ) * Real.sqrt |(discr K : ℝ)|) ^ ((finrank ℚ K : ℝ)⁻¹) := by
  obtain ⟨a, ha, hne, hlt⟩ := exists_small_mem_ideal K I hI
  exact ⟨a, ha, hne, fun σ => (InfinitePlace.apply σ (a : K)).symm ▸ hlt (InfinitePlace.mk σ)⟩

end ReciprocityTheory.ChartRestriction.G.TB.Mink
