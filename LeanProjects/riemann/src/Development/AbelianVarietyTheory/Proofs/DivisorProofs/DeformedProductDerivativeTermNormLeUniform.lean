import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DTermOrigin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdNormSq

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum

namespace GlobalTheory.DeformedSum.Bound

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem defCoord_lower (φ : I → E →+* ℂ) (z : I → ℂ) (x : E) (i : I) {r : ℝ} (hz : ‖z i‖ ≤ r) :
    (1 - r) * ‖φ i x‖ ≤ ‖defCoord φ z x i‖ := by
  have h1 : ‖z i * starRingEnd ℂ (φ i x)‖ = ‖z i‖ * ‖φ i x‖ := by rw [norm_mul, Complex.norm_conj]
  have h2 := norm_sub_norm_le (φ i x) (-(z i * starRingEnd ℂ (φ i x)))
  rw [norm_neg, h1, sub_neg_eq_add] at h2
  unfold defCoord
  nlinarith [norm_nonneg (φ i x)]

theorem factor_le (φ : I → E →+* ℂ) (k : ℕ) (m : I → ℕ) (z : I → ℂ) (x : E) (hx : x ≠ 0) (i : I) {r : ℝ} (hr : r < 1)
    (hz : ‖z i‖ ≤ r) :
    ‖((-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), ((k : ℂ) + j)) * (starRingEnd ℂ (φ i x)) ^ m i *
        (defCoord φ z x i)⁻¹ ^ (k + m i)‖ ≤
      ‖(-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), ((k : ℂ) + j)‖ * ((1 - r)⁻¹) ^ (k + m i) * (‖φ i x‖⁻¹) ^ k := by
  have hp : 0 < ‖φ i x‖ := by simpa using hx
  have hr' : 0 < 1 - r := by linarith
  have hl := defCoord_lower φ z x i hz
  have hd : 0 < ‖defCoord φ z x i‖ := lt_of_lt_of_le (mul_pos hr' hp) hl
  have hinv : ‖defCoord φ z x i‖⁻¹ ≤ (1 - r)⁻¹ * ‖φ i x‖⁻¹ := by
    rw [← mul_inv]; exact inv_anti₀ (mul_pos hr' hp) hl
  rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj, norm_inv]
  rw [mul_assoc, mul_assoc]
  gcongr ‖_‖ * ?_
  calc ‖φ i x‖ ^ m i * ‖defCoord φ z x i‖⁻¹ ^ (k + m i)
      ≤ ‖φ i x‖ ^ m i * ((1 - r)⁻¹ * ‖φ i x‖⁻¹) ^ (k + m i) := by gcongr
    _ = (1 - r)⁻¹ ^ (k + m i) * ‖φ i x‖⁻¹ ^ k := by
      rw [mul_pow, pow_add ‖φ i x‖⁻¹]
      have : ‖φ i x‖ ^ m i * ‖φ i x‖⁻¹ ^ m i = 1 := by rw [← mul_pow, mul_inv_cancel₀ hp.ne', one_pow]
      calc ‖φ i x‖ ^ m i * ((1 - r)⁻¹ ^ (k + m i) * (‖φ i x‖⁻¹ ^ k * ‖φ i x‖⁻¹ ^ m i))
          = (1 - r)⁻¹ ^ (k + m i) * ‖φ i x‖⁻¹ ^ k * (‖φ i x‖ ^ m i * ‖φ i x‖⁻¹ ^ m i) := by ring
        _ = _ := by rw [this, mul_one]

theorem dTerm_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    IsCMType φ → ∀ (s : ℕ) (m : I → ℕ) (r : ℝ), r < 1 → ∃ C : ℝ, ∀ z : I → ℂ, (∀ i, ‖z i‖ ≤ r) → ∀ x : E, x ≠ 0 →
      ‖dTerm φ (2 * s) m z x‖ ≤ C * |(Algebra.norm ℚ x : ℝ)| ^ (-(s : ℝ)) := by
  intro E _ _ _ I _ φ hφ s m r hr
  refine ⟨∏ i, (‖(-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), (((2 * s : ℕ) : ℂ) + j)‖ * ((1 - r)⁻¹) ^ (2 * s + m i)),
    fun z hz x hx => ?_⟩
  have hN : |(Algebra.norm ℚ x : ℝ)| ^ (-(s : ℝ)) = ∏ i, (‖φ i x‖⁻¹) ^ (2 * s) := by
    rw [← TermUnit.prod_norm_sq hφ x, Real.rpow_neg (Finset.prod_nonneg fun i _ => by positivity), Real.rpow_natCast,
      ← Finset.prod_pow, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [pow_mul, inv_pow, inv_pow]
  rw [hN, ← Finset.prod_mul_distrib, dTerm, norm_prod]
  refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
  exact factor_le φ (2 * s) m z x hx i hr (hz i)

end GlobalTheory.DeformedSum.Bound
