import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelGaussianPairStandardGaussianStatement
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

theorem GlobalTheory.vacuum_coef_sq : ∀ (l : Type) [Fintype l] [DecidableEq l] (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (P Q : Matrix l l ℂ), (∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ)) → (∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ)) → P.det ≠ 0 → GlobalTheory.IsSiegel (-(Q * P⁻¹)) → ∀ c : ℂ, c ^ 2 * P.det = 1 → (∫ x : l → ℝ, c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (-(Q * P⁻¹)) *ᵥ fun i => (x i : ℂ))) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)))) ^ 2 * (GlobalTheory.Published.Metaplectic.holPart s).det = (∫ x : l → ℝ, cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)))) ^ 2 := by
  intro l _ _ s P Q hP hQ hdet hS c hc
  set K := (∫ x : l → ℝ, c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (-(Q * P⁻¹)) *ᵥ fun i => (x i : ℂ))) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ))))
  set J := (∫ x : l → ℝ, cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ))))
  have h1 := GlobalTheory.T.siegelGaussian_pair_standardGaussian l (-(Q * P⁻¹)) c hS
  have hSI : GlobalTheory.IsSiegel ((I • (1 : Matrix l l ℂ))) := by
    refine ⟨?_, ?_⟩
    · simp [Matrix.IsSymm]
    · have : ((I • (1 : Matrix l l ℂ)).map Complex.im) = 1 := by
        ext i j; by_cases h : i = j <;> simp [h, Matrix.one_apply]
      rw [this]; exact Matrix.PosDef.one
  have h2 := GlobalTheory.T.siegelGaussian_pair_standardGaussian l (I • (1 : Matrix l l ℂ)) 1 hSI
  have hJ : (∫ x : l → ℝ, (1:ℂ) * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (I • (1 : Matrix l l ℂ)) *ᵥ fun i => (x i : ℂ))) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)))) = J := by
    congr 1; ext x
    congr 2
    rw [one_mul]; congr 1
    rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul]
    simp only [dotProduct, smul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul]
    rw [← mul_assoc, mul_assoc _ I I, I_mul_I]; ring
  rw [hJ] at h2
  have hdet2 : (1 - I • (I • (1 : Matrix l l ℂ))).det = 2 ^ Fintype.card l := by
    have : (1 - I • (I • (1 : Matrix l l ℂ))) = (2:ℂ) • (1 : Matrix l l ℂ) := by
      rw [smul_smul, I_mul_I]; ext i j; by_cases h : i = j <;> simp [h, Matrix.one_apply]; norm_num
    rw [this, det_smul, det_one, mul_one]
  rw [hdet2, one_pow] at h2
  have hprod : (1 - I • (-(Q * P⁻¹))) * P = (2:ℂ) • GlobalTheory.Published.Metaplectic.holPart s := by
    have hu : IsUnit P.det := isUnit_iff_ne_zero.mpr hdet
    rw [sub_mul, one_mul, smul_mul_assoc, neg_mul, Matrix.mul_assoc, nonsing_inv_mul _ hu, mul_one]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul, hP, hQ, GlobalTheory.Published.Metaplectic.holPart]
    push_cast
    ring_nf; rw [I_sq]; ring
  have h3 : K ^ 2 * ((2:ℂ) ^ Fintype.card l * (GlobalTheory.Published.Metaplectic.holPart s).det) = 1 := by
    rw [← det_smul, ← hprod, det_mul, ← mul_assoc, h1, hc]
  have h2ne : (2:ℂ) ^ Fintype.card l ≠ 0 := pow_ne_zero _ two_ne_zero
  apply mul_left_cancel₀ h2ne
  linear_combination h3 - h2
