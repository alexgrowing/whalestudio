import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.CountSt
import Mathlib

noncomputable section

namespace ReciprocityTheory.GeometryOfNumbersTheory

open NumberField Module MeasureTheory
open scoped ComplexOrder

def intBasisBound (K : Type*) [Field K] [NumberField K] : ℝ :=
  Real.sqrt (∑ a, ∑ σ : K →+* ℂ, ‖σ (RingOfIntegers.basis K a : K)‖ ^ 2)

variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem HermFam.nrm_smul_up (h : HermFam K V) (σ : K →+* ℂ) (c : K) (x : V) :
    h.nrm σ (c • x) = ‖σ c‖ * h.nrm σ x := by
  unfold HermFam.nrm
  have h2 : h.form σ (c • x) x = starRingEnd ℂ (σ c) * h.form σ x x := by
    rw [← h.conj_symm σ x (c • x), h.smul_right, map_mul, h.conj_symm σ x x]
  have h1 : h.form σ (c • x) (c • x) = ((‖σ c‖ ^ 2 : ℝ) : ℂ) * h.form σ x x := by
    rw [h.smul_right, h2, ← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h1, Complex.re_ofReal_mul, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]

end ReciprocityTheory.GeometryOfNumbersTheory
