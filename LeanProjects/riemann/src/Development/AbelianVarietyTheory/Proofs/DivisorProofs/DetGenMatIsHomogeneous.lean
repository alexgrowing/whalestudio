import Mathlib
import GroundTheory.Brauer.Splitting
open IsLocalRing

namespace GlobalTheory.ReducedNormExists

open MvPolynomial TensorProduct

noncomputable abbrev genMat {R ι : Type} [CommRing R] [Fintype ι] {n : ℕ}
    (M : ι → Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) (MvPolynomial ι R) :=
  ∑ i, (X i : MvPolynomial ι R) • (M i).map (C : R →+* MvPolynomial ι R)

theorem isUnit_one_tmul_iff {K E B : Type} [Field K] [Field E] [Algebra K E] [Ring B]
    [Algebra K B] [FiniteDimensional K B] (x : B) :
    IsUnit ((1 : E) ⊗ₜ[K] x) ↔ IsUnit x := by
  constructor
  · intro hu
    have hinj : Function.Injective (Algebra.TensorProduct.includeRight : B →ₐ[K] E ⊗[K] B) :=
      Algebra.TensorProduct.includeRight_injective (algebraMap K E).injective
    have hL : Function.Injective (LinearMap.mulLeft K x) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro z hz
      have h0 : ((1 : E) ⊗ₜ[K] x) * (1 ⊗ₜ z) = 0 := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        simp only [LinearMap.mulLeft_apply] at hz
        rw [hz, TensorProduct.tmul_zero]
      have h1 : (1 : E) ⊗ₜ[K] z = 0 := hu.mul_right_eq_zero.mp h0
      exact hinj (by simpa using h1)
    have hR : Function.Injective (LinearMap.mulRight K x) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro z hz
      have h0 : ((1 : E) ⊗ₜ[K] z) * (1 ⊗ₜ x) = 0 := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        simp only [LinearMap.mulRight_apply] at hz
        rw [hz, TensorProduct.tmul_zero]
      have h1 : (1 : E) ⊗ₜ[K] z = 0 := hu.mul_left_eq_zero.mp h0
      exact hinj (by simpa using h1)
    obtain ⟨z, hz⟩ := LinearMap.injective_iff_surjective.mp hL 1
    obtain ⟨w, hw⟩ := LinearMap.injective_iff_surjective.mp hR 1
    simp only [LinearMap.mulLeft_apply] at hz
    simp only [LinearMap.mulRight_apply] at hw
    have hwz : w = z := by
      calc w = w * (x * z) := by rw [hz, mul_one]
        _ = (w * x) * z := (mul_assoc _ _ _).symm
        _ = z := by rw [hw, one_mul]
    exact ⟨⟨x, z, hz, hwz ▸ hw⟩, rfl⟩
  · intro hx
    exact hx.map (Algebra.TensorProduct.includeRight : B →ₐ[K] E ⊗[K] B)

end GlobalTheory.ReducedNormExists
