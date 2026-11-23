import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP
import Formalism.HarderNarasimhan.FinalCor
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues
open scoped Matrix ComplexOrder

namespace GlobalTheory.DualInt

theorem star_mem_one_O {K : Type} [Field K] [NumberField K] [StarRing K] {a : K}
    (ha : a ∈ (1 : Submodule (𝓞 K) K)) : star a ∈ (1 : Submodule (𝓞 K) K) := by
  rw [Submodule.mem_one] at ha ⊢
  obtain ⟨r, rfl⟩ := ha
  have hi : IsIntegral ℤ (star (algebraMap (𝓞 K) K r)) := by
    have := (r.isIntegral_coe).map (starRingAut (R := K) : K ≃+* K).toRingHom.toIntAlgHom
    simpa using this
  exact ⟨⟨_, hi⟩, rfl⟩

theorem hform_eq_dot {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ}
    (H : Matrix (Fin n) (Fin n) K) (a b : Fin n → K) :
    hform H a b = star a ⬝ᵥ H *ᵥ b := by
  simp [hform, Matrix.toLinearMapₛₗ₂'_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, starRingEnd_apply, mul_comm]

theorem inv_mulVec_star_mem_dual {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ}
    (H : Matrix (Fin n) (Fin n) K) (hH : IsUnit H.det) (M : Submodule (𝓞 K) (Fin n → K))
    (y : Fin n → K) (hy : ∀ x ∈ M, y ⬝ᵥ x ∈ (1 : Submodule (𝓞 K) K)) :
    H⁻¹ *ᵥ star y ∈ Formalism.HermitianLatticesTheory.dual (hform H) M := by
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap]
  intro x hx
  change hform H x (H⁻¹ *ᵥ star y) ∈ (1 : Submodule (𝓞 K) K)
  rw [hform_eq_dot, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hH, Matrix.one_mulVec]
  have e : star x ⬝ᵥ star y = star (y ⬝ᵥ x) := by
    simp [dotProduct, mul_comm]
  rw [e]
  exact star_mem_one_O (hy x hx)

theorem dual_form_integral :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) (H : Matrix (Fin n) (Fin n) K),
      Hᴴ = H → IsUnit H.det → ∀ M : Submodule (𝓞 K) (Fin n → K),
      Formalism.HermitianLatticesTheory.dual (hform H) M ≤ M → ∀ y y' : Fin n → K,
      (∀ x ∈ M, y ⬝ᵥ x ∈ (1 : Submodule (𝓞 K) K)) →
      (∀ x ∈ M, y' ⬝ᵥ x ∈ (1 : Submodule (𝓞 K) K)) →
      hform (H⁻¹)ᵀ y y' ∈ (1 : Submodule (𝓞 K) K) := by
  intro K _ _ _ n H _ hH M hM y y' hy hy'
  have hz := hM (inv_mulVec_star_mem_dual H hH M y hy)
  have e : hform (H⁻¹)ᵀ y y' = y' ⬝ᵥ (H⁻¹ *ᵥ star y) := by
    rw [hform_eq_dot, Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec]
  rw [e]
  exact hy' _ hz

end GlobalTheory.DualInt
