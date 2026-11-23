import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst

theorem measurePreserving_of_sum_sq_eq : ∀ (k a b : ℕ), k = a + b → ∀ Q : (Fin k → ℝ) →ₗ[ℝ] (Fin a → ℝ) × (Fin b → ℝ), (∀ z, ∑ i, (Q z).1 i ^ 2 + ∑ i, (Q z).2 i ^ 2 = ∑ i, z i ^ 2) → MeasurePreserving Q volume volume := by
  intro k a b hk Q hQ
  let L : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin a ⊕ Fin b) :=
    (WithLp.linearEquiv 2 ℝ (Fin a ⊕ Fin b → ℝ)).symm.toLinearMap ∘ₗ
      (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin b) ℝ ℝ).symm.toLinearMap ∘ₗ Q ∘ₗ
      (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).toLinearMap
  have hL : ∀ z, ‖L z‖ = ‖z‖ := by
    intro z
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simp only [Real.norm_eq_abs, sq_abs, Fintype.sum_sum_type]
    rw [← hQ z.ofLp]
    rfl
  let Li : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a ⊕ Fin b) := ⟨L, hL⟩
  have hd : Module.finrank ℝ (EuclideanSpace ℝ (Fin k))
      = Module.finrank ℝ (EuclideanSpace ℝ (Fin a ⊕ Fin b)) := by
    simp [hk]
  have h1 := (Li.toLinearIsometryEquiv hd).measurePreserving
  have h2 := PiLp.volume_preserving_toLp (Fin k)
  have h3 := PiLp.volume_preserving_ofLp (Fin a ⊕ Fin b)
  have h4 := volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin a ⊕ Fin b => ℝ)
  have h := h4.comp (h3.comp (h1.comp h2))
  exact h

end GlobalTheory.IwConst
