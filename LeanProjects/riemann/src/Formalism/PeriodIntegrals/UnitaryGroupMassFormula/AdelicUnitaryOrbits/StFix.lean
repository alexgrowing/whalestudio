import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.UnitChoice
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.QuadFiniteDimensional

noncomputable section

namespace PIW.AdelicOrbitU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

theorem stFix : StFix := by
  intro F E _ _ _ _ σ h2 hfix R _ _
  have hσσ : ∀ a : E, σ (σ a) = a := fun a => quad_sigma_sigma (σ := σ) (h2 := h2) (hfix := hfix) a
  refine ⟨fun z => quad_sig_sig σ R hσσ z, ?_⟩
  intro z hz
  obtain ⟨θ, _hθ0, hσθ, ⟨d, _hd0, hd⟩, hli⟩ := quad_exists_theta (σ := σ) (h2 := h2) (hfix := hfix)
  obtain ⟨a, b, rfl⟩ : ∃ a b : R, z = a ⊗ₜ[F] (1 : E) + b ⊗ₜ[F] θ :=
    ⟨_, _, quad_decomp (h2 := h2) (hli := hli) (R := R) z⟩
  rw [quad_sig (R := R) (σ := σ) (hσθ := hσθ)] at hz
  have h1 : (-b) ⊗ₜ[F] θ = b ⊗ₜ[F] θ := add_left_cancel hz
  have hb : b ⊗ₜ[F] θ = 0 := by
    have h2' : (2 : F) • (b ⊗ₜ[F] θ) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← h1]
      rw [TensorProduct.neg_tmul, neg_add_cancel]
    exact (smul_eq_zero.mp h2').resolve_left two_ne_zero
  have h12 : algebraMap F R (1 / 2) * (2 * a) = a := by
    rw [← mul_assoc, show (2 : R) = algebraMap F R 2 from (map_ofNat _ 2).symm, ← map_mul]
    norm_num
  rw [quad_trace (R := R) (hd := hd), hb, add_zero, h12]
  · simp [Algebra.TensorProduct.algebraMap_apply]
  · exact h2
  · exact hli

end PIW.AdelicOrbitU
