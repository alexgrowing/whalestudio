import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFieldCmCurvesUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGoodReductionAlgebraicWeierstrassModel

open GlobalTheory GlobalTheory.CMCurves

namespace GlobalTheory.ThLoc

theorem cm1 : Formalism.L2.Th1.CM.JInvariantIntegrality := by
  intro d L _ hd hL
  obtain ⟨a, τ, ha, h⟩ := exists_lattice_eq_mul_tau L
  rw [Formalism.L2.Th1.CM.jInv, g₂_cube_div_eq_modularJ ha h]
  refine isIntegral_modularJ_of_mul_mem (α := Formalism.L2.Th1.CM.omegaK d) (fun m hm => ?_) fun x hx ↦ ?_
  · have := congrArg Complex.im hm
    have h0 : (0:ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < d))
    simp [Formalism.L2.Th1.CM.omegaK] at this
    omega
  · have key : ∀ y : ℂ, y ∈ Submodule.span ℤ {(τ : ℂ), 1} ↔ a * y ∈ L.lattice := fun y ↦ by
      rw [h, Submodule.mem_span_pair]
      simp [mul_right_inj' ha]
    rw [key] at hx ⊢
    simpa [mul_left_comm] using hL _ hx

end GlobalTheory.ThLoc
