import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ThetaKeyFormula.ZeroSetFinite
import GroundTheory.HeightsAndTheta.Heights.ThetaKeyFormula.ThetaThreeFamLinearIndependent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.KeyFormula

open Complex Matrix

noncomputable section

theorem rigSymFormTauI_isBasisOf :
    rigSymFormTauI.IsBasisOf 3 (r := 2) thetaThreeFam :=
  ⟨fun i => thetaThreeSec_mem i, thetaThreeFam_linearIndependent, thetaThreeFam_span⟩

theorem vanishingCech_hyps :
    rigSymFormTauI.g = 1 ∧ 3 ≤ 3 ∧ rigSymFormTauI.IsBasisOf 3 (r := 2) thetaThreeFam ∧ 1 ≤ 1 ∧
      rigSymFormTauI.IsCocycle 3 1 (0 + 1) thetaThreeFam (fun _ _ => 0) := by
  refine ⟨rfl, le_rfl, rigSymFormTauI_isBasisOf, le_rfl, ?_, ?_⟩
  · intro J _
    exact ⟨0, 0, Submodule.zero_mem _, fun z _ => by simp⟩
  · intro J _ z _
    simp [cechD]

lemma formSec_X_zero :
    rigSymFormTauI.formSec (r := 2) thetaThreeFam (MvPolynomial.X 0) = thetaThreeSec 0 := by
  funext z
  simp [RigSymForm.formSec, thetaThreeFam]

theorem exactField_hyps :
    rigSymFormTauI.g = 1 ∧ 3 ≤ 3 ∧ 1 ≤ 1 ∧ rigSymFormTauI.IsBasisOf 3 (r := 2) thetaThreeFam ∧
      (∀ i : Fin rigSymFormTauI.g,
        ((fun _ => MvPolynomial.X 0 : Fin rigSymFormTauI.g → MvPolynomial (Fin (2 + 1)) ℂ) i).IsHomogeneous 1) ∧
      rigSymFormTauI.ZeroSetFinite
        (fun i => rigSymFormTauI.formSec (r := 2) thetaThreeFam
          ((fun _ => MvPolynomial.X 0 : Fin rigSymFormTauI.g → MvPolynomial (Fin (2 + 1)) ℂ) i)) := by
  refine ⟨rfl, le_rfl, le_rfl, rigSymFormTauI_isBasisOf, fun _ => MvPolynomial.isHomogeneous_X _ _, ?_⟩
  obtain ⟨W, hW⟩ := thetaThree_zero_finite
  refine ⟨W.image (fun w => (fun _ => w : Fin 1 → ℂ)), fun z hz => ?_⟩
  have h0 : thetaThree 0 (z (0 : Fin 1)) = 0 := by
    have := hz (0 : Fin 1)
    simp only [formSec_X_zero] at this
    exact this
  obtain ⟨w', hw', m, k, hz0⟩ := hW (z (0 : Fin 1)) h0
  refine ⟨fun _ => w', Finset.mem_image.mpr ⟨w', hw', rfl⟩, fun _ => k, fun _ => m, ?_⟩
  funext i
  have hi : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
  subst hi
  show z (0 : Fin 1) = w' + (tauI.τ *ᵥ intVec (fun _ : Fin 1 => k)) 0 + ((m : ℤ) : ℂ)
  have hτ : (tauI.τ *ᵥ intVec (fun _ : Fin 1 => k)) 0 = (k : ℂ) * I := by
    simp [tauI, Matrix.mulVec, dotProduct, intVec, mul_comm]
  rw [hz0, hτ]

end

end GroundTheory.Heights₂.Heights.KeyFormula
