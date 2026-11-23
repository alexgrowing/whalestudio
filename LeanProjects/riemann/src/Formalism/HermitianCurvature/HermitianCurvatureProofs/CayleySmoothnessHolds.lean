import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightTypeAction0

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def MC (m : ℕ) : Type := Matrix (Fin m) (Fin m) ℂ

noncomputable instance instNRMC (m : ℕ) : NormedRing (MC m) := Matrix.linftyOpNormedRing

noncomputable instance instNAMC (m : ℕ) : NormedAlgebra ℝ (MC m) := Matrix.linftyOpNormedAlgebra

instance instFDMC (m : ℕ) : FiniteDimensional ℝ (MC m) :=
  inferInstanceAs (FiniteDimensional ℝ (Matrix (Fin m) (Fin m) ℂ))

instance instCSMC (m : ℕ) : CompleteSpace (MC m) := FiniteDimensional.complete ℝ (MC m)

def toMC (m : ℕ) : Matrix (Fin m) (Fin m) ℂ ≃L[ℝ] MC m :=
  LinearEquiv.toContinuousLinearEquiv
    (LinearEquiv.refl ℝ (Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ ≃ₗ[ℝ] MC m)

def cayMC {m : ℕ} (g₀ X : MC m) : MC m := g₀ * ((1 + X) * Ring.inverse (1 - X))

def cinvMC {m : ℕ} (a Y : MC m) : MC m := (a * Y - 1) * Ring.inverse (a * Y + 1)

theorem cay_eq_MC {k r : ℕ} (g₀ : B.Mat k r) :
    (fun X : B.Mat k r => g₀ * cay X) = fun X => (toMC _).symm (cayMC (toMC _ g₀) (toMC _ X)) := by
  funext X
  show g₀ * ((1 + X) * (1 - X)⁻¹) = g₀ * ((1 + X) * Ring.inverse (1 - X))
  rw [Matrix.nonsing_inv_eq_ringInverse]

theorem cayInv_eq_MC {k r : ℕ} (g₀ : B.Mat k r) :
    (fun m : B.Mat k r => cayInv (g₀⁻¹ * m)) = fun m => (toMC _).symm (cinvMC (toMC _ g₀⁻¹) (toMC _ m)) := by
  funext m
  show (g₀⁻¹ * m - 1) * (g₀⁻¹ * m + 1)⁻¹ = (g₀⁻¹ * m - 1) * Ring.inverse (g₀⁻¹ * m + 1)
  rw [Matrix.nonsing_inv_eq_ringInverse (g₀⁻¹ * m + 1)]

theorem cayMC_contDiffAt {m : ℕ} (g₀ X : MC m) (hX : IsUnit (1 - X)) : ContDiffAt ℝ ∞ (cayMC g₀) X := by
  obtain ⟨u, hu⟩ := hX
  have h1 : ContDiffAt ℝ ∞ (fun Y : MC m => Ring.inverse (1 - Y)) X := by
    have := contDiffAt_ringInverse (𝕜 := ℝ) (n := ∞) u
    rw [hu] at this
    exact this.comp X (contDiffAt_const.sub contDiffAt_id)
  exact contDiffAt_const.mul ((contDiffAt_const.add contDiffAt_id).mul h1)

theorem cinvMC_contDiffAt {m : ℕ} (a Y : MC m) (hY : IsUnit (a * Y + 1)) : ContDiffAt ℝ ∞ (cinvMC a) Y := by
  obtain ⟨u, hu⟩ := hY
  have h1 : ContDiffAt ℝ ∞ (fun Z : MC m => Ring.inverse (a * Z + 1)) Y := by
    have := contDiffAt_ringInverse (𝕜 := ℝ) (n := ∞) u
    rw [hu] at this
    exact this.comp Y ((contDiffAt_const.mul contDiffAt_id).add contDiffAt_const)
  exact ((contDiffAt_const.mul contDiffAt_id).sub contDiffAt_const).mul h1

theorem cayley_smoothness_holds : CaySmooth := by
  intro k r g₀
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ((Units.isOpen (R := MC (2 * r + k + 1))).preimage
      (continuous_const.sub continuous_id)).preimage (toMC _).continuous
  · exact ((Units.isOpen (R := MC (2 * r + k + 1))).preimage
      ((continuous_const.mul continuous_id).add continuous_const)).preimage (toMC _).continuous
  · rw [cay_eq_MC g₀]
    intro X hX
    have hX' : IsUnit (1 - toMC _ X) := hX
    exact ((toMC _).symm.contDiff.contDiffAt.comp X
      ((cayMC_contDiffAt (toMC _ g₀) _ hX').comp X (toMC _).contDiff.contDiffAt)).contDiffWithinAt
  · rw [cayInv_eq_MC g₀]
    intro m hm
    have hm' : IsUnit (toMC _ g₀⁻¹ * toMC _ m + 1) := hm
    exact ((toMC _).symm.contDiff.contDiffAt.comp m
      ((cinvMC_contDiffAt (toMC _ g₀⁻¹) _ hm').comp m (toMC _).contDiff.contDiffAt)).contDiffWithinAt

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
