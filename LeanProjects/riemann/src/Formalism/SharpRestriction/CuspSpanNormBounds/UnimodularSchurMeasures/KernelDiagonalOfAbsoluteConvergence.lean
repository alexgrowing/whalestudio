import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.KernelDiagonalOfL2UnfoldIdempotent
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrkaMeasKabRight
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrkbLeOneAddSq
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrkpCoefCont

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set TopologicalSpace
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def AbsKernelSquareIntegrable (X : CData) : Prop :=
  ∀ᵐ x ∂X.μ, ∫⁻ y, (∑' γ : X.I.GFset, ‖X.φ (x⁻¹ * (γ : X.I.GA) * y)‖ₑ) ^ 2 ∂X.μ ≠ ∞

def PhiIdem (X : CData) : Prop :=
  Measurable X.φ ∧ (∀ z, X.φ z⁻¹ = star (X.φ z)) ∧ ∀ z, ∫ g, X.φ g * X.φ (g⁻¹ * z) ∂(X.I.muA X.μf) = X.φ z

theorem rrk_steps_of_abs (X : CData) (hd : RegData X) (hu : UnimodA X) (hφ : PhiIdem X) (hK : AbsKernelSquareIntegrable X) :
    KernelL2RowsColumns X ∧ KerUnfold X ∧ KerIdem X := by
  obtain ⟨hH, hF, hR⟩ := hd
  have := hH
  have : SecondCountableTopology X.I.Gf := rr_secondCountable X.I X.μf
  have : (X.I.muA X.μf).IsMulLeftInvariant := rr_muA_left X.I X.μf
  have : (X.I.muA X.μf).IsMulRightInvariant := hu
  have : SigmaFinite (X.I.muA X.μf) := rr_muA_sigmaFinite X.I X.μf
  have h1 := rr_FD_of X.I X.μf X.fund hF
  have h2 := rr_IsReg_of X.I X.μf X.fund X.R hR
  have hK' : ∀ᵐ x ∂(X.I.muA X.μf).restrict X.fund,
      ∫⁻ y in X.fund, (rrk_Kab (rr_GF X.I) X.φ x y) ^ 2 ∂(X.I.muA X.μf) ≠ ∞ := hK
  refine ⟨?_, ?_, ?_⟩
  · unfold KernelL2RowsColumns CData.μ
    filter_upwards [hK'] with x hx
    exact (rrk_idem h1 hφ.1 hφ.2.1 hφ.2.2 x hx).2.2
  · intro T hT f
    exact rrk_unfold h1 hφ.1 h2 T hT.1 hT.2 hK' f
  · unfold KerIdem CData.μ
    filter_upwards [hK'] with x hx
    have := rrk_idem h1 hφ.1 hφ.2.1 hφ.2.2 x hx
    exact ⟨this.1, this.2.1⟩

theorem kernel_diagonal_of_absolute_convergence (X : CData) (hd : RegData X) (hu : UnimodA X) (hφ : PhiIdem X) (hK : AbsKernelSquareIntegrable X) :
    X.KernelDiag := by
  obtain ⟨a, b, c⟩ := rrk_steps_of_abs X hd hu hφ hK
  exact kernel_diagonal_of_L2_unfold_idempotent X hd.1 a b c

theorem PhiIdem_of (D : Formalism.BasicNotions.D7) (hloc : LocalProjectorRealPlace D) (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) (h1 : X.GapAboveThreeHalvesPower) :
    PhiIdem X :=
  ⟨rrk_phi_meas X hX, rrk_phi_star D hloc X hX h1, rrk_phi_idem D hloc X hX h1⟩

theorem kernel_diagonal_of_local_projector_of_abs_kernel_L2 (D : Formalism.BasicNotions.D7) (hloc : LocalProjectorRealPlace D) (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A)
    (h1 : X.GapAboveThreeHalvesPower) (hu : UnimodA X) (hK : AbsKernelSquareIntegrable X) : X.KernelDiag :=
  kernel_diagonal_of_absolute_convergence X (RegData_of_HypB X hX) hu (PhiIdem_of D hloc X hX h1) hK

end Formalism.MainNotions.LeviCoordinates

end
