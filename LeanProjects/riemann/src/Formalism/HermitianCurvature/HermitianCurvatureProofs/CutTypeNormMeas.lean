import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopFormTDM
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB

namespace Formalism.FourierDecayAlt.P.CutBP.TNM

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory Matrix

noncomputable section

def TypeComm : Prop :=
  ∀ (P : M.Par) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (π : B.Mat P.k P.r → (Wp →L[ℂ] Wp)) (z e : Fin (2 * P.r + P.k + 1) → ℂ) (TP : Top.TypeProj P π z e),
    IsCRepOn (UWset P.k P.r z) π → ContinuousOn π (UWset P.k P.r z) →
    (∀ h ∈ UWset P.k P.r z, ∀ v, ‖π h v‖ = ‖v‖) →
    1 ≤ P.k → inWb P.k P.r z → 0 < Tz P.k P.r z → inWb P.k P.r e → herm (Hpk P.k P.r) e z = 0 →
    herm (Hpk P.k P.r) e e = 1 →
    ∀ g ∈ UWset P.k P.r z, ∀ l : ℂ, g *ᵥ e = l • e → ∀ ρ, (TP.E ρ).comp (π g) = (π g).comp (TP.E ρ)

def HouseMeas : Prop :=
  ∀ (k r : ℕ) (z e : Fin (2 * r + k + 1) → ℂ), inWb k r z → (herm (Hpk k r) z z).re < 0 →
    inWb k r e → herm (Hpk k r) e z = 0 → herm (Hpk k r) e e = 1 →
    ∃ h : (Fin (2 * r + k + 1) → ℂ) → B.Mat k r, Measurable h ∧ (∀ u, h u ∈ UWset k r z) ∧
      ∀ u, inWb k r u → herm (Hpk k r) u z = 0 → u ≠ 0 → ∃ l : ℂ, h u *ᵥ u = l • e

end

end Formalism.FourierDecayAlt.P.CutBP.TNM
