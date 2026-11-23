import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupRepTwistedIsUnitaryRep
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)), inWb k r z → 0 < Tz k r z → IsURepOn (UWset k r z) π → (∀ h ∈ UWset k r z, ∀ m ∈ Nset k r, hPart k r (h * m) = h ∧ PiS (psiGen k r z c) π (h * m) = psiGen k r z c m • π h) ∧ IsURepOn (Sset k r z) (PiS (psiGen k r z c) π) ∧ (∀ s ∈ Sset k r z, ‖PiS (psiGen k r z c) π s‖ ≤ 1 ∧ ContinuousLinearMap.adjoint (PiS (psiGen k r z c) π s) = PiS (psiGen k r z c) π s⁻¹) ∧ ContinuousOn (PiS (psiGen k r z c) π) (Sset k r z) ∧ (∀ m ∈ Nset k r, ‖psiGen k r z c m‖ = 1 ∧ ∀ m' ∈ Nset k r, psiGen k r z c (m * m') = psiGen k r z c m * psiGen k r z c m') := by
  first | exact @GlobalTheory.SgInf.PiUnitary.piS_unitary | exact GlobalTheory.SgInf.PiUnitary.piS_unitary | (intros; apply GlobalTheory.SgInf.PiUnitary.piS_unitary <;> assumption)
