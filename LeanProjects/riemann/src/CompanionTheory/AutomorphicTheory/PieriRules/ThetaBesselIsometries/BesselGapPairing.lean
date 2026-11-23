import Mathlib
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselGapVanishingStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem besselIntegral_sesquilinear : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → (∀ v ∈ R.TK, ∀ w ∈ R.sm, ∀ w' ∈ R.sm, ∀ a : ℂ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (w + w') v = be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v + be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w' v ∧ be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (a • w) v = a • be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v) ∧ ∀ w ∈ R.sm, ∀ v ∈ R.TK, ∀ v' ∈ R.TK, ∀ a : ℂ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w (v + v') = be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v + be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v' ∧ be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w (a • v) = star a • be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v := by
  intro hG k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hDG hGap hOK hSide
  have hI := Gp91.GlobalTheory.T.besselIntegral_integrable_and_cwContinuous_of_gap hG k r ε mu h R Wp z π u μW μN μG νq hDG hGap hOK hSide
  refine ⟨fun v hv w hw w' hw' a => ⟨?_, ?_⟩, fun w hw v hv v' hv' a => ⟨?_, ?_⟩⟩
  · unfold Formalism.FourierDecayAlt.ThreeDimData.be
    rw [← MeasureTheory.integral_add ((hI v hv).1 w hw) ((hI v hv).1 w' hw')]
    congr 1
    funext p
    simp only [Formalism.FourierDecayAlt.ThreeDimData.beInt, map_add, inner_add_right, add_mul, add_smul]
  · unfold Formalism.FourierDecayAlt.ThreeDimData.be
    rw [← MeasureTheory.integral_smul]
    congr 1
    funext p
    simp only [Formalism.FourierDecayAlt.ThreeDimData.beInt, map_smul, inner_smul_right, smul_smul, mul_assoc]
  · unfold Formalism.FourierDecayAlt.ThreeDimData.be
    rw [← MeasureTheory.integral_add ((hI v hv).1 w hw) ((hI v' hv').1 w hw)]
    congr 1
    funext p
    simp only [Formalism.FourierDecayAlt.ThreeDimData.beInt, inner_add_left, add_mul, add_smul]
  · unfold Formalism.FourierDecayAlt.ThreeDimData.be
    rw [← MeasureTheory.integral_smul]
    congr 1
    funext p
    simp only [Formalism.FourierDecayAlt.ThreeDimData.beInt, inner_smul_left, starRingEnd_apply, smul_smul, mul_assoc]

end GlobalTheory
