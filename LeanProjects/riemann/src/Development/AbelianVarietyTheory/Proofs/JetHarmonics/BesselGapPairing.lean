import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapVanishingStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem besselIntegral_sesquilinear : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → (∀ v ∈ R.TK, ∀ w ∈ R.sm, ∀ w' ∈ R.sm, ∀ a : ℂ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (w + w') v = be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v + be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w' v ∧ be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (a • w) v = a • be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v) ∧ ∀ w ∈ R.sm, ∀ v ∈ R.TK, ∀ v' ∈ R.TK, ∀ a : ℂ, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w (v + v') = be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v + be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v' ∧ be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w (a • v) = star a • be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v := by
  intro H k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq h1 h2 h3 h4
  have hc := GlobalTheory.T.besselIntegral_integrable_and_cwContinuous_of_gap H k r ε mu h R Wp z π u μW μN μG νq h1 h2 h3 h4
  refine ⟨fun v hv w hw w' hw' a => ⟨?_, ?_⟩, fun w hw v hv v' hv' a => ⟨?_, ?_⟩⟩
  · unfold be
    rw [← integral_add ((hc v hv).1 w hw) ((hc v hv).1 w' hw')]
    congr 1
    funext p
    simp only [beInt, map_add, inner_add_right, add_smul, mul_add, add_mul, smul_add]
  · unfold be
    rw [← integral_smul]
    congr 1
    funext p
    simp only [beInt, map_smul, inner_smul_right, smul_smul, mul_assoc, mul_left_comm]
  · unfold be
    rw [← integral_add ((hc v hv).1 w hw) ((hc v' hv').1 w hw)]
    congr 1
    funext p
    simp only [beInt, inner_add_left, add_smul, mul_add, add_mul, smul_add]
  · unfold be
    rw [← integral_smul]
    congr 1
    funext p
    simp only [beInt, inner_smul_left, smul_smul, mul_assoc, mul_left_comm, RCLike.star_def]

end GlobalTheory
