import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiffQuotientBesselMapTendsto
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diffQuotient_besselMap_tendsto : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (z : Fin (2 * r + k + 1) → ℂ) (ψ : Mat k r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (l : H → Wp) (x : H) (X : Mat k r), IsURepOn (GG k r) σ → IsBesselMapSm z ψ σ π l → IsSmoothVec σ x → InLieHpk k r X → Filter.Tendsto (fun t : ℝ => l ((t : ℂ)⁻¹ • (σ (NormedSpace.exp ((t : ℂ) • X)) x - x))) (nhdsWithin 0 {0}ᶜ) (nhds (l (dsig σ X x))) ∧ ContinuousOn (fun g => l (σ g x)) (GG k r) ∧ ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ GG k r ∧ σ (NormedSpace.exp ((t : ℂ) • X)) x - x = ∫ u in (0 : ℝ)..t, σ (NormedSpace.exp ((u : ℂ) • X)) (dsig σ X x) := by
  first | exact @GlobalTheory.diffQuot_bessel | exact GlobalTheory.diffQuot_bessel | (intros; apply GlobalTheory.diffQuot_bessel <;> assumption)
