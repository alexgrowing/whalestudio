import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsScalarStableLatticeAutomorphismFundamental
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scalarStable_latticeAutomorphismFundamentalDomain : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, ∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsLattice E Λ → ∃ D : Set (MatInf E j), MeasurableSet D ∧ D ⊆ {g | 0 < detNorm E j g} ∧ (∀ g, 0 < detNorm E j g → ∃ γ ∈ autGL E j Λ, γ * g ∈ D) ∧ (∀ g ∈ D, ∀ t : ℝ, 0 < t → (fun w a b => (t : ℂ) * g w a b) ∈ D) ∧ ∀ (G : MatInf E j → ENNReal) (A : Set (MatInf E j)), Measurable (fun g => {g | 0 < detNorm E j g}.indicator G g) → (∀ γ ∈ autGL E j Λ, ∀ g, 0 < detNorm E j g → G (γ * g) = G g) → MeasurableSet A → A ⊆ {g | 0 < detNorm E j g} → (∀ γ ∈ autGL E j Λ, ∀ g ∈ A, γ * g ∈ A) → covol (autGL E j Λ) (((haarGL E j).restrict {g | 0 < detNorm E j g}).withDensity G) A = ∫⁻ g in A ∩ D, G g ∂(haarGL E j) := by
  first | exact @GlobalTheory.LatDom.exists_cone_domain | exact GlobalTheory.LatDom.exists_cone_domain | (intros; apply GlobalTheory.LatDom.exists_cone_domain <;> assumption)
