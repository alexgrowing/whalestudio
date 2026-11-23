import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodCoordinatesQuadraticRelation
import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Formalism.LocalToGlobal.ProjectiveLattices.FibreUniformisationLevelTwo
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_coordinates_quadratic_relation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (hr : 0 < r) (τ₁ : E →+* ℂ) (κ : Frame X.Ψ r → Fin r → ℂ), ContinuousOn κ X.dom → (∀ O : Set (Frame X.Ψ r), IsOpen O → O ⊆ X.dom → ∀ x ∈ O, ∀ ξ : Fin r → ℂ, ∀ᶠ t in nhdsWithin (0 : ℂ) {0}ᶜ, ∃ x' ∈ O, κ x' = κ x + t • ξ) → ∀ (S : Set (Matrix (Fin r) (Fin r) E)), (∀ x ∈ X.dom, ∃ W ∈ S, ∀ v ∈ X.Λ, ∀ w ∈ X.Λ, (κ x ⬝ᵥ Data.emb τ₁ (W *ᵥ v)) * (κ x ⬝ᵥ Data.emb τ₁ w) = (κ x ⬝ᵥ Data.emb τ₁ (W *ᵥ w)) * (κ x ⬝ᵥ Data.emb τ₁ v)) → ∃ W ∈ S, ∃ ζ : E, W = ζ • (1 : Matrix (Fin r) (Fin r) E) := by
  first | exact @GlobalTheory.FramesCover.exists_scalar_mem | exact GlobalTheory.FramesCover.exists_scalar_mem | (intros; apply GlobalTheory.FramesCover.exists_scalar_mem <;> assumption)
