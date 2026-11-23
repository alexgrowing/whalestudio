import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffinePeriodCoordinate
import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Formalism.LocalToGlobal.ProjectiveLattices.FibreUniformisationLevelTwo
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_period_coordinate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (τ₁ : E →+* ℂ), τ₁ ∈ X.Ψ → ∀ (i : ℕ), X.p0 + i + 1 = r → ∃ κ : Frame X.Ψ r → Fin r → ℂ, ContinuousOn κ X.dom ∧ (∀ O : Set (Frame X.Ψ r), IsOpen O → O ⊆ X.dom → ∀ x ∈ O, ∀ ξ : Fin r → ℂ, ∀ᶠ t in nhdsWithin (0 : ℂ) {0}ᶜ, ∃ x' ∈ O, κ x' = κ x + t • ξ) ∧ ∀ x ∈ X.dom, ∀ v, Formalism.L2.PjFree.perFr X x v τ₁ i = κ x ⬝ᵥ Data.emb τ₁ v := by
  first | exact @GlobalTheory.FrameLastRow.lastRow_moves | exact GlobalTheory.FrameLastRow.lastRow_moves | (intros; apply GlobalTheory.FrameLastRow.lastRow_moves <;> assumption)
