import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardUnimodularGluingsTwoLinesLe
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_unimodular_gluings_two_lines_le : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ (β₁ β₂ : E) (N₁ N₂ : Submodule (𝓞 E) E) (𝔫 : Ideal (𝓞 E)), star β₁ = β₁ → star β₂ = β₂ → β₁ ≠ 0 → β₂ ≠ 0 → Submodule.IsLattice E N₁ → Submodule.IsLattice E N₂ → Submodule.span (𝓞 E) {t | ∃ x ∈ N₁, ∃ y ∈ N₁, t = star x * β₁ * y} = Submodule.map (Algebra.linearMap (𝓞 E) E) 𝔫 → ENat.card {M : Submodule (𝓞 E) (Fin 2 → E) // Submodule.IsLattice E M ∧ (∀ x, x ∈ M ↔ ∀ y ∈ M, star y ⬝ᵥ ((Matrix.diagonal ![β₁, β₂]) *ᵥ x) ∈ (algebraMap (𝓞 E) E).range) ∧ (∀ t, t ∈ N₁ ↔ ![t, 0] ∈ M) ∧ ∀ t, t ∈ N₂ ↔ ![0, t] ∈ M} ≤ (Ideal.absNorm 𝔫 : ENat) := by
  first | exact @GlobalTheory.GlueLines.card_gluings_le | exact GlobalTheory.GlueLines.card_gluings_le | (intros; apply GlobalTheory.GlueLines.card_gluings_le <;> assumption)
