import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NineStatements

open ReciprocityTheory.AnForm.A (IsPsh)

def PshLocal.Statement : Prop :=
  ∀ (D : ℕ) (U : Set (Fin D → ℂ)) (φ : (Fin D → ℂ) → ℝ), IsOpen U →
    (∀ z ∈ U, ∃ W : Set (Fin D → ℂ), IsOpen W ∧ z ∈ W ∧ W ⊆ U ∧ IsPsh W φ) → IsPsh U φ

end GroundTheory.Heights₂.Heights.NineStatements
