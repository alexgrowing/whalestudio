import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
  GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal

noncomputable section

def TopSecCompact.Statement : Prop :=
  ∀ (D : ℕ) (X : EmbDatum D) (m : ℕ) (F : ℕ → Fin X.A.n → X.U → ℂ) (C : ℝ),
    (∀ n, F n ∈ topSections X.A X.L₂ X.L m) →
    (∀ n, topNormSq X.A (X.wt m) (F n) ≤ ENNReal.ofReal C) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G ∈ topSections X.A X.L₂ X.L m,
      ∀ k x, Tendsto (fun n => F (φ n) k x) atTop (𝓝 (G k x))

end

end GroundTheory.Heights₂.Heights.EffectiveHS
