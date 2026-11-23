import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.Statements
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.SymbolExtensionProperty
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open ReciprocityTheory.AnForm.M

def TopFormNormEqIntegral.Statement : Prop :=
  ∀ (D : ℕ) (X : Type) [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    (A : FinHolAtlas D X) (B : IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.HolLineBundle A)
    (ψ : Fin A.n → X → ℝ) (F : Fin A.n → X → ℂ),
    IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.IsWeight B ψ → F ∈ IndefiniteRowSideFullHecke.EffectiveHS.topForms B →
    topNormSq A ψ F = IndefiniteRowSideFullHecke.EffectiveHS.topFormWeightedL2 ψ F

end GroundTheory.Heights₂.Heights.EffectiveHS
