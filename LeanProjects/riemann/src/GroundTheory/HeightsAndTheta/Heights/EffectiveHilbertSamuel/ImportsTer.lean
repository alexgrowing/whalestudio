import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.Statements
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.SymbolExtensionProperty
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open ReciprocityTheory.AnForm.M

def HasSymbolIffSymEq.Statement : Prop :=
  ∀ (D : ℕ) (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (A : FinHolAtlas D X)
    (d : IndefiniteRowSideFullHecke.EffectiveHS.FSData A Y) (B : IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.HolLineBundle A)
    (s : Fin D → Fin d.W.n → ℂ) (a : ℕ) (F : Fin A.n → X → ℂ) (g : (Fin D → ℕ) → X → ℂ),
    F ∈ IndefiniteRowSideFullHecke.EffectiveHS.topForms B →
    (d.HasSymbol s a F g ↔ d.InFil s a F ∧ SymEq A (fun i => d.W.sec (s i)) F a g)

end GroundTheory.Heights₂.Heights.EffectiveHS
