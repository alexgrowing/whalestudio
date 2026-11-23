import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.Statements
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.SymbolExtensionProperty
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.HolLineBundleToAltTransition
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights.HilbertSamuel

def NatSpaceEqVnat.Statement : Prop :=
  ∀ (D : ℕ) (X Y : Type) [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [TopologicalSpace Y] (A : FinHolAtlas D X) (d : IndefiniteRowSideFullHecke.EffectiveHS.HSData A Y) (j : ℕ),
    ((d.natSpace j : Submodule ℂ (Fin A.n → X → ℂ)) : Set (Fin A.n → X → ℂ)) =
      Vnat A (HolLineBundle.split_model_to_place_model d.L₂) (HolLineBundle.split_model_to_place_model d.L) d.φA
        (IndefiniteRowSideFullHecke.EffectiveHS.fsPhi d.W) j

end GroundTheory.Heights₂.Heights.EffectiveHS
