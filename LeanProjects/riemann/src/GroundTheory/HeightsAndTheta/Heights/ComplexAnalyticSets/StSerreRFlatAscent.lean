import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSerreConditions
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def SerreRFlatAscent.Statement : Prop :=
  ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], IsNoetherianRing A → IsNoetherianRing B →
    Module.Flat A B → ∀ k : ℕ, SerreR A k →
      (∀ (P : Ideal B) [P.IsPrime], SerreRAt (primeFibreLocalRing A P) k) → SerreR B k

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
