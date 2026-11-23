import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSerreConditions
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def SerreSFlatAscent.Statement : Prop :=
  ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], IsNoetherianRing A → IsNoetherianRing B →
    Module.Flat A B → ∀ k : ℕ, SerreS A k →
      (∀ (P : Ideal B) [P.IsPrime], SerreSAt (primeFibreLocalRing A P) k) → SerreS B k

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
