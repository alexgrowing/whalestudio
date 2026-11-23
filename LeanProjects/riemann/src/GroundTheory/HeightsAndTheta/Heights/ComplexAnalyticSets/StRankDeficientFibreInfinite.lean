import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric

def RankDeficientFibreInfinite.Statement : Prop :=
  ∀ (k m : ℕ) (U : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → Fin m → ℂ),
    IsOpen U → U.Nonempty → DifferentiableOn ℂ f U →
    (∀ v ∈ U, ¬ Function.Injective (fderiv ℂ f v)) →
      ∃ y : Fin m → ℂ, {t | t ∈ U ∧ f t = y}.Infinite

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
