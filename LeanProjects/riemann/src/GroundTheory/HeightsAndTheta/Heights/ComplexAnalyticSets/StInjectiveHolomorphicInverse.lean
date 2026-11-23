import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StInjectiveHolomorphicOpen
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def InjectiveHolomorphicInverse.Statement : Prop :=
  ∀ (k : ℕ) (U : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → Fin k → ℂ),
    IsOpen U → DifferentiableOn ℂ f U → Set.InjOn f U →
      IsOpen (f '' U) ∧
        ∃ g : (Fin k → ℂ) → Fin k → ℂ, DifferentiableOn ℂ g (f '' U) ∧ ∀ t ∈ U, g (f t) = t

theorem InjectiveHolomorphicInverse.hypotheses_inhabited :
    IsOpen (Metric.ball (0 : Fin 2 → ℂ) 1) ∧
      DifferentiableOn ℂ (fun t : Fin 2 → ℂ => ![t 0, t 1 + t 0 ^ 2]) (Metric.ball 0 1) ∧
      Set.InjOn (fun t : Fin 2 → ℂ => ![t 0, t 1 + t 0 ^ 2]) (Metric.ball 0 1) :=
  InjectiveHolomorphicOpen.hypotheses_inhabited

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
