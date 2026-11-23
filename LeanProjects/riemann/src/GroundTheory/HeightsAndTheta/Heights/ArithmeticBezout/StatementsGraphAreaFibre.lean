import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeTangentAverage
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

noncomputable section

def graphBase {d k n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin k) (y : EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace ℂ (Fin d) :=
  WithLp.toLp 2 fun i => y (e.symm (Sum.inl i))

theorem graphBase_graphPt {d k n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin k)
    (F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin k)) (x : EuclideanSpace ℂ (Fin d)) :
    graphBase e (graphPt e F x) = x := by
  ext i
  simp [graphBase, graphPt]

theorem graphPt_injective_of_graphBase {d k n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin k)
    (F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin k)) : Function.Injective (graphPt e F) :=
  Function.LeftInverse.injective (graphBase_graphPt e F)

theorem continuousOn_graphPt {d k n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin k)
    {F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin k)} {Ω : Set (EuclideanSpace ℂ (Fin d))}
    (hF : ContinuousOn F Ω) : ContinuousOn (graphPt e F) Ω := by
  refine (PiLp.continuous_toLp 2 _).comp_continuousOn (continuousOn_pi.2 fun j => ?_)
  rcases e j with i | i
  · exact ((PiLp.continuous_apply 2 _ i)).continuousOn
  · exact (PiLp.continuous_apply 2 _ i).comp_continuousOn hF

def GraphAreaFibre.Statement : Prop :=
  ∀ (d k n : ℕ) (e : Fin n ≃ Fin d ⊕ Fin k) (Ω : Set (EuclideanSpace ℂ (Fin d)))
    (Φ : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin k)),
    IsOpen Ω → DifferentiableOn ℂ Φ Ω →
    ∀ P ⊆ graphPt e Φ '' Ω, MeasurableSet P →
    ∀ T : EuclideanSpace ℂ (Fin n) → Submodule ℂ (EuclideanSpace ℂ (Fin n)),
      (∀ x ∈ Ω, graphPt e Φ x ∈ P → T (graphPt e Φ x) =
        LinearMap.range (fderiv ℂ (graphPt e Φ) x :
          EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))) →
    ∀ π : Fin d → Fin n → ℂ,
      AEMeasurable (fun w : EuclideanSpace ℂ (Fin d) =>
          (({y | y ∈ P ∧ linProj π y = w}.encard : ℕ∞) : ℝ≥0∞)) ∧
        ∀ g : EuclideanSpace ℂ (Fin d) → ℝ≥0∞, Measurable g →
          volume (Metric.ball (0 : EuclideanSpace ℂ (Fin d)) 1) *
              ∫⁻ y in P, g (linProj π y) * ENNReal.ofReal (tangentJac π (T y))
                ∂(Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ)) =
            Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) (Metric.ball (0 : EuclideanSpace ℂ (Fin d)) 1) *
              ∫⁻ w : EuclideanSpace ℂ (Fin d),
                (({y | y ∈ P ∧ linProj π y = w}.encard : ℕ∞) : ℝ≥0∞) * g w

end

end GroundTheory.Heights₂.Heights
