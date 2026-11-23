import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.RingKrullDimQuotBotOne
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.FrameProjEq
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MeasureTheory

open scoped ENNReal

noncomputable section

def AreaGraph.LebesgueForm : Prop :=
  ∀ (k m : ℕ) (U : Set (EuclideanSpace ℝ (Fin k)))
    (F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m)),
    IsOpen U → ContDiffOn ℝ 1 F U → ∀ A ⊆ U, MeasurableSet A →
      μH[(k : ℝ)] (GroundTheory.Heights₂.Heights.realGraphPt F '' A) =
        ∫⁻ x in A, ENNReal.ofReal (graphDensity F x)

theorem AreaGraph.statement_iff :
    GroundTheory.Heights₂.Heights.AreaGraph.Statement ↔ AreaGraph.Statement := by
  constructor
  · intro h k m F U A hU hF hA hAU
    rw [graphOver_eq]
    exact h k m U F hU hF A hAU hA
  · intro h k m U F hU hF A hAU hA
    have key := h k m F U A hU hF hA hAU
    rw [graphOver_eq] at key
    exact key

theorem AreaGraph.rowPoisson_half_implies_one :
    GroundTheory.Heights₂.Heights.AreaGraph.Statement → AreaGraph.Statement :=
  AreaGraph.statement_iff.1

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
