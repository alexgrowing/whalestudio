import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StZariskiObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

def HolGermPointIdealSpan.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ),
    holGermPointIdeal w = Ideal.span (Set.range fun i : σ => polyGerm w (X i - C (w i)))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
