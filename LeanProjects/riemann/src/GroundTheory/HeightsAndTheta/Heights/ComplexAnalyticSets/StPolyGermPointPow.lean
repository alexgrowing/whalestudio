import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StZariskiObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

def PolyGermPointPow.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (k : ℕ) (q : MvPolynomial σ ℂ),
    polyGerm w q ∈ holGermPointIdeal w ^ k → q ∈ RingHom.ker (MvPolynomial.eval w) ^ k

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
