import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StZariskiObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def GermCompletionEquiv.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ),
    ∃ e : AdicCompletion (germQuotPointIdeal I w) (holGerms w ⧸ I.map (polyGerm w)) ≃+*
        AdicCompletion (polyPointIdeal I w) (MvPolynomial σ ℂ ⧸ I),
      ∀ q : MvPolynomial σ ℂ,
        e (AdicCompletion.of (germQuotPointIdeal I w) (holGerms w ⧸ I.map (polyGerm w))
            (Ideal.Quotient.mk (I.map (polyGerm w)) (polyGerm w q))) =
          AdicCompletion.of (polyPointIdeal I w) (MvPolynomial σ ℂ ⧸ I) (Ideal.Quotient.mk I q)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
