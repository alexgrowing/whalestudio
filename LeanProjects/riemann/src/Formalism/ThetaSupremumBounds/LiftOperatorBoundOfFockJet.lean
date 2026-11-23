import Formalism.ThetaSupremumBounds.GaussianShiftBounds.Assembly
import Formalism.ThetaSupremumBounds.GaussianShiftBounds.HeightsoundOf
import Formalism.ThetaSupremumBounds.GaussianShiftBounds.BlockIntegralOf
import Formalism.ThetaSupremumBounds.GaussianShiftBounds.ClassSchur
import Mathlib
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.TheoremDivIneq
import Formalism.ThetaSupremumBounds.StatementD
import Formalism.ThetaSupremumBounds.GaussianShiftBounds.DominanceMono
import Formalism.ThetaSupremumBounds.GaussianShiftBounds.FockJet
import Formalism.ThetaSupremumBounds.GaussianShiftBounds.GaussCoord
import Formalism.ThetaSupremumBounds.StatementE

namespace Formalism.DimensionVariation

theorem liftOperatorBound_of_fockJet (hF : FockJet) : LiftOperatorBound := by
  intro Pl ι Cl Cl' _ _ _ _ A B _ _ _ _ _ r ν n s Th c Rc lam Om S γ γ' ε hν hn hs hs2 hTh hc hS hRc hRs
    hOm hlam hγ hγ' hε
  have hB := blockBound_of_fockJet hF
  unfold liftNormSq
  apply csInf_le ⟨0, fun X hX => hX.1⟩
  refine ⟨?_, fun fn => ?_⟩
  · exact mul_nonneg (by positivity) (mul_nonneg (sq_nonneg S) (Finset.prod_nonneg fun τ _ =>
      mul_nonneg (pow_nonneg (inv_nonneg.2 (hOm τ).le) _) (by positivity)))
  · exact weightedSchurBound Cl Cl' A B γ γ' ε (fun L L' => liftBlock (c L L') Rc lam) _ fn hγ hγ' hε
      (fun L L' => hB Pl ι (A →L[ℂ] B) r ν n s (Th L L') (c L L') Rc lam Om S hν hn hs hs2 (hTh L L')
        (hc L L') (hS L L') hRc hRs hOm hlam)

theorem blockBound : BlockBound := blockBound_of_fockJet gaussianCoeffIntegral
theorem periodValue : PeriodValue := period_value
theorem liftOperatorBound : LiftOperatorBound := liftOperatorBound_of_fockJet gaussianCoeffIntegral

end Formalism.DimensionVariation
