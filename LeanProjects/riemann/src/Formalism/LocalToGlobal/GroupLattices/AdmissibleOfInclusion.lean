import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSy
import Formalism.SharpRestriction.SmoothDesignExistence.SumOverPrimesHypotheses
import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLs
import Formalism.SharpRestriction.Divisibility.ChainOperators.PerCol

noncomputable section

namespace Formalism.L2.G.Adm2In

open Formalism.BasicNotions Formalism.MainNotions

structure Adm2In (𝒞 : FamClass) : Prop where

  pt0 : Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (_ : Fm.x1 < x) (i : Fm.Ix x), ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 (Fm.D x i) u
  ptTw : Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    Formalism.MainNotions.WeightDegreeSizes.TwistedChainIntegral (Fm.D x i) (Fm.ex x hx i).tw
  per0 : Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (_ : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.WeightDegreeSizes.PeriodClassSumWeyl (Fm.D x i)
  perTw : Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    Formalism.MainNotions.WeightDegreeSizes.TwistedPeriodIntegral (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).tw

  serv : Closed 𝒞 fun Fm _ => WeilJacquetShalikaLaw.ServF Fm

  p10 : Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp (Fm.D x i) u ∧ Formalism.MainNotions.product_first_zeroth_parts.TupleChainSharpColumnValuation (Fm.X x i) (Fm.ex x hx i).tw u

  dgt : Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (_ : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.WeightDegreeSizes.LevelPrimeCoprimeStabiliser (Fm.D x i)

  atG : Closed 𝒞 fun Fm _ => ∃ C1 C2 : ℝ, Formalism.MainNotions.WeightDegreeSizes.FamilyPeriodFormCond Fm C1 C2 ∧ Formalism.MainNotions.WeightDegreeSizes.familySizeBoundAtTypePrime Fm C1

end Formalism.L2.G.Adm2In

end
