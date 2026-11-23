import ReciprocityTheory.L2DbarEstimates.Localization.SSmooth
import ReciprocityTheory.L2DbarEstimates.Localization.MultAdj
import ReciprocityTheory.L2DbarEstimates.Localization.Cutoff
import ReciprocityTheory.L2DbarEstimates.Localization.UnweightRel
import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBack
import ReciprocityTheory.L2DbarEstimates.Localization.Localize
import ReciprocityTheory.L2DbarEstimates.Localization.Extend
import ReciprocityTheory.L2DbarEstimates.Localization.IntegrableFd
import ReciprocityTheory.L2DbarEstimates.Localization.ChartFlat
import ReciprocityTheory.L2DbarEstimates.Localization.Imports
import ReciprocityTheory.L2DbarEstimates.Localization.PrimZeroOfNonpos
import ReciprocityTheory.L2DbarEstimates.Localization.DerivSmoothTransitionOfOneLt
import ReciprocityTheory.L2DbarEstimates.Localization.ShellCeilEq
import ReciprocityTheory.L2DbarEstimates.Localization.LeviZCoordChart
import ReciprocityTheory.L2DbarEstimates.Localization.Choice
import ReciprocityTheory.L2DbarEstimates.Localization.Primed
import ReciprocityTheory.L2DbarEstimates.Localization.Closure
import ReciprocityTheory.L2DbarEstimates.Localization.KPsiHasCompactSupport
import ReciprocityTheory.L2DbarEstimates.Localization.SplitTest
import ReciprocityTheory.L2DbarEstimates.Localization.Locality
import ReciprocityTheory.L2DbarEstimates.Localization.TestIneq
import ReciprocityTheory.L2DbarEstimates.HormanderEstimate.RegMDbEqZeroOfNotMem
import ReciprocityTheory.L2DbarEstimates.HormanderEstimate.Hormander

namespace ReciprocityTheory.L2DbarEstimates.F

theorem hStatement_of (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
    (hAP : APStatement n M) (hTIbp : TStarIbpStatement n M) (hChain : ChainStatement n M)
    (hReg : C.RegStatement) (hGraph : B.GraphSt (V n) MeasureTheory.volume ℝ)
    (hSmooth : B.SmoothSt (V n) MeasureTheory.volume) (hSupp : B.SupportSt (V n) MeasureTheory.volume)
    (hStd : B.StdSt (V n) MeasureTheory.volume) : HStatement n M :=
  hormander n M
    (testIneq n M
      (choice n M chi (psi n M) (shell n M) (leviNormSq n M) hChain)
      (primedIneq n M hAP)
      (closureIneq n M
        (dens n M (cutoff n M (multAdj n M) (multS n M)) (unweightRel n M) (unweightBack n M)
          (localize n M (multDiv n M) (multS n M))
          (chartFlat n M (extend n M) (flatGraph n hGraph hSmooth hSupp hStd))))
      (splitTest n M (kSub n M) (weakSSmooth n M) (sbarDbar n M) hTIbp)
      (locality n M) (weakSSmooth n M) (sbarDbar n M))
    (regM n M hReg (extend n M))

end ReciprocityTheory.L2DbarEstimates.F
