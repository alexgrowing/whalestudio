import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndVerbB
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpChartOf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpActOf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTiePf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpUniqChart
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeUniqPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.EvalSinglePointId
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.KillAddVal
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PsiCover
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.HarmInvPf

set_option autoImplicit false

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open ReciprocityTheory.ChartRestriction.G.Out NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem chartIndep2_of_open (hGauge : ExpGaugeOfSt) (hKill : KillAddValSt) (hGlob : GlobalFnsSt)
    (hFix : FrTruncFixSt) (hInv : HarmInvSt) : ChartIndepSt2 :=
  chartIndep2_of_fix
    (chartIndepTrunc_of (expChartOf_of (expActOf_of linEigSt_holds)) hGauge tie_holds ExpUniqChart.expUniqTan
      (gaugeUniq_of_global hGlob) hKill)
    hFix germFix_holds hInv

theorem chartIndep2_of_open' (hGauge : ExpGaugeOfSt) (hPsi : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : Host E), PsiCoverSt H) (hGlob : GlobalFnsSt) (hFix : FrTruncFixSt) (hInv : HarmInvSt) : ChartIndepSt2 :=
  chartIndep2_of_open hGauge (killAddVal_of hPsi) hGlob hFix hInv

theorem chartIndep2_of_open'' (hGauge : ExpGaugeOfSt) (hGlob : GlobalFnsSt) (hFix : FrTruncFixSt)
    (hInv : HarmInvSt) : ChartIndepSt2 :=
  chartIndep2_of_open' hGauge (fun _ _ _ _ H => psiCover_holds H) hGlob hFix hInv

theorem chartIndep2_of_gauge (hGauge : ExpGaugeOfSt) (hGlob : GlobalFnsSt) (hFix : FrTruncFixSt) : ChartIndepSt2 :=
  chartIndep2_of_open'' hGauge hGlob hFix (harmInv_of (expActOf_of linEigSt_holds))

end Formalism.MainNotions.ModuliIntegralCharts.H1
