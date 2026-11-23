import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeakOfPi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.GrowthPiJHolds
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PiTermEqTraceSumOfDegreeFourTest

open UpperTheory.V.Z.Tf.GlobalTraceComparison

namespace UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem runTh : RunTh := runTh_of_pi Pi.piTerm_holds Pi.piFin_holds Pi.piAdm_pf Pi.twTrSum_pf Pi.growthPiJ_holds

theorem descWeak (hW : GalWeak 4) : UpperTheory.V.Z.Desc.DescWeak := descWeak_of_galWeak hW runTh

end UpperTheory.V.Z.Tf.GaloisFromTraceFormula
