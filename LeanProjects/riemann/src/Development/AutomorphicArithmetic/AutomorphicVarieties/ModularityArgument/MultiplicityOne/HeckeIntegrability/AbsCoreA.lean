import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.AbsGlobA
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.OpFormA
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.GlobalTwistedTraceBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.LiftRestrict
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.SeenTrA
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.HeckeComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.LevelTrA
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.PiTermAOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.PRankOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.PCorner
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.PMinIdem
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.PAbsCoreA
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.PLevIdx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.PVolIdx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PiTermEqTraceSumOfDegreeFourTest

namespace UpperTheory.V.Z.Mult.Pi

open UpperTheory.V.Z.GSp4Splitting UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

theorem global_twisted_trace_bound : GlobalTwistedTraceBound :=
  twisted_trace_global_bound_of_archimedean avgEx (absGlobA multiFac lieStab projEx avgFacts (onePlace coreG lieStab projEx avgFacts (avgTr avgFacts))) lowIso2 heckeMem
    (rlEx petEx heckeMem) rlPair rlChar rlK rlTheta rlComm (rlHecke heckeMem) (rlSimple heckeMem lieStab rlK) rlFin
    (rlLow heckeMem lowType) (opFormA locAct)

theorem absCoreA : AbsCoreA := absCoreA_pf (absCore_pf traceForm_pf) rankOne_pf corner_pf minIdem_pf

theorem levelTrA_holds : LevelTrA :=
  levelTrA adm (zTrA adm pfHecke prodOp locComm yLoc zSimple (ySwap_pf slotFacts pfHecke prodOp) (isot_pf slotFacts)
    (simpleFix_pf cvOp) absCoreA) (seenTrA trLevel adm cvOp) tTr

end UpperTheory.V.Z.Mult.Pi

open UpperTheory.V.Z.Mult.Pi UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm in
theorem UpperTheory.V.Z.Mult.piTermA : UpperTheory.V.Z.Mult.PiTermA :=
  piTermA_of global_twisted_trace_bound UpperTheory.V.Z.Tf.GOne.thetaFixOf wtEx_pf levTop levFix lcLevel_pf
    (toYdA slotFacts levTop translF_pf heckeSum_pf lvShift_pf) levelTrA_holds twUniq_pf (levIdx_pf slotFacts levTop) volIdx_pf
    (kf_top slotFacts levTop places)
