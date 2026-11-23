import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.RCountAt

open UpperTheory.V.Z.Mult UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

theorem UpperTheory.V.Z.Mult.offSec :
    UpperTheory.V.Z.Mult.OffSec := by
  intro E _ _ _ n S K' K'' h
  unfold GlobalTheory.BCT.globLev
  refine iInf_congr fun w => iInf_congr fun hw => ?_
  rw [h w hw]
