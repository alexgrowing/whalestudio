import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

open GlobalTheory.BCT

theorem hintSph : HintSph := by
  intro G _ K u hu
  have hK : rStab u ⊓ K = K := inf_eq_right.mpr fun k hk x => hu k hk x
  unfold hint
  rw [hK, Subgroup.relIndex_self]
  simp

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
