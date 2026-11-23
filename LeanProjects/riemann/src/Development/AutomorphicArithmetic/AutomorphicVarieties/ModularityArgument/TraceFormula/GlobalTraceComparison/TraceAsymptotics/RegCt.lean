import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SplitLineAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConstantTermSplitPlaceRegular

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.regCt :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.RegCt := by
  intro E _ _ _ w hw μ n a b h f hf
  exact GlobalTheory.BCT.CtReg.ctMu_regAt2 E a b n h w (μ.loc w) (fun x => f w x.1) hw (fun y => hf y.1)
