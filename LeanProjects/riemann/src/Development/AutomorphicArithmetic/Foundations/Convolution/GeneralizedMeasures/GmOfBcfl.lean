import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.LinearMapCompEqOnSmulOfEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.LocUnit
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.UnitSplit

theorem UpperTheory.ConvolutionTheory.GM.gm_of_bcfl (h : PositivityTheory.Rg.Tf.Loc.BCFLUnit) : UpperTheory.ConvolutionTheory.GM.GM :=
  UpperTheory.ConvolutionTheory.GM.gm_of_unit (UpperTheory.V.Z.Tf.Orb.locUnit_of h fun F E _ _ _ _ _ _ σ hσ _ n _ v hv =>
    UpperTheory.ConvolutionTheory.L1.unitSplit F E σ hσ n v hv)
