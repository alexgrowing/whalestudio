import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.ExtraV
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PotentiallySemistableType
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.V.Z.J.D
theorem UpperTheory.V.Z.J.D.type_pst_of_type_v :
    _root_.UpperTheory.V.Z.J.D.TypeVAlt → _root_.UpperTheory.V.Z.J.D.PotentiallySemistableType := by
  intro hV N L Ω _ _ _ _ _ _ n hn π w A h τ hτ χ hχ hT
  obtain ⟨rc, hrc⟩ := UpperTheory.Zero.LLC.recTExists L Ω A w h
  exact hV N L Ω n hn π w A h τ hτ χ hχ rc (UpperTheory.V.Z.Win.toV' hrc) (hT rc hrc)
end
