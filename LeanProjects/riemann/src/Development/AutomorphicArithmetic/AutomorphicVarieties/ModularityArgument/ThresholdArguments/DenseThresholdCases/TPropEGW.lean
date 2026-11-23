import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WEGCore

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
theorem UpperTheory.V.Z.Sym.W.prop_eg_w_of_printed_hida :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Z.Sym.W.PropEGW :=
  fun P l _ Ω _ _ _ ι c hc N w φ θ h1 h2 h3 =>
    (_root_.UpperTheory.V.Z.Sym.W.prop_eg_complex_of_printed_hida P l Ω ι c hc N w φ θ h1 h2 h3).imp fun _ H k hk hp =>
      (H k hk hp).imp fun ρ hρ =>
        ⟨hρ.1, hρ.2.1, UpperTheory.V.Z.Sym.Unl.adUnl ℚ Ω l ι ρ hρ.2.2.1 hρ.2.2.2⟩
end
