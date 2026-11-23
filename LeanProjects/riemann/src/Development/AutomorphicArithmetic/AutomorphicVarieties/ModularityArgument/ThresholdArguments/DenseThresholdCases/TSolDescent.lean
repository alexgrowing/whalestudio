import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SolDescent
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CuspUnique

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField UpperTheory.V.Af
theorem UpperTheory.V.Af.solvable_descent_of_printed_hida :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Af.SolDescent := by
  intro H F₀ F M Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hF hsol hplus hM l _ ι n hn r μ hr hirr hμ hs ⟨c, P, hc, hP⟩
  have hM' : IsCMField M := hM.resolve_left fun h => by
    obtain ⟨v⟩ : Nonempty (InfinitePlace M) := inferInstance
    exact (InfinitePlace.not_isReal_iff_isComplex.2 ((isTotallyComplex_of_algebra F M).isComplex v)) (h.isReal v)
  exact _root_.UpperTheory.V.Z.Bc.solC_alt H H.cyc F M Ω hsol hF hM' l ι n hn r hr hirr ⟨F₀, _, _, _, _, inferInstance, inferInstance, hplus.1, μ, c, P, hμ, hs, hc, hP⟩
end
