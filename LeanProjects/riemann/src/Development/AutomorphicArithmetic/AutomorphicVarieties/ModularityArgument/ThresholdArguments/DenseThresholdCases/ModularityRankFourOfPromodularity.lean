import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Pur
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.MapRepComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.CharpolyMapRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PromodularityCaseThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PotentialModularityTower
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsAut4
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Gsp4PromodularityCaseTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ContradictionStarPromodular
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CharpolyConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.MapRepComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWinPm

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
theorem UpperTheory.V.Cu.modularity_rank_four_of_promodularity_case_three : _root_.UpperTheory.V.Cu.PromodularityCaseThreeDense → _root_.UpperTheory.V.Cu.AutomorphyRankFourDense := by
  intro hA4 hP hFW hFit h2 h4 hPM Ω _ _ _ h t hB l _ c e _ he0 het ψ hψ D hD hcase
  have hctx : Ctx2 D ∨ Ctx3 D :=
    hcase.imp (fun hc => ⟨hD, h, t, e, ψ, hB, he0, het, hψ, hc.1, hc.2⟩)
      (fun hc => ⟨hD, h, t, e, ψ, hB, he0, het, hψ, hc.1, hc.2⟩)
  obtain ⟨ι⟩ := (UpperTheory.V.Ws.ambZero l).2
  have hA : ∀ (𝔞 : Amb l) r u, KPair D 𝔞 r u → Star (mapRep 𝔞.toK r) → _root_.UpperTheory.V.Ws.ProModAlt D ι 𝔞 r := by
    intro 𝔞 r u hK hS
    rcases hctx with h₂ | h₃
    · exact _root_.UpperTheory.V.Ws.proMod_of_pmEx_of_ctx2_of_kPair_of_star hP hFW h2 hPM D h₂ ι 𝔞 r u hK hS
    · exact hA4 hP hFW hFit h4 hPM D h₃ ι 𝔞 r u hK hS
  have hcon : Con D := fun 𝔞 hch r u hK hS =>
    _root_.UpperTheory.V.Ws.contradiction_star_promodular D hD ι 𝔞 hch r u hK (hA 𝔞 r u hK hS) hS
  have hpur : _root_.UpperTheory.V.Ws.PurityAtPoints D ι := fun 𝔞 e' he' r u hK hS =>
    _root_.UpperTheory.V.Ws.pureW_of_proModular_of_isZero D hD ι 𝔞 e' he' r (hA 𝔞 r u hK hS)
  have haut : _root_.UpperTheory.V.Ws.AutmAlt D ι := fun 𝔞 e' he' r u hK hI =>
    _root_.UpperTheory.V.Ws.aut_n_alt D hD ι 𝔞 e' he' r u hK (hA 𝔞 r u hK (Or.inl hI)) hI
  obtain ⟨hF, hN, hAll⟩ := _root_.UpperTheory.V.Ws.fin0_no_end_all_irr_of_good_con_purity_aut hP D hD ι hcon hpur haut
  exact ⟨hF, hN, ι, hAll⟩
end
