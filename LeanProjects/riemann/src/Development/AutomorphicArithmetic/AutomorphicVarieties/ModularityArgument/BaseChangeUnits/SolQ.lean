import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SolvableEquivalenceOfBaseChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SolCOfSolDescent

theorem UpperTheory.V.Z.Bc.solQ (h : UpperTheory.V.Z.Bc.SolE) : UpperTheory.V.Z.Bc.SolC := by
  intro F₀ F M Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsol hplus hF hM l _ ι n hn r μ hr hirr hμ hs ⟨c, P, hc, hP⟩
  exact h F M Ω hsol hF hM l ι n hn r hr hirr ⟨F₀, _, _, _, _, inferInstance, inferInstance, hplus.1, μ, c, P, hμ, hs, hc, hP⟩
