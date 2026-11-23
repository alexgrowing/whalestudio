import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.RankFourAutomorphyOfTensor
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PotOfFlag
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.FlagLaws

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N UpperTheory.V UpperTheory.V.Sd

theorem UpperTheory.V.Z.Win.Birth.potOrd :
    UpperTheory.V.Z.Win.Birth.PotOrd := by
  intro F Ω _ _ _ _ _ l _ n r m ψ κ hm H v hv
  have hp : UpperTheory.V.Z.Win.PotUnl r v := by
    refine UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.potOfFlag F Ω l n r m hm v hv fun A hA => ?_
    have hAl : A.valuation (l : Ω) < 1 := by
      have h1 := (hA ((l : ℕ) : 𝓞 F)).2 hv
      simpa using h1
    obtain ⟨c, hflag, hc, -⟩ := H A hAl
    exact ⟨c, 1, one_pos, hflag, fun i s hs => by rw [pow_one, pow_one]; exact hc i s hs⟩
  exact ((((UpperTheory.V.Z.Win.flagLaws F Ω l n r).2.1 κ).2.2 v).2).1 hp
