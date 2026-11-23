import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PlainAtR
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PlainIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.SphUnl
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.WinUnl

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Gam UpperTheory.V.Z.Win
open GroundTheory.Global.SemiLocal UpperTheory.V.Published

theorem UpperTheory.V.Z.Win.plainOf :
    PlainOf := by
  intro K _ _ _ n hn π v
  refine ⟨fun t hw => ?_, ?_⟩
  · exact (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.plainIff K n hn π v).2 ⟨hw.1, UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.winUnl K n π t v hw⟩
  · rintro ⟨B, hB⟩
    exact (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.plainIff K n hn π v).2 (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.sphUnl K n hn π v B hB)
