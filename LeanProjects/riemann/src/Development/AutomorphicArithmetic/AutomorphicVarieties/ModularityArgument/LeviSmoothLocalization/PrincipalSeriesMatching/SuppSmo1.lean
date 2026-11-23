import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.Bridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.Strong

open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.suppSmo1 :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.SuppSmo1 := by
  intro K _ _ _ π π' h t v hw
  have e : π = π' := GlobalTheory.CuspRep.CuspSub.ext (UpperTheory.V.Af.strongMultOneC K 1 π π' h)
  exact e ▸ hw
