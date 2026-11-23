import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.AdjointEta
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.SumCardLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.AdSysOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.AnEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.NotDih

open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.adWit :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.AdWit := by
  intro hp l _ Ω _ _ _ ι k hk ρ hc hi hf K _ _ _ _ hd P ha w
  obtain ⟨N, _, χ, g, hχ, _, hr⟩ := hf
  rcases UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.anEx hp k N hk χ hχ g with hD | ⟨D, rfl, hs, hA⟩
  · exact absurd hD (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.notDih l Ω ι _ N χ g ρ hc hi hr)
  · have hsys := UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.adSysOf l Ω ι N χ D g ρ hr hs K P ha
    have hw : w.asIdeal.LiesOver (w.under (𝓞 ℚ)).asIdeal := ⟨rfl⟩
    exact (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.adK K hd D hA P hsys (w.under (𝓞 ℚ)) ⟨w, hw⟩).1
