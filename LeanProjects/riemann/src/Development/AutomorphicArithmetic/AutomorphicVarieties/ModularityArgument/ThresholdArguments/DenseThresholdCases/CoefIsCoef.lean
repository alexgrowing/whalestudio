import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.ModU
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HidaU
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PointTheoremBaseObject

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.W
private theorem coef_isCoef (l : ℕ) [hl : Fact l.Prime] (c : Coef l) : Pa.IsCoef l c.O := by
  obtain ⟨hc, hf, hlm, -, -, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  refine ⟨hc, hf, (CharP.charP_iff_prime_eq_zero hl.out).2 ?_⟩
  rw [← map_natCast (IsLocalRing.residue c.O), IsLocalRing.residue_eq_zero_iff]
  exact hlm
theorem UpperTheory.V.W.modU_of_printsH :
    Pa.CohP → LocCFTAll → Pa.PfromAut → _root_.UpperTheory.V.W.HidaUAlt → _root_.UpperTheory.V.W.ModUAlt := by
  intro hcoh hloc hP hH l _ L Ω _ _ _ _ _ _ s V hS hμ c hc n hn r B Λ ι
  obtain ⟨J, hJ, hA⟩ := hH l L Ω s V hS hμ c hc n hn r B Λ ι
  haveI := coef_isCoef l c
  obtain ⟨h1, h3⟩ := hP hcoh l L Ω s V c.O n r B J hn hS (hloc l L Ω s) ((muL l L Ω s V).1 hμ) hA
  exact ⟨J, hJ, h1, h3⟩
end
