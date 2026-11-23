import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.KatoGlobalUnitLawOfSmoothedClasses
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.NormFactorLeOne
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.AdmissibleWeightedDataMonoCoef
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SmoothedZetaClasses.SmoothedZetaClassHodgeTateLaw
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAdmissibleHeckeProjectionNonvanishingStatement

namespace UpperTheory.V.Z.Kato.Final

theorem zetaUr : GlobalTheory.Ord2.ZetaUr := GlobalTheory.KZ.zetaUr_of_halves2 _
  (UpperTheory.V.Z.Kato.Joint.kato_global_unit_law_of_smoothed_classes UpperTheory.Kd.K4.kato_eulerSystem_integrality UpperTheory.V.Z.Kato.K5.smoothedZetaClass_hodgeTateLaw
    (fun {Ω} _ _ _ => GlobalTheory.T.exists_admissible_hecke_projection_nonvanishing))
  UpperTheory.Kd.C7.pLocu

end UpperTheory.V.Z.Kato.Final
