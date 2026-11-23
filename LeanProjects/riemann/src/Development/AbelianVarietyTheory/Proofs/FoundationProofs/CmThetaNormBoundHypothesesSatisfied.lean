import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationIntertwinerUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdmissibleCharactersExistStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateCurveDatumLatticeIsCurveLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateGaloisRationalityCmPointsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisDataExistsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaComplexConjugationCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugatesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugateStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTaylorCoeffsAlgebraicAtComplexMultiplicatioStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaVacuaConjugatesCmPointsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumNormConjCmPointsAllEmbeddingsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilRepresentationVacuumSignInertPlacesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddnessConditionHoldsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitaryClassRepTrivialAtCmStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DatumCurveIntegralUnitDiscModelStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTorsionTranslateIntegralSeriesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaValuesVanishAtOddSplitPrimeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaFunctionsOverTwoUnitAndIntegralStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmNormalizedThetaJetsIntegralStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertPrimeOrderParitySignRadicalIntegralForm
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum

theorem inp_all : ∀ D, Inp D := fun D =>
  { g1 := (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1
    perm := (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).2
    uni := GlobalTheory.T.intertwinerUnitary_all D
    mu := GlobalTheory.T.admissible_characters_exist D
    curve := GlobalTheory.T.conjugate_curveDatum_lattice_isCurveLattice D
    gal := GlobalTheory.T.thetaTranslate_galoisRationality_cmPoints D
    galEx := GlobalTheory.T.galois_data_exists D
    t0Ex := GlobalTheory.T.exists_twoTorsionCMPoint_all_conjugates D
    use1 := GlobalTheory.T.forall_use1 D
    alg := GlobalTheory.T.thetaTaylorCoeffs_algebraic_at_complexMultiplication D
    conj := GlobalTheory.T.thetaVacua_conjugates_cmPoints D
    nrm := GlobalTheory.T.vacuumNorm_conj_cmPoints_all_embeddings D
    bar := GlobalTheory.T.cmTheta_complexConjugation_compatible D
    odd3 := GlobalTheory.T.weilRepresentation_vacuum_sign_inert_places D
    odd4 := GlobalTheory.T.oddness_condition_holds D
    rep := GlobalTheory.T.exists_unitaryClass_rep_trivial_at_cm D
    model := GlobalTheory.T.datum_curve_integral_unitDisc_model D
    transl := GlobalTheory.T.cm_theta_torsion_translate_integral_series D
    two := GlobalTheory.T.cm_theta_functions_over_two_unit_and_integral D
    jets := GlobalTheory.T.cm_normalized_theta_jets_integral D
    split := GlobalTheory.T.cm_theta_values_vanish_at_odd_split_prime D
    eqv := GlobalTheory.OddRank.exact_equivariance D }

end GlobalTheory.NormSum
