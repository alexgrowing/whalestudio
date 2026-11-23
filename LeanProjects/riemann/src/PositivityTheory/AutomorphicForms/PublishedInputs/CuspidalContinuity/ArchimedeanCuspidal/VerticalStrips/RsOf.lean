import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.RsAsm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergLocalFirstStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergLocalSecondStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergLocalFourthStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergThirdOfSecondFourthStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergFifthOfSecondStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergSixthOfEarlierStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergSeventhOfSecondStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelFunctionalEquationOfTwoVariableStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergGammaFactorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergFunctionalEquationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergMeromorphicContinuationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergLocalNonvanishingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupCosetDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCosetRepresentativesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformHeckeEigenvalueStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformTorusVanishingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformMultiplicityOneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformMultiplicityOneUnramifiedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedRankinSelbergLocalFactorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedWhittakerNewformStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalRankinSelbergBasicFactsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainDescriptionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainInvarianceOfDescriptionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainIntegralCentralInvarianceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterIntegralPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingBottomRowOrbitsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingMirabolicCosetsStatementStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingIntegralBottomRowStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EpsteinSeriesAbsoluteConvergenceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergUnfoldingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaIntegralAbsoluteConvergenceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalZetaIntegralConvergenceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalZetaIntegralUnfoldedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinBasicFirstStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinBasicSecondStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinBasicThirdStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianSchwartzBruhatStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SymplecticFourierGaussianStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanLocalIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalFunctionalEquationH1Statement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftExistenceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftConductorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLevelStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLevelCharacterStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLocalTypeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftHeckeEigenvaluesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftWhittakerExpansionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftRapidDecayStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftFourierCoefficientsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftCuspidalityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftCuspFormStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLocalWhittakerStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinEulerProductStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergEulerProductPartialStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergEulerProductStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeProjectionEigenformStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergGlobalIdentityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergGammaBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergArchimedeanFactorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergLFunctionAnalyticStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergTheoremStatement

namespace Ad3.R

theorem rs_of : Ad3.Loc2 → Ad3.RS :=
  rs_asm
    (@GlobalTheory.T.rankin_selberg_local_first : Ad3.R.A1)
    (@GlobalTheory.T.rankin_selberg_local_second : Ad3.R.A2)
    (@GlobalTheory.T.rankin_selberg_local_fourth : Ad3.R.A4)
    (@GlobalTheory.T.rankin_selberg_third_of_second_fourth : Ad3.R.A2 → Ad3.R.A4 → Ad3.R.A3)
    (@GlobalTheory.T.rankin_selberg_fifth_of_second : Ad3.R.A2 → Ad3.R.A5)
    (@GlobalTheory.T.rankin_selberg_sixth_of_earlier : Ad3.R.A1 → Ad3.R.A3 → Ad3.R.A4 → Ad3.R.A5 → Ad3.R.A6)
    (@GlobalTheory.T.rankin_selberg_seventh_of_second : Ad3.R.A2 → Ad3.R.A7)
    (@GlobalTheory.T.kernel_functional_equation_of_two_variable : Ad3.R.A7 → Ad3.R.A8)
    (@GlobalTheory.T.rankin_selberg_gamma_factor : Ad3.R.LocalGammaFunctionalEquation)
    (@GlobalTheory.T.rankin_selberg_functional_equation : Ad3.R.A1 → Ad3.R.A6 → Ad3.R.A8 → Ad3.R.LocalGammaFunctionalEquation → Ad3.R.A9)
    (@GlobalTheory.T.rankin_selberg_meromorphic_continuation : Ad3.Loc2 → Ad3.R.A10)
    (@GlobalTheory.T.rankin_selberg_local_nonvanishing : Ad3.Loc2 → Ad3.R.A10 → Ad3.R.A11)
    (@GlobalTheory.T.congruence_subgroup_coset_decomposition : Ad3.R.C1)
    (@GlobalTheory.T.hecke_coset_representatives : Ad3.R.C0)
    (@GlobalTheory.T.newform_hecke_eigenvalue : Ad3.R.C1 → Ad3.R.U1)
    (@GlobalTheory.T.newform_torus_vanishing : Ad3.R.C1 → Ad3.R.U0)
    (@GlobalTheory.T.newform_multiplicity_one : Ad3.R.A2 → Ad3.R.C1 → Ad3.R.M1)
    (@GlobalTheory.T.newform_multiplicity_one_unramified : Ad3.R.A2 → Ad3.R.C1 → Ad3.R.M0)
    (@GlobalTheory.T.unramified_rankin_selberg_local_factor : Ad3.Loc2 → Ad3.R.E4)
    (@GlobalTheory.T.unramified_whittaker_newform : Ad3.R.U2)
    (@GlobalTheory.T.global_rankin_selberg_basic_facts : Ad3.R.B0)
    (@GlobalTheory.T.fundamental_domain_description : Ad3.R.D0)
    (@GlobalTheory.T.fundamental_domain_invariance_of_description : Ad3.R.D0 → Ad3.R.G0)
    (@GlobalTheory.T.fundamental_domain_integral_central_invariance : Ad3.R.G1a)
    (@GlobalTheory.T.central_character_integral_properties : Ad3.R.G1a → Ad3.R.G1)
    (@GlobalTheory.T.unfolding_bottom_row_orbits : Ad3.R.G2a)
    (@GlobalTheory.T.unfolding_mirabolic_cosets_statement : Ad3.R.G2b)
    (@GlobalTheory.T.unfolding_integral_bottom_row : Ad3.R.G2b → Ad3.R.G2c)
    (@GlobalTheory.T.epstein_series_absolute_convergence : Ad3.R.G3a)
    (@GlobalTheory.T.rankin_selberg_unfolding : Ad3.R.G2a → Ad3.R.G2b → Ad3.R.G3a → Ad3.R.G3)
    (@GlobalTheory.T.zeta_integral_absolute_convergence : Ad3.R.AdelicThetaPoissonSummation)
    (@GlobalTheory.T.global_zeta_integral_convergence : Ad3.R.G1a → Ad3.R.G3 → Ad3.R.AdelicThetaPoissonSummation → Ad3.R.G4)
    (@GlobalTheory.T.global_zeta_integral_unfolded : Ad3.R.G2c → Ad3.R.G3 → Ad3.R.G3a → Ad3.R.G5)
    (@GlobalTheory.T.eisenstein_basic_first : Ad3.R.B0 → Ad3.R.E1)
    (@GlobalTheory.T.eisenstein_basic_second : Ad3.R.B0 → Ad3.R.E2)
    (@GlobalTheory.T.eisenstein_basic_third : Ad3.R.B0 → Ad3.R.E3)
    (@GlobalTheory.T.gaussian_schwartz_bruhat : Ad3.R.GS)
    (@GlobalTheory.T.symplectic_fourier_gaussian : Ad3.R.B0 → Ad3.R.FT)
    (@GlobalTheory.T.archimedean_local_integral : Ad3.R.E5)
    (@GlobalTheory.T.global_functional_equation_h1 : Ad3.R.B0 → Ad3.R.E2 → Ad3.R.H1)
    (@GlobalTheory.T.newform_lift_existence : Ad3.R.B0 → Ad3.R.F0)
    (@GlobalTheory.T.newform_lift_conductor : Ad3.R.B0 → Ad3.R.F0b)
    (@GlobalTheory.T.newform_lift_level : Ad3.R.B0 → Ad3.R.F1)
    (@GlobalTheory.T.newform_lift_level_character : Ad3.R.B0 → Ad3.R.AutomorphicLevelEquivariance)
    (@GlobalTheory.T.newform_lift_local_type : Ad3.R.B0 → Ad3.R.HeckeSumLocalTranslates)
    (@GlobalTheory.T.newform_lift_hecke_eigenvalues : Ad3.R.B0 → Ad3.R.C0 → Ad3.R.C1 → Ad3.R.F0b → Ad3.R.F1 → Ad3.R.AutomorphicLevelEquivariance → Ad3.R.HeckeSumLocalTranslates → Ad3.R.F3)
    (@GlobalTheory.T.newform_lift_whittaker_expansion : Ad3.R.F2)
    (@GlobalTheory.T.newform_lift_rapid_decay : Ad3.R.B0 → Ad3.R.F5)
    (@GlobalTheory.T.newform_lift_fourier_coefficients : Ad3.R.B0 → Ad3.R.C1 → Ad3.R.U2 → Ad3.R.G0 → Ad3.R.G1 → Ad3.R.F0b → Ad3.R.F1 → Ad3.R.F2 → Ad3.R.F3 → Ad3.R.F5 → Ad3.R.F4)
    (@GlobalTheory.T.newform_lift_cuspidality : Ad3.R.F6)
    (@GlobalTheory.T.newform_lift_cusp_form : Ad3.R.B0 → Ad3.R.ConstantTermVanishingAlt)
    (@GlobalTheory.T.newform_lift_local_whittaker : Ad3.Loc2 → Ad3.R.B0 → Ad3.R.U0 → Ad3.R.U1 → Ad3.R.M0 → Ad3.R.M1 → Ad3.R.F0b → Ad3.R.F1 → Ad3.R.F2 → Ad3.R.F3 → Ad3.R.F4 → Ad3.R.F7)
    (@GlobalTheory.T.eisenstein_euler_product : Ad3.R.B0 → Ad3.R.M0 → Ad3.R.F3 → Ad3.R.E0)
    (@GlobalTheory.T.rankin_selberg_euler_product_partial : Ad3.Loc2 → Ad3.R.B0 → Ad3.R.A10 → Ad3.R.M0 → Ad3.R.E4 → Ad3.R.E0 → Ad3.R.E1 → Ad3.R.E2 → Ad3.R.UnramifiedEulerProductIntegral)
    (@GlobalTheory.T.rankin_selberg_euler_product : Ad3.Loc2 → Ad3.R.B0 → Ad3.R.A10 → Ad3.R.E2 → Ad3.R.E3 → Ad3.R.E5 → Ad3.R.UnramifiedEulerProductIntegral → Ad3.R.F2 → Ad3.R.E6)
    (@GlobalTheory.T.hecke_projection_eigenform : Ad3.R.B0 → Ad3.R.C1 → Ad3.R.G1 → Ad3.R.F0b → Ad3.R.F1 → Ad3.R.F3 → Ad3.R.F5 → Ad3.R.G6)
    (@GlobalTheory.T.rankin_selberg_global_identity : Ad3.R.B0 → Ad3.R.A1 → Ad3.R.G0 → Ad3.R.G2a → Ad3.R.G4 → Ad3.R.G5 → Ad3.R.GS → Ad3.R.FT → Ad3.R.F2 → Ad3.R.F5 → Ad3.R.F6 → Ad3.R.ConstantTermVanishingAlt → Ad3.R.E6 → Ad3.R.G6 → Ad3.R.X0)
    (@GlobalTheory.T.rankin_selberg_gamma_bound : Ad3.R.RealPlaceGammaFactors)
    (@GlobalTheory.T.rankin_selberg_archimedean_factor : Ad3.R.HalfPlaneAnalyticIdentities)
    (@GlobalTheory.T.rankin_selberg_l_function_analytic : Ad3.Loc2 → Ad3.R.B0 → Ad3.R.A9 → Ad3.R.LocalGammaFunctionalEquation → Ad3.R.A10 → Ad3.R.A11 → Ad3.R.H1 → Ad3.R.F0b → Ad3.R.F1 → Ad3.R.X0 → Ad3.R.RealPlaceGammaFactors → Ad3.R.HalfPlaneAnalyticIdentities → Ad3.R.X1)
    (@GlobalTheory.T.rankin_selberg_theorem : Ad3.R.B0 → Ad3.R.F0 → Ad3.R.F1 → Ad3.R.F7 → Ad3.R.X1 → Ad3.RS)

end Ad3.R
