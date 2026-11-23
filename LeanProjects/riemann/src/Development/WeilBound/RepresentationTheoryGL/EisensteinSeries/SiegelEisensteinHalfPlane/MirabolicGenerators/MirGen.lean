import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageMembershipStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageInvarianceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingOfAverageStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagonalTermGoodStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightTermGoodStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundaryTermGoodStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MasterIdentityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SideTermIdentityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVSmulStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VecKapMulStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaIntegralOfEpsteinConvStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SideTermUnfoldingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SideTermConvergenceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionSphericalKStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaValueAtOneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrincipalIdentityAssemblyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicGenerationStatement

namespace PositivityTheory.RgEis.MG

theorem mirGen : SecLaw → StdGood → BdetLaw → EpConv → EpMain → TestFun → TestSph → MirGen :=
  fun hS hG hB hC hM hT hSph =>
    have hO := GlobalTheory.T.side_term_identity hG hB
    have hZ := GlobalTheory.T.zeta_integral_of_epstein_conv hC
    GlobalTheory.T.mirabolic_generation hS hSph GlobalTheory.T.average_membership (GlobalTheory.T.average_invariance GlobalTheory.T.average_membership) hO (GlobalTheory.T.test_function_spherical_K hG hB hT)
      (GlobalTheory.T.principal_identity_assembly hM GlobalTheory.T.diagonal_term_good (GlobalTheory.T.master_identity GlobalTheory.T.average_membership GlobalTheory.T.diagonal_term_good GlobalTheory.T.height_term_good GlobalTheory.T.boundary_term_good) hO GlobalTheory.T.block_term_identity hZ
        (GlobalTheory.T.side_term_unfolding hC (GlobalTheory.T.unfolding_of_average hS GlobalTheory.T.average_membership) GlobalTheory.T.lines_decomposition GlobalTheory.T.block_term_identity hZ) (GlobalTheory.T.side_term_convergence hC hSph GlobalTheory.T.lines_decomposition GlobalTheory.T.block_term_identity) (GlobalTheory.T.zeta_value_at_one hM))

end PositivityTheory.RgEis.MG
