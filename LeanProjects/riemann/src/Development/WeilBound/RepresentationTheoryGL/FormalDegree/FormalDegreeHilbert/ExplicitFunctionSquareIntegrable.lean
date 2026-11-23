import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.NormIndOfSteps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormInductionOfEstimates
import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.FormalDegreeFormula.CoefPow

namespace PositivityTheory.RgFd

open PositivityTheory.RgDs

theorem psiNorm : PsiNorm := psiNorm_of (normInd_of_steps coefPow GlobalTheory.CompanionTheory.RgFdNorm.norm_induction_of_estimates)

theorem explicit_function_square_integrable : ExplicitFunctionSquareIntegrable := square_integrable_of_norm psiNorm

theorem fdAll_of_key (hK : Key) (hH : Hilb) : FdAll := fdAll_of_norm psiNorm hK hH

end PositivityTheory.RgFd
