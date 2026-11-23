import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.HsLinksOfUse
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackInputsOfStatements
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem inputs_of_use :
    ArithIntersectionSystemStatement → PositivityTheory.MbHsUse.HSUse →
      ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → ResK.ResKStatement → GlobalTheory.CompanionTheory.Ar.PB.Inputs := by
  intro hII hU hBig hRes
  exact ⟨⟨GlobalTheory.T.convergence_statement_holds, GlobalTheory.T.signed_convergence_statement_holds, GlobalTheory.T.convergence_rate_statement_holds, GlobalTheory.T.uniform_integrability_statement_holds, GlobalTheory.T.pullback_statement_holds, GlobalTheory.T.global_regularization_statement_holds⟩,
    ⟨GlobalTheory.T.resolution_exists_of_resolution_statement hRes, degree_of_system hII, (hsLinks_of_use hU hBig).1⟩,
    ⟨GlobalTheory.T.rationality_of_resolution_statement hRes, metricLocal⟩,
    ⟨GlobalTheory.T.projection_formula_of_arith_system hII, lineFibre_holds, fibreDim⟩,
    ⟨GlobalTheory.T.kleiman_nef_criteria_hold.1, GlobalTheory.T.kleiman_nef_criteria_hold.2, GlobalTheory.T.siu_inequality_integral_holds⟩⟩

end GlobalTheory.CompanionTheory.Ar.Giv
