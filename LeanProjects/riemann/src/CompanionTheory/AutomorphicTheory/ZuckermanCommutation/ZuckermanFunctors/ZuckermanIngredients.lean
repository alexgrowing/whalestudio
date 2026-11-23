import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.DecompositionOfInjective
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DecompositionOfTraceStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HomCategoryStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorPowerIntegralStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TensorPowerIntegralStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MatrixHomStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SnTens2Statement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.UnitaryIsoStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CasimirSplittingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CasimirDiagonalSumStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StandardDifferentialStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorIntegralityStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorDifferentialMatrixUnitFormulaStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorDifferentialSignRuleQuadraticStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ZuckermanHypothesisStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DecompositionOfTensorFromHomLawsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ToRawComplexStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CountingBoundStatement
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.AdjFromApply
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.OrbitDerivatives.LieAlgebraHomomorphism
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.OrbitDerivatives.EtaleClosedPointLiftsSimpleRootsMonic
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.ShiftApply

namespace CompanionTheory.Zuck

theorem zuckerman_ingredients : Steps where
  infChar := CompanionTheory.D.DSIC.discrete_series_infinitesimal_character
  decOfInj := decomposition_of_injective
  decOfTrace := GlobalTheory.T.DecompositionOfTrace
  homCat := GlobalTheory.T.HomCategory
  okTriv := trivial_rep_admissible
  okVr := vector_rep_admissible
  okWedge := GlobalTheory.T.ExteriorPowerIntegral
  okTens := GlobalTheory.T.TensorPowerIntegral
  matHom := GlobalTheory.T.MatrixHom
  uIso := GlobalTheory.T.UnitaryIso
  homLie := CompanionTheory.D.gk.FinalFormK.lie_algebra_homomorphism
  casSplit := GlobalTheory.T.CasimirSplitting
  casDS := GlobalTheory.T.CasimirDiagonalSum
  wedgeInt := GlobalTheory.T.ExteriorIntegrality
  wedgeQ := GlobalTheory.T.exterior_differential_sign_rule_quadratic GlobalTheory.T.StandardDifferential GlobalTheory.T.exterior_differential_matrix_unit_formula
  schur := CompanionTheory.D.gk.FinalFormK.schur'
  adj := adj_of GlobalTheory.T.HomCategory GlobalTheory.T.MatrixHom GlobalTheory.T.tensHom'
  multOne := multOne_of GlobalTheory.T.HomCategory GlobalTheory.T.MatrixHom GlobalTheory.T.tensHom' CompanionTheory.D.gk.FinalFormK.lie_algebra_homomorphism GlobalTheory.T.CasimirSplitting GlobalTheory.T.StandardDifferential
    CompanionTheory.D.gk.FinalFormK.kerZero' trivial_rep_admissible vector_rep_admissible GlobalTheory.T.TensorPowerIntegral
  inj := CompanionTheory.D.gk.FinalFormK.injectivity_induction
  occ := CompanionTheory.D.gk.FinalFormK.occurrence_induction
  zuckH := GlobalTheory.T.zuckerman_hypothesis
  decTens := GlobalTheory.T.decomposition_of_tensor_from_hom_laws GlobalTheory.T.HomCategory GlobalTheory.T.MatrixHom GlobalTheory.T.tensHom' CompanionTheory.D.gk.FinalFormK.lie_algebra_homomorphism trivial_rep_admissible
  toRaw := GlobalTheory.T.ToRawComplex
  count := GlobalTheory.T.CountingBound

end CompanionTheory.Zuck
