import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IterationAndLinearityCuspidalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsExpansionZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowRealIteratedIntegralEqConstMulFiniteStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CellSumRelationsPassToIntegralsProofStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowPeriodGroupsSplitRealFiniteLargeDepthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedIntegrandBiInvariantLargeDepthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrandSupportedOnCellsLargeDepthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestCellValueOfStepsLargeDepthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SingleCosetOffTwistPlacesLargeDepthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefinitePeriodDependsOnProductFunctionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestDefinitePeriodChangeOfMeasuresStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CellMassesAgainstLevelVolumesLargeDepthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodReductionToFockVectorsLargeDepthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowUnfoldingBasicHypothesesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestSupportFamiliesStaircaseCosetsStatement

open GlobalTheory.RowClaim GlobalTheory.RowVal GlobalTheory.RowReal

namespace GlobalTheory.RowUnfLast

theorem stepUnfold : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → SumOKK → StepUnfold := fun p c s =>
  have rel := GlobalTheory.T.lastRow_real_iterated_integral_eq_const_mul_finite
  have hcv := GlobalTheory.T.cellSumRelationsPassToIntegrals_proof
  have grp := GlobalTheory.T.rowPeriodGroups_split_real_finite_large_depth
  have it := GlobalTheory.T.iteration_and_linearity_cuspidal
  have inv := GlobalTheory.T.unfolded_integrand_biInvariant_large_depth
  have flat := GlobalTheory.RowFlatAsm.flatAt_big
  have supp := GlobalTheory.T.integrand_supported_on_cells_largeDepth
  have rep := GlobalTheory.T.representation_at_every_place
  have val := GlobalTheory.T.rowTest_cellValue_of_steps_large_depth
  have off := GlobalTheory.T.singleCosetOffTwistPlaces_largeDepth
  have tens := GlobalTheory.T.definitePeriod_depends_on_productFunction
  have vol := GlobalTheory.T.rowTest_definitePeriod_change_of_measures
  have wt := GlobalTheory.T.cell_masses_against_level_volumes_large_depth
  have fock := GlobalTheory.T.periodReductionToFockVectors_large_depth
  have bas := GlobalTheory.T.lastRow_unfolding_basicHypotheses
  have one := GlobalTheory.T.rowTest_support_families_staircase_cosets
  have rl := GlobalTheory.RowReal.realLine
  big_mono (fun ch ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨rel, grp⟩, it⟩, inv⟩, ⟨e, fl⟩⟩, supp⟩, rep⟩, val⟩, off⟩, tens⟩, vol⟩, wt⟩, fock⟩, bas⟩, one⟩, rl⟩, s⟩ =>
    rel grp it.1 it.2 inv ⟨e, supp e fl off inv tens bas, rep e, val e fl tens vol (wt e) fock bas one s⟩ rl s)
  (((((((((((((((((rel hcv).and grp).and (it p c)).and inv).and flat).and supp).and rep).and val).and off).and tens).and vol).and wt).and fock).and bas).and one).and rl).and s)

end GlobalTheory.RowUnfLast
