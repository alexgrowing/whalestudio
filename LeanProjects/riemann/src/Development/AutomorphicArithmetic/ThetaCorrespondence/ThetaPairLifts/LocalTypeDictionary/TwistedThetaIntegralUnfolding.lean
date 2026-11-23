import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingOfCuspidalLifts
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedIterateEventuallyLarge
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingOfCuspidalLiftsStatement

section
open GlobalTheory.RowClaim GlobalTheory.RowVal GlobalTheory.RowReal
namespace GlobalTheory.RowUnfLast
theorem twisted_theta_integral_unfolding : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → SumOKK → StepUnfold := fun p c s =>
  have rel := GlobalTheory.T.lastRow_real_iterated_integral_eq_const_mul_finite
  have hcv := GlobalTheory.T.cellSumRelationsPassToIntegrals_proof
  have grp := GlobalTheory.T.rowPeriodGroups_split_real_finite_large_depth
  have it := _root_.GlobalTheory.T.twisted_iterate_chain
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
end

section
open GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_theta_integral_unfolds : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → SumOKK → StepUnfold := by
  first | exact @_root_.GlobalTheory.RowUnfLast.twisted_theta_integral_unfolding | exact _root_.GlobalTheory.RowUnfLast.twisted_theta_integral_unfolding | (intros; apply _root_.GlobalTheory.RowUnfLast.twisted_theta_integral_unfolding <;> assumption)
end
