import Mathlib
import Development.EtaleCohomology.CohomologicalPurity.FinLeafAW
import Development.EtaleCohomology.CohomologicalPurity.FinLeafBd
import Development.EtaleCohomology.CohomologicalPurity.FinLeafChart
import Development.EtaleCohomology.CohomologicalPurity.FinLeafCl
import Development.EtaleCohomology.CohomologicalPurity.FinLeafExc
import Development.EtaleCohomology.CohomologicalPurity.FinLeafHens
import Development.EtaleCohomology.CohomologicalPurity.FinLeafIndExc
import Development.EtaleCohomology.CohomologicalPurity.FinLeafSemi
import Development.EtaleCohomology.CohomologicalPurity.FinLeafThom
import Development.EtaleCohomology.CohomologicalPurity.LeafAbvPf
import Development.EtaleCohomology.CohomologicalPurity.LeafActNatPf
import Development.EtaleCohomology.CohomologicalPurity.LeafAugInjPf
import Development.EtaleCohomology.CohomologicalPurity.LeafAugLocalPf
import Development.EtaleCohomology.CohomologicalPurity.LeafAugSurjPf
import Development.EtaleCohomology.CohomologicalPurity.LeafChPushPf
import Development.EtaleCohomology.CohomologicalPurity.LeafChainsSumPf
import Development.EtaleCohomology.CohomologicalPurity.LeafChiSqProof
import Development.EtaleCohomology.CohomologicalPurity.LeafEqvOfExcPf
import Development.EtaleCohomology.CohomologicalPurity.LeafExcAffPf
import Development.EtaleCohomology.CohomologicalPurity.LeafExcLevelPf
import Development.EtaleCohomology.CohomologicalPurity.LeafExcOfEqvPfSq
import Development.EtaleCohomology.CohomologicalPurity.LeafFstHocPf
import Development.EtaleCohomology.CohomologicalPurity.LeafGysinPf
import Development.EtaleCohomology.CohomologicalPurity.LeafHKSplitPf
import Development.EtaleCohomology.CohomologicalPurity.LeafHKSumPf
import Development.EtaleCohomology.CohomologicalPurity.LeafHensHPf
import Development.EtaleCohomology.CohomologicalPurity.LeafHomLocPf
import Development.EtaleCohomology.CohomologicalPurity.LeafHsSumPfR
import Development.EtaleCohomology.CohomologicalPurity.LeafLevelPf
import Development.EtaleCohomology.CohomologicalPurity.LeafLocBasePf
import Development.EtaleCohomology.CohomologicalPurity.LeafLocCutAug
import Development.EtaleCohomology.CohomologicalPurity.LeafLocExcPf
import Development.EtaleCohomology.CohomologicalPurity.LeafLocFstPf
import Development.EtaleCohomology.CohomologicalPurity.LeafLocHenPf
import Development.EtaleCohomology.CohomologicalPurity.LeafLocIsoPf
import Development.EtaleCohomology.CohomologicalPurity.LeafLocPrdPfX
import Development.EtaleCohomology.CohomologicalPurity.LeafMLevPf
import Development.EtaleCohomology.CohomologicalPurity.LeafPbSumPfR
import Development.EtaleCohomology.CohomologicalPurity.LeafPrdAffPfQuot
import Development.EtaleCohomology.CohomologicalPurity.LeafPrdHocPfX
import Development.EtaleCohomology.CohomologicalPurity.LeafPrdRingPf
import Development.EtaleCohomology.CohomologicalPurity.LeafPurNatPf
import Development.EtaleCohomology.CohomologicalPurity.LeafPurPf
import Development.EtaleCohomology.CohomologicalPurity.LeafPurProjPf
import Development.EtaleCohomology.CohomologicalPurity.LeafPurRedPf
import Development.EtaleCohomology.CohomologicalPurity.LeafPushPf
import Development.EtaleCohomology.CohomologicalPurity.LeafQisLocalPf
import Development.EtaleCohomology.CohomologicalPurity.LeafQuotPf
import Development.EtaleCohomology.CohomologicalPurity.LeafRefinePf
import Development.EtaleCohomology.CohomologicalPurity.LeafRelHocPfX
import Development.EtaleCohomology.CohomologicalPurity.LeafRelLevPfX
import Development.EtaleCohomology.CohomologicalPurity.LeafRelPf
import Development.EtaleCohomology.CohomologicalPurity.LeafSumPf
import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut
import Development.EtaleCohomology.CohomologicalPurity.LeafUnivSumPf
import Development.EtaleCohomology.CohomologicalPurity.LeafZPf
import Development.EtaleCohomology.CohomologicalPurity.Imports
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EtaleExcisionHocolimOfLocalProperties
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.HocolimAugmentationInjectiveOfPurityInputs
import Development.AutomorphicArithmetic.CommutativeAlgebra.ProductLevelwiseOfAlexanderWhitney

theorem UpperTheory.Et.purAll : LateralTheory.CohomologicalPurity.LeafTube ∧ LateralTheory.CohomologicalPurity.LeafGysin ∧ LateralTheory.CohomologicalPurity.Goal := by
  have h_EPur_LeafAW : LateralTheory.CohomologicalPurity.LeafAW := LateralTheory.Fin.LeafAW.intersectionNumber_baseChange
  have h_EPur_LeafBd : LateralTheory.CohomologicalPurity.LeafBd := by apply LateralTheory.Fin.LeafBd.intersectionNumber_baseChange
  have h_EPur_LeafCl : LateralTheory.CohomologicalPurity.LeafCl := by apply LateralTheory.Fin.LeafCl.intersectionNumber_baseChange
  have h_EPur_LeafChart : LateralTheory.CohomologicalPurity.LeafChart := by apply LateralTheory.Fin.LeafChart.intersectionNumber_baseChange
  have h_EPur_LeafHens : LateralTheory.CohomologicalPurity.LeafHens := by apply LateralTheory.Fin.LeafHens.intersectionNumber_baseChange
  have h_EPur_LeafIndExc : LateralTheory.CohomologicalPurity.LeafIndExc := by apply LateralTheory.Fin.LeafIndExc.intersectionNumber_baseChange
  have h_EPur_LeafThom : LateralTheory.CohomologicalPurity.LeafThom := by apply LateralTheory.Fin.LeafThom.intersectionNumber_baseChange
  have h_EPur_LeafSemi : LateralTheory.CohomologicalPurity.LeafSemi := by apply LateralTheory.Fin.LeafSemi.intersectionNumber_baseChange
  have h_EPur_LeafExc : LateralTheory.CohomologicalPurity.LeafExc := by apply LateralTheory.Fin.LeafExc.intersectionNumber_baseChange
  have h_EPur_LeafPurNat : LateralTheory.CohomologicalPurity.EtalePurityNaturality := by apply LateralTheory.CohomologicalPurity.LeafPurNat_of
  have h_EPur_LeafPurProj : LateralTheory.CohomologicalPurity.EtalePurityProjection := by apply LateralTheory.CohomologicalPurity.LeafPurProj_of
  have h_EPur_LeafPurRed : LateralTheory.CohomologicalPurity.EtalePurityReduction := by apply LateralTheory.CohomologicalPurity.LeafPurRed_of
  have h_EPur_TubeCut_LeafChPush : LateralTheory.CohomologicalPurity.TubeCut.LeafChPush := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafChPush_of
  have h_EPur_TubeCut_LeafHKSplit : LateralTheory.CohomologicalPurity.TubeCut.LeafHKSplit := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafHKSplit_of
  have h_relative : LateralTheory.CohomologicalPurity.TubeCut.LeafRel := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafRel_of <;> assumption
  have h_equivalence_of_excision : LateralTheory.CohomologicalPurity.TubeCut.LeafEqvOfExc := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafEqvOfExc_of <;> assumption
  have h_EPur_TubeCut_LeafChiSq : LateralTheory.CohomologicalPurity.TubeCut.LeafChiSq := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafChiSq_of
  have h_excision_of_equivalence : LateralTheory.CohomologicalPurity.TubeCut.LeafExcOfEqv := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafExcOfEqv_of_sq <;> assumption
  have h_EPur_TubeCut_LeafMLev : LateralTheory.CohomologicalPurity.TubeCut.LeafMLev := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafMLev_of
  have h_excision_levelwise : LateralTheory.CohomologicalPurity.TubeCut.LeafExcLevel := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafExcLevel_of <;> assumption
  have h_levelwise : LateralTheory.CohomologicalPurity.TubeCut.LeafLevel := by apply LateralTheory.CohomologicalPurity.LeafLevelPf.LeafLevel_of
  have h_pullback_sum : LateralTheory.CohomologicalPurity.TubeCut.LeafPbSum := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafPbSum_of
  have h_double_sum : LateralTheory.CohomologicalPurity.TubeCut.LeafDblSum := by apply LateralTheory.CohomologicalPurity.TubeCut.leafDblSum_of <;> assumption
  have h_EPur_TubeCut_LeafDiscSumH : LateralTheory.CohomologicalPurity.TubeCut.LeafDiscSumH := by apply LateralTheory.CohomologicalPurity.TubeCut.leafDiscSumH
  have h_chains_sum : LateralTheory.CohomologicalPurity.TubeCut.SumCut.LeafChainsSum := by apply LateralTheory.CohomologicalPurity.TubeCut.SumCut.LeafChainsSum_of
  have h_EPur_TubeCut_SumCut_LeafHKSum : LateralTheory.CohomologicalPurity.TubeCut.SumCut.LeafHKSum := by apply LateralTheory.CohomologicalPurity.TubeCut.SumCut.LeafHKSum_of
  have h_sum₂ : LateralTheory.CohomologicalPurity.TubeCut.LeafSum := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafSum_of <;> assumption
  have h_EPur_TubeCut_LeafHsSum : LateralTheory.CohomologicalPurity.TubeCut.LeafHsSum := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafHsSum_of_dbl <;> assumption
  have h_excision_hocolim : LateralTheory.CohomologicalPurity.TubeCut.LeafExcHoc := by apply UpperTheory.Cb.etale_excision_hocolim_of_local_properties <;> assumption
  have h_EPur_TubeCut_LeafDiscPb : LateralTheory.CohomologicalPurity.TubeCut.LeafDiscPb := by apply LateralTheory.CohomologicalPurity.TubeCut.leafDiscPb
  have h_universal_sum : LateralTheory.CohomologicalPurity.TubeCut.LeafUnivSum := by apply LateralTheory.CohomologicalPurity.TubeCut.leafUnivSum
  have h_EPur_TubeCut_LeafFstHoc : LateralTheory.CohomologicalPurity.TubeCut.LeafFstHoc := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafFstHoc_of <;> assumption
  have h_augmentation_injective_at : LateralTheory.CohomologicalPurity.TubeCut.EtaleAugInjAt := by apply UpperTheory.Cb.hocolimAugmentation_injective_of_purity_inputs <;> assumption
  have h_augmentation_injective : LateralTheory.CohomologicalPurity.TubeCut.LeafAugInj := by apply LateralTheory.CohomologicalPurity.TubeCut.EtaleAugInj_of_augInjAt <;> assumption
  have h_augmentation_surjective : LateralTheory.CohomologicalPurity.TubeCut.LeafAugSurj := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafAugSurj_of
  have h_EPur_TubeCut_LeafHomLoc : LateralTheory.CohomologicalPurity.TubeCut.LeafHomLoc := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafHomLoc_of
  have h_augmentation_local : LateralTheory.CohomologicalPurity.TubeCut.LeafAugLocal := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafAugLocal_of <;> assumption
  have h_EPur_TubeCut_LeafLocBase : LateralTheory.CohomologicalPurity.TubeCut.EtaleLocBase := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafLocBase_of
  have h_quasi_isomorphism_local : LateralTheory.CohomologicalPurity.TubeCut.LeafQisLocal := by apply LateralTheory.CohomologicalPurity.QisLocalPf.LeafQisLocal_of
  have h_EPur_TubeCut_LeafLoc : LateralTheory.CohomologicalPurity.TubeCut.LeafLoc := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafLocCutAll.goal_of <;> assumption
  have h_EPur_TubeCut_LeafLocExc : LateralTheory.CohomologicalPurity.TubeCut.LeafLocExc := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafLocExc_of <;> assumption
  have h_EPur_TubeCut_LeafZ : LateralTheory.CohomologicalPurity.TubeCut.LeafZ := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafZ_of
  have h_EPur_TubeCut_LeafLocFst : LateralTheory.CohomologicalPurity.TubeCut.LeafLocFst := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafLocFst_of <;> assumption
  have h_EPur_TubeCut_LeafAbv : LateralTheory.CohomologicalPurity.TubeCut.LeafAbv := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafAbv_of
  have h_EPur_TubeCut_LeafLocHen : LateralTheory.CohomologicalPurity.TubeCut.LeafLocHen := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafLocHen_of <;> assumption
  have h_quotient : LateralTheory.CohomologicalPurity.TubeCut.LeafQuot := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafQuot_of
  have h_EPur_TubeCut_LeafLocIso : LateralTheory.CohomologicalPurity.TubeCut.LeafLocIso := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafLocIso_of <;> assumption
  have h_EPur_TubeCut_LeafActNat : LateralTheory.CohomologicalPurity.TubeCut.LeafActNat := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafActNat_of
  have h_excision_affine : LateralTheory.CohomologicalPurity.TubeCut.LeafExcAff := by apply LateralTheory.CohomologicalPurity.TubeCut.leafExcAff_pf
  have h_EPur_TubeCut_LeafHensH : LateralTheory.CohomologicalPurity.TubeCut.LeafHensH := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafHensH_of
  have h_product_affine : LateralTheory.CohomologicalPurity.TubeCut.LeafPrdAff := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafPrdAff_of' <;> assumption
  have h_product_ring : LateralTheory.CohomologicalPurity.TubeCut.LeafPrdRing := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafPrdRing_of <;> assumption
  have h_EPur_TubeCut_LeafLocPrd : LateralTheory.CohomologicalPurity.TubeCut.LeafLocPrd := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafLocPrd_of <;> assumption
  have h_product_levelwise : LateralTheory.CohomologicalPurity.TubeCut.LeafPrdLevel := by apply UpperTheory.productLevelwise_of_alexanderWhitney <;> assumption
  have h_product_hocolim : LateralTheory.CohomologicalPurity.TubeCut.LeafPrdHoc := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafPrdHoc_of <;> assumption
  have h_EPur_TubeCut_LeafPush : LateralTheory.CohomologicalPurity.TubeCut.LeafPush := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafPush_of
  have h_refinement : LateralTheory.CohomologicalPurity.TubeCut.LeafRefine := by apply LateralTheory.CohomologicalPurity.TubeCut.EtaleRefine_of_push <;> assumption
  have h_relative_levelwise : LateralTheory.CohomologicalPurity.TubeCut.LeafRelLev := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafRelLev_of
  have h_relative_hocolim : LateralTheory.CohomologicalPurity.TubeCut.LeafRelHoc := by apply LateralTheory.CohomologicalPurity.TubeCut.LeafRelHoc_of <;> assumption
  have h_EPur_LeafTube : LateralTheory.CohomologicalPurity.LeafTube := by apply LateralTheory.CohomologicalPurity.TubeCut.goal_of <;> assumption
  have h_EPur_LeafPur : LateralTheory.CohomologicalPurity.LeafPur := by apply LateralTheory.CohomologicalPurity.EtalePurity_of_parts <;> assumption
  have h_EPur_LeafGysin : LateralTheory.CohomologicalPurity.LeafGysin := by apply LateralTheory.CohomologicalPurity.LeafGysin_of <;> assumption
  have h_cohomological_purity : LateralTheory.CohomologicalPurity.Goal := by apply LateralTheory.CohomologicalPurity.goal_of <;> assumption
  exact ⟨h_EPur_LeafTube, h_EPur_LeafGysin, h_cohomological_purity⟩

theorem UpperTheory.Et.purTube : LateralTheory.CohomologicalPurity.LeafTube := UpperTheory.Et.purAll.1
theorem UpperTheory.Et.purGysin : LateralTheory.CohomologicalPurity.LeafGysin := UpperTheory.Et.purAll.2.1
theorem UpperTheory.Et.purGoal : LateralTheory.CohomologicalPurity.Goal := UpperTheory.Et.purAll.2.2
