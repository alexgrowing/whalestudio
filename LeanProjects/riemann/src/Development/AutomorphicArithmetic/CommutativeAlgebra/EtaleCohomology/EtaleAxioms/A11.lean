import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.LeafProdLeafLocOfLeafLevel
import Development.AutomorphicArithmetic.CommutativeAlgebra.LeafProdHolds
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineLeafOfProjectiveLeaves
import Development.EtaleCohomology.EtaleSheaves.ChartAwayPf
import Development.EtaleCohomology.EtaleSheaves.ChartGeoPf
import Development.EtaleCohomology.EtaleSheaves.AwSpec
import Development.EtaleCohomology.EtaleSheaves.LeafChartAffPf
import Development.EtaleCohomology.EtaleSheaves.LeafChartAwayPf
import Development.EtaleCohomology.EtaleSheaves.LeafChartPf
import Development.EtaleCohomology.EtaleSheaves.LeafChartRingPf
import Development.EtaleCohomology.EtaleSheaves.LeafCokIsoPf
import Development.EtaleCohomology.EtaleSheaves.LeafCoordsPfNakH
import Development.EtaleCohomology.EtaleSheaves.LeafCoordsPointPf
import Development.EtaleCohomology.EtaleSheaves.LeafCoordsPointResPfY
import Development.EtaleCohomology.EtaleSheaves.LeafCov1Of
import Development.EtaleCohomology.EtaleSheaves.EtLocOfOpens
import Development.EtaleCohomology.EtaleSheaves.LeafDiscPf
import Development.EtaleCohomology.EtaleSheaves.ConeExcision.ExcisionOfCokernel
import Development.EtaleCohomology.EtaleSheaves.LeafExcRingOf
import Development.EtaleCohomology.EtaleSheaves.LeafFreeLocPf
import Development.EtaleCohomology.EtaleSheaves.LeafHIPf
import Development.EtaleCohomology.EtaleSheaves.LeafJacobianPf
import Development.EtaleCohomology.EtaleSheaves.LeafLevelPf
import Development.EtaleCohomology.EtaleSheaves.LeafPolyEtPf
import Development.EtaleCohomology.EtaleSheaves.LeafProjPf
import Development.EtaleCohomology.EtaleSheaves.LeafQuotEtPf
import Development.EtaleCohomology.EtaleSheaves.LeafRelPf
import Development.EtaleCohomology.EtaleSheaves.LeafResDimQePf
import Development.EtaleCohomology.EtaleSheaves.LeafResKerPf
import Development.EtaleCohomology.EtaleSheaves.LeafRoofEtPPf
import Development.EtaleCohomology.EtaleSheaves.LeafRoofEtPf
import Development.EtaleCohomology.EtaleSheaves.LeafRoofPf
import Development.EtaleCohomology.EtaleSheaves.LeafSqPf
import Development.EtaleCohomology.EtaleSheaves.SheafPushoutSquare
import Development.EtaleCohomology.EtaleSheaves.ChainTower
import Development.EtaleCohomology.EtaleSheaves.InstCommRingR
import Development.EtaleCohomology.EtaleSheaves.LeafChartRing

namespace UpperTheory.Et.E6

theorem a0 : LateralTheory.E.t_E6Cut.LeafRel := LateralTheory.E.t_E6Cut.LeafRel_of
theorem a1 : LateralTheory.E.LeafLevelPf.LeafDisc := LateralTheory.E.LeafDiscPf.LeafDisc_of
theorem a2 : LateralTheory.E.LeafLevelPf.LeafFilt := LateralTheory.E.ChainTower.LeafFilt_of
theorem a3 : LateralTheory.E.t_E6Cut.LeafLevel := LateralTheory.E.LeafLevelPf.LeafLevel_of a0 a1 a2
theorem a4 : LateralTheory.E.t_E6Cut.LeafProd := UpperTheory.leafProd_holds
theorem a5 : LateralTheory.E.t_E6Cut.LeafLoc := UpperTheory.leafProd_leafLoc_of_leafLevel a3 a4
theorem a6 : LateralTheory.E.LeafSqPf.LeafSheafPush := LateralTheory.E.SheafPushoutSquare.LeafSheafPush_pf
theorem a7 : LateralTheory.E.LeafSqPf.LeafFreeLoc := LateralTheory.E.LeafFreeLocPf.LeafFreeLoc_of a0
theorem a8 : LateralTheory.E.LeafExcPf.LeafSq := LateralTheory.E.LeafSqPf.square_of_pushout_and_free_local a6 a7
theorem a9 : LateralTheory.E.LeafExcPf.LeafCokIso := LateralTheory.E.LeafCokIsoPf.LeafCokIso_of
theorem a10 : LateralTheory.E.t_E6Cut.LeafExc := LateralTheory.E.LeafExcPf.excision_of_cokernel a0 a8 a9
theorem a11 : LateralTheory.E.LeafExcRingPf.LeafCov1 := LateralTheory.E.LeafCov1Pf.LeafCov1_of a10
theorem a12 : LateralTheory.E.LeafExcRingPf.LeafCov2 := LateralTheory.E.LeafCov2Pf.LeafCov2_of
theorem a13 : LateralTheory.E.t_E6Cut.LeafExcRing := LateralTheory.E.LeafExcRingPf2.LeafExcRing_of' a10 a11 a12
theorem a14 : LateralTheory.E.LeafRoofEtPPf.LeafQuotEt := LateralTheory.E.LeafQuotEtPf.LeafQuotEt_of
theorem a15 : LateralTheory.E.LeafRoofEtPPf.LeafPolyEt := LateralTheory.E.LeafPolyEtPf.LeafPolyEt_of
theorem a16 : LateralTheory.E.LeafRoofEtPf.LeafRoofEtP := LateralTheory.E.LeafRoofEtPPf.roofEtale_of_quotientEtale_polynomialEtale a14 a15
theorem a17 : LateralTheory.E.LeafRoofPf.LeafRoofEt := LateralTheory.E.LeafRoofEtPf.LeafRoofEt_of a16
theorem a18 : LateralTheory.E.t_E6Cut.LeafRoof := LateralTheory.E.LeafRoofPf.LeafRoof_of a17
theorem a19 : LateralTheory.E.LeafCoordsPointResPf.LeafResDimQe := LateralTheory.E.LeafResDimQePf.LeafResDimQe_of
theorem a20 : LateralTheory.E.LeafCoordsPointResPf.LeafResKer := LateralTheory.E.LeafCoordsPointResPf.LeafResKer_of
theorem a21 : LateralTheory.E.LeafCoordsPointPf.LeafCoordsPointRes := LateralTheory.E.LeafCoordsPointResPf.LeafCoordsPointRes_of_leaves a19 a20
theorem a22 : LateralTheory.E.LeafCoordsPf.LeafCoordsPoint := LateralTheory.E.LeafCoordsPointPf.LeafCoordsPoint_of_res a21
theorem a23 : LateralTheory.E.LeafChartRingPf.LeafCoords := LateralTheory.E.LeafCoordsPf.NakH.LeafCoords_of_point a22
theorem a24 : LateralTheory.E.LeafChartRingPf.LeafJacobian := LateralTheory.E.LeafJacobianPf.LeafJacobian_of
theorem a25 : LateralTheory.E.t_E6Cut.LeafChartRing := LateralTheory.E.LeafChartRingPf.LeafChartRing_of a23 a24
theorem a26 : LateralTheory.E.ChartGeoPf.ChartStdGeo := LateralTheory.E.ChartGeoPf.chartStdGeo_pf
theorem a27 : LateralTheory.E.ChartGeoPf.RangeKer := LateralTheory.E.ChartGeoPf.rangeKer_pf
theorem a28 : LateralTheory.E.ChartGeoPf.QuotLoc := LateralTheory.E.ChartGeoPf.quotLoc_pf
theorem a29 : LateralTheory.E.LeafChartAffPf.ChartGeo := LateralTheory.E.ChartGeoPf.ChartGeo_of_parts a26 a27 a28
theorem a30 : LateralTheory.E.LeafChartAffPf.ChartAway := LateralTheory.E.ChartAwayPf.ChartAway_of
theorem a31 : LateralTheory.E.LeafChartPf.LeafChartAff := LateralTheory.E.LeafChartAffPf.LeafChartAff_of a29 a30
theorem a32 : LateralTheory.E.LeafChartPf.LeafChartAway := LateralTheory.E.LeafChartAwayPf.LeafChartAway_of
theorem a33 : LateralTheory.E.t_E6Cut.LeafChart := LateralTheory.E.LeafChartPf.LeafChart_of a25 a31 a32
theorem a34 : LateralTheory.E.D2.LeafA6nat := LateralTheory.Fix.EtaleChapterDTwo.s0
theorem a35 : LateralTheory.E.t_E6Cut.LeafNat := (fun (h : LateralTheory.E.D2.LeafA6nat) _ _ _ _ _ => h) a34
theorem a36 : LateralTheory.E.t_E6Cut.LeafProj := LateralTheory.E.LeafProjPf.LeafProj_of a35
theorem a37 : LateralTheory.E.t_E6Cut.LeafHI := LateralTheory.E.LeafHIPf.LeafHI_of
theorem a38 : LateralTheory.E.t_E6Cut.LeafAff := UpperTheory.Cb.affine_leaf_of_projective_leaves a36 a10 a37
theorem a39 : LateralTheory.E.EtaleChapterESix := LateralTheory.E.t_E6Cut.goal_of a5 a13 a18 a33 a38

theorem intersectionNumber_baseChange : LateralTheory.E.EtaleChapterESix := a39

end UpperTheory.Et.E6
