import Development.EtaleCohomology.CohomologicalPurity.FinLeafThom
import Development.EtaleCohomology.CohomologicalPurity.FinLeafChart
import Development.EtaleCohomology.CohomologicalPurity.FinLeafExc
import Development.EtaleCohomology.CohomologicalPurity.LeafClCut
import Development.EtaleCohomology.CohomologicalPurity.LeafDescOSepPf
import Development.EtaleCohomology.CohomologicalPurity.LeafDescOGluePfP
import Development.EtaleCohomology.CohomologicalPurity.LeafDescPfGlue
import Development.EtaleCohomology.CohomologicalPurity.LeafDictPfDbl
import Development.EtaleCohomology.CohomologicalPurity.LeafDiscNrmPf
import Development.EtaleCohomology.CohomologicalPurity.LeafEvPf
import Development.EtaleCohomology.CohomologicalPurity.LeafPairPf
import Development.EtaleCohomology.CohomologicalPurity.LeafZornPf
import Development.EtaleCohomology.CohomologicalPurity.LeafBdAddPf
import Development.EtaleCohomology.CohomologicalPurity.LeafBZPf
import Development.EtaleCohomology.CohomologicalPurity.LeafZlocPf
import Development.EtaleCohomology.CohomologicalPurity.LeafZeroPf
import Development.EtaleCohomology.CohomologicalPurity.LeafStepPf
import Development.EtaleCohomology.CohomologicalPurity.LeafTopPf
import Development.EtaleCohomology.CohomologicalPurity.LeafFlqPf
import Development.EtaleCohomology.CohomologicalPurity.LeafNbPf
import Development.EtaleCohomology.CohomologicalPurity.LeafVanRingPf
import Development.EtaleCohomology.CohomologicalPurity.LeafVanPf
import Development.EtaleCohomology.CohomologicalPurity.LeafVanFPf
import Development.EtaleCohomology.CohomologicalPurity.LeafOffPf
import Development.EtaleCohomology.CohomologicalPurity.LeafGenRingPf
import Development.EtaleCohomology.CohomologicalPurity.LeafGenKerPf
import Development.EtaleCohomology.CohomologicalPurity.LeafGenPf
import Development.EtaleCohomology.CohomologicalPurity.LeafMatPf
import Development.EtaleCohomology.CohomologicalPurity.LeafCmpPfAll

theorem LateralTheory.Fix.LeafCl.intersectionNumber_baseChange : LateralTheory.CohomologicalPurity.LeafCl := by
  have h54 : LateralTheory.CohomologicalPurity.LeafThom := LateralTheory.Fin.LeafThom.intersectionNumber_baseChange
  have h80 : LateralTheory.CohomologicalPurity.LeafChart := LateralTheory.Fin.LeafChart.intersectionNumber_baseChange
  have h89 : LateralTheory.CohomologicalPurity.LeafExc := LateralTheory.Fin.LeafExc.intersectionNumber_baseChange
  have h55 : LateralTheory.CohomologicalPurity.Cl.LeafDisc := LateralTheory.CohomologicalPurity.Cl.LeafDisc_of'
  have h56 : LateralTheory.CohomologicalPurity.DictPf.LeafEv := LateralTheory.CohomologicalPurity.DictPf.LeafEv_of
  have h57 : LateralTheory.CohomologicalPurity.DictPf.LeafPair := LateralTheory.CohomologicalPurity.LeafPairPf.LeafPair_of
  have h58 : LateralTheory.CohomologicalPurity.Cl.LeafDict := LateralTheory.CohomologicalPurity.DictPf.LeafDict_of' h55 h56 h57
  have h59 : LateralTheory.CohomologicalPurity.Cl.LeafZorn := LateralTheory.CohomologicalPurity.ZornPf.LeafZorn_of
  have h60 : LateralTheory.CohomologicalPurity.Cl.Flq.LeafBdAdd := LateralTheory.CohomologicalPurity.Cl.Flq.LeafBdAdd_of
  have h61 : LateralTheory.CohomologicalPurity.Cl.Flq.LeafBZ := LateralTheory.CohomologicalPurity.Cl.Flq.LeafBZ_of
  have h62 : LateralTheory.CohomologicalPurity.Cl.Flq.LeafZloc := LateralTheory.CohomologicalPurity.ZlocPf.LeafZloc_of
  have h63 : LateralTheory.CohomologicalPurity.Cl.Flq.LeafZero := LateralTheory.CohomologicalPurity.Cl.Flq.LeafZero_of
  have h64 : LateralTheory.CohomologicalPurity.Cl.Flq.LeafStep := LateralTheory.CohomologicalPurity.Cl.Flq.StepPf.LeafStep_of
  have h65 : LateralTheory.CohomologicalPurity.Cl.Flq.LeafTop := LateralTheory.CohomologicalPurity.Cl.Flq.LeafTop_of
  have h66 : LateralTheory.CohomologicalPurity.Cl.LeafFlq := LateralTheory.CohomologicalPurity.Cl.Flq.LeafFlq_of h59 h60 h61 h62 h63 h64 h65
  have h67 : LateralTheory.CohomologicalPurity.Cl.LeafDescOSep := LateralTheory.CohomologicalPurity.Cl.LeafDescOSep_of
  have h68 : LateralTheory.CohomologicalPurity.Cl.LeafDescOGlue := LateralTheory.CohomologicalPurity.Cl.LeafDescOGlue_of
  have h69 : LateralTheory.CohomologicalPurity.Cl.LeafDesc := LateralTheory.CohomologicalPurity.Cl.LeafDesc_of' h58 h66 h67 h68
  have h90 : LateralTheory.CohomologicalPurity.Cl.LeafNb := LateralTheory.CohomologicalPurity.NbPf.nb h89
  have h91 : LateralTheory.CohomologicalPurity.Cl.LeafVanRing := LateralTheory.CohomologicalPurity.Cl.LeafVanRing_of h90 h54
  have h92 : LateralTheory.CohomologicalPurity.Cl.LeafVan := LateralTheory.CohomologicalPurity.Cl.LeafVan_of h80 h91
  have h93 : LateralTheory.CohomologicalPurity.Cl.LeafVanF := LateralTheory.CohomologicalPurity.Cl.LeafVanF_of h92
  have h94 : LateralTheory.CohomologicalPurity.Cl.LeafOff := LateralTheory.CohomologicalPurity.Cl.LeafOff_of
  have h95 : LateralTheory.CohomologicalPurity.Cl.LeafGenRing := LateralTheory.CohomologicalPurity.Cl.LeafGenRing_of
  have h96 : LateralTheory.CohomologicalPurity.Cl.LeafGenKer := LateralTheory.CohomologicalPurity.Cl.LeafGenKer_of
  have h97 : LateralTheory.CohomologicalPurity.Cl.LeafGen := LateralTheory.CohomologicalPurity.Cl.LeafGen_of h80 h95 h96
  have h98 : LateralTheory.CohomologicalPurity.Cl.LeafMat := LateralTheory.CohomologicalPurity.Cl.LeafMat_of
  have h99 : LateralTheory.CohomologicalPurity.Cl.LeafCmp := LateralTheory.CohomologicalPurity.Cl.LeafCmp_of_Mat h98
  exact LateralTheory.CohomologicalPurity.Cl.goal_of h54 h69 h92 h93 h94 h97 h99
