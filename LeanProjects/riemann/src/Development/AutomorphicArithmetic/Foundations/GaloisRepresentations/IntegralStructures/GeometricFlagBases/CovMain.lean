import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.RationalSplittingExists
import Development.AutomorphicArithmetic.CommutativeAlgebra.BaseExtensionHolds
import Development.AutomorphicArithmetic.CommutativeAlgebra.PowerProjectorExists
import Development.AutomorphicArithmetic.CommutativeAlgebra.SiteExistsOfSplittingAndPowerProjector
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsGenericModuliPoint
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsNumberFieldPointOfGeneric
import Development.AutomorphicArithmetic.CommutativeAlgebra.LatticeGeneration
import Development.AutomorphicArithmetic.CommutativeAlgebra.GroupSchemePullbackExists
import Development.AutomorphicArithmetic.CommutativeAlgebra.PowerMapCartesian
import Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientModuliObjectExists
import Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientMapComp
import Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientUniqueOfComp
import Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientModuliIso
import Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientLevelOfLatticeGeneration
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsogenyClassExistsOfQuotient
import Development.AutomorphicArithmetic.CommutativeAlgebra.TraceEtaIdentity
import Development.AutomorphicArithmetic.CommutativeAlgebra.TraceEtaPointwise
import Development.AutomorphicArithmetic.CommutativeAlgebra.MultiplierIsUnit
import Development.AutomorphicArithmetic.CommutativeAlgebra.TracePullbackIdentity
import Development.AutomorphicArithmetic.CommutativeAlgebra.TraceUnitOfPullbackMultiplier
import Development.AutomorphicArithmetic.CommutativeAlgebra.TraceIdentityOfTjElement
import Development.AutomorphicArithmetic.CommutativeAlgebra.CongruenceCRTOfLatticeGen
import Development.AutomorphicArithmetic.CommutativeAlgebra.CongruenceSubgroupIsLatticeStatement
import Development.AutomorphicArithmetic.CommutativeAlgebra.ArithmeticGroupCongruenceSubgroupProperty
import Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientInvariantOfTraceUnitCrt
import Development.AutomorphicArithmetic.CommutativeAlgebra.TowerInvariantOfBaseInvariantPowerCartesian
import Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientSeparatedOfTraceUnitCrt
import Development.AutomorphicArithmetic.CommutativeAlgebra.TowerTrivialOfQuotientTracePowerCartesian
import Development.AutomorphicArithmetic.CommutativeAlgebra.TowerFiniteEtaleOfTrivialPowerCartesian
import Development.AutomorphicArithmetic.CommutativeAlgebra.TowerSeparatedOfTrivialPowerCartesian
import Development.AutomorphicArithmetic.CommutativeAlgebra.IntegralGeometricGaloisSplitting
import Development.AutomorphicArithmetic.CommutativeAlgebra.TowerCoveringOfInvariantFiniteEtaleSeparated
import Development.AutomorphicArithmetic.CommutativeAlgebra.HeckeCorrespondenceIsogenyOfTraceCrt
import Development.AutomorphicArithmetic.CommutativeAlgebra.HeckeLiftExistsOfQuotientLevel
import Development.AutomorphicArithmetic.CommutativeAlgebra.HeckeLiftSeparatedOfLatticeCongruence
import Development.AutomorphicArithmetic.CommutativeAlgebra.TowerPointCountStatement
import Development.AutomorphicArithmetic.CommutativeAlgebra.HeckeCorrespondenceLiesInTowerOfLiftCount
import Development.AutomorphicArithmetic.CommutativeAlgebra.StandardDatumExists
import Development.AutomorphicArithmetic.CommutativeAlgebra.TowerCoveringCongruenceOfHeckeLies

namespace UpperTheory.Gal.Int.Geo.CovMain

set_option linter.unusedVariables false

theorem splitQ_of (I : MIn) : SplitQ := UpperTheory.rational_splitting_exists

theorem baseEx_of (I : MIn) : BaseEx := UpperTheory.baseExtension_holds

theorem powProj_of (I : MIn) : PowProj := UpperTheory.power_projector_exists

theorem siteEx_of (I : MIn) : SiteEx := UpperTheory.site_exists_of_splitting_and_power_projector I (splitQ_of I) (baseEx_of I) (powProj_of I)

theorem genEx_of (I : MIn) : GenEx := UpperTheory.exists_generic_moduli_point

theorem numEx_of (I : MIn) : NumEx := UpperTheory.exists_number_field_point_of_generic (genEx_of I)

theorem latGen_of (I : MIn) : LatGen := UpperTheory.lattice_generation

theorem gPull_of (I : MIn) : GPull := UpperTheory.group_scheme_pullback_exists

theorem powCart_of (I : MIn) : PowCart := UpperTheory.power_map_cartesian

theorem qObj_of (I : MIn) : QObj := UpperTheory.quotient_moduli_object_exists

theorem qComp_of (I : MIn) : QComp := UpperTheory.quotient_map_comp

theorem qUniq_of (I : MIn) : QUniq := UpperTheory.quotient_unique_of_comp (qComp_of I)

theorem qIso_of (I : MIn) : QIso := UpperTheory.quotient_moduli_iso

theorem qLev_of (I : MIn) : QLev := UpperTheory.quotient_level_of_lattice_generation (latGen_of I)

theorem clsEx_of (I : MIn) : ClsEx := UpperTheory.isogeny_class_exists_of_quotient (qObj_of I) (qComp_of I) (qUniq_of I) (qLev_of I)

theorem trEta_of (I : MIn) : TrEta := UpperTheory.trace_eta_identity

theorem trEtaPt_of (I : MIn) : TrEtaPt := UpperTheory.trace_eta_pointwise

theorem multUnit_of (I : MIn) : MultUnit := UpperTheory.multiplier_is_unit

theorem trBack_of (I : MIn) : TrBack := UpperTheory.trace_pullback_identity

theorem trUnit_of (I : MIn) : TrUnit := UpperTheory.trace_unit_of_pullback_multiplier (trBack_of I) (multUnit_of I)

theorem trTj_of (I : MIn) : TrTj := UpperTheory.trace_identity_of_tjElement

theorem congCRT_of (I : MIn) : CongCRT := UpperTheory.congruenceCRT_of_latticeGen (latGen_of I)

theorem grpLat_of (I : MIn) : GrpLat := UpperTheory.congruenceSubgroup_isLattice_statement

theorem grpCong_of (I : MIn) : GrpCong := UpperTheory.arithmeticGroup_congruenceSubgroupProperty

theorem baseInv_of (I : MIn) : BaseInv := UpperTheory.quotient_invariant_of_trace_unit_crt (numEx_of I) (qComp_of I) (qIso_of I) (clsEx_of I) (trEta_of I) (trUnit_of I) (congCRT_of I)

theorem piInv_of (I : MIn) : PiInv := UpperTheory.tower_invariant_of_base_invariant_powerCartesian (baseInv_of I) (powCart_of I)

theorem baseSep_of (I : MIn) : BaseSep := UpperTheory.quotient_separated_of_trace_unit_crt (gPull_of I) (qComp_of I) (qIso_of I) (qUniq_of I) (trEta_of I) (trEtaPt_of I) (trUnit_of I) (congCRT_of I)

theorem piZero_of (I : MIn) : PiZero := UpperTheory.tower_trivial_of_quotient_trace_powerCartesian I (qObj_of I) (qComp_of I) (qIso_of I) (qUniq_of I) (trEta_of I) (trUnit_of I) (powCart_of I)

theorem piFet_of (I : MIn) : PiFet := UpperTheory.tower_finiteEtale_of_trivial_powerCartesian (piZero_of I) (powCart_of I)

theorem piSep_of (I : MIn) : PiSep := UpperTheory.tower_separated_of_trivial_powerCartesian (piZero_of I) (baseSep_of I) (powCart_of I)

theorem splitOf_of (I : MIn) : SplitOf := UpperTheory.integralGeometricGalois_splitting

theorem kSCover_of (I : MIn) : KSCover := UpperTheory.tower_covering_of_invariant_finiteEtale_separated (piInv_of I) (piFet_of I) (piSep_of I) (splitOf_of I)

theorem tjIsog_of (I : MIn) : TjIsog := UpperTheory.heckeCorrespondence_isogeny_of_trace_crt (trEta_of I) (trBack_of I) (trTj_of I) (multUnit_of I) (congCRT_of I)

theorem liftEx_of (I : MIn) : LiftEx := UpperTheory.hecke_lift_exists_of_quotient_level (numEx_of I) (qObj_of I) (qComp_of I) (qUniq_of I) (qLev_of I) (tjIsog_of I) (trEta_of I) (congCRT_of I)

theorem liftSep_of (I : MIn) : LiftSep := UpperTheory.hecke_lift_separated_of_lattice_congruence (numEx_of I) (baseInv_of I) (trEta_of I) (trEtaPt_of I) (congCRT_of I) (grpLat_of I) (grpCong_of I)

theorem count_of (I : MIn) : Count := UpperTheory.tower_point_count_statement

theorem tjLies_of (I : MIn) : TjLies := UpperTheory.heckeCorrespondence_lies_in_tower_of_lift_count I (numEx_of I) (clsEx_of I) (powCart_of I) (piInv_of I) (piFet_of I) (liftEx_of I) (liftSep_of I) (count_of I)

theorem stdEx_of (I : MIn) : StdEx := UpperTheory.standard_datum_exists

theorem kSCong_of (I : MIn) : KSCong := UpperTheory.tower_covering_congruence_of_hecke_lies I (siteEx_of I) (numEx_of I) (clsEx_of I) (kSCover_of I) (tjLies_of I)

end UpperTheory.Gal.Int.Geo.CovMain
