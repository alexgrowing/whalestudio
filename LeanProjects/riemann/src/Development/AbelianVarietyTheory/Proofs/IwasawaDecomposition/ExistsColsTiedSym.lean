import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RedivisionStructureEq
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Formalism.LocalToGlobal.NumberFieldFamilies.OwnStruct
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsRe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermRe

noncomputable section

namespace GlobalTheory.Mem.SRe.ColRe

open Formalism.BasicNotions Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.SRe NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (Z : New D)

set_option maxHeartbeats 4000000 in

def colsRe (C : ColsTiedSym D) : ColsTiedSym (reD D Z) := (by with_unfolding_all exact ((@ColsTiedSym.mk (reD D Z) (hermRe Z C.herm) ((by with_unfolding_all exact ((fun u => formsRe Z (C.forms u)) :)))
    ((by with_unfolding_all exact (C.eV :)))
    ((by with_unfolding_all exact (C.piU :)))
    ((by with_unfolding_all exact (C.res :)))
    ((by with_unfolding_all exact (C.car0 :)))
    ((by with_unfolding_all exact (C.carC :)))
    ((by with_unfolding_all exact (C.carM :)))
    ((by with_unfolding_all exact (C.carP :)))
    ((by with_unfolding_all exact (C.lattice₂ :)))
    ((by with_unfolding_all exact (C.pr :)))
    ((by with_unfolding_all exact (C.prk :)))
    ((by with_unfolding_all exact (C.prC :)))
    ((by with_unfolding_all exact (C.z0 :)))
    ((by with_unfolding_all exact (C.ga :)))
    ((by with_unfolding_all exact (C.sp :)))
    ((by with_unfolding_all exact (C.piG :)))
    ((by with_unfolding_all exact (C.fr0 :)))
    ((by with_unfolding_all exact (C.gl_const :)))
    ((by with_unfolding_all exact (C.chi :)))
    ((by with_unfolding_all exact (C.frame_level_zero_const :)))
    ((by with_unfolding_all exact (C.frP_const :)))) :))

set_option maxHeartbeats 4000000 in

theorem sameF_colsRe (C : ColsTiedSym D) :
    SameForms0LevelsAndValues Z (fun u => (C.forms u).to0) (fun u => ((colsRe Z C).forms u).to0) := by
  intro u
  refine ⟨?_, ?_, ?_⟩
  · exact (by with_unfolding_all exact ((Eq.refl (C.forms u).to0.cls0.lev) :))
  · exact (by with_unfolding_all exact ((Eq.refl (C.forms u).to0.cls0.y) :))
  · exact (by with_unfolding_all exact ((Eq.refl (C.forms u).to0.val0.eY) :))

set_option maxHeartbeats 4000000 in

theorem exists_colsTiedSym (D : D7) (Z : New D) (C : ColsTiedSym D) :
    ∃ C' : ColsTiedSym (reD D Z), SameForms0LevelsAndValues Z (fun u => (C.forms u).to0) (fun u => (C'.forms u).to0) :=
  ⟨colsRe Z C, sameF_colsRe Z C⟩

end GlobalTheory.Mem.SRe.ColRe

end
