import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed

noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold

def FlagPairStabilizer {D : D7} {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') :
    Subgroup (GV D) where
  carrier := H0 F F'
  one_mem' := ⟨Subgroup.one_mem _, fun _ => rfl, fun _ => rfl⟩
  mul_mem' := by
    rintro a b ⟨ha, ha1, ha2⟩ ⟨hb, hb1, hb2⟩
    refine ⟨Subgroup.mul_mem _ ha hb, fun i => ?_, fun i => ?_⟩
    · show a (b _) = _
      rw [hb1, ha1]
    · show a (b _) = _
      rw [hb2, ha2]
  inv_mem' := by
    rintro a ⟨ha, ha1, ha2⟩
    refine ⟨Subgroup.inv_mem _ ha, fun i => ?_, fun i => ?_⟩
    · conv_lhs => rw [← ha1 i]
      show a.symm (a _) = _
      simp
    · conv_lhs => rw [← ha2 i]
      show a.symm (a _) = _
      simp

theorem mem_H0sub {D : D7} {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T')
    (h : GV D) : h ∈ FlagPairStabilizer F F' ↔ h ∈ H0 F F' := Iff.rfl

end GlobalTheory.Unfold
