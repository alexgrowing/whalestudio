import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedFlagFrameVectorMemRowLattice
import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
open scoped Classical ENNReal Pointwise
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixedFlag_frameVector_mem_rowLattice : ∀ (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : LV D), IsRowLat D F0 Λ → ∀ a, frame (lf D F0) a ∈ Λ := by
  first | exact @GlobalTheory.Unfold.RowFrame.frame_mem | exact GlobalTheory.Unfold.RowFrame.frame_mem | (intros; apply GlobalTheory.Unfold.RowFrame.frame_mem <;> assumption)
