import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedFrameMemRowLatticesOfWord
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixedFrame_mem_rowLattices_of_word : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V), Λ ∈ Y.what₂ u → ∀ a, frame (lf D (X.Fu u)) a ∈ Λ := by
  first | exact @GlobalTheory.RowFrame.frame_mem_rows | exact GlobalTheory.RowFrame.frame_mem_rows | (intros; apply GlobalTheory.RowFrame.frame_mem_rows <;> assumption)
