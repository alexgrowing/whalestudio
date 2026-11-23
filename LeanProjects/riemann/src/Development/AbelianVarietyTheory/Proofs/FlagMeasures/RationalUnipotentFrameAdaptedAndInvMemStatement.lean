import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnipotentFrameAdaptedAndInvMem
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalUnipotent_frameAdapted_and_inv_mem : ∀ (D : D7) (T : D.host.E) (F : LFlag (VS D) D.R.rS T) (n : GV D), n ∈ NRat F → Adapt n F F ∧ n⁻¹ ∈ NRat F := by
  first | exact @GlobalTheory.NRatInv.adapt_and_inv_mem | exact GlobalTheory.NRatInv.adapt_and_inv_mem | (intros; apply GlobalTheory.NRatInv.adapt_and_inv_mem <;> assumption)
