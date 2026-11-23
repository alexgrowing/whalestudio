import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryUnitriangularizingFlagStabilizer
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isometry_unitriangularizing_flag_stabilizer : ∀ (D : D7) (T : D.host.E) (F0 : FlagG (VS D) D.R.rS T) (γ : GV D), γ ∈ stabF D F0 → ∃ t ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT, (∀ x ∈ perpS (VS D) F0.X, t x - x ∈ F0.X) ∧ Adapt (t * γ) (lf D F0) (lf D F0) := by
  first | exact @GlobalTheory.FlagTorus.flag_torus | exact GlobalTheory.FlagTorus.flag_torus | (intros; apply GlobalTheory.FlagTorus.flag_torus <;> assumption)
