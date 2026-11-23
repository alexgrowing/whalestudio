import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlueUnimodularLatticeRepsMoveIsometryFrames
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glueUnimodularLatticeReps_move_isometry_frames : ∀ (D : D7) (T T' : D.host.E) (F G : LFlag (VS D) D.R.rS T) (F' G' : LFlag (VS D) D.R.rS T') (n : GV D), n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → (∀ a, frame G a = n (frame F a)) → (∀ a, frame G' a = n (frame F' a)) → ∀ s : Finset (LV D), Glue F F' s → ∃ s' : Finset (LV D), Glue G G' s' ∧ glueSum G G' s' = glueSum F F' s := by
  first | exact @GlobalTheory.GlueMove.glue_move | exact GlobalTheory.GlueMove.glue_move | (intros; apply GlobalTheory.GlueMove.glue_move <;> assumption)
