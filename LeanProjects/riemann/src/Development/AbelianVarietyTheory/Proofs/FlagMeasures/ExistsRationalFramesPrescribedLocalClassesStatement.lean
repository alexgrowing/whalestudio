import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRationalFramesPrescribedLocalClasses
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_frames_prescribed_local_classes : ∀ (D : D7) (Z : LocDat D) (u u' : D.what₂.Word) (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (P : Finset (PlF D)) (f f' : ∀ p : PlF D, Fin (D.R.rS + 1) → Vp D p), (∀ p ∈ P, Tri (D.s.atP p).Ep (scaled Z p (frame F)) (f p) ∧ Tri (D.s.atP p).Ep (scaled Z p (frame F')) (f' p)) → ∃ (G : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (G' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)), StdOff Z P F G F' G' ∧ ∀ p ∈ P, ∃ A A' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep, Uni A ∧ Uni A' ∧ (∀ a b, A a b ∈ (Z.M p).L.O ∧ A' a b ∈ (Z.M p).L.O ∧ A a b - A' a b ∈ Submodule.span (Z.M p).L.O {algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (LocNG.theta (Z.M p))}) ∧ Chg (f p) A (scaled Z p (frame G)) ∧ Chg (f' p) A' (scaled Z p (frame G')) := by
  first | exact @GlobalTheory.FrameChoice.choose_frames | exact GlobalTheory.FrameChoice.choose_frames | (intros; apply GlobalTheory.FrameChoice.choose_frames <;> assumption)
