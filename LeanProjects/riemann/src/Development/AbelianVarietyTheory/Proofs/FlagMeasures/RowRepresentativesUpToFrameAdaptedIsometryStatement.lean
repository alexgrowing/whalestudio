import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowRepresentativesUpToFrameAdaptedIsometry
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_representatives_up_to_frame_adapted_isometry : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), (∀ Λ, IsRowLat D (X.Fu u) Λ → ∃ Λ' ∈ Y.what₂ u, ∃ σ, Adapt σ (lf D (X.Fu u)) (lf D (X.Fu u)) ∧ Formalism.HermitianLatticesTheory.gmap σ Λ' = Λ) ∧ ∀ Λ ∈ Y.what₂ u, ∀ Λ' ∈ Y.what₂ u, ∀ σ, Adapt σ (lf D (X.Fu u)) (lf D (X.Fu u)) → Formalism.HermitianLatticesTheory.gmap σ Λ' = Λ → Λ' = Λ := by
  first | exact @GlobalTheory.RowRep.rowReps | exact GlobalTheory.RowRep.rowReps | (intros; apply GlobalTheory.RowRep.rowReps <;> assumption)
