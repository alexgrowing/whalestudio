import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalIndexFrameLogDet
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlaceEqOneOfNotMem
open NumberField Matrix IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_index_frame_log_det : ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (v : FinitePlace L) (T : Matrix (Fin n) (Fin n) L), T.det ≠ 0 → gIdx (locAt v (frame T)).toAddSubgroup (locAt v (frame (1 : Matrix (Fin n) (Fin n) L))).toAddSubgroup = Real.log (v T.det) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.gIdx_locAt_frame | exact GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.gIdx_locAt_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.gIdx_locAt_frame <;> assumption)
