import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GlobalIndexFrameLogNorm
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlaceEqOneOfNotMem
open NumberField Matrix IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_index_frame_log_norm : ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (C : Matrix (Fin n) (Fin n) L), C.det ≠ 0 → (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup.relIndex (frame C).toAddSubgroup ≠ 0 ∧ (frame C).toAddSubgroup.relIndex (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup ≠ 0 ∧ gIdx (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup (frame C).toAddSubgroup = ∑ σ : L →+* ℂ, Real.log ‖σ C.det‖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.GlobDet.gIdx_frame | exact GlobalTheory.CompanionTheory.Ar.Cusp.GlobDet.gIdx_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.GlobDet.gIdx_frame <;> assumption)
