import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GluedLatticeFiniteIndex
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlaceEqOneOfNotMem
open NumberField Matrix IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glued_lattice_finite_index : ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (T : FinitePlace L → Matrix (Fin n) (Fin n) L), (∀ v, (T v).det ≠ 0) → {v : FinitePlace L | ¬ UnitAt v (T v)}.Finite → (glued T).toAddSubgroup.relIndex (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup ≠ 0 ∧ (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup.relIndex (glued T).toAddSubgroup ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.Comm.glued_commensurable | exact GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.Comm.glued_commensurable | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.Comm.glued_commensurable <;> assumption)
