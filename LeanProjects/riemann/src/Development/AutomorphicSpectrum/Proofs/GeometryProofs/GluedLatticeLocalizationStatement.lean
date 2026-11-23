import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GluedLatticeLocalization
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlaceEqOneOfNotMem
open NumberField Matrix IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glued_lattice_localization : ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (T : FinitePlace L → Matrix (Fin n) (Fin n) L), (∀ v, (T v).det ≠ 0) → {v : FinitePlace L | ¬ UnitAt v (T v)}.Finite → ∀ v, locAt v (glued T) = locAt v (frame (T v)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.locAt_glued | exact GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.locAt_glued | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.locAt_glued <;> assumption)
