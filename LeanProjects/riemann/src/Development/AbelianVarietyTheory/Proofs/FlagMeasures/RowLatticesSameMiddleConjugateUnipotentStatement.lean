import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticesSameMiddleConjugateUnipotent
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_lattices_same_middle_conjugate_unipotent : ∀ (D : D7) (u : D.what₂.Word), (Tu D u).Prime → 3 ≤ Tu D u → SplitsCompletely (E := D.host.E) (Tu D u) → ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u → ∀ Λ₁ Λ₂ : LatV D, IsRowLat D F0 Λ₁ → IsRowLat D F0 Λ₂ → Lsub Λ₁ (lf D F0) = Lsub Λ₂ (lf D F0) → ∃ n ∈ stabF D F0, (∀ x ∈ orth (hS D) F0.X, n x - x ∈ F0.X) ∧ Formalism.HermitianLatticesTheory.gmap n Λ₁ = Λ₂ := by
  first | exact @GlobalTheory.LoopC.rowsLift | exact GlobalTheory.LoopC.rowsLift | (intros; apply GlobalTheory.LoopC.rowsLift <;> assumption)
