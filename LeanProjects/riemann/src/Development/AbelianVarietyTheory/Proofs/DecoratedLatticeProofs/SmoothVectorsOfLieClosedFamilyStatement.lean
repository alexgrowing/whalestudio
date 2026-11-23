import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmoothVectorsOfLieClosedFamily
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorsSubspaceStableSobolevFormDeriv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JacobianCommutation.PCkPartials
open Matrix
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothVectors_of_lie_closed_family : ∀ (n : ℕ) (Hm : Matrix (Fin n) (Fin n) ℂ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (ι : Type) (v : ι → H) (δ : Matrix (Fin n) (Fin n) ℂ → ι → ι), Hm.det ≠ 0 → Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ → (∀ i X Y, v (δ (X + Y) i) = v (δ X i) + v (δ Y i)) → (∀ i (c : ℝ) X, v (δ ((c : ℂ) • X) i) = (c : ℂ) • v (δ X i)) → (∀ X, Xᴴ * Hm + Hm * X = 0 → ∀ i, HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) (v i)) (v (δ X i)) 0) → ∀ i, Formalism.L2.Theta.SmoothVec {X | Xᴴ * Hm + Hm * X = 0} σ (v i) := by
  first | exact @GlobalTheory.SmoothCrit.smoothVec_of_closed_family | exact GlobalTheory.SmoothCrit.smoothVec_of_closed_family | (intros; apply GlobalTheory.SmoothCrit.smoothVec_of_closed_family <;> assumption)
