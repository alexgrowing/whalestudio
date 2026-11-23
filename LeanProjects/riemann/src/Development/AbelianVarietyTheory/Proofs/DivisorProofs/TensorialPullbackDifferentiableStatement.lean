import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorialPullbackDifferentiable
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
open Matrix Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Pullback
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorial_pullback_differentiable : ∀ {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E'] [FiniteDimensional ℂ E'] {g m n : ℕ} (N : Fin n → Pt E g → E → Ext m) (φ : E' → E) (β : Fin n → E') (b : E') (z : Fin g → ℂ), (∀ i Q, IsLinearMap ℝ (N i Q)) → (∀ i v, DifferentiableAt ℝ (fun Q => N i Q v) (φ b, z)) → (∀ᶠ c in 𝓝 b, DifferentiableAt ℂ φ c) → DifferentiableAt ℝ (fun P : Pt E' g => ∑ i, N i (φ P.1, P.2) (fderiv ℂ φ P.1 (β i) - fderiv ℂ φ b (β i))) (b, z) ∧ ∀ w : Pt E' g, fderiv ℝ (fun P : Pt E' g => ∑ i, N i (φ P.1, P.2) (fderiv ℂ φ P.1 (β i) - fderiv ℂ φ b (β i))) (b, z) w = ∑ i, N i (φ b, z) (fderiv ℂ (fun c => fderiv ℂ φ c (β i)) b w.1) := by
  first | exact @GlobalTheory.TorsionForm.Pullback.corr_deriv_base_change | exact GlobalTheory.TorsionForm.Pullback.corr_deriv_base_change | (intros; apply GlobalTheory.TorsionForm.Pullback.corr_deriv_base_change <;> assumption)
