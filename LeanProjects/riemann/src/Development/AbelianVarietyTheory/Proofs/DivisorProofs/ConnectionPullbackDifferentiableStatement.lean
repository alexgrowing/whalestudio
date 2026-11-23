import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectionPullbackDifferentiable
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
open Matrix Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Pullback
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.connection_pullback_differentiable : ∀ {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E'] {g n : ℕ} (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (φ : E' → E) (β : Fin n → E') (u : ℝ) (s : Pt E g → Ext (n + n + g)) (P : Pt E' g), DifferentiableAt ℂ φ P.1 → (∀ i j, DifferentiableAt ℂ (fun b => τ b i j) (φ P.1)) → DifferentiableAt ℝ h (φ P.1, P.2) → h (φ P.1, P.2) ≠ 0 → DifferentiableAt ℝ s (φ P.1, P.2) → superconn (τ ∘ φ) (fun Q => h (φ Q.1, Q.2)) β u (fun Q => s (φ Q.1, Q.2)) P = superconn τ h (fun i => fderiv ℂ φ P.1 (β i)) u s (φ P.1, P.2) := by
  first | exact @GlobalTheory.TorsionForm.SuperconnComp.superconn_comp | exact GlobalTheory.TorsionForm.SuperconnComp.superconn_comp | (intros; apply GlobalTheory.TorsionForm.SuperconnComp.superconn_comp <;> assumption)
