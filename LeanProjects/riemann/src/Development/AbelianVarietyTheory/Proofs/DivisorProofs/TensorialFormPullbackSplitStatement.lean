import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorialFormPullbackSplit
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
open Matrix Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Pullback
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorial_form_pullback_split : ∀ {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E'] {g n : ℕ} (τ' : E' → Matrix (Fin g) (Fin g) ℂ) (h' : Pt E' g → ℝ) (β : Fin n → E') (u : ℝ) (R : Pt E' g → Ext (n + n + g)) (P : Pt E' g) (A Ab : E → Ext (n + n + g)) (ψ : Fin n → E' →L[ℂ] E), (∀ v w, A (v + w) = A v + A w) → (∀ v, A (Complex.I • v) = Complex.I • A v) → (∀ v w, Ab (v + w) = Ab v + Ab w) → (∀ v, Ab (Complex.I • v) = -Complex.I • Ab v) → (∀ i k, ψ i (β k) = ψ k (β i)) → R P = 0 → (∀ w : Pt E' g, fderiv ℝ R P w = ∑ i, (wedge (dt g i) (A (ψ i w.1)) + wedge (dtb g i) (Ab (ψ i w.1)))) → superconn τ' h' β u R P = 0 := by
  first | exact @GlobalTheory.TorsionForm.Pullback.Tensorial.superconn_eq_zero | exact GlobalTheory.TorsionForm.Pullback.Tensorial.superconn_eq_zero | (intros; apply GlobalTheory.TorsionForm.Pullback.Tensorial.superconn_eq_zero <;> assumption)
