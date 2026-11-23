import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseDifferentialDualBasisCancel
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DBaseApply
open Matrix MeasureTheory Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Gauge GlobalTheory.TorsionForm.Fibrewise
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_differential_dual_basis_cancel : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ} (β : Fin n → E) (ψ : E → ℂ) (b : E) (w : Ext (n + n + g)), ContDiff ℝ 2 ψ → ∑ i, (dBase β (fun b' => d10 ψ b' (β i)) b (wedge (dt g i) w) + dBase β (fun b' => d01 ψ b' (β i)) b (wedge (dtb g i) w)) = 0 := by
  first | exact @GlobalTheory.TorsionForm.Fibrewise.SqZero.d_sq_zero | exact GlobalTheory.TorsionForm.Fibrewise.SqZero.d_sq_zero | (intros; apply GlobalTheory.TorsionForm.Fibrewise.SqZero.d_sq_zero <;> assumption)
