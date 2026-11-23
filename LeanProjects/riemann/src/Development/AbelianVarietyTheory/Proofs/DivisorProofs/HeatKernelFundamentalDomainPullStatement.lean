import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatKernelFundamentalDomainPull
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullFullL
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.OneVec
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heat_kernel_fundamental_domain_pull : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g n : ℕ} {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} {M : Submodule ℤ (Fl g)} {j : Fl g → Pt E g → ℂ} {h : Pt E g → ℝ}, IsDatum B τ M j h → ∀ (β : Fin n → E) (a : Fin n → ℂ) {b : E}, b ∈ B → ∀ (u : ℝ) (D : Set (Fl g)), IsAddFundamentalDomain M D volume → ∀ (K : ℝ → (Fin g → ℂ) → (Fin g → ℂ) → Ext (n + n + g) →L[ℂ] Ext (n + n + g)), IsHeatKernel τ M j h β b u D K → IsHeatKernel τ M j h ![∑ i, a i • β i] b u D fun t z z' => pullOp a (K t z z') := by
  first | exact @GlobalTheory.TorsionForm.OneVec.isHeatKernel_pullOp | exact GlobalTheory.TorsionForm.OneVec.isHeatKernel_pullOp | (intros; apply GlobalTheory.TorsionForm.OneVec.isHeatKernel_pullOp <;> assumption)
