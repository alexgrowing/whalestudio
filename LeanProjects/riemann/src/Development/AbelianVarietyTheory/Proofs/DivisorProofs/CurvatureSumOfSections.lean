import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullFullL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvFinsetSumOfDiff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperconnectionDifferentiableStatement

set_option autoImplicit false

noncomputable section

open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.OneVec
open scoped Real ContDiff

namespace GlobalTheory.TorsionForm.OneVec

theorem curv_sum : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g m : ℕ}
    {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} {M : Submodule ℤ (Fl g)} {j : Fl g → Pt E g → ℂ}
    {h : Pt E g → ℝ}, IsDatum B τ M j h → ∀ (β : Fin m → E) {b : E}, b ∈ B → ∀ {ι : Type} (s : Finset ι)
    (G : ι → (Fin g → ℂ) → Ext (m + m + g)), (∀ i, ContDiff ℝ ∞ (G i)) → ∀ (u : ℝ) (z : Fin g → ℂ),
    curv τ h β b u (fun y => ∑ i ∈ s, G i y) z = ∑ i ∈ s, curv τ h β b u (G i) z := by
  intro E _ _ _ g m B τ M j h hD β b hb ι s G hG u z
  exact curv_finset_sum_of_diff τ h β b u s G (fun i => (hG i).differentiable (by simp)) z
    fun i _ => GlobalTheory.T.superconnection_differentiable hD β hb (G i) (hG i) u z

end GlobalTheory.TorsionForm.OneVec
