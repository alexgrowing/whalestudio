import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LowKSubSingleSqrtCkvLeStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CompactCasimirBoundProjectionDualTensorStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WtNearLeOfAddDistLe
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AlgTensWtNearStatement

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem algTens_pr_single_lev :
    ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool)
      (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)]
      [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s))
      (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ)
      (w : M), IsMod ε E μ → (∀ s, IsMod ε (F s) (μ - Pi.single s 1)) → AlgTens ε E N F io pr →
      Shape ε kk μ bv → j ≤ 4 * n ^ 2 → Lev ε E μ j w →
      ∀ c s, Lev ε (F s) (μ - Pi.single s 1) (j + 2) (pr s (Pi.single c w)) := by
  intro M _ _ n ε E N _ _ F io pr μ kk j bv w hE hF hT hS _ hw c s
  obtain ⟨hlow, hsq⟩ := GlobalTheory.T.lowK_sub_single_sqrt_ckv_le n kk ε μ bv s hS
  obtain ⟨hw1, hw2⟩ := hw
  have h0 : 0 ≤ Real.sqrt (ckv ε (lowK ε μ)) + 4 * (n : ℝ) * (j : ℝ) := by positivity
  refine ⟨?_, ?_⟩
  · obtain ⟨S, hS1, hS2, hS3, hS4⟩ :=
      GlobalTheory.T.compactCasimirBound_projection_dualTensor M n ε E N F io pr _ w hE.2.1 (fun s => (hF s).2.1) hT h0 hw1 s c
    refine ⟨S, hS1, hS2, hS3, fun x hx => (hS4 x hx).trans ?_⟩
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply pow_le_pow_left₀ (add_nonneg h0 (Real.sqrt_nonneg _))
    push_cast
    linarith
  · have h1 := (GlobalTheory.T.wtNear_pr_and_io_of_algTens M n ε E N F io pr (lowK ε μ) (j : ℝ) hT).1 w hw2 s c
    refine wtNear_le_of_add_dist_le (N s) n ε (F s) _ _ _ _ ?_ h1
    have h2 : ∑ a, |lowK ε μ a - lowK ε (μ - Pi.single s 1) a| = 1 := by
      rw [hlow, Finset.sum_eq_single s]
      · simp
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb]
      · simp
    rw [h2]
    push_cast
    linarith

end GlobalTheory
