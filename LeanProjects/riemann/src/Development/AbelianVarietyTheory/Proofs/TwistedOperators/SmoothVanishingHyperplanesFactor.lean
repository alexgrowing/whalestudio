import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmoothVanishingHyperplaneFactorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousVanishingHyperplaneExtendStatement
open GlobalTheory.Chamber
open scoped InnerProductSpace ContDiff Classical

namespace GlobalTheory

theorem smooth_div_prod_linear_forms : ∀ {k : ℕ} (L : Finset (A0 k)) (N : A0 k → ℂ), (∀ b ∈ L, b ≠ 0) →
    (∀ b ∈ L, ∀ b' ∈ L, b ≠ b' → ∀ r : ℝ, b' ≠ r • b) →
    ContDiff ℝ ∞ N → (∀ b ∈ L, ∀ x, ⟪x, b⟫_ℝ = 0 → N x = 0) →
    ∃ F : A0 k → ℂ, ContDiff ℝ ∞ F ∧ ∀ x, N x = (∏ b ∈ L, (⟪x, b⟫_ℝ : ℂ)) * F x := by
  intro k L
  induction L using Finset.induction_on with
  | empty =>
    intro N _ _ hN _
    exact ⟨N, hN, fun x => by simp⟩
  | insert b0 L hb0 ih =>
    intro N hne hdist hN hvan
    obtain ⟨N1, hN1, hN1eq⟩ := GlobalTheory.T.smooth_vanishing_hyperplane_factor b0 N (hne b0 (Finset.mem_insert_self _ _)) hN
      (hvan b0 (Finset.mem_insert_self _ _))
    have hvan1 : ∀ b ∈ L, ∀ x, ⟪x, b⟫_ℝ = 0 → N1 x = 0 := by
      intro b hb
      refine GlobalTheory.T.continuous_vanishing_hyperplane_extend b {b0} N1 hN1.continuous ?_ ?_
      · intro b' hb' r
        rw [Finset.mem_singleton] at hb'
        subst hb'
        exact hdist b (Finset.mem_insert_of_mem hb) b' (Finset.mem_insert_self _ _)
          (fun h => hb0 (h ▸ hb)) r
      · intro x hx hoff
        have h1 := hvan b (Finset.mem_insert_of_mem hb) x hx
        rw [hN1eq x] at h1
        have h2 : (⟪x, b0⟫_ℝ : ℂ) ≠ 0 := by
          exact_mod_cast hoff b0 (Finset.mem_singleton_self _)
        exact (mul_eq_zero.mp h1).resolve_left h2
    obtain ⟨F, hF, hFeq⟩ := ih N1 (fun b hb => hne b (Finset.mem_insert_of_mem hb))
      (fun b hb b' hb' => hdist b (Finset.mem_insert_of_mem hb) b' (Finset.mem_insert_of_mem hb')) hN1 hvan1
    refine ⟨F, hF, fun x => ?_⟩
    rw [hN1eq x, hFeq x, Finset.prod_insert hb0, mul_assoc]

end GlobalTheory
