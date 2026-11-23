import Mathlib

namespace GlobalTheory

theorem coords_bounded_by_period_matrix : ∀ (g r : ℕ) (lam : Fin r → Fin g → ℂ) (ρ : Fin g → Fin r → ℂ) (E F : Fin g → Fin g → ℂ) (τ : Fin g → Fin g → ℂ) (P Q : Fin r → Fin g → ℝ), (∀ m, lam m = ∑ k, (P m k : ℂ) • E k + ∑ k, (Q m k : ℂ) • F k) → (∀ j, F j = ∑ i, τ i j • E i) → (∀ i, ∑ m, ρ i m • lam m = Pi.single i 1) → ∀ u : Fin g → ℂ, ∃ a : Fin g → ℂ, u = ∑ k, a k • E k ∧ ‖a‖ ≤ (g : ℝ) * ((r : ℝ) * ‖ρ‖ * (‖P‖ + (g : ℝ) * ‖Q‖ * ‖τ‖)) * ‖u‖ := by
  intro g r lam ρ E F τ P Q hlam hF hρ u
  set K : ℝ := ‖P‖ + (g : ℝ) * ‖Q‖ * ‖τ‖ with hK
  let B : Fin r → Fin g → ℂ := fun m l => (P m l : ℂ) + ∑ k, (Q m k : ℂ) * τ l k
  let c : Fin g → Fin g → ℂ := fun i l => ∑ m, ρ i m * B m l
  have hB : ∀ m, lam m = ∑ l, B m l • E l := by
    intro m
    rw [hlam m]
    simp only [hF, B, add_smul, Finset.sum_add_distrib, Finset.sum_smul, Finset.smul_sum, smul_smul]
    congr 1
    rw [Finset.sum_comm]
  have hc : ∀ i, ∑ l, c i l • E l = Pi.single i 1 := by
    intro i
    rw [← hρ i]
    simp only [c, hB, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
  refine ⟨fun l => ∑ i, u i * c i l, ?_, ?_⟩
  · have h1 : ∑ k, (∑ i, u i * c i k) • E k = ∑ i, u i • ∑ k, c i k • E k := by
      simp only [Finset.sum_smul, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
    rw [h1]
    simp only [hc]
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  · have n2 : ∀ {a b : ℕ} (X : Fin a → Fin b → ℂ) (m : Fin a) (l : Fin b), ‖X m l‖ ≤ ‖X‖ :=
      fun X m l => (norm_le_pi_norm (X m) l).trans (norm_le_pi_norm X m)
    have n2r : ∀ {a b : ℕ} (X : Fin a → Fin b → ℝ) (m : Fin a) (l : Fin b), ‖(X m l : ℂ)‖ ≤ ‖X‖ :=
      fun X m l => by rw [Complex.norm_real]; exact (norm_le_pi_norm (X m) l).trans (norm_le_pi_norm X m)
    have hBn : ∀ m l, ‖B m l‖ ≤ K := by
      intro m l
      calc ‖B m l‖ ≤ ‖(P m l : ℂ)‖ + ‖∑ k, (Q m k : ℂ) * τ l k‖ := norm_add_le _ _
        _ ≤ ‖P‖ + ∑ k, ‖(Q m k : ℂ) * τ l k‖ := add_le_add (n2r P m l) (norm_sum_le _ _)
        _ ≤ ‖P‖ + ∑ _k : Fin g, ‖Q‖ * ‖τ‖ := by
            gcongr with k
            rw [norm_mul]
            exact mul_le_mul (n2r Q m k) (n2 τ l k) (norm_nonneg _) (norm_nonneg _)
        _ = K := by simp [hK, Finset.sum_const, mul_assoc]
    have hK0 : 0 ≤ K := by rw [hK]; positivity
    have hcn : ∀ i l, ‖c i l‖ ≤ (r : ℝ) * ‖ρ‖ * K := by
      intro i l
      calc ‖c i l‖ ≤ ∑ m, ‖ρ i m * B m l‖ := norm_sum_le _ _
        _ ≤ ∑ _m : Fin r, ‖ρ‖ * K := by
            gcongr with m
            rw [norm_mul]
            exact mul_le_mul (n2 ρ i m) (hBn m l) (norm_nonneg _) (norm_nonneg _)
        _ = (r : ℝ) * ‖ρ‖ * K := by simp [Finset.sum_const, mul_assoc]
    have hC0 : 0 ≤ (r : ℝ) * ‖ρ‖ * K := by positivity
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun l => ?_
    calc ‖∑ i, u i * c i l‖ ≤ ∑ i, ‖u i * c i l‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin g, ‖u‖ * ((r : ℝ) * ‖ρ‖ * K) := by
          gcongr with i
          rw [norm_mul]
          exact mul_le_mul (norm_le_pi_norm u i) (hcn i l) (norm_nonneg _) (norm_nonneg _)
      _ = _ := by simp [Finset.sum_const]; ring

end GlobalTheory
