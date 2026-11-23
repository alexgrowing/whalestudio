import Mathlib

namespace GlobalTheory

theorem mvPowerSeries_coeff_eq_zero_of_mul_coeff_eq_zero :
    ∀ (F : Type) [Field F] (σ : Type) [Fintype σ] (h : MvPowerSeries σ F), h ≠ 0 → ∃ k : ℕ, ∀ (m : ℕ) (u : MvPowerSeries σ F), (∀ e : σ →₀ ℕ, e.degree ≤ m → MvPowerSeries.coeff e (h * u) = 0) → ∀ e : σ →₀ ℕ, e.degree + k ≤ m → MvPowerSeries.coeff e u = 0 := by
  intro F _ σ _ h hh
  have hfin : h.order ≠ ⊤ := fun ht => hh (MvPowerSeries.order_eq_top_iff.mp ht)
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hfin
  refine ⟨k, fun m u hu e he => ?_⟩
  by_contra hne
  have h1 : u.order ≤ (e.degree : ℕ∞) := MvPowerSeries.order_le hne
  have h2 : ((m + 1 : ℕ) : ℕ∞) ≤ (h * u).order :=
    MvPowerSeries.nat_le_order fun d hd => hu d (Nat.lt_succ_iff.mp hd)
  rw [MvPowerSeries.order_mul, ← hk] at h2
  have h3 : ((m + 1 : ℕ) : ℕ∞) ≤ ((k + e.degree : ℕ) : ℕ∞) := by
    refine h2.trans ?_
    rw [Nat.cast_add]
    exact add_le_add le_rfl h1
  have h4 : m + 1 ≤ k + e.degree := by exact_mod_cast h3
  omega

end GlobalTheory
