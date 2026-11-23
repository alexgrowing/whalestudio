import Mathlib
open scoped PowerSeries Pointwise

namespace GlobalTheory.InertiaEigenvalues.PowerSeriesFree

theorem coeff_term {O : Type} [CommRing O] (l : ℕ) (φ : O⟦X⟧ →ₐ[O] O⟦X⟧)
    (hφ : ∀ (f : O⟦X⟧) (m : ℕ), PowerSeries.coeff m (φ f) = if l ∣ m then PowerSeries.coeff (m / l) f else 0)
    (j m : ℕ) (g : O⟦X⟧) :
    PowerSeries.coeff m (PowerSeries.X ^ j * φ g) =
      if j ≤ m ∧ l ∣ (m - j) then PowerSeries.coeff ((m - j) / l) g else 0 := by
  rw [PowerSeries.coeff_X_pow_mul']
  by_cases h : j ≤ m
  · simp only [h, true_and, if_true]
    exact hφ g (m - j)
  · simp [h]

theorem coeff_sum {O : Type} [CommRing O] (l : ℕ) (hl : 2 ≤ l) (φ : O⟦X⟧ →ₐ[O] O⟦X⟧)
    (hφ : ∀ (f : O⟦X⟧) (m : ℕ), PowerSeries.coeff m (φ f) = if l ∣ m then PowerSeries.coeff (m / l) f else 0)
    (g : Fin l → O⟦X⟧) (m : ℕ) :
    PowerSeries.coeff m (∑ j : Fin l, PowerSeries.X ^ j.val * φ (g j)) =
      PowerSeries.coeff (m / l) (g ⟨m % l, Nat.mod_lt _ (by omega)⟩) := by
  have hl0 : 0 < l := by omega
  rw [map_sum]
  rw [Finset.sum_eq_single (⟨m % l, Nat.mod_lt _ hl0⟩ : Fin l)]
  · rw [coeff_term l φ hφ]
    have h1 : m % l ≤ m := Nat.mod_le _ _
    have h2 : l ∣ m - m % l := by
      have := Nat.div_add_mod m l
      exact ⟨m / l, by omega⟩
    have h3 : (m - m % l) / l = m / l := by
      have := Nat.div_add_mod m l
      rw [show m - m % l = l * (m / l) by omega]
      exact Nat.mul_div_cancel_left _ hl0
    simp only [h1, h2, and_self, if_true, h3]
  · intro j _ hj
    rw [coeff_term l φ hφ]
    rw [if_neg]
    rintro ⟨hjm, k, hk⟩
    apply hj
    ext
    simp only
    have hjl := j.isLt
    have : m = l * k + j.val := by omega
    rw [this, Nat.mul_add_mod]
    exact (Nat.mod_eq_of_lt hjl).symm
  · intro h; exact absurd (Finset.mem_univ _) h

theorem main : ∀ {O : Type} [CommRing O] (l : ℕ), 2 ≤ l → ∀ (φ : O⟦X⟧ →ₐ[O] O⟦X⟧), (∀ (f : O⟦X⟧) (m : ℕ), PowerSeries.coeff m (φ f) = if l ∣ m then PowerSeries.coeff (m / l) f else 0) → ∀ f : O⟦X⟧, ∃! g : Fin l → O⟦X⟧, f = ∑ j : Fin l, PowerSeries.X ^ j.val * φ (g j) := by
  intro O _ l hl φ hφ f
  have hl0 : 0 < l := by omega
  refine ⟨fun j => PowerSeries.mk (fun n => PowerSeries.coeff (n * l + j.val) f), ?_, ?_⟩
  · ext m
    rw [coeff_sum l hl φ hφ, PowerSeries.coeff_mk]
    simp only
    rw [Nat.div_add_mod']
  · intro g hg
    funext j
    ext n
    rw [PowerSeries.coeff_mk, hg, coeff_sum l hl φ hφ]
    have hj := j.isLt
    have e1 : (n * l + j.val) / l = n := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hl0, Nat.div_eq_of_lt hj, Nat.zero_add]
    have e2 : (n * l + j.val) % l = j.val := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    simp only [e1, e2]

end GlobalTheory.InertiaEigenvalues.PowerSeriesFree
