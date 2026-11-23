import Mathlib

namespace GlobalTheory.LogSubst

open MvPowerSeries

theorem coeff_pow_pow_eq_zero {C σ : Type} [CommRing C] {l : ℕ} (hl : 2 ≤ l)
    {u : MvPowerSeries σ C} (hu : constantCoeff u = 0) {μ : σ →₀ ℕ} {s : ℕ}
    (h : μ.degree ≤ s) : coeff μ (u ^ (l ^ s)) = 0 := by
  apply coeff_of_lt_order
  refine lt_of_lt_of_le ?_ (le_order_pow_of_constantCoeff_eq_zero _ hu)
  have : s < l ^ s := Nat.lt_pow_self (by omega)
  exact_mod_cast lt_of_le_of_lt h this

theorem coeff_subst_sum_pow_pow : ∀ (C : Type) [Field C] (σ τ I : Type) [Fintype σ] [Fintype τ] [Fintype I] (l : ℕ), 2 ≤ l → ∀ (co : I → ℕ → C) (t : I → MvPowerSeries σ C) (F : MvPowerSeries σ C) (f : σ → MvPowerSeries τ C), (∀ x, MvPowerSeries.constantCoeff (f x) = 0) → (∀ c, MvPowerSeries.constantCoeff (t c) = 0) → (∀ μ : σ →₀ ℕ, MvPowerSeries.coeff μ F = ∑ s ∈ Finset.range (μ.degree + 1), ∑ c, co c s * MvPowerSeries.coeff μ (t c ^ (l ^ s))) → ∀ ν : τ →₀ ℕ, MvPowerSeries.coeff ν (MvPowerSeries.subst f F) = ∑ s ∈ Finset.range (ν.degree + 1), ∑ c, co c s * MvPowerSeries.coeff ν ((MvPowerSeries.subst f (t c) : MvPowerSeries τ C) ^ (l ^ s)) := by
  intro C _ σ τ I _ _ _ l hl co t F f hf ht hF ν
  have hs : HasSubst f := hasSubst_of_constantCoeff_zero hf
  set G : MvPowerSeries σ C :=
    ∑ s ∈ Finset.range (ν.degree + 1), ∑ c, co c s • t c ^ (l ^ s) with hG
  have hord : ((ν.degree + 1 : ℕ) : ℕ∞) ≤ (F - G).order := by
    apply nat_le_order
    intro μ hμ
    rw [map_sub, hF μ, hG, sub_eq_zero]
    simp only [map_sum, coeff_smul]
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) ?_
    intro s _ hs'
    rw [Finset.mem_range] at hs'
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [coeff_pow_pow_eq_zero hl (ht c) (by omega), mul_zero]
  have h1 : (1 : ℕ∞) ≤ ⨅ i, (f i).order :=
    le_iInf fun i => one_le_order_iff_constCoeff_eq_zero.2 (hf i)
  have h2 : ((ν.degree + 1 : ℕ) : ℕ∞) ≤ (subst f (F - G) : MvPowerSeries τ C).order := by
    refine le_trans ?_ (le_order_subst hs (F - G))
    calc ((ν.degree + 1 : ℕ) : ℕ∞) = 1 * ((ν.degree + 1 : ℕ) : ℕ∞) := (one_mul _).symm
      _ ≤ _ := mul_le_mul' h1 hord
  have h3 : coeff ν (subst f (F - G) : MvPowerSeries τ C) = 0 := by
    apply coeff_of_lt_order
    refine lt_of_lt_of_le ?_ h2
    exact_mod_cast Nat.lt_succ_self _
  rw [← substAlgHom_apply hs, map_sub, map_sub, sub_eq_zero, substAlgHom_apply] at h3
  rw [h3, hG]
  simp only [map_sum, map_smul, map_pow, substAlgHom_apply, smul_eq_mul]

end GlobalTheory.LogSubst
