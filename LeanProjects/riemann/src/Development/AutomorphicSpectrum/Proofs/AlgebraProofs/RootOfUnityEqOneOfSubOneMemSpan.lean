import Mathlib
open MeasureTheory NumberField Matrix Filter Topology
open scoped Pointwise ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem rootOfUnity_eq_one_of_sub_one_mem_span : ∀ (E : Type) [Field E] [NumberField E] (z : 𝓞 E) (n M : ℕ), 0 < n → 3 ≤ M → z ^ n = 1 → z - 1 ∈ Ideal.span {(M : 𝓞 E)} → z = 1 := by
  intro E _ _ z n M hn hM hz hmem
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hmem
  suffices hw0 : w = 0 by
    rw [hw0, zero_mul] at hw
    exact sub_eq_zero.mp hw.symm
  have hMpos : (0 : ℝ) < M := by
    have : 0 < M := by omega
    exact_mod_cast this
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hzE : (z : E) ^ n = 1 := by
    have h := congrArg (algebraMap (𝓞 E) E) hz
    rw [map_pow, map_one] at h
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap]
    exact h
  have hwE : (w : E) * (M : E) = (z : E) - 1 := by
    have h := congrArg (algebraMap (𝓞 E) E) hw
    rw [map_mul, map_sub, map_natCast, map_one] at h
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap w, NumberField.RingOfIntegers.coe_eq_algebraMap z]
    exact h
  have hbound : ∀ σ : E →ₐ[ℚ] ℂ, ‖σ (w : E)‖ ≤ 2 / M := by
    intro σ
    have hz1 : ‖σ (z : E)‖ = 1 := by
      have h1 : ‖σ (z : E)‖ ^ n = 1 := by
        rw [← norm_pow, ← map_pow, hzE, map_one, norm_one]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').mp h1
    have h2 : σ (w : E) * (M : ℂ) = σ (z : E) - 1 := by
      have h := congrArg σ hwE
      rw [map_mul, map_sub, map_natCast, map_one] at h
      exact h
    have h3 : ‖σ (w : E)‖ * (M : ℝ) ≤ 2 := by
      have h4 : ‖σ (w : E) * (M : ℂ)‖ = ‖σ (w : E)‖ * (M : ℝ) := by
        rw [norm_mul, Complex.norm_natCast]
      rw [← h4, h2]
      calc ‖σ (z : E) - 1‖ ≤ ‖σ (z : E)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [hz1, norm_one]; norm_num
    exact (le_div_iff₀ hMpos).mpr h3
  have hcard : Fintype.card (E →ₐ[ℚ] ℂ) ≠ 0 := by
    rw [AlgHom.card ℚ E ℂ]
    exact (Module.finrank_pos).ne'
  have hprod : ‖((Algebra.norm ℤ w : ℤ) : ℂ)‖ < 1 := by
    have h1 : ((Algebra.norm ℤ w : ℤ) : ℂ) = algebraMap ℚ ℂ (Algebra.norm ℚ (w : E)) := by
      rw [← Algebra.coe_norm_int, map_intCast]
    rw [h1, Algebra.norm_eq_prod_embeddings ℚ ℂ (w : E), norm_prod]
    calc ∏ σ : E →ₐ[ℚ] ℂ, ‖σ (w : E)‖ ≤ ∏ _σ : E →ₐ[ℚ] ℂ, (2 / M : ℝ) :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun σ _ => hbound σ)
      _ = (2 / M : ℝ) ^ Fintype.card (E →ₐ[ℚ] ℂ) := by rw [Finset.prod_const, Finset.card_univ]
      _ < 1 := pow_lt_one₀ (by positivity) ((div_lt_one hMpos).mpr (by linarith)) hcard
  have hN : Algebra.norm ℤ w = 0 := by
    rw [Complex.norm_intCast] at hprod
    have habs : ((|Algebra.norm ℤ w| : ℤ) : ℝ) < 1 := by
      push_cast
      exact hprod
    have habs' : |Algebra.norm ℤ w| < 1 := by exact_mod_cast habs
    exact Int.abs_lt_one_iff.mp habs'
  exact Algebra.norm_eq_zero_iff.mp hN

end GlobalTheory.CompanionTheory.Ar.Cmp
