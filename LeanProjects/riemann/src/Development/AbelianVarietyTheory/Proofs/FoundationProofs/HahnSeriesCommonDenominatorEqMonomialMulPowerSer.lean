import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem fnShape : ∀ (Ω : Type) [Field Ω] (h : HahnSeries ℚ Ω), Den h → h ≠ 0 → ∃ (N : ℕ) (n₀ : ℤ) (a : ℕ → Ω), 0 < N ∧ a 0 ≠ 0 ∧ (∀ k : ℕ, h.coeff (((n₀ + k : ℤ) : ℚ) / N) = a k) ∧ ∀ r : ℚ, (∀ k : ℕ, r ≠ ((n₀ + k : ℤ) : ℚ) / N) → h.coeff r = 0 := by
  intro Ω _ h hD h0
  obtain ⟨N, hN, hd⟩ := hD
  have hc : h.coeff h.order ≠ 0 := fun e => h0 (HahnSeries.coeff_order_eq_zero.mp e)
  obtain ⟨n₀, hn₀⟩ := hd _ hc
  refine ⟨N, n₀, fun k => h.coeff (((n₀ + k : ℤ) : ℚ) / N), hN, ?_, fun k => rfl, ?_⟩
  · simpa [← hn₀] using hc
  · intro r hr
    by_contra hne
    obtain ⟨n, rfl⟩ := hd r hne
    have hle : h.order ≤ (n : ℚ) / N := HahnSeries.order_le_of_coeff_ne_zero hne
    rw [hn₀] at hle
    have hNq : (0 : ℚ) < N := by exact_mod_cast hN
    have : (n₀ : ℚ) ≤ n := by
      have := (div_le_div_iff_of_pos_right hNq).mp hle
      exact this
    have hnn : n₀ ≤ n := by exact_mod_cast this
    apply hr (n - n₀).toNat
    congr 2
    push_cast
    rw [Int.toNat_of_nonneg (by omega)]
    ring

end GlobalTheory
