import Mathlib

namespace GlobalTheory.PowerSeriesShift

noncomputable def shift {σ O : Type} [CommRing O] (i : σ) (f : MvPowerSeries σ O) : MvPowerSeries σ O :=
  fun m : σ →₀ ℕ => MvPowerSeries.coeff (Finsupp.single i 1 + m) f

noncomputable def free {σ O : Type} [CommRing O] (i : σ) (f : MvPowerSeries σ O) : MvPowerSeries σ O :=
  fun m : σ →₀ ℕ => if m i = 0 then MvPowerSeries.coeff m f else (0 : O)

theorem eq_X_mul_shift_add {σ O : Type} [CommRing O] (i : σ) (f : MvPowerSeries σ O) :
    f = MvPowerSeries.X i * shift i f + free i f := by
  classical
  ext m
  rw [map_add, MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]
  by_cases h : m i = 0
  · have h1 : ¬ Finsupp.single i 1 ≤ m := by
      rw [Finsupp.single_le_iff]; omega
    rw [if_neg h1, zero_add]
    change _ = if m i = 0 then MvPowerSeries.coeff m f else (0 : O)
    rw [if_pos h]
  · have h1 : Finsupp.single i 1 ≤ m := by
      rw [Finsupp.single_le_iff]; omega
    rw [if_pos h1, one_mul]
    change _ = MvPowerSeries.coeff (Finsupp.single i 1 + (m - Finsupp.single i 1)) f +
      if m i = 0 then MvPowerSeries.coeff m f else (0 : O)
    rw [if_neg h, add_zero, add_tsub_cancel_of_le h1]

theorem main : (let d1 : {σ O : Type} → [CommRing O] → σ → MvPowerSeries σ O → MvPowerSeries σ O := @(fun {σ O : Type} [CommRing O] (i : σ) (f : MvPowerSeries σ O) (m : σ →₀ ℕ) ↦ (MvPowerSeries.coeff ((fun₀ | i => (1 : ℕ)) + m) : MvPowerSeries σ O → O) f); let d2 : {σ O : Type} → [CommRing O] → σ → MvPowerSeries σ O → MvPowerSeries σ O := @(fun {σ O : Type} [CommRing O] (i : σ) (f : MvPowerSeries σ O) (m : σ →₀ ℕ) ↦ if (m : σ → ℕ) i = (0 : ℕ) then (MvPowerSeries.coeff m : MvPowerSeries σ O → O) f else (0 : O)); ∀ {σ O : Type} [inst : CommRing O] (i : σ) (f : MvPowerSeries σ O), f = MvPowerSeries.X i * d1 i f + d2 i f) := by
  intro d1 d2 σ O _ i f
  exact eq_X_mul_shift_add i f

end GlobalTheory.PowerSeriesShift
