import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR

open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

theorem cc_smul_q {S σ : Type} [CommRing S] {q : MvPowerSeries σ S} (hq : MvPowerSeries.constantCoeff q = 0)
    (r : S) : MvPowerSeries.constantCoeff (r • q) = 0 := by
  rw [MvPowerSeries.smul_eq_C_mul, map_mul, hq, mul_zero]

theorem exp_pow_eq {S σ : Type} [CommRing S] [Algebra ℚ S] (q : MvPowerSeries σ S)
    (hq : MvPowerSeries.constantCoeff q = 0) : ∀ k : ℕ,
    PowerSeries.subst q (PowerSeries.exp S) ^ k = PowerSeries.subst ((k : S) • q) (PowerSeries.exp S)
  | 0 => by rw [pow_zero, Nat.cast_zero, zero_smul, exp_zero]
  | k + 1 => by
    rw [pow_succ, exp_pow_eq q hq k, ← exp_add (ha := cc_smul_q hq (k : S)) (hb := hq), Nat.cast_succ, add_smul,
      one_smul]

theorem exp_pow_mul_exp_neg {S σ : Type} [CommRing S] [Algebra ℚ S] (q : MvPowerSeries σ S)
    (hq : MvPowerSeries.constantCoeff q = 0) (k : ℕ) :
    PowerSeries.subst q (PowerSeries.exp S) ^ k * PowerSeries.subst (-((k : S) • q)) (PowerSeries.exp S) = 1 := by
  have hneg : MvPowerSeries.constantCoeff (-((k : S) • q)) = 0 := by
    rw [map_neg, cc_smul_q hq, neg_zero]
  rw [exp_pow_eq q hq k, ← exp_add (cc_smul_q hq _) hneg, add_neg_cancel, exp_zero]

end Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
