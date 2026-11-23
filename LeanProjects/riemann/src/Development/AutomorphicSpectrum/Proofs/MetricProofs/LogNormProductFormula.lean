import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsFibreChartIff
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem log_norm_mul_prod_ite_zpow (N : ℕ) (P : Fin N → Prop) (t : ℂ) (v f : Fin N → ℂ)
    (e : Fin N → ℤ) (ht : t ≠ 0) (h : ∀ i, ¬ P i → v i ≠ 0 ∧ f i ≠ 0) :
    Real.log ‖t * ∏ i : Fin N, (if P i then 1 else v i * f i) ^ e i‖ =
      Real.log ‖t‖ + ∑ i : Fin N, (e i : ℝ) *
        (if P i then 0 else Real.log ‖v i‖ + Real.log ‖f i‖) := by
  have hne : ∀ i, (if P i then (1 : ℂ) else v i * f i) ≠ 0 := by
    intro i
    split_ifs with hp
    · exact one_ne_zero
    · exact mul_ne_zero (h i hp).1 (h i hp).2
  have hfac : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      ‖(if P i then (1 : ℂ) else v i * f i) ^ e i‖ ≠ 0 :=
    fun i _ => norm_ne_zero_iff.mpr (zpow_ne_zero _ (hne i))
  have hprod : ∏ i : Fin N, ‖(if P i then (1 : ℂ) else v i * f i) ^ e i‖ ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hfac
  rw [norm_mul, norm_prod, Real.log_mul (norm_ne_zero_iff.mpr ht) hprod, Real.log_prod hfac]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_zpow, Real.log_zpow]
  split_ifs with hp
  · simp
  · rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (h i hp).1)
      (norm_ne_zero_iff.mpr (h i hp).2)]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
