import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem PositivityTheory.Xgp.t_pol_sec : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (α : K → ℤ) (dβ : K → ℕ), (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∃ k : ℕ, 1 ≤ k ∧ ∃ e ∈ chartLat y (fun κ => (k : ℤ) * α κ - 1) 1, e ≠ 0) → ∃ k : ℕ, 1 ≤ k ∧ ∃ e ∈ chartLat y (fun κ => (k : ℤ) * α κ - 1 - dβ κ) 1, e ≠ 0 := by
  intro K _ ι _ Ω _ y α dβ hy hex
  obtain ⟨k, hk, e, he, hne⟩ := hex
  choose i hi using hy
  set D := ∑ κ, dβ κ with hDdef
  have hD : ∀ κ, dβ κ ≤ D := fun κ =>
    Finset.single_le_sum (f := dβ) (fun _ _ => Nat.zero_le _) (Finset.mem_univ κ)
  refine ⟨(D + 1) * k, le_trans hk (Nat.le_mul_of_pos_left k (Nat.succ_pos D)),
    e ^ (D + 1) * ∏ κ, y ⟨κ, i κ⟩ ^ (D - dβ κ), ?_, ?_⟩
  · intro c hc
    have h1 := he c hc
    have key : e ^ (D + 1) * (∏ κ, y ⟨κ, i κ⟩ ^ (D - dβ κ)) *
        ∏ κ, y ⟨κ, c κ⟩ ^ (-(((1 : ℕ) : ℤ) * ((((D + 1) * k : ℕ) : ℤ) * α κ - 1 - (dβ κ : ℤ))))
        = (e * ∏ κ, y ⟨κ, c κ⟩ ^ (-(((1 : ℕ) : ℤ) * ((k : ℤ) * α κ - 1)))) ^ (D + 1) *
          ∏ κ, (y ⟨κ, i κ⟩ / y ⟨κ, c κ⟩) ^ (D - dβ κ) := by
      rw [mul_pow, ← Finset.prod_pow, mul_assoc, mul_assoc]
      congr 1
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun κ _ => ?_)
      have hyc : y ⟨κ, c κ⟩ ≠ 0 := hc κ
      rw [div_pow, ← zpow_natCast (y ⟨κ, c κ⟩) (D - dβ κ),
        ← zpow_natCast (y ⟨κ, c κ⟩ ^ (-(((1 : ℕ) : ℤ) * ((k : ℤ) * α κ - 1)))) (D + 1), ← zpow_mul]
      have hexp : -(((1 : ℕ) : ℤ) * ((((D + 1) * k : ℕ) : ℤ) * α κ - 1 - (dβ κ : ℤ)))
          = -(((1 : ℕ) : ℤ) * ((k : ℤ) * α κ - 1)) * ((D + 1 : ℕ) : ℤ) - ((D - dβ κ : ℕ) : ℤ) := by
        rw [Nat.cast_sub (hD κ)]
        push_cast
        ring
      rw [hexp, zpow_sub₀ hyc]
      ring
    rw [key]
    refine Subalgebra.mul_mem _ (Subalgebra.pow_mem _ h1 _) (Subalgebra.prod_mem _ (fun κ _ => ?_))
    refine Subalgebra.pow_mem _ ?_ _
    unfold chartRingZ
    exact Algebra.subset_adjoin (Set.mem_range.2 ⟨⟨κ, i κ⟩, rfl⟩)
  · exact mul_ne_zero (pow_ne_zero _ hne)
      (Finset.prod_ne_zero_iff.2 fun κ _ => pow_ne_zero _ (hi κ))
