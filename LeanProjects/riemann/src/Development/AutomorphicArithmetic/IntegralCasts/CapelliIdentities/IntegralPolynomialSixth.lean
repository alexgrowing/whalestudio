import Mathlib

noncomputable def UpperTheory.Reformulated.B.IntegralMvPowerSeriesOverPadicComplex.IsIntP :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → ℂ_[p] → Prop :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (x : ℂ_[p]) ↦ ‖x‖ ≤ (1 : ℝ)

noncomputable def UpperTheory.Reformulated.B.IntegralMvPowerSeriesOverPadicComplex.IntegralMv.{u_1} :
    {σ : Type u_1} → {p : ℕ} → [inst : Fact (Nat.Prime p)] → MvPowerSeries σ ℂ_[p] → Prop :=
    fun {σ : Type u_1} {p : ℕ} [Fact (Nat.Prime p)] (F : MvPowerSeries σ ℂ_[p]) ↦
      ∀ (n : σ →₀ ℕ), UpperTheory.Reformulated.B.IntegralMvPowerSeriesOverPadicComplex.IsIntP ((MvPowerSeries.coeff n : MvPowerSeries σ ℂ_[p] → ℂ_[p]) F)

theorem UpperTheory.Reformulated.B.IntegralMvPowerSeriesOverPadicComplex.intMv_zero.{u_1} :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {σ : Type u_1}, UpperTheory.Reformulated.B.IntegralMvPowerSeriesOverPadicComplex.IntegralMv (0 : MvPowerSeries σ ℂ_[p]) := by
  intro p inst σ n
  show ‖(MvPowerSeries.coeff n : MvPowerSeries σ ℂ_[p] → ℂ_[p]) 0‖ ≤ (1 : ℝ)
  rw [map_zero, norm_zero]
  exact zero_le_one
