import Mathlib

noncomputable def UpperTheory.Reformulated.B.IntegralPolynomialThird.IsIntP :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → ℂ_[p] → Prop :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (x : ℂ_[p]) ↦ ‖x‖ ≤ (1 : ℝ)

noncomputable def UpperTheory.Reformulated.B.IntegralPolynomialThird.IntegralMv.{u_1} :
    {σ : Type u_1} → {p : ℕ} → [inst : Fact (Nat.Prime p)] → MvPowerSeries σ ℂ_[p] → Prop :=
    fun {σ : Type u_1} {p : ℕ} [Fact (Nat.Prime p)] (F : MvPowerSeries σ ℂ_[p]) ↦
      ∀ (n : σ →₀ ℕ), UpperTheory.Reformulated.B.IntegralPolynomialThird.IsIntP ((MvPowerSeries.coeff n : MvPowerSeries σ ℂ_[p] → ℂ_[p]) F)

theorem UpperTheory.Reformulated.B.IntegralPolynomialThird.intMv_C.{u_1} :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {σ : Type u_1} {c : ℂ_[p]},
      UpperTheory.Reformulated.B.IntegralPolynomialThird.IsIntP c → UpperTheory.Reformulated.B.IntegralPolynomialThird.IntegralMv ((MvPowerSeries.C : ℂ_[p] → MvPowerSeries σ ℂ_[p]) c) := by
  intro p _ σ c hc n
  classical
  rw [MvPowerSeries.coeff_C]
  split_ifs
  · exact hc
  · show ‖(0 : ℂ_[p])‖ ≤ (1 : ℝ)
    rw [norm_zero]
    exact zero_le_one
