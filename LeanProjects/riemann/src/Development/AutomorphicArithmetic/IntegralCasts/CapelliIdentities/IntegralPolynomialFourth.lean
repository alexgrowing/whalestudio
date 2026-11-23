import Mathlib

noncomputable def UpperTheory.Reformulated.B.IntegralPolynomialFourth.IsIntP :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → ℂ_[p] → Prop :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (x : ℂ_[p]) ↦ ‖x‖ ≤ (1 : ℝ)

noncomputable def UpperTheory.Reformulated.B.IntegralPolynomialFourth.IntegralMv.{u_1} :
    {σ : Type u_1} → {p : ℕ} → [inst : Fact (Nat.Prime p)] → MvPowerSeries σ ℂ_[p] → Prop :=
    fun {σ : Type u_1} {p : ℕ} [Fact (Nat.Prime p)] (F : MvPowerSeries σ ℂ_[p]) ↦
      ∀ (n : σ →₀ ℕ), UpperTheory.Reformulated.B.IntegralPolynomialFourth.IsIntP ((MvPowerSeries.coeff n : MvPowerSeries σ ℂ_[p] → ℂ_[p]) F)

theorem UpperTheory.Reformulated.B.IntegralPolynomialFourth.intMv_neg.{u_1} :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {σ : Type u_1} {F : MvPowerSeries σ ℂ_[p]},
      UpperTheory.Reformulated.B.IntegralPolynomialFourth.IntegralMv F → UpperTheory.Reformulated.B.IntegralPolynomialFourth.IntegralMv (-F) := by
  intro p _ σ F h n
  have hn : ‖MvPowerSeries.coeff n F‖ ≤ (1 : ℝ) := h n
  show ‖MvPowerSeries.coeff n (-F)‖ ≤ (1 : ℝ)
  rw [map_neg, norm_neg]
  exact hn
