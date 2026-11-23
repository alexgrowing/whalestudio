import Mathlib

noncomputable def UpperTheory.Reformulated.B.IntegralPolynomialFirst.IsIntP :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → ℂ_[p] → Prop :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (x : ℂ_[p]) ↦ ‖x‖ ≤ (1 : ℝ)

noncomputable def UpperTheory.Reformulated.B.IntegralPolynomialFirst.IntegralMv.{u_1} :
    {σ : Type u_1} → {p : ℕ} → [inst : Fact (Nat.Prime p)] → MvPowerSeries σ ℂ_[p] → Prop :=
    fun {σ : Type u_1} {p : ℕ} [Fact (Nat.Prime p)] (F : MvPowerSeries σ ℂ_[p]) ↦
      ∀ (n : σ →₀ ℕ), UpperTheory.Reformulated.B.IntegralPolynomialFirst.IsIntP ((MvPowerSeries.coeff n : MvPowerSeries σ ℂ_[p] → ℂ_[p]) F)

theorem UpperTheory.Reformulated.B.IntegralPolynomialFirst.intMv_add.{u_1} :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {σ : Type u_1} {F G : MvPowerSeries σ ℂ_[p]},
      UpperTheory.Reformulated.B.IntegralPolynomialFirst.IntegralMv F → UpperTheory.Reformulated.B.IntegralPolynomialFirst.IntegralMv G → UpperTheory.Reformulated.B.IntegralPolynomialFirst.IntegralMv (F + G) := by
  intro p _ σ F G hF hG n
  have h1 : ‖MvPowerSeries.coeff n F‖ ≤ (1 : ℝ) := hF n
  have h2 : ‖MvPowerSeries.coeff n G‖ ≤ (1 : ℝ) := hG n
  show ‖MvPowerSeries.coeff n (F + G)‖ ≤ (1 : ℝ)
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)
