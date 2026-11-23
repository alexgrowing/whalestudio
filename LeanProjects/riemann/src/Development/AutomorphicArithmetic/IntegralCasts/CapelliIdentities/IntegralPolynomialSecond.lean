import Mathlib

noncomputable def UpperTheory.Reformulated.B.IntegralPolynomialSecond.IsIntP :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → ℂ_[p] → Prop :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (x : ℂ_[p]) ↦ ‖x‖ ≤ (1 : ℝ)

noncomputable def UpperTheory.Reformulated.B.IntegralPolynomialSecond.IntegralMv.{u_1} :
    {σ : Type u_1} → {p : ℕ} → [inst : Fact (Nat.Prime p)] → MvPowerSeries σ ℂ_[p] → Prop :=
    fun {σ : Type u_1} {p : ℕ} [Fact (Nat.Prime p)] (F : MvPowerSeries σ ℂ_[p]) ↦
      ∀ (n : σ →₀ ℕ), UpperTheory.Reformulated.B.IntegralPolynomialSecond.IsIntP ((MvPowerSeries.coeff n : MvPowerSeries σ ℂ_[p] → ℂ_[p]) F)

theorem UpperTheory.Reformulated.B.IntegralPolynomialSecond.intMv_mul.{u_1} :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {σ : Type u_1} {F G : MvPowerSeries σ ℂ_[p]},
      UpperTheory.Reformulated.B.IntegralPolynomialSecond.IntegralMv F → UpperTheory.Reformulated.B.IntegralPolynomialSecond.IntegralMv G → UpperTheory.Reformulated.B.IntegralPolynomialSecond.IntegralMv (F * G) := by
  intro p _ σ F G hF hG n
  classical
  change ‖MvPowerSeries.coeff n (F * G)‖ ≤ 1
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
  intro q _
  rw [norm_mul]
  exact mul_le_one₀ (hF q.1) (norm_nonneg _) (hG q.2)
