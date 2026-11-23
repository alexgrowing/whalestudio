import Mathlib

noncomputable def UpperTheory.Reformulated.B.IsIntegralNatCast.IsIntP :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → ℂ_[p] → Prop :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (x : ℂ_[p]) ↦ ‖x‖ ≤ (1 : ℝ)

theorem UpperTheory.Reformulated.B.IsIntegralNatCast.isPadicIntegral_natCast :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] (n : ℕ), UpperTheory.Reformulated.B.IsIntegralNatCast.IsIntP (↑n : ℂ_[p]) := by
  intro p _ n
  exact IsUltrametricDist.norm_natCast_le_one ℂ_[p] n
