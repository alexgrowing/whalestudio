import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.EntireEqZeroOrEqZeroOfMulEqZero
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsEqCexpQuadraticOfEquivalentFactors

namespace GlobalTheory

theorem log_translate_sub_const_of_quasiPeriodic {g : ℕ} {θ ρ q : (Fin g → ℂ) → ℂ}
    {la : Fin g → ℂ} {A B : (Fin g → ℂ) →ₗ[ℂ] ℂ} {a b : ℂ} (hθ : Differentiable ℂ θ) (hθ0 : θ ≠ 0)
    (hρ : Differentiable ℂ ρ) (hq : Continuous q) (hqρ : ∀ z, Complex.exp (q z) = ρ z)
    (ha : a ≠ 0) (h1 : ∀ z, θ (z + la) = a * Complex.exp (A z) * θ z)
    (h2 : ∀ z, θ (z + la) * ρ (z + la) = b * Complex.exp (B z) * (θ z * ρ z)) (z w) :
    q (z + la) - q z - (B z - A z) = q (w + la) - q w - (B w - A w) := by
  have hA : Differentiable ℂ A := (LinearMap.toContinuousLinearMap A).differentiable
  have hB : Differentiable ℂ B := (LinearMap.toContinuousLinearMap B).differentiable
  have hρ' : Differentiable ℂ fun z => ρ (z + la) := hρ.comp (differentiable_id.add_const la)
  have hF : Differentiable ℂ fun z =>
      a * Complex.exp (A z) * ρ (z + la) - b * Complex.exp (B z) * ρ z :=
    ((hA.cexp.const_mul a).mul hρ').sub ((hB.cexp.const_mul b).mul hρ)
  have key : ∀ z, a * Complex.exp (A z) * ρ (z + la) - b * Complex.exp (B z) * ρ z = 0 := by
    rcases entire_eq_zero_or_eq_zero_of_mul_eq_zero θ _ hθ hF (fun z => by
      have := h2 z
      rw [h1 z] at this
      linear_combination this) with h | h
    · exact absurd (funext h) hθ0
    · exact h
  have hexp : ∀ z, Complex.exp (q (z + la) - q z - (B z - A z)) = b / a := by
    intro z
    have hk := key z
    rw [← hqρ, ← hqρ] at hk
    have e1 := Complex.exp_ne_zero (q z)
    have e2 := Complex.exp_ne_zero (A z)
    have e3 := Complex.exp_ne_zero (B z)
    rw [Complex.exp_sub, Complex.exp_sub, Complex.exp_sub]
    field_simp
    linear_combination hk
  have hc : Continuous fun z => q (z + la) - q z - (B z - A z) :=
    ((hq.comp (continuous_id.add continuous_const)).sub hq).sub
      (hB.continuous.sub hA.continuous)
  exact Complex.isCoveringMap_exp.const_of_comp hc
    (fun u v => Subtype.ext ((hexp u).trans (hexp v).symm)) z w

theorem factor_commutator_eq_of_nonvanishing :
    ∀ (g : ℕ) (θ ρ : (Fin g → ℂ) → ℂ) (la mu : Fin g → ℂ) (A₁ A₂ B₁ B₂ : (Fin g → ℂ) →ₗ[ℂ] ℂ)
      (a₁ a₂ b₁ b₂ : ℂ), Differentiable ℂ θ → θ ≠ 0 → Differentiable ℂ ρ → (∀ z, ρ z ≠ 0) →
      a₁ ≠ 0 → a₂ ≠ 0 → (∀ z, θ (z + la) = a₁ * Complex.exp (A₁ z) * θ z) →
      (∀ z, θ (z + mu) = a₂ * Complex.exp (A₂ z) * θ z) →
      (∀ z, θ (z + la) * ρ (z + la) = b₁ * Complex.exp (B₁ z) * (θ z * ρ z)) →
      (∀ z, θ (z + mu) * ρ (z + mu) = b₂ * Complex.exp (B₂ z) * (θ z * ρ z)) →
      B₁ mu - A₁ mu = B₂ la - A₂ la := by
  intro g θ ρ la mu A₁ A₂ B₁ B₂ a₁ a₂ b₁ b₂ hθ hθ0 hρ hρ0 ha₁ ha₂ h1 h2 h3 h4
  obtain ⟨q, hq, hqρ⟩ := exists_continuous_cexp_eq hρ.continuous hρ0
  have e1 := log_translate_sub_const_of_quasiPeriodic hθ hθ0 hρ hq hqρ ha₁ h1 h3 mu 0
  have e2 := log_translate_sub_const_of_quasiPeriodic hθ hθ0 hρ hq hqρ ha₂ h2 h4 la 0
  simp only [zero_add, map_zero, sub_zero] at e1 e2
  rw [add_comm mu la] at e1
  linear_combination e2 - e1

end GlobalTheory
