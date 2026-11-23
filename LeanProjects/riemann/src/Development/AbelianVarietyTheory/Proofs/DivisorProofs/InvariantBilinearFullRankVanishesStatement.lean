import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantBilinearFullRankVanishes
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShearGLTransposeMul
open scoped Matrix
open GlobalTheory.WeilM GlobalTheory.FullRankCoinv

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_bilinear_full_rank_vanishes : GlobalTheory.ThK.KP → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n ρ d : ℕ) (ν : kˣ →* ℂˣ) (ϖ : kˣ), n < d → ρ < n → GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν → (∀ m : ℕ, 0 < m → ∀ r : ℝ, ((ν ϖ : ℂ)) ^ m ≠ (r : ℂ)) →
    ∀ Bf : fullRk k n d →ₗ[ℂ] fullRk k ρ d →ₗ⋆[ℂ] ℂ,
      (∀ (g : GL (Fin n) k) (Ψ₁ Ψ₁' : fullRk k n d) (Ψ₂ : fullRk k ρ d), Ψ₁'.1 = lact ν g Ψ₁.1 → Bf Ψ₁' Ψ₂ = Bf Ψ₁ Ψ₂) →
      (∀ h : GL (Fin d) k, ∃ m : ℝ, 0 < m ∧ ∀ (Ψ₁ Ψ₁' : fullRk k n d) (Ψ₂ Ψ₂' : fullRk k ρ d),
        Ψ₁'.1 = (fun Y => Ψ₁.1 (Y * h.1)) → Ψ₂'.1 = (fun Y => Ψ₂.1 (Y * h.1)) → (m : ℂ) * Bf Ψ₁' Ψ₂' = Bf Ψ₁ Ψ₂) →
      ∀ Ψ₁ Ψ₂, Bf Ψ₁ Ψ₂ = 0 := by
  first | exact @GlobalTheory.FibreVanish.form_eq_zero | exact GlobalTheory.FibreVanish.form_eq_zero | (intros; apply GlobalTheory.FibreVanish.form_eq_zero <;> assumption)
