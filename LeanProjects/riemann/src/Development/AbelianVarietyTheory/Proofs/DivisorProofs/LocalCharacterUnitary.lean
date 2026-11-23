import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreduc
open ValuativeRel
open scoped Matrix Topology

namespace GlobalTheory

theorem addChar_norm_eq_one_of_continuous {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [CharZero k]
    (ψ0 : AddChar k ℂ) (hψ : Continuous ψ0) (x : k) : ‖ψ0 x‖ = 1 := by
  have hK : IsCompact (𝒪[k] : Set k) := IsNonarchimedeanLocalField.isCompact_closedBall k 1
  have hbd : ∀ y : k, ∃ C : ℝ, ∀ n : ℕ, ‖ψ0 y‖ ^ n ≤ C := by
    intro y
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
      (f := fun o : k => ψ0 (o * y)) (by fun_prop)
    refine ⟨C, fun n => ?_⟩
    have := hC (n : k) (natCast_mem _ n)
    rwa [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow, norm_pow] at this
  have hle : ∀ y : k, ‖ψ0 y‖ ≤ 1 := by
    intro y
    obtain ⟨C, hC⟩ := hbd y
    by_contra h
    push_neg at h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C h
    exact absurd (hC n) (not_le.2 hn)
  have hmul : ‖ψ0 x‖ * ‖ψ0 (-x)‖ = 1 := by
    rw [← norm_mul, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, norm_one]
  have h1 := hle x
  have h2 := hle (-x)
  have h3 := norm_nonneg (ψ0 x)
  have h4 := norm_nonneg (ψ0 (-x))
  nlinarith

theorem addChar_norm_eq_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [CharZero k]
    (ψ0 : AddChar k ℂ), Continuous ψ0 → ∀ x : k, ‖ψ0 x‖ = 1 :=
  fun ψ0 hψ x => addChar_norm_eq_one_of_continuous ψ0 hψ x

end GlobalTheory
