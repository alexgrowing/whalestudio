import Mathlib
import Formalism.PairingDivisors.StatementA
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeLEntireAndNonzeroAtOneHolds

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal

theorem IsHeckeL.ne_zero_nat {E : Type} [Field E] [NumberField E] {χ : HChar E} {Λ : ℂ → ℂ} (hu : IsUnitary χ)
    (hΛ : IsHeckeL χ Λ) {s : ℕ} (hs : 1 ≤ s) : Λ s ≠ 0 := by
  rcases hs.eq_or_lt with rfl | h
  · obtain ⟨Z, hZd, hZ⟩ := GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire E
    rw [Nat.cast_one]
    exact GlobalTheory.eulerProduct_ne_zero_one_of_entire _ _ (GlobalTheory.HeckeOne.cf χ) GlobalTheory.HeckeOne.two_le_N
      (GlobalTheory.HeckeOne.norm_cf hu) GlobalTheory.HeckeOne.sumN GlobalTheory.HeckeOne.nonemptyN Z Λ hZd hΛ.1 hZ
      fun s hs => (hΛ.2 s hs).unique (GlobalTheory.HeckeOne.hasProd_exp hu hs)
  · have hs' : 1 < (s : ℂ).re := by
      rw [Complex.natCast_re]; exact_mod_cast h
    rw [(hΛ.2 _ hs').unique (GlobalTheory.HeckeOne.hasProd_exp hu hs')]
    exact Complex.exp_ne_zero _

theorem heckeL_ne_zero_nat : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (m : I → ℤ) (χ : HChar E), IsCMType φ → IsUnitary χ → HasInf χ φ m → (∃ i, m i ≠ 0) → ∃ Λ, IsHeckeL χ Λ) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (m : I → ℤ) (χ : HChar E) (Λ : ℂ → ℂ) (s : ℕ), IsUnitary χ → HasInf χ φ m → (∀ i, 0 < m i) → IsHeckeL χ Λ → 1 ≤ s → Λ s ≠ 0 :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ hu _ _ hΛ hs => hΛ.ne_zero_nat hu hs

end GlobalTheory.CMVal
