import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

private theorem UpperTheory.eisenstein_coeff_root_pow {K : Type} [Field K] [CharZero K] (j M : ℕ) (ζ : K) (a₁ a₂ : ℤ) (β n : ℕ) :
    eisF j M (ζ ^ β) a₁ a₂ n = eisF j M ζ a₁ ((β : ℤ) * a₂) n := by
  have hz : ∀ t : ℤ, (ζ ^ β) ^ t = ζ ^ ((β : ℤ) * t) := fun t => by
    rw [zpow_mul, zpow_natCast]
  unfold eisF const0 coefPos
  simp only [hz, mul_neg, mul_assoc]

theorem UpperTheory.smoothedEisenstein_root_pow :
    ∀ {K : Type} [Field K] [CharZero K] (c : ℤ) (j M : ℕ) (ζ : K) (a₁ a₂ : ℤ) (β : ℕ), ζ ≠ 0 → smF c j M (ζ ^ β) a₁ a₂ = smF c j M ζ a₁ ((β : ℤ) * a₂) := by
  intro K _ _ c j M ζ a₁ a₂ β _
  funext n
  unfold smF
  rw [UpperTheory.eisenstein_coeff_root_pow, UpperTheory.eisenstein_coeff_root_pow, mul_left_comm (β : ℤ) c a₂]
