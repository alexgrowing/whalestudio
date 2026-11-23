import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization

noncomputable section

open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory.Published

def PartialZetaFunctionalEquation : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (C C' : ClassGroup (𝓞 F)) (D : (Ideal (𝓞 F))⁰),
    (D : Ideal (𝓞 F)) = differentIdeal ℤ (𝓞 F) → C * C' = ClassGroup.mk0 D →
    ∃ Z Z' : ℂ → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C Z ∧ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C' Z' ∧
      ∀ s : ℂ, (∀ n : ℕ, s ≠ -2 * n) → (∀ n : ℕ, 1 - s ≠ -2 * n) →
        (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ (s / 2) * Complex.Gammaℝ s ^ Module.finrank ℚ F * Z s =
          (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ ((1 - s) / 2) * Complex.Gammaℝ (1 - s) ^ Module.finrank ℚ F * Z' (1 - s)

end GlobalTheory.Published
