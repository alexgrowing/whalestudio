import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNarrowRayClassLFunctionMulPrimeWideIndicator
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateWideInd
open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNarrowRayClassLFunction_mul_prime_wideIndicator : ∀ {F : Type} [Field F] [NumberField F] (𝔪 𝔭 : Ideal (𝓞 F)), 𝔭.IsMaximal → 𝔭 ≠ ⊥ → 𝔭 ⊔ 𝔪 = ⊤ →
    ∀ (C : ClassGroup (𝓞 F)) (Z Z' : ℂ → ℂ), IsRayL 𝔪 (wideInd C) Z → IsRayL 𝔪 (wideInd (C * (cls 𝔭)⁻¹)) Z' →
    IsRayL (𝔪 * 𝔭) (wideInd C) (fun s => Z s - ((Ideal.absNorm 𝔭 : ℕ) : ℂ) ^ (-s) * Z' s) := by
  first | exact @GlobalTheory.isRayL_mul_prime_wideInd | exact GlobalTheory.isRayL_mul_prime_wideInd | (intros; apply GlobalTheory.isRayL_mul_prime_wideInd <;> assumption)
