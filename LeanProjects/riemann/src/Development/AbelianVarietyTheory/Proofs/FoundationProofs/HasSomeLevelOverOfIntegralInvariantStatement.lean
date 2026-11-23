import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSomeLevelOverOfIntegralInvariant
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSomeLevelOver_of_integral_invariant : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (M n : ℕ) (h : ℍ → ℂ) (r : Fin n → ℍ → ℂ), 0 < M → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h → (∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, h (γ • τ) = h τ) → (∀ j, InR ε.range (r j)) → (∀ τ, h τ ^ n + ∑ j, r j τ * h τ ^ (j : ℕ) = 0) → InR ε.range h := by
  first | exact @GlobalTheory.FN.inR_of_integral | exact GlobalTheory.FN.inR_of_integral | (intros; apply GlobalTheory.FN.inR_of_integral <;> assumption)
