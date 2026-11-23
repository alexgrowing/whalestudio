import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryOfUniformLimitCoboundaries
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coboundary_of_uniform_limit_coboundaries : ∀ {𝕜 : Type} [NormedField 𝕜] {Γ : Type} (H : Set Γ) (k f : Γ → 𝕜), (∃ s ∈ H, k s ≠ 1) → (∀ ε : ℝ, 0 < ε → ∃ X : 𝕜, ∀ s ∈ H, ‖f s - (k s * X - X)‖ ≤ ε) → ∃ X : 𝕜, ∀ s ∈ H, f s = k s * X - X := by
  first | exact @GlobalTheory.coboundary_closed_of_uniform_approx | exact GlobalTheory.coboundary_closed_of_uniform_approx | (intros; apply GlobalTheory.coboundary_closed_of_uniform_approx <;> assumption)
