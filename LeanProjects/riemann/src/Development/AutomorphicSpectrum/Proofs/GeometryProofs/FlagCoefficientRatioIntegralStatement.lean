import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagCoefficientRatioIntegral
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
open GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_coefficient_ratio_integral : ∀ (Ω : Type) [Field Ω] (Li : Type) [AddCommGroup Li] [Module Ω Li] (W : Subring Ω) (r : ℕ) (b₀ b b' : Fin r → Li) (N : Ω) (k : Fin r) (t t' : Ω), LinearIndependent Ω b → (∀ j, flagStep Ω b j = flagStep Ω b₀ j) → (∀ j, flagStep Ω b' j = flagStep Ω b₀ j) → (∀ j, N • b' j ∈ Submodule.span W (Set.range b)) → b k - t • b₀ k ∈ flagStep Ω b₀ k → b' k - t' • b₀ k ∈ flagStep Ω b₀ k → N * (t' / t) ∈ W := by
  first | exact @GlobalTheory.CompanionTheory.Ar.leadCoef_ratio_mem | exact GlobalTheory.CompanionTheory.Ar.leadCoef_ratio_mem | (intros; apply GlobalTheory.CompanionTheory.Ar.leadCoef_ratio_mem <;> assumption)
