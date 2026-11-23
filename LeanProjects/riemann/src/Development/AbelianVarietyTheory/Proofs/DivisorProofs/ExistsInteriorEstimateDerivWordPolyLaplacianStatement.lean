import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInteriorEstimateDerivWordPolyLaplacian
import GroundTheory.AutomorphicForms.GKModules.Casimir
import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
import GroundTheory.AutomorphicForms.DixmierMalliavin
import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_interior_estimate_deriv_word_polyLaplacian : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (P : Polynomial ℂ), P.Monic → ∃ Kc : Set G, IsCompact Kc ∧ ∀ l : List 𝔤, ∃ C : ℝ, 0 ≤ C ∧ ∀ f : h.smoothFuns (F := ℂ), Polynomial.aeval (∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) P f = 0 → ∀ (g : G) (M : ℝ), (∀ y ∈ Kc, ‖(f : G → ℂ) (g * y)‖ ≤ M) → ‖l.foldr h.rightDeriv (f : G → ℂ) g‖ ≤ C * M := by
  first | exact @GlobalTheory.interior_word_bound | exact GlobalTheory.interior_word_bound | (intros; apply GlobalTheory.interior_word_bound <;> assumption)
