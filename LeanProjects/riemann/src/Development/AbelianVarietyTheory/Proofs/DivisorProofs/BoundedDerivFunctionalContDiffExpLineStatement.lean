import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedDerivFunctionalContDiffExpLine
import Development.AbelianVarietyTheory.Definitions.Divisors.IsExpLieAlgebraComplexUnits
import GroundTheory.AutomorphicForms.GKModules.Casimir
import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
import GroundTheory.AutomorphicForms.DixmierMalliavin
import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral
open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundedDerivFunctional_contDiff_expLine : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ (S : Submodule ℂ (G → ℂ)), (∀ f ∈ S, Continuous f) → (∀ f ∈ S, ∀ g, (fun y => f (g * y)) ∈ S) → ∀ K : Set G, IsCompact K → ∀ Λ : List (Fin d) → (G → ℂ) → ℂ, SmFn h b μ S K Λ → ∀ l i, ∀ f ∈ S, ContDiff ℝ ∞ (fun t : ℝ => Λ l fun y => f (h.expG (t • b i) * y)) ∧ ∀ (p : ℕ) (s : ℝ), iteratedDeriv p (fun t : ℝ => Λ l fun y => f (h.expG (t • b i) * y)) s = Λ (List.replicate p i ++ l) fun y => f (h.expG (s • b i) * y) := by
  first | exact @GlobalTheory.HCA.smFn_contDiff_line | exact GlobalTheory.HCA.smFn_contDiff_line | (intros; apply GlobalTheory.HCA.smFn_contDiff_line <;> assumption)
