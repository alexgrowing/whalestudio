import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralUniformNearParameter
import Mathlib
open MeasureTheory
open scoped ENNReal NNReal Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_uniform_near_parameter : ∀ (X P : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace P] [FirstCountableTopology P] (N : ℕ) (e : X ≃+ (Fin N → ℝ)), Continuous e → ∀ (c : P) (m0 : Measure X) (A : P → X →+ X), (∀ s, Continuous (A s)) → (∀ x, Filter.Tendsto (fun s => A s x) (nhds c) (nhds (A c x))) → ∀ δ : ℝ, 0 < δ → (∀ᶠ s in nhds c, ∀ x, δ * ‖e x‖ ≤ ‖e (A s x)‖) → ∫⁻ x, ENNReal.ofReal ((1 + ‖e x‖) ^ (-((N + 1 : ℕ) : ℝ))) ∂m0 ≠ ⊤ → ∀ (u : (Fin N → ℝ) → ℂ) (C : ℝ), Continuous u → (∀ y, ‖u y‖ ≤ C * (1 + ‖y‖) ^ (-((N + 1 : ℕ) : ℝ))) → (∀ᶠ s in nhds c, Integrable (fun x => u (e (A s x))) m0) ∧ ContinuousAt (fun s => ∫ x, u (e (A s x)) ∂m0) c := by
  first | exact @GlobalTheory.CompanionTheory.FibSch.integral_comp_additive_continuousAt | exact GlobalTheory.CompanionTheory.FibSch.integral_comp_additive_continuousAt | (intros; apply GlobalTheory.CompanionTheory.FibSch.integral_comp_additive_continuousAt <;> assumption)
