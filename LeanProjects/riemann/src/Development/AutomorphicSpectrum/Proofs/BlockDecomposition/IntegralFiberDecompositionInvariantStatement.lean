import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralFiberDecompositionInvariant
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousConjNilSymm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableNilrad
open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.LocVan
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_fiber_decomposition_invariant : ∀ {H X : Type} [MeasurableSpace H] [MeasurableSpace X] (ν : Measure H) [SFinite ν]
  (act : H → X → X), Measurable (fun p : H × X => act p.1 p.2) →
  ∀ (r : H → H → H), (∀ h₀, MeasurePreserving (r h₀) ν ν) →
  (∀ h₀ h x, act (r h₀ h) x = act h (act h₀ x)) →
  ∀ (D Z : ℕ → Set X), (∀ i, MeasurableSet (D i)) → (∀ i, MeasurableSet (Z i)) →
  (∀ i h x, act h x ∈ Z i ↔ x ∈ Z i) → (∀ x, ∃ i, x ∈ Z i) →
  (∀ i x, ν {h | act h x ∈ D i} ≠ ⊤) → (∀ i x, x ∈ Z i → ν {h | act h x ∈ D i} ≠ 0) →
  ∀ S : Set (X → X), (∀ s ∈ S, ∀ i x, s x ∈ D i ↔ x ∈ D i) → (∀ s ∈ S, ∀ i x, s x ∈ Z i ↔ x ∈ Z i) →
  (∀ s ∈ S, ∀ h, ∃ s' ∈ S, ∀ x, act h (s x) = s' (act h x)) →
  ∃ ρ : X → ℝ≥0∞, Measurable ρ ∧ (∀ x, ∫⁻ h, ρ (act h x) ∂ν = 1) ∧ ∀ s ∈ S, ∀ x, ρ (s x) = ρ x := by
  first | exact @GlobalTheory.CompanionTheory.LocVan.NormaliserAbs.exists_normaliser | exact GlobalTheory.CompanionTheory.LocVan.NormaliserAbs.exists_normaliser | (intros; apply GlobalTheory.CompanionTheory.LocVan.NormaliserAbs.exists_normaliser <;> assumption)
