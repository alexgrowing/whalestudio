import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothKFiniteCenter
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_K_finite_center : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (φ : Sm E a), (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) → (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)) → FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a)) → MemL2Quotient (latticeGL E a) μ φ.1 → ∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ.1 (g * infGL E a y)‖ ≤ C * height y ^ N := by
  first | exact @GlobalTheory.CompanionTheory.Growth.moderate_growth | exact GlobalTheory.CompanionTheory.Growth.moderate_growth | (intros; apply GlobalTheory.CompanionTheory.Growth.moderate_growth <;> assumption)
