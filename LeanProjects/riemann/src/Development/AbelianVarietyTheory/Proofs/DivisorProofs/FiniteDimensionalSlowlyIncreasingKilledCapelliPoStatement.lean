import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalSlowlyIncreasingKilledCapelliPo
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkEquivInl
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_slowlyIncreasing_killed_capelliPolynomials : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (b : ℕ), (∀ (L : Subgroup (GL (Fin b) (Af E))), IsOpen (L : Set (GL (Fin b) (Af E))) → ∀ W : Submodule ℂ (Kinf E b → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E b) → ℂ), X.Finite → ∀ N : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E b L W X N))) → ∀ (L : Subgroup (GL (Fin b) (Af E))), IsOpen (L : Set (GL (Fin b) (Af E))) → ∀ W : Submodule ℂ (Kinf E b → ℂ), FiniteDimensional ℂ W → ∀ q : (E →+* ℂ) → ℂ → Polynomial ℂ, (∀ τ u, q τ u ≠ 0) → ∃ V : Submodule ℂ (Sm E b), FiniteDimensional ℂ V ∧ ∀ ψ : Sm E b, (∀ γ g, ψ.1 (ratGL E b γ * g) = ψ.1 g) → (∀ k ∈ L, finRep E b k ψ = ψ) → (∀ g : GA E b, (fun k : Kinf E b => (cptRep E b k ψ).1 g) ∈ W) → (∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖ψ.1 (g * infGL E b y)‖ ≤ C * height y ^ N) → (∀ τ u, Polynomial.aeval (cap τ u) (q τ u) ψ = 0) → ψ ∈ V := by
  first | exact @GlobalTheory.CapKilled.finite_of_finiteness | exact GlobalTheory.CapKilled.finite_of_finiteness | (intros; apply GlobalTheory.CapKilled.finite_of_finiteness <;> assumption)
