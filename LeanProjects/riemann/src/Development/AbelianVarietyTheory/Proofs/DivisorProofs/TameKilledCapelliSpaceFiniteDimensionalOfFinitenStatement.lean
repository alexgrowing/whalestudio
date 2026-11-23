import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameKilledCapelliSpaceFiniteDimensionalOfFiniten
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKilled
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalOfCommutingFiniteAlgebraJointEi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CenterActsByScalarOnEigenforms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainMeasureFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalCentreAnnihilatorCompatibleMaps
open NumberField GlobalTheory.CuspRep GlobalTheory.AutGrowth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameKilledCapelliSpace_finiteDimensional_of_finiteness : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (b : ℕ), (∀ (L : Subgroup (GL (Fin b) (Af E))), IsOpen (L : Set (GL (Fin b) (Af E))) → ∀ W : Submodule ℂ (Kinf E b → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E b) → ℂ), X.Finite → ∀ N : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E b L W X N))) → (∀ (τ : E →+* ℂ) (u : ℂ), ∃ w : Fin (b + 1) → ℂ, cap (a := b) τ u = ∑ j : Fin (b + 1), w j • cap (a := b) τ ((j : ℕ) : ℂ)) → ∀ (L : Subgroup (GL (Fin b) (Af E))), IsOpen (L : Set (GL (Fin b) (Af E))) → ∀ W : Submodule ℂ (Kinf E b → ℂ), FiniteDimensional ℂ W → ∀ q : (E →+* ℂ) → ℂ → Polynomial ℂ, (∀ τ u, q τ u ≠ 0) → (∀ z ∈ Zalg E b, ∀ ψ ∈ GlobalTheory.CapKilled.space E b L W q, z ψ ∈ GlobalTheory.CapKilled.space E b L W q) → FiniteDimensional ℂ (GlobalTheory.CapKilled.space E b L W q) := by
  first | exact @GlobalTheory.CapKilled.finiteDimensional_space | exact GlobalTheory.CapKilled.finiteDimensional_space | (intros; apply GlobalTheory.CapKilled.finiteDimensional_space <;> assumption)
