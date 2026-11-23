import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeSpanIntersectionBasis
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigCoordApply
open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_span_intersection_basis : ∀ (V C : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [Algebra V C] [IsFractionRing V C] (W : Type) [AddCommGroup W] [Module C W] [Module V W] [IsScalarTower V C W] [FiniteDimensional C W] (Lie : Submodule V W) (n : ℕ) (w : Fin n → W), Lie.FG → Submodule.span C (Lie : Set W) = ⊤ → LinearIndependent C w → (∀ y, y ∈ Submodule.span V (Set.range w) ↔ y ∈ Lie ∧ y ∈ Submodule.span C (Set.range w)) → ∀ j, ∃ φ : Module.Dual C W, (∀ y ∈ Lie, φ y ∈ (algebraMap V C).range) ∧ ∀ k, φ (w k) = if k = j then 1 else 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_dual_integral_of_saturated_free_part | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_dual_integral_of_saturated_free_part | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_dual_integral_of_saturated_free_part <;> assumption)
