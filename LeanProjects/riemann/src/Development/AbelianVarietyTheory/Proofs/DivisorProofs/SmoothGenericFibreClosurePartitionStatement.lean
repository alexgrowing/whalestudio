import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothGenericFibreClosurePartition
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.disjoint_closure_and_union_eq_univ_of_genericFibre_partition : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)), Smooth f → ∀ C C' : Set X, C ∪ C' = f ⁻¹' {(⊥ : PrimeSpectrum R)} → Disjoint C (closure C') → Disjoint (closure C) C' → Disjoint (closure C) (closure C') ∧ closure C ∪ closure C' = Set.univ := by
  first | exact @GlobalTheory.smooth_genericFibre_closure_partition | exact GlobalTheory.smooth_genericFibre_closure_partition | (intros; apply GlobalTheory.smooth_genericFibre_closure_partition <;> assumption)
