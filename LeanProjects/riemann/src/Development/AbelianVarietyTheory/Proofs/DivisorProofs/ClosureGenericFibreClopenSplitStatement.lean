import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureGenericFibreClopenSplit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closure_generic_fibre_clopen_split_alt : ∀ (R A : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing A] [Algebra R A], Algebra.Smooth R A → ∀ C C' : Set (PrimeSpectrum A), C ∪ C' = {r | r.asIdeal.comap (algebraMap R A) = ⊥} → Disjoint C (closure C') → Disjoint (closure C) C' → Disjoint (closure C) (closure C') ∧ closure C ∪ closure C' = Set.univ := by
  first | exact @GlobalTheory.closure_generic_fibre_clopen_split | exact GlobalTheory.closure_generic_fibre_clopen_split | (intros; apply GlobalTheory.closure_generic_fibre_clopen_split <;> assumption)
