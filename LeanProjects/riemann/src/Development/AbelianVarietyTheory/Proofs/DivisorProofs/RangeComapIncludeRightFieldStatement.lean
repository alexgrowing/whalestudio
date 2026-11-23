import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeComapIncludeRightField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.range_comap_includeRight_eq_comap_eq_ker : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (k : Type) [Field k] [Algebra A k], Set.range (PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] k ⊗[A] B).toRingHom) = {r : PrimeSpectrum B | r.asIdeal.comap (algebraMap A B) = RingHom.ker (algebraMap A k)} := by
  first | exact @GlobalTheory.range_comap_includeRight_field | exact GlobalTheory.range_comap_includeRight_field | (intros; apply GlobalTheory.range_comap_includeRight_field <;> assumption)
