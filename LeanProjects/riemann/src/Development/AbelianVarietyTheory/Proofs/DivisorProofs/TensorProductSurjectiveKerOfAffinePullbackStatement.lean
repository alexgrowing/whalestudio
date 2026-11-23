import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorProductSurjectiveKerOfAffinePullback
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorProduct_surjective_ker_of_affine_pullback : ∀ {R O R' Q : Type} [CommRing R] [CommRing O] [CommRing R'] [CommRing Q] [Algebra R O] [Algebra R R'] [Algebra R Q] (I : Ideal R') (a : O →ₐ[R] Q) (b : R' ⧸ I →ₐ[R] Q), IsPullback (spMap (a : O →+* Q)) (spMap (b : R' ⧸ I →+* Q)) (spMap (algebraMap R O)) (spMap (algebraMap R (R' ⧸ I))) → Function.Surjective (Algebra.TensorProduct.lift a (b.comp (Ideal.Quotient.mkₐ R I)) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift a (b.comp (Ideal.Quotient.mkₐ R I)) fun _ _ => Commute.all _ _) = I.map (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R O R') := by
  first | exact @GlobalTheory.Mum.tensor_of_pullback_surj_ker | exact GlobalTheory.Mum.tensor_of_pullback_surj_ker | (intros; apply GlobalTheory.Mum.tensor_of_pullback_surj_ker <;> assumption)
