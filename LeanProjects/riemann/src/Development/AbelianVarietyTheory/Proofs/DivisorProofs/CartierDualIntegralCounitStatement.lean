import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualIntegralCounit
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartier_dual_integral_counit : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (A : Type) [CommRing A] [HopfAlgebra R A] [IsCocomm R A] [Module.Finite R A] [Module.Projective R A] (f : CartierDual R A →ₐc[R] A) (Λ : CartierDual R A) (y : R), (∀ d : CartierDual R A, d * Λ = algebraMap R _ (Coalgebra.counit (R := R) d) * Λ) → Coalgebra.counit (R := R) Λ = y → algebraMap R K y ^ 2 = (Nat.card (A →ₐ[R] K) : K) → Function.Injective f → Function.Surjective f := by
  first | exact @GlobalTheory.HopfFourier.surjective_of_integral_sq_card | exact GlobalTheory.HopfFourier.surjective_of_integral_sq_card | (intros; apply GlobalTheory.HopfFourier.surjective_of_integral_sq_card <;> assumption)
