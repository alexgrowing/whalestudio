import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrouplikeOfMultiplicativeFunctionHopf
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
theorem _root_.GlobalTheory.T.exists_element_of_multiplicative_function_hopf : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (A : Type) [CommRing A] [HopfAlgebra R A] [IsCocomm R A] [Module.Finite R A] [Module.Projective R A] (χ : (A →ₐ[R] K) → K), (∀ x y z : A →ₐ[R] K, toConv z = toConv x * toConv y → χ z = χ x * χ y) → (∀ x, χ x ≠ 0) → ∃ a : A, ∀ x : A →ₐ[R] K, x a = χ x := by
  first | exact @GlobalTheory.HopfPoints.exists_element_eval_eq_character | exact GlobalTheory.HopfPoints.exists_element_eval_eq_character | (intros; apply GlobalTheory.HopfPoints.exists_element_eval_eq_character <;> assumption)
