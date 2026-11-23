import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePointsFixedFrobeniusPower
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_points_fixed_frobenius_power : ∀ (K : Type) [Field K] [Fintype K] (σ : Gal K) (X : Over (Sp K)) (s : Finset (ptOver K (AlgebraicClosure K) ⟶ X)), LocallyOfFiniteType X.hom → ∃ m : ℕ, ∀ x ∈ s, specAut σ ≫ x = specAut (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K) ^ m) ≫ x := by
  first | exact @GlobalTheory.AV.GalPow.exists_frob_pow_on_finset | exact GlobalTheory.AV.GalPow.exists_frob_pow_on_finset | (intros; apply GlobalTheory.AV.GalPow.exists_frob_pow_on_finset; all_goals assumption)
