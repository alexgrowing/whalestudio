import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOfSqZeroAgreePairs
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FormallyUnramifiedMulN
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comp_eq_of_sqZero_agree_pairs : ∀ (C C₀ : Type) [CommRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = 0 → ∀ (K G : Over (Sp C)) (g g' : K ⟶ G), (∀ (T₀ : Over (Sp C₀)) (y : Over.mk (T₀.hom ≫ spMap π) ⟶ K), y ≫ g = y ≫ g') → ∀ (T : Over (Sp C)) (w w' : T ⟶ K), (∀ (T₀ : Over (Sp C₀)) (j : Over.mk (T₀.hom ≫ spMap π) ⟶ T), j ≫ w = j ≫ w') → w' ≫ g = w' ≫ g' → w ≫ g = w ≫ g' := by
  first | (exact @GlobalTheory.comp_eq_of_sqZero_agree) | (exact GlobalTheory.comp_eq_of_sqZero_agree) | (intros; apply GlobalTheory.comp_eq_of_sqZero_agree  <;> assumption)
