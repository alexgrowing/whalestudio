import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineChartSmoothLiftSqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThickId
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_chart_smooth_lift_sqZero : ∀ (R : Type) [CommRing R] (J : Ideal R), J ^ 2 = ⊥ → ∀ (g : ℕ) (B : Over (Sp R)) (b : B ⟶ Over.mk (spMap (Ideal.Quotient.mk J))), SmoothOfRelativeDimension g b.left → ∀ x : B.left, ∃ (C : Type) (_ : CommRing C) (σ : R →+* C) (j : Over.mk (spMap σ) ⊗ Over.mk (spMap (Ideal.Quotient.mk J)) ⟶ B), SmoothOfRelativeDimension g (spMap σ) ∧ j ≫ b = snd _ _ ∧ IsOpenImmersion j.left ∧ x ∈ Set.range j.left := by
  first | exact @GlobalTheory.LBLift.exists_chart_lift | exact GlobalTheory.LBLift.exists_chart_lift | (intros; apply GlobalTheory.LBLift.exists_chart_lift <;> assumption)
