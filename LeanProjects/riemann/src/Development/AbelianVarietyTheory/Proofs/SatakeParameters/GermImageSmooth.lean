import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XMemOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothSectionsInFunctionField
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover

namespace GlobalTheory

theorem germImage_smooth : ∀ (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [Smooth p] [inst : Algebra ℂ Z.functionField], inst = ffAlg p → ∀ (U : Z.Opens), IsAffineOpen U → ∀ (h : genericPoint Z ∈ U) (B : Subalgebra ℂ Z.functionField), (∀ y, y ∈ B ↔ ∃ f : Γ(Z, U), (Z.presheaf.germ U (genericPoint Z) h).hom f = y) → Algebra.Smooth ℂ B := by
  intro Z _ p hp inst hinst U hU h B hB
  exact smooth_sections_in_functionField Z p hp hinst U hU h B hB

end GlobalTheory
