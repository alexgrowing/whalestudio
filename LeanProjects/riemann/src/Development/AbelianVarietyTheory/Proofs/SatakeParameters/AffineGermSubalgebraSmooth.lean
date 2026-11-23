import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GermImageSmooth
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XMemOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_germ_subalgebra_smooth : ∀ (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [Smooth p] [inst : Algebra ℂ Z.functionField], inst = ffAlg p → ∀ (U : Z.Opens), IsAffineOpen U → ∀ (h : genericPoint Z ∈ U) (B : Subalgebra ℂ Z.functionField), (∀ y, y ∈ B ↔ ∃ f : Γ(Z, U), (Z.presheaf.germ U (genericPoint Z) h).hom f = y) → Algebra.Smooth ℂ B := by
  first | (exact @GlobalTheory.germImage_smooth) | (exact GlobalTheory.germImage_smooth) | (intros; apply GlobalTheory.germImage_smooth  <;> assumption)
