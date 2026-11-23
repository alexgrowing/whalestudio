import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaProductOrthogonalSum
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProd
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory NumberField
open Limits MonoidalCategory CartesianMonoidalCategory GlobalTheory.VB
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_product_orthogonal_sum : ∀ (g g₁ g₂ : ℕ), g = g₁ + g₂ → ∀ (H : Matrix (Fin g) (Fin g) ℂ) (H₁ : Matrix (Fin g₁) (Fin g₁) ℂ) (H₂ : Matrix (Fin g₂) (Fin g₂) ℂ) (M₁ : Matrix (Fin g₁) (Fin g) ℂ) (M₂ : Matrix (Fin g₂) (Fin g) ℂ), H.PosDef → H₁.PosDef → H₂.PosDef → (∀ z w, HermFrame.form H z w = HermFrame.form H₁ (M₁.mulVec z) (M₁.mulVec w) + HermFrame.form H₂ (M₂.mulVec z) (M₂.mulVec w)) → ∀ (t : ℝ), 0 < t → ∀ (a a' : Fin g₁ → ℂ) (b b' : Fin g₂ → ℂ), HermFrame.form (HermFrame.dualGram ((t : ℂ) • H)) (M₁.transpose.mulVec a + M₂.transpose.mulVec b) (M₁.transpose.mulVec a' + M₂.transpose.mulVec b') = HermFrame.form (HermFrame.dualGram ((t : ℂ) • H₁)) a a' + HermFrame.form (HermFrame.dualGram ((t : ℂ) • H₂)) b b' := by
  first | exact @GlobalTheory.DualOrthSum.form_dualGram_orthSum | exact GlobalTheory.DualOrthSum.form_dualGram_orthSum | (intros; apply GlobalTheory.DualOrthSum.form_dualGram_orthSum <;> assumption)
