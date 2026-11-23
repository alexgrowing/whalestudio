import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPointPrimitiveComponentValuationZer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsion_point_primitive_component_valuation_zero : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ k n : ℕ, 4 ≤ k → n.Prime → IsUnit (n : V) → ∀ (s : Fam D.toPre F k) (α : D.toPre.X), VGe D F v k α (s.s α) 0 → (∀ q : ℚ, 0 < q → ¬ VGe D F v k α (s.s α) q) → ∃ (i : ℕ) (g o : GtPtF D.toPre F), o.IsZero ∧ GtPtF.IsNsmul (n ^ i) g o ∧ ∀ w : Frm D.toPre F k g.b, w.IsGen → GenV hϖ hv w 0 → v (coef s g w α) = 0 := by
  first | exact @GlobalTheory.OneBasis.UnitTerm.exists_torsion_coef_val_zero | exact GlobalTheory.OneBasis.UnitTerm.exists_torsion_coef_val_zero | (intros; apply GlobalTheory.OneBasis.UnitTerm.exists_torsion_coef_val_zero <;> assumption)
