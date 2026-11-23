import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianGenericPullback
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_generic_pullback : ∀ (O : Type) [CommRing O] (c : O →+* O) (C C' : Scheme.{0}) [IsIntegral C] [IsIntegral C'] (π : C' ⟶ C), π (genericPoint C') = genericPoint C → ∀ (G : Over C) [GrpObj G] (i : OAct O G) (G' : Over C') [GrpObj G'] (i' : OAct O G') (φ : G'.left ⟶ G.left), IsActPull i' i π φ → AbGen c i → AbGen c i' := by
  first | exact @GlobalTheory.CurveRootGeometry.abGen_of_isActPull | exact GlobalTheory.CurveRootGeometry.abGen_of_isActPull | (intros; apply GlobalTheory.CurveRootGeometry.abGen_of_isActPull <;> assumption)
