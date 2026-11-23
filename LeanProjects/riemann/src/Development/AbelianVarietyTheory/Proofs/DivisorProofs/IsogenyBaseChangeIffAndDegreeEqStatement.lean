import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyBaseChangeIffAndDegreeEq
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isogeny_baseChange_iff_and_degree_eq : ∀ (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] (A B : AbVar K) (f : A ⟶ B), (IsIsogeny (bcMap L f) ↔ IsIsogeny f) ∧ deg (bcMap L f) = deg f := by
  first | exact @GlobalTheory.AV.AbVar.isIsogeny_bcMap_iff_and_deg_bcMap | exact GlobalTheory.AV.AbVar.isIsogeny_bcMap_iff_and_deg_bcMap | (intros; apply GlobalTheory.AV.AbVar.isIsogeny_bcMap_iff_and_deg_bcMap <;> assumption)
