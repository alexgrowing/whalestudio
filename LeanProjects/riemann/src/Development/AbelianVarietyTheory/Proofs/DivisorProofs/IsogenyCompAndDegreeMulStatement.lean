import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyCompAndDegreeMul
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isogeny_comp_and_degree_mul : ∀ (K : Type) [Field K] (A B C : AbVar K) (f : A ⟶ B) (g : B ⟶ C), IsIsogeny f → IsIsogeny g → IsIsogeny (f ≫ g) ∧ deg (f ≫ g) = deg f * deg g := by
  first | exact @GlobalTheory.AV.AbVar.isIsogeny_comp_and_deg_comp | exact GlobalTheory.AV.AbVar.isIsogeny_comp_and_deg_comp | (intros; apply GlobalTheory.AV.AbVar.isIsogeny_comp_and_deg_comp <;> assumption)
