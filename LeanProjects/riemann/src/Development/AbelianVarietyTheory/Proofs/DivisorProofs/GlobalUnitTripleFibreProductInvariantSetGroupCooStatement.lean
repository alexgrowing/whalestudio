import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalUnitTripleFibreProductInvariantSetGroupCoo
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZbLeftWhiskerRight
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open GlobalTheory.LBDescent GlobalTheory.DescNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalUnit_tripleFibreProduct_invariant_setGroupCoordZero : ∀ (K : Type) [Field K] (A A' B : Over (Sp K)) [GrpObj B] (q : A ⟶ A'), IsAbelianScheme B → ∀ (D : Γ(Triple (q ▷ B).left, ⊤)ˣ) (w : Triple (q ▷ B).left), gm (rhoW q) w ⊤ D = gm (𝟙 _) w ⊤ D := by
  first | exact @GlobalTheory.DescNorm.RigidW.gm_rhoW_eq_gm_id_of_abelian | exact GlobalTheory.DescNorm.RigidW.gm_rhoW_eq_gm_id_of_abelian | (intros; apply GlobalTheory.DescNorm.RigidW.gm_rhoW_eq_gm_id_of_abelian <;> assumption)
