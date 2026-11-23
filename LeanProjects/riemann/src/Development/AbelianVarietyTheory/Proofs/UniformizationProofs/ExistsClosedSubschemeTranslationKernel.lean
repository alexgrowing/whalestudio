import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsClosedSubschemeLocallyTrivialProductLineBuStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU.TwistKer

theorem cls_twist_pull {S : Scheme.{0}} (B : Over S) [GrpObj B] {L O : LB B.left} (hL : L.IsLB) (hO : O.IsLB)
    {T : Over S} (x : T ⟶ B) (h : (LB.div (translDiff B L x) (O.pull (snd T B).left)).IsLB)
    (h' : (LB.div (translDiff B L (𝟙 B)) (O.pull (snd B B).left)).IsLB) :
    CechPic.cls _ h = CechPic.pull (x ▷ B).left (CechPic.cls _ h') := by
  have e₁ : (x ▷ B).left ≫ (snd B B).left = (snd T B).left := by
    rw [← Over.comp_left, whiskerRight_snd]
  have e₂ : (x ▷ B).left ≫ (lift (fst B B ≫ 𝟙 B) (snd B B) ≫ μ[B]).left =
      (lift (fst T B ≫ x) (snd T B) ≫ μ[B]).left := by
    rw [← Over.comp_left, ← Category.assoc, comp_lift, Category.comp_id, whiskerRight_snd, whiskerRight_fst]
  have hx : (translDiff B L x).IsLB := LB.isLB_linComb hL _ _
  have h1 : (translDiff B L (𝟙 B)).IsLB := LB.isLB_linComb hL _ _
  rw [CechPic.cls_div hx (pull_isLB hO _), CechPic.cls_div h1 (pull_isLB hO _), map_sub,
    CechPic.cls_pull hO, CechPic.cls_pull hO, ← CechPic.pull_comp, e₁]
  congr 1
  refine (CechPic.cls_linComb hL _ _ hx).trans ?_
  refine Eq.trans ?_ (congrArg (CechPic.pull (x ▷ B).left) (CechPic.cls_linComb hL _ _ h1)).symm
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_zsmul,
    ← CechPic.pull_comp, e₁, e₂]

theorem exists_closed_twist_kernel : GlobalFnsSt → ∀ (R : Type) [CommRing R] (B : Over (Spec (CommRingCat.of R))) [GrpObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ L O : LB B.left, L.IsLB → O.IsLB → ∃ (H : Over (Spec (CommRingCat.of R))) (j : H ⟶ B), IsClosedImmersion j.left ∧ (∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ B), (∀ p : (T).left, ∃ U : (T).left.Opens, p ∈ U ∧ Triv ((LB.div (translDiff B L x) (O.pull (snd (T) B).left)).pull ((fst (T) B).left ⁻¹ᵁ U).ι)) ↔ ∃ y : T ⟶ H, y ≫ j = x) := by
  intro hG R _ B _ hB hP L O hL hO
  have hF : (LB.div (translDiff B L (𝟙 B)) (O.pull (snd B B).left)).IsLB :=
    LB.isLB_div (LB.isLB_linComb hL _ _) (pull_isLB hO _)
  obtain ⟨H, j, hj, h⟩ := GlobalTheory.T.exists_closedSubscheme_locallyTrivial_product_lineBundle hG R B B hB hP _ hF
  refine ⟨H, j, hj, fun T x => Iff.trans ?_ (h T x)⟩
  have hx : (LB.div (translDiff B L x) (O.pull (snd T B).left)).IsLB :=
    LB.isLB_div (LB.isLB_linComb hL _ _) (pull_isLB hO _)
  refine forall_congr' fun p => exists_congr fun U => and_congr Iff.rfl ?_
  refine (CechPic.cls_eq_zero_iff (pull_isLB hx _)).symm.trans
    (Iff.trans ?_ (CechPic.cls_eq_zero_iff (pull_isLB (pull_isLB hF _) _)))
  rw [CechPic.cls_pull hx, CechPic.cls_pull (pull_isLB hF _), CechPic.cls_pull hF, cls_twist_pull B hL hO x hx hF]

end GlobalTheory.UU.TwistKer
end
