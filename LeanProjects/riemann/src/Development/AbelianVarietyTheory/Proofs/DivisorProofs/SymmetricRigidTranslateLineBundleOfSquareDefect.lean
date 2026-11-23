import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRigidTranslatePrincipalPolarisationOrderTw
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RigidifiedSymDescendToSubring
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionPointsDivisible
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsGenThetaOfIsAbelianScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolarisationFormIntPolynomialBundles
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelFamilyTangentDimensionBound
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open MonoidalCategory CartesianMonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam)

noncomputable section

namespace GlobalTheory.SymTranslate

theorem sym_rigTransl_of_sq : ∀ (K : Type) [Field K] (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (L : LB B.left) (hL : L.IsLB), (∃ t : LB.Gen (Theta B L), t.IsGen) → ∀ a : 𝟙_ (Over (Sp K)) ⟶ B, CechPic.pull (GrpObj.inv : B ⟶ B).left (cls L hL) - cls L hL = lam (cls L hL) (toUnit B ≫ a ^ 2) (𝟙 B) → Out.Sym B (GlobalTheory.RigidTranslate.rigTransl L a) := by
  intro K _ B _ _ L hL _ a h
  have hc : ∀ x : 𝟙_ (Over (Sp K)) ⟶ B, CechPic.pull (toUnit B ≫ x).left (cls L hL) = 0 := fun x => by
    rw [Over.comp_left, CechPic.pull_comp,
      GlobalTheory.PrimitiveOverField.pic_field (CechPic.pull x.left (cls L hL))]
    exact map_zero _
  have h1 : CechPic.pull (1 : B ⟶ B).left (cls L hL) = 0 := hc _
  have h2 : CechPic.pull (GrpObj.inv : B ⟶ B).left (cls L hL) =
      CechPic.pull ((toUnit B ≫ a ^ 2) * 𝟙 B).left (cls L hL) := by
    rw [lam, hc, h1, Over.id_left, CechPic.pull_id, sub_zero, add_zero] at h
    exact sub_left_injective h
  have h3 := congrArg (CechPic.pull (𝟙 B * (toUnit B ≫ a)⁻¹).left) h2
  rw [← CechPic.pull_comp, ← CechPic.pull_comp, ← Over.comp_left, ← Over.comp_left] at h3
  have e1 : (𝟙 B * (toUnit B ≫ a)⁻¹) ≫ (GrpObj.inv : B ⟶ B) =
      (GrpObj.inv : B ⟶ B) ≫ (𝟙 B * (toUnit B ≫ a)) := by
    rw [← Hom.inv_def, MonObj.comp_mul, ← Category.assoc, comp_toUnit, Category.comp_id, mul_inv, inv_inv,
      Hom.inv_def, Category.id_comp]
  have e2 : (𝟙 B * (toUnit B ≫ a)⁻¹) ≫ ((toUnit B ≫ a ^ 2) * 𝟙 B) = 𝟙 B * (toUnit B ≫ a) := by
    rw [MonObj.comp_mul, ← Category.assoc, comp_toUnit, Category.comp_id, MonObj.comp_pow, sq,
      _root_.mul_comm (𝟙 B), _root_.mul_comm (𝟙 B), _root_.mul_assoc, mul_inv_cancel_left]
  rw [e1, e2, Over.comp_left, CechPic.pull_comp] at h3
  have hL' : (GlobalTheory.RigidTranslate.rigTransl L a).IsLB := LB.isLB_linComb hL _ _
  have h4 : cls _ hL' = CechPic.pull (𝟙 B * (toUnit B ≫ a)).left (cls L hL) := by
    rw [CechPic.cls_linComb hL, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hc, smul_zero, add_zero, one_smul]
    rfl
  exact GlobalTheory.RigSymSubring.sym_of_cls hL' (by rw [h4]; exact h3)

end GlobalTheory.SymTranslate
