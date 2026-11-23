import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearisationInvariantRigidifiedBundle
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfCubeAbelianSchemeOverArbitraryBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TranslInv

theorem translSnd : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (L : LB (G2 A).left), L.IsLB → (∃ t : (L.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (L.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ h : 𝟙_ (Over S) ⟶ A,
    (∃ t : (L.pull (lift (𝟙 A) (toUnit A ≫ h)).left).Gen, t.IsGen) →
    LBIso L (L.pull (GlobalTheory.UPel.HT.Hecke.transl (lift 1 h : 𝟙_ (Over S) ⟶ G2 A)).left) := by
  intro S A _ _ hA L hL h0 h1 h hh
  have hAA : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have cube := GlobalTheory.CubeTop.cubeTheorem S (G2 A) hAA L hL (G2 A) (lift (1 : G2 A ⟶ A) (snd A A))
    (toUnit _ ≫ lift 1 h) (lift (fst A A) 1)
  have zero_of : ∀ {Y : Scheme.{0}} (ψ : Y ⟶ (G2 A).left), (∃ t : (L.pull ψ).Gen, t.IsGen) →
      GlobalTheory.CechPic.pull ψ (GlobalTheory.CechPic.cls L hL) = 0 := fun ψ hψ =>
    (GlobalTheory.CechPic.cls_pull hL ψ (pull_isLB hL ψ)).symm.trans ((GlobalTheory.CechPic.cls_eq_zero_iff _).2 hψ)
  have e_abc : lift (1 : G2 A ⟶ A) (snd A A) * (toUnit _ ≫ lift 1 h) * lift (fst A A) 1 =
      GlobalTheory.UPel.HT.Hecke.transl (lift 1 h : 𝟙_ (Over S) ⟶ G2 A) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [GlobalTheory.UPel.HT.Hecke.transl, MonObj.mul_comp, MonObj.comp_mul]
  have e_ab : lift (1 : G2 A ⟶ A) (snd A A) * (toUnit _ ≫ lift 1 h) =
      (snd A A * (toUnit _ ≫ h)) ≫ lift (1 : A ⟶ A) (𝟙 A) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.mul_comp, MonObj.comp_mul]
  have e_ac : lift (1 : G2 A ⟶ A) (snd A A) * lift (fst A A) 1 = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.mul_comp, MonObj.comp_mul]
  have e_bc : (toUnit _ ≫ lift 1 h) * lift (fst A A) 1 = fst A A ≫ lift (𝟙 A) (toUnit A ≫ h) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.mul_comp, MonObj.comp_mul]
  have e_a : lift (1 : G2 A ⟶ A) (snd A A) = snd A A ≫ lift (1 : A ⟶ A) (𝟙 A) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have e_b : (toUnit _ ≫ lift 1 h : G2 A ⟶ G2 A) = (toUnit _ ≫ h) ≫ lift (1 : A ⟶ A) (𝟙 A) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have e_c : lift (fst A A) (1 : G2 A ⟶ A) = fst A A ≫ lift (𝟙 A) (1 : A ⟶ A) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have e_1 : (1 : G2 A ⟶ G2 A) = (1 : G2 A ⟶ A) ≫ lift (1 : A ⟶ A) (𝟙 A) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  obtain ⟨t, ht⟩ := cube
  have hz := (GlobalTheory.CechPic.cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 ⟨t, ht⟩
  rw [GlobalTheory.CechPic.cls_linComb hL] at hz
  simp only [Fin.sum_univ_eight, Matrix.cons_val] at hz
  rw [e_abc, e_ab, e_ac, e_bc, e_a, e_b, e_c, e_1] at hz
  simp only [Over.comp_left, Over.id_left, GlobalTheory.CechPic.pull_comp, GlobalTheory.CechPic.pull_id,
    zero_of _ h0, zero_of _ h1, zero_of _ hh, map_zero] at hz
  simp only [one_zsmul, neg_one_zsmul, neg_zero, add_zero, ← sub_eq_add_neg, sub_eq_zero] at hz
  exact (GlobalTheory.CechPic.cls_eq_iff hL (pull_isLB hL _)).1
    ((GlobalTheory.CechPic.cls_pull hL _ (pull_isLB hL _)).trans hz).symm

end GlobalTheory.TranslInv
