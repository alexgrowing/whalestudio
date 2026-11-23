import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquares
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenOfRigidifiedFaithfullyFlatDescent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GaloisLBDescent

theorem lbIso_of_galoisCover : ∀ (S S₁ Y : Scheme.{0}) (π₁ : S₁ ⟶ S) (Ga : Type) [Group Ga] (ρ₁ : Ga → (S₁ ⟶ S₁)) (f : S ⟶ Y) (A' : Over S₁) (A : Over S) (B : Over Y) [GrpObj A'] [GrpObj A] [IsCommMonObj A] [GrpObj B] (φ₁ : A'.left ⟶ A.left) (φ : A.left ⟶ B.left) (PA : RigLB A) (PB : RigLB B) (L' : LB A'.left), IsAbelianScheme A → GlobalTheory.ZM.IsGaloisCover Ga ρ₁ π₁ → IsGrpPullback A' A π₁ φ₁ → IsGrpPullback A B f φ → L'.IsLB → LBIso L' (PA.L.pull φ₁) → LBIso L' (PB.L.pull (φ₁ ≫ φ)) → LBIso PA.L (PB.L.pull φ) := by
  intro S S₁ Y π₁ Ga _ ρ₁ f A' A B _ _ _ _ φ₁ φ PA PB L' hA hG h₁ h hL' i₁ i₂
  have := hG.fin
  have := hG.etale
  have := hG.onto
  have hPA := PA.isLB
  have h₂ := pull_isLB PB.isLB φ
  have hN := LB.isLB_div h₂ hPA
  have cN : CechPic.cls _ hN = CechPic.pull φ (CechPic.cls _ PB.isLB) - CechPic.cls _ hPA :=
    CechPic.cls_div h₂ hPA hN
  have zA : CechPic.pull (eSec A) (CechPic.cls _ PA.isLB) = 0 :=
    (CechPic.cls_eq_zero_iff (pull_isLB PA.isLB _)).2 ⟨_, PA.rigGen⟩
  have zB : CechPic.pull (eSec B) (CechPic.cls _ PB.isLB) = 0 :=
    (CechPic.cls_eq_zero_iff (pull_isLB PB.isLB _)).2 ⟨_, PB.rigGen⟩
  have c₁ : CechPic.cls _ hL' = CechPic.pull φ₁ (CechPic.cls _ PA.isLB) :=
    (CechPic.cls_eq_iff hL' (pull_isLB PA.isLB _)).2 i₁
  have c₂ : CechPic.cls _ hL' = CechPic.pull (φ₁ ≫ φ) (CechPic.cls _ PB.isLB) :=
    (CechPic.cls_eq_iff hL' (pull_isLB PB.isLB _)).2 i₂
  refine GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange GlobalTheory.SemiRigid.globalFns S S₁ π₁ A _ hA hN
    inferInstance inferInstance inferInstance ((CechPic.cls_eq_zero_iff (pull_isLB hN _)).1 ?_)
    ((CechPic.cls_eq_zero_iff (pull_isLB hN _)).1 ?_)
  · have he : eSec A ≫ φ = f ≫ eSec B := GlobalTheory.PolBaseChange.eSec_comm h
    rw [CechPic.cls_pull hN, cN, map_sub, ← CechPic.pull_comp, zA, he, CechPic.pull_comp, zB, map_zero,
      sub_zero]
  · rw [CechPic.cls_pull hN, cN, ← h₁.1.isoPullback_inv_fst, CechPic.pull_comp, map_sub,
      ← CechPic.pull_comp φ₁ φ, ← c₁, ← c₂, sub_self, map_zero]

end GlobalTheory.GaloisLBDescent
