import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymTranslate
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.ThetaAlgClosed

theorem hasTheta_of_isAlgClosed : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (P : PPAS (Sp Ω)), P.HasTheta := by
  intro Ω _ _ P
  have h := isGrpPullback_pullback P.A (𝟙 (Sp Ω))
  obtain ⟨L, hL, ha, hk, hc⟩ := P.isPol.2.2 Ω (𝟙 _)
  have hB : IsAbelianScheme ((Over.pullback (𝟙 (Sp Ω))).obj P.A) :=
    PolPull.isAbelianScheme_of_isGrpPullback P.isAb h
  obtain ⟨L', hL', -, hs, -, -, hl⟩ := RiemannExists.exists_sym_translate Ω _ hB L hL ha hk
  have hA : IsGrpPullback P.A P.A (𝟙 (Sp Ω)) (𝟙 P.A.left) := by
    haveI : IsMonHom (Iso.refl P.A).hom := by dsimp; infer_instance
    exact isGrpPullback_of_iso (Iso.refl P.A)
  obtain ⟨e, he, hφ⟩ := grpPullback_iso hA h
  have h₁ := isGrpPullback_of_iso e
  have hM := pull_isLB hL' e.hom.left
  refine ⟨_, hM, PolBaseChange.sym_pull h₁ hs, ?_⟩
  have hcomp : sqMap h₁.1.w ≫ IndefiniteRowSideFullHecke.ZeroSectionBase.sqToBase P.A (𝟙 (Sp Ω)) = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, PPAS.sqToBase_fst]
      show pullback.lift _ _ _ ≫ pullback.fst _ _ ≫ pullback.fst P.A.hom (𝟙 (Sp Ω)) = _
      rw [pullback.lift_fst_assoc, Category.assoc, hφ, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, PPAS.sqToBase_snd]
      show pullback.lift _ _ _ ≫ pullback.snd _ _ ≫ pullback.fst P.A.hom (𝟙 (Sp Ω)) = _
      rw [pullback.lift_snd_assoc, Category.assoc, hφ, Category.comp_id, Category.id_comp]
  rw [CechPic.cls_pull hL', ← PPAS.pull_sqMap_lam h₁, hl, ← hc, ← CechPic.pull_comp, hcomp, CechPic.pull_id]

end GlobalTheory.ThetaAlgClosed
