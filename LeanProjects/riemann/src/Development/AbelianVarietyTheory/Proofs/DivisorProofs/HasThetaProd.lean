import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProd
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitModelToPlaceModel
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory NumberField
open Limits MonoidalCategory CartesianMonoidalCategory GlobalTheory.VB
open scoped ComplexOrder

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PPAS
open CechPic

theorem lam_add_class {S : Scheme.{0}} {G T : Over S} [GrpObj G] (a b : Pic G.left) (x y : T ⟶ G) :
    lam (a + b) x y = lam a x y + lam b x y := by
  simp only [lam, map_add]; abel

theorem pull_inv_pull {S : Scheme.{0}} {G Q : Over S} [GrpObj G] [GrpObj Q] (π : G ⟶ Q) [IsMonHom π]
    (c : Pic Q.left) :
    pull (GrpObj.inv : G ⟶ G).left (pull π.left c) = pull π.left (pull (GrpObj.inv : Q ⟶ Q).left c) := by
  rw [← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, GrpObj.inv_hom]

theorem hasTheta_of_isProd {S : Scheme.{0}} {P P₁ P₂ : PPAS S} (h : P.IsProd P₁ P₂) (h₁ : P₁.HasTheta)
    (h₂ : P₂.HasTheta) : P.HasTheta := by
  obtain ⟨π₁, π₂, m₁, m₂, -, -, hc⟩ := h
  obtain ⟨L₁, hL₁, s₁, e₁⟩ := h₁
  obtain ⟨L₂, hL₂, s₂, e₂⟩ := h₂
  obtain ⟨L, hL, hcls⟩ := cls_surj (pull π₁.left (cls L₁ hL₁) + pull π₂.left (cls L₂ hL₂))
  refine ⟨L, hL, ?_, ?_⟩
  · refine PolCompare.sym_of_isSymmetric (A := P.A) hL ((PolCompare.isSymmetric_iff_cls (A := P.A) hL).2 ?_)
    have k₁ := (PolCompare.isSymmetric_iff_cls (A := P₁.A) hL₁).1
      ((PolCompare.sym_iff (A := P₁.A) P₁.isAb hL₁).1 s₁)
    have k₂ := (PolCompare.isSymmetric_iff_cls (A := P₂.A) hL₂).1
      ((PolCompare.sym_iff (A := P₂.A) P₂.isAb hL₂).1 s₂)
    rw [hcls, map_add, pull_inv_pull π₁, pull_inv_pull π₂, sub_eq_zero.1 k₁, sub_eq_zero.1 k₂, sub_self]
  · rw [hc, e₁, e₂, hcls, pull_lam, pull_lam, tensorHom_fst, tensorHom_snd, tensorHom_fst, tensorHom_snd,
      ← lam_pull, ← lam_pull, lam_add_class]

theorem hasTheta_prod : ∀ (S : Scheme.{0}) (P P₁ P₂ : PPAS S), P.IsProd P₁ P₂ → P₁.HasTheta → P₂.HasTheta →
    P.HasTheta := fun _ _ _ _ h h₁ h₂ => hasTheta_of_isProd h h₁ h₂

end GlobalTheory.PPAS
