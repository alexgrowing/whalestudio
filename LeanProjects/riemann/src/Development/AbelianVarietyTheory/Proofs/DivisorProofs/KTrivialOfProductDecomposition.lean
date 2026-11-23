import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitModelToPlaceModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCompOfIsGrpPullback
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory NumberField
open Limits MonoidalCategory CartesianMonoidalCategory GlobalTheory.VB
open scoped ComplexOrder CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam pull)
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)
open MonObj

namespace GlobalTheory.KTrivProduct

theorem lam_add {S : Scheme.{0}} {G T : Over S} [GrpObj G] (c d : Pic G.left) (x y : T ⟶ G) :
    lam (c + d) x y = lam c x y + lam d x y := by
  simp only [lam, map_add]
  abel

theorem memK_comp {T : Scheme.{0}} {C B₁ B₂ : Over T} [GrpObj C] [GrpObj B₁] [GrpObj B₂]
    (q₁ : C ⟶ B₁) (q₂ : C ⟶ B₂) [IsMonHom q₁] [IsMonHom q₂] (i : B₁ ⟶ C) (h₁ : i ≫ q₁ = 𝟙 B₁)
    (h₂ : i ≫ q₂ = 1) {L₁ : LB B₁.left} (hL₁ : L₁.IsLB) (c₂ : Pic B₂.left) {L : LB C.left} (hL : L.IsLB)
    (e : cls L hL = pull q₁.left (cls L₁ hL₁) + pull q₂.left c₂) {U : Over T} (x : U ⟶ C)
    (hx : IndefiniteRowSideFullHecke.PolarizedAbelianVarieties.MemK C L x) : IndefiniteRowSideFullHecke.PolarizedAbelianVarieties.MemK B₁ L₁ (x ≫ q₁) := by
  rw [PolCompare.memK_iff_cls C hL, e, lam_add, CechPic.lam_pull, CechPic.lam_pull] at hx
  rw [PolCompare.memK_iff_cls B₁ hL₁]
  have H := congrArg (pull (lift (fst U B₁) (snd U B₁ ≫ i) : U ⊗ B₁ ⟶ U ⊗ C).left) hx
  rw [map_add, CechPic.pull_lam, CechPic.pull_lam, map_zero] at H
  simp only [Category.assoc, lift_fst_assoc, lift_snd_assoc, h₁, h₂, Category.comp_id, MonObj.comp_one,
    CechPic.lam_one_right, add_zero] at H
  exact H

theorem kTriv_prod {T : Scheme.{0}} {C B₁ B₂ : Over T} [GrpObj C] [GrpObj B₁] [GrpObj B₂]
    (q₁ : C ⟶ B₁) (q₂ : C ⟶ B₂) [IsMonHom q₁] [IsMonHom q₂] (hq : IsLimit (BinaryFan.mk q₁ q₂))
    {L₁ : LB B₁.left} (hL₁ : L₁.IsLB) (k₁ : Out.KTriv B₁ L₁) {L₂ : LB B₂.left} (hL₂ : L₂.IsLB)
    (k₂ : Out.KTriv B₂ L₂) {L : LB C.left} (hL : L.IsLB)
    (e : cls L hL = pull q₁.left (cls L₁ hL₁) + pull q₂.left (cls L₂ hL₂)) : Out.KTriv C L := by
  rw [PolCompare.kTriv_iff _ hL₁] at k₁
  rw [PolCompare.kTriv_iff _ hL₂] at k₂
  rw [PolCompare.kTriv_iff _ hL]
  intro U x hx
  obtain ⟨i₁, a₁, b₁⟩ := BinaryFan.IsLimit.lift' hq (𝟙 B₁) (1 : B₁ ⟶ B₂)
  obtain ⟨i₂, a₂, b₂⟩ := BinaryFan.IsLimit.lift' hq (1 : B₂ ⟶ B₁) (𝟙 B₂)
  have x₁ : x ≫ q₁ = 1 := k₁ U _ (memK_comp q₁ q₂ i₁ a₁ b₁ hL₁ _ hL e x hx)
  have x₂ : x ≫ q₂ = 1 := k₂ U _ (memK_comp q₂ q₁ i₂ b₂ a₂ hL₂ _ hL (e.trans (add_comm _ _)) x hx)
  show x = 1
  exact BinaryFan.IsLimit.hom_ext hq (x₁.trans (MonObj.one_comp q₁).symm) (x₂.trans (MonObj.one_comp q₂).symm)

end GlobalTheory.KTrivProduct
