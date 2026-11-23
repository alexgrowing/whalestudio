import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitModelToPlaceModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCompOfIsGrpPullback

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory NumberField
open Limits MonoidalCategory CartesianMonoidalCategory GlobalTheory.VB
open scoped ComplexOrder CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam pull)
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)
open MonObj

namespace GlobalTheory.ProdAmple

theorem isPullback_of_isLimit_binaryFan {T : Scheme.{0}} {C B₁ B₂ : Over T} (q₁ : C ⟶ B₁) (q₂ : C ⟶ B₂)
    (hq : IsLimit (BinaryFan.mk q₁ q₂)) : IsPullback q₁.left q₂.left B₁.hom B₂.hom := by
  refine ⟨⟨by rw [Over.w, Over.w]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s ↦ (BinaryFan.IsLimit.lift' hq (W := Over.mk (s.fst ≫ B₁.hom)) (Over.homMk s.fst rfl)
      (Over.homMk s.snd s.condition.symm)).1.left) (fun s ↦ ?_) (fun s ↦ ?_) (fun s m h₁ h₂ ↦ ?_)⟩⟩
  · exact congrArg (·.left) (BinaryFan.IsLimit.lift' hq (W := Over.mk (s.fst ≫ B₁.hom)) (Over.homMk s.fst rfl)
      (Over.homMk s.snd s.condition.symm)).2.1
  · exact congrArg (·.left) (BinaryFan.IsLimit.lift' hq (W := Over.mk (s.fst ≫ B₁.hom)) (Over.homMk s.fst rfl)
      (Over.homMk s.snd s.condition.symm)).2.2
  · have hm : m ≫ C.hom = s.fst ≫ B₁.hom := by rw [← h₁, Category.assoc, Over.w]
    have t := (BinaryFan.IsLimit.lift' hq (W := Over.mk (s.fst ≫ B₁.hom)) (Over.homMk s.fst rfl)
      (Over.homMk s.snd s.condition.symm)).2
    have e : (Over.homMk m hm : Over.mk (s.fst ≫ B₁.hom) ⟶ C) =
        (BinaryFan.IsLimit.lift' hq (W := Over.mk (s.fst ≫ B₁.hom)) (Over.homMk s.fst rfl)
          (Over.homMk s.snd s.condition.symm)).1 := by
      refine BinaryFan.IsLimit.hom_ext hq ?_ ?_
      · rw [t.1]
        ext
        exact h₁
      · rw [t.2]
        ext
        exact h₂
    exact congrArg (·.left) e

theorem relAmple_of_cls_eq_add : ∀ {T : Scheme.{0}} [IsAffine T] {C B₁ B₂ : Over T} [GrpObj C] [GrpObj B₁] [GrpObj B₂], IsAbelianScheme B₁ → IsAbelianScheme B₂ → ∀ (q₁ : C ⟶ B₁) (q₂ : C ⟶ B₂), IsLimit (BinaryFan.mk q₁ q₂) → ∀ {L₁ : LB B₁.left} (hL₁ : L₁.IsLB), Out.RelAmple B₁ L₁ → ∀ {L₂ : LB B₂.left} (hL₂ : L₂.IsLB), Out.RelAmple B₂ L₂ → ∀ {L : LB C.left} (hL : L.IsLB), cls L hL = pull q₁.left (cls L₁ hL₁) + pull q₂.left (cls L₂ hL₂) → Out.RelAmple C L := by
  intro T _ C B₁ B₂ _ _ _ hB₁ hB₂ q₁ q₂ hq L₁ hL₁ a₁ L₂ hL₂ a₂ L hL e
  have hp := isPullback_of_isLimit_binaryFan q₁ q₂ hq
  have hd := LB.isLB_div hL (pull_isLB hL₁ q₁.left)
  have last : LBIso (L₂.pull q₂.left) (L.div (L₁.pull q₁.left)) := by
    refine (CechPic.cls_eq_iff (pull_isLB hL₂ _) hd).1 ?_
    rw [CechPic.cls_div hL (pull_isLB hL₁ q₁.left), e, CechPic.cls_pull hL₁, CechPic.cls_pull hL₂,
      add_sub_cancel_left]
  haveI := hB₁.proper
  haveI := hB₂.proper
  haveI : IsProper q₁.left := MorphismProperty.of_isPullback hp.flip hB₂.proper
  haveI : IsProper C.hom := by
    rw [← Over.w q₁]
    infer_instance
  exact (relAmple_iff_isAmpleLB_of_isAffine _ hL).2 (IsAmpleLB.box
    ((relAmple_iff_isAmpleLB_of_isAffine _ hL₁).1 a₁) ((relAmple_iff_isAmpleLB_of_isAffine _ hL₂).1 a₂)
    hL (p := q₁.left) (q := q₂.left) (f := B₁.hom) (g := B₂.hom) hp last)

end GlobalTheory.ProdAmple
