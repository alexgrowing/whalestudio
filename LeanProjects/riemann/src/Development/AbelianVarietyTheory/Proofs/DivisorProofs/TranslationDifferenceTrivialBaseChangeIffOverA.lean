import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcR
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TwistFlat

theorem pull_restrict_eq_zero_iff {X₁ X₂ Z : Scheme.{0}} (f₁ : X₁ ⟶ Z) (f₂ : X₂ ⟶ Z) (h : X₁ ⟶ X₂) (k : X₂ ⟶ X₁)
    (hk : k ≫ h = 𝟙 X₂) (hf : h ≫ f₂ = f₁) (hf' : k ≫ f₁ = f₂) (U : Z.Opens) (c : Pic X₂) :
    CechPic.pull (f₁ ⁻¹ᵁ U).ι (CechPic.pull h c) = 0 ↔ CechPic.pull (f₂ ⁻¹ᵁ U).ι c = 0 := by
  constructor
  · intro e
    have e' := pull_eq_zero_of_mem (f₁ ⁻¹ᵁ U) ((f₂ ⁻¹ᵁ U).ι ≫ k) (fun z ↦ by
      show f₁ (k ((f₂ ⁻¹ᵁ U).ι z)) ∈ U
      rw [← Scheme.Hom.comp_apply, hf']
      exact z.2) (c := CechPic.pull h c) e
    rwa [← pull_comp, Category.assoc, hk, Category.comp_id] at e'
  · intro e
    rw [← pull_comp]
    exact pull_eq_zero_of_mem (f₂ ⁻¹ᵁ U) ((f₁ ⁻¹ᵁ U).ι ≫ h) (fun z ↦ by
      show f₂ (h ((f₁ ⁻¹ᵁ U).ι z)) ∈ U
      rw [← Scheme.Hom.comp_apply, hf]
      exact z.2) e

section Iso
variable {R : Type} [CommRing R] (A : Over (Sp R)) {T : Over (Sp R)} {V : Type} [CommRing V] (φ : Sp V ⟶ T.left)
  (Y : Over (Sp V))

def cmpHom : pullback Y.hom (pullback.snd A.hom (φ ≫ T.hom)) ⟶ pullback (Y.hom ≫ φ ≫ T.hom) A.hom :=
  pullback.lift (pullback.fst Y.hom _) (pullback.snd Y.hom _ ≫ pullback.fst A.hom (φ ≫ T.hom)) (by
    rw [← Category.assoc, pullback.condition, Category.assoc, Category.assoc, pullback.condition])

def cmpInv : pullback (Y.hom ≫ φ ≫ T.hom) A.hom ⟶ pullback Y.hom (pullback.snd A.hom (φ ≫ T.hom)) :=
  pullback.lift (pullback.fst _ A.hom)
    (pullback.lift (pullback.snd _ A.hom) (pullback.fst _ A.hom ≫ Y.hom) (by
      rw [Category.assoc]; exact pullback.condition.symm)) (pullback.lift_snd _ _ _).symm

theorem cmpInv_hom : cmpInv A φ Y ≫ cmpHom A φ Y = 𝟙 _ := by
  apply pullback.hom_ext <;>
    simp only [cmpHom, cmpInv, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc, Category.id_comp]

theorem cmpHom_fst : cmpHom A φ Y ≫ pullback.fst _ A.hom = pullback.fst Y.hom (pullback.snd A.hom (φ ≫ T.hom)) :=
  pullback.lift_fst _ _ _

theorem cmpInv_fst : cmpInv A φ Y ≫ pullback.fst Y.hom (pullback.snd A.hom (φ ≫ T.hom)) = pullback.fst _ A.hom :=
  pullback.lift_fst _ _ _

theorem cmpHom_snd : cmpHom A φ Y ≫ pullback.snd (Y.hom ≫ φ ≫ T.hom) A.hom =
    pullback.snd Y.hom (pullback.snd A.hom (φ ≫ T.hom)) ≫ pullback.fst A.hom (φ ≫ T.hom) :=
  pullback.lift_snd _ _ _

end Iso

section Main
variable {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {T : Over (Sp R)} {V : Type} [CommRing V]
  (φ : Sp V ⟶ T.left)

def cmpOver (Y : Over (Sp V)) : Over.mk ((Y ⊗ bc A φ).hom ≫ φ ≫ T.hom) ⟶ up φ Y ⊗ A :=
  Over.homMk (cmpHom A φ Y) (by
    show cmpHom A φ Y ≫ (up φ Y ⊗ A).hom = (Y ⊗ bc A φ).hom ≫ φ ≫ T.hom
    rw [← Over.w (fst (up φ Y) A), ← Over.w (fst Y (bc A φ))]
    show cmpHom A φ Y ≫ pullback.fst _ A.hom ≫ (Y.hom ≫ φ ≫ T.hom) =
      (pullback.fst Y.hom (pullback.snd A.hom (φ ≫ T.hom)) ≫ Y.hom) ≫ φ ≫ T.hom
    rw [← Category.assoc, cmpHom_fst, Category.assoc])

theorem mul_left_fst {Y : Over (Sp V)} (x : Y ⟶ bc A φ) :
    ((fst Y (bc A φ) ≫ x) * snd Y (bc A φ)).left ≫ pullback.fst A.hom (φ ≫ T.hom) =
      cmpHom A φ Y ≫ ((fst (up φ Y) A ≫ upa φ x) * snd (up φ Y) A).left := by
  have hG := (ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback A (φ ≫ T.hom)).2 (Y ⊗ bc A φ)
    (fst Y (bc A φ) ≫ x) (snd Y (bc A φ)) (cmpOver A φ Y ≫ fst (up φ Y) A ≫ upa φ x)
    (cmpOver A φ Y ≫ snd (up φ Y) A) (by
      show cmpHom A φ Y ≫ pullback.fst _ A.hom ≫ x.left ≫ pullback.fst A.hom (φ ≫ T.hom) =
        (pullback.fst Y.hom (pullback.snd A.hom (φ ≫ T.hom)) ≫ x.left) ≫ pullback.fst A.hom (φ ≫ T.hom)
      rw [← Category.assoc, cmpHom_fst, Category.assoc]) (cmpHom_snd A φ Y)
  rw [← MonObj.comp_mul] at hG
  exact hG.symm

theorem snd_lift_pa_pt (Y : Over (Sp V)) :
    (snd Y (bc A φ)).left ≫ (lift (pa A φ) (pt A φ)).left =
      cmpHom A φ Y ≫ (lift (snd (up φ Y) A) (fst (up φ Y) A ≫ upt φ Y)).left := by
  apply pullback.hom_ext
  · show (snd Y (bc A φ)).left ≫ (lift (pa A φ) (pt A φ) ≫ fst A T).left =
      cmpHom A φ Y ≫ (lift (snd (up φ Y) A) (fst (up φ Y) A ≫ upt φ Y) ≫ fst A T).left
    rw [lift_fst, lift_fst]
    exact (cmpHom_snd A φ Y).symm
  · show (snd Y (bc A φ)).left ≫ (lift (pa A φ) (pt A φ) ≫ snd A T).left =
      cmpHom A φ Y ≫ (lift (snd (up φ Y) A) (fst (up φ Y) A ≫ upt φ Y) ≫ snd A T).left
    rw [lift_snd, lift_snd]
    show pullback.snd Y.hom (pullback.snd A.hom (φ ≫ T.hom)) ≫ pullback.snd A.hom (φ ≫ T.hom) ≫ φ =
      cmpHom A φ Y ≫ pullback.fst _ A.hom ≫ Y.hom ≫ φ
    rw [← Category.assoc (cmpHom A φ Y), cmpHom_fst, ← Category.assoc, ← pullback.condition, Category.assoc]

theorem triv_pull_iff {X : Scheme.{0}} {D : LB X} (hD : D.IsLB) (W : X.Opens) :
    Triv (D.pull W.ι) ↔ CechPic.pull W.ι (cls D hD) = 0 := by
  unfold Triv
  rw [← cls_eq_zero_iff (pull_isLB hD _), cls_pull hD]

theorem triv_twist_iff (L : LB A.left) (hL : L.IsLB) (N : LB (A ⊗ T).left) (hN : N.IsLB) (Y : Over (Sp V))
    (x : Y ⟶ bc A φ) (U : Y.left.Opens) :
    Triv ((LB.div (translDiff (bc A φ) (L.pull (pullback.fst A.hom (φ ≫ T.hom))) x)
        ((twist A φ N).pull (snd Y (bc A φ)).left)).pull ((fst Y (bc A φ)).left ⁻¹ᵁ U).ι) ↔
      Triv ((LB.div (translDiff A L (upa φ x)) (ev N (snd (up φ Y) A) (fst (up φ Y) A ≫ upt φ Y))).pull
        ((fst (up φ Y) A).left ⁻¹ᵁ U).ι) := by
  have hL' : (L.pull (pullback.fst A.hom (φ ≫ T.hom))).IsLB := pull_isLB hL _
  have h₁ : (translDiff (bc A φ) (L.pull (pullback.fst A.hom (φ ≫ T.hom))) x).IsLB := LB.isLB_linComb hL' _ _
  have hO : (twist A φ N).IsLB := pull_isLB hN _
  have h₂ : ((twist A φ N).pull (snd Y (bc A φ)).left).IsLB := pull_isLB hO _
  have h₃ : (translDiff A L (upa φ x)).IsLB := LB.isLB_linComb hL _ _
  have h₄ : (ev N (snd (up φ Y) A) (fst (up φ Y) A ≫ upt φ Y)).IsLB := pull_isLB hN _
  have hc : cls _ (LB.isLB_div h₁ h₂) = CechPic.pull (cmpHom A φ Y) (cls _ (LB.isLB_div h₃ h₄)) := by
    rw [cls_div h₁ h₂, cls_div h₃ h₄, map_sub]
    have e₁ := pull_translDiff hL' x h₁ (fst Y (bc A φ)) (snd Y (bc A φ))
    rw [lift_fst_snd, Over.id_left, pull_id] at e₁
    have e₂ := pull_translDiff hL (upa φ x) h₃ (fst (up φ Y) A) (snd (up φ Y) A)
    rw [lift_fst_snd, Over.id_left, pull_id] at e₂
    rw [e₁, e₂, map_sub, cls_pull hL, ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp, mul_left_fst]
    have e₅ : (snd Y (bc A φ)).left ≫ pullback.fst A.hom (φ ≫ T.hom) = cmpHom A φ Y ≫ (snd (up φ Y) A).left :=
      (cmpHom_snd A φ Y).symm
    rw [e₅, cls_pull hO _ h₂,
      show cls (twist A φ N) hO = CechPic.pull (lift (pa A φ) (pt A φ)).left (cls N hN) from cls_pull hN _ hO,
      cls_pull hN, ← pull_comp, ← pull_comp, snd_lift_pa_pt]
  rw [triv_pull_iff (LB.isLB_div h₁ h₂), triv_pull_iff (LB.isLB_div h₃ h₄), hc]
  exact pull_restrict_eq_zero_iff _ _ (cmpHom A φ Y) (cmpInv A φ Y) (cmpInv_hom A φ Y) (cmpHom_fst A φ Y)
    (cmpInv_fst A φ Y) U _

end Main

end GlobalTheory.TwistFlat
