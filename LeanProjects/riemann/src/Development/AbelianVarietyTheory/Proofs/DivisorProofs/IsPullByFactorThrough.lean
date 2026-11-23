import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RealMult.Obj

theorem IsPullBy.exists_of_comp {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S' S'' : Scheme.{0}}
    {X : Obj F 𝔠 S} {X' : Obj F 𝔠 S'} {X'' : Obj F 𝔠 S''}
    {b : S' ⟶ S} {b' : S'' ⟶ S'} {φ : X'.A.left ⟶ X.A.left} {χ : X''.A.left ⟶ X.A.left}
    (h : X''.IsPullBy X (b' ≫ b) χ) (h' : X'.IsPullBy X b φ) :
    ∃ ψ : X''.A.left ⟶ X'.A.left, X''.IsPullBy X' b' ψ ∧ ψ ≫ φ = χ := by
  have hp := h'.grp.1
  let ψ : X''.A.left ⟶ X'.A.left := hp.lift χ (X''.A.hom ≫ b') (by rw [h.grp.1.w, Category.assoc])
  have hψ : ψ ≫ φ = χ := hp.lift_fst _ _ _
  have hw : ψ ≫ X'.A.hom = X''.A.hom ≫ b' := hp.lift_snd _ _ _
  refine ⟨ψ, ⟨IsGrpPullback.cancel h'.grp (by rw [hψ]; exact h.grp) hw, fun a ↦ ?_, ?_⟩, hψ⟩
  · apply hp.hom_ext
    · rw [Category.assoc, hψ, h.act, Category.assoc, h'.act, ← Category.assoc, hψ]
    · have e₁ : (X''.rm.act a).left ≫ X''.A.hom = X''.A.hom := Over.w (X''.rm.act a)
      have e₂ : (X'.rm.act a).left ≫ X'.A.hom = X'.A.hom := Over.w (X'.rm.act a)
      rw [Category.assoc, hw, ← Category.assoc, e₁, Category.assoc, e₂, hw]
  · obtain ⟨φ₂'', hsq'', hP''⟩ := h.pol
    obtain ⟨φ₂', hsq', hP'⟩ := h'.pol
    let ψ₂ : (G2 X''.A).left ⟶ (G2 X'.A).left :=
      (lift (pushPt hw (fst X''.A X''.A)) (pushPt hw (snd X''.A X''.A))).left
    have hsq : IsSquare ψ ψ₂ := by
      constructor
      · change (lift (pushPt hw (fst X''.A X''.A)) (pushPt hw (snd X''.A X''.A)) ≫ fst X'.A X'.A).left = _
        rw [lift_fst]; rfl
      · change (lift (pushPt hw (fst X''.A X''.A)) (pushPt hw (snd X''.A X''.A)) ≫ snd X'.A X'.A).left = _
        rw [lift_snd]; rfl
    have hcomp : ψ₂ ≫ φ₂' = φ₂'' := by
      apply pullback.hom_ext
      · change ψ₂ ≫ φ₂' ≫ (fst X.A X.A).left = φ₂'' ≫ (fst X.A X.A).left
        rw [hsq'.1, ← Category.assoc, hsq.1, Category.assoc, hψ, hsq''.1]
      · change ψ₂ ≫ φ₂' ≫ (snd X.A X.A).left = φ₂'' ≫ (snd X.A X.A).left
        rw [hsq'.2, ← Category.assoc, hsq.2, Category.assoc, hψ, hsq''.2]
    refine ⟨ψ₂, hsq, fun c ↦ ?_⟩
    have hX := X.isLB c
    have hX' := X'.isLB c
    refine (GlobalTheory.CechPic.cls_eq_iff (X''.isLB c) (pull_isLB hX' ψ₂)).1 ?_
    rw [(GlobalTheory.CechPic.cls_eq_iff (X''.isLB c) (pull_isLB hX φ₂'')).2 (hP'' c),
      GlobalTheory.CechPic.cls_pull hX' ψ₂, GlobalTheory.CechPic.cls_pull hX φ₂'', ← hcomp, GlobalTheory.CechPic.pull_comp,
      ← GlobalTheory.CechPic.cls_pull hX φ₂' (pull_isLB hX φ₂'),
      ← (GlobalTheory.CechPic.cls_eq_iff hX' (pull_isLB hX φ₂')).2 (hP' c)]

end GlobalTheory.RealMult.Obj
