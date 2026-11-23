import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleFormBundlePowerOfPosDef
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RealMult.Obj

theorem relAmple_diag_of_isGrpPullback : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S' : Scheme.{0}} (X : Obj F 𝔠 S) (b : S' ⟶ S) (A' : Over S') [GrpObj A'] [IsCommMonObj A']
    (φ : A'.left ⟶ X.A.left), IsGrpPullback A' X.A b φ → ∀ (φ₂ : (G2 A').left ⟶ (G2 X.A).left), IsSquare φ φ₂ →
    ∀ c : 𝔠.elt, IsTotPos (c : F) → Out.RelAmple A' (((X.P c).pull φ₂).pull (lift (𝟙 A') (𝟙 A')).left) := by
  intro F _ _ 𝔠 S S' X b A' _ _ φ hg φ₂ hsq c hc
  haveI : IsProper X.A.hom := X.ab.proper
  have hP : IsPullback φ A'.hom X.A.hom b := hg.1
  haveI : IsProper A'.hom := MorphismProperty.of_isPullback (P := @IsProper) hP inferInstance
  have hM := pull_isLB (X.isLB c) (lift (𝟙 X.A) (𝟙 X.A)).left
  have h1 : Out.RelAmple A' (((X.P c).pull (lift (𝟙 X.A) (𝟙 X.A)).left).pull φ) :=
    GlobalTheory.AmpleBaseChange.relAmple_of_isPullback hM (X.pos c hc) hP
  have hL := pull_isLB (pull_isLB (X.isLB c) φ₂) (lift (𝟙 A') (𝟙 A')).left
  have hM' := pull_isLB hM φ
  have key : (lift (𝟙 A') (𝟙 A')).left ≫ φ₂ = φ ≫ (lift (𝟙 X.A) (𝟙 X.A)).left := by
    apply pullback.hom_ext
    · show ((lift (𝟙 A') (𝟙 A')).left ≫ φ₂) ≫ (fst X.A X.A).left =
        (φ ≫ (lift (𝟙 X.A) (𝟙 X.A)).left) ≫ (fst X.A X.A).left
      rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc,
        ← Over.comp_left, lift_fst, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]
    · show ((lift (𝟙 A') (𝟙 A')).left ≫ φ₂) ≫ (snd X.A X.A).left =
        (φ ≫ (lift (𝟙 X.A) (𝟙 X.A)).left) ≫ (snd X.A X.A).left
      rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc,
        ← Over.comp_left, lift_snd, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]
  refine GlobalTheory.PosDefAmple.relAmple_of_nsmul hL hM' (N := 1) le_rfl ?_ h1
  rw [one_smul]
  show GlobalTheory.CechPic.pull _ (GlobalTheory.CechPic.pull _ (GlobalTheory.CechPic.cls _ (X.isLB c))) =
    GlobalTheory.CechPic.pull _ (GlobalTheory.CechPic.pull _ (GlobalTheory.CechPic.cls _ (X.isLB c)))
  rw [← GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.pull_comp, key]

end GlobalTheory.RealMult.Obj
