import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGrpPullbackOfLoc
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRigidTranslatePrincipalPolarisationOrderTw
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PolKerPull

theorem hasGen_pull_pull_comp {X Y Z W : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (ℓ : Z ⟶ Y)
    (g : W ⟶ Z) (m : W ⟶ X) (hm : g ≫ ℓ ≫ f = m) (h : HasGen ((L.pull f).pull ℓ)) : HasGen (L.pull m) := by
  obtain ⟨t, ht⟩ := h
  have h₁ : HasGen ((L.pull f).pull (g ≫ ℓ)) :=
    ⟨LB.pullGen (L.pull f) (fun _ : PUnit => ℓ) (fun _ => 1) t g,
      DVR.pullGen_isGen (L.pull f) (fun _ : PUnit => ℓ) (fun _ => 1) t ht g⟩
  obtain ⟨s, hs⟩ := h₁
  obtain ⟨u, hu⟩ := RigidTranslate.gen_of_lbIso (pull_isLB (pull_isLB hL f) _) (pull_isLB hL _)
    (FamRep.lbIso_pull_pull hL f (g ≫ ℓ)) s hs
  have e : (g ≫ ℓ) ≫ f = m := by rw [Category.assoc, hm]
  subst e
  exact ⟨u, hu⟩

theorem ker_pull : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S' : Scheme.{0}} (X : Obj F 𝔠 S) (b : S' ⟶ S) (A' : Over S') [GrpObj A'] [IsCommMonObj A']
    (φ : A'.left ⟶ X.A.left), IsGrpPullback A' X.A b φ → ∀ (rm' : OAct (𝓞 F) A'),
    (∀ a, (rm'.act a).left ≫ φ = φ ≫ (X.rm.act a).left) → ∀ (φ₂ : (G2 A').left ⟶ (G2 X.A).left), IsSquare φ φ₂ →
    ∀ (c : 𝔠.elt) (T : Over S') (x : T ⟶ A'),
      HasGen (((X.P c).pull φ₂).pull (lift (fst A' T) (snd A' T ≫ x)).left) →
      ∀ a : 𝓞 F, (∀ d : 𝔠.elt, ∃ b : 𝓞 F, a • d = b • c) → x ≫ rm'.act a = 1 := by
  intro F _ _ 𝔠 S S' X b A' _ _ φ hφ rm' hact φ₂ hsq c T x hgen a ha
  let T₀ : Over S := Over.mk (T.hom ≫ b)
  let x₀ : T₀ ⟶ X.A := pushPt hφ.1.w x

  let Z' : Over S' := Over.mk ((snd X.A T₀).left ≫ T.hom)
  have w₁ : (fst X.A T₀).left ≫ X.A.hom = ((snd X.A T₀).left ≫ T.hom) ≫ b := by
    rw [Over.w (fst X.A T₀), Category.assoc]
    exact (Over.w (snd X.A T₀)).symm
  let p₁ : Z' ⟶ A' := Over.homMk (hφ.1.lift (fst X.A T₀).left ((snd X.A T₀).left ≫ T.hom) w₁)
    (hφ.1.lift_snd _ _ _)
  let p₂ : Z' ⟶ T := Over.homMk (snd X.A T₀).left rfl
  have hp₁ : p₁.left ≫ φ = (fst X.A T₀).left := hφ.1.lift_fst _ _ _
  have key : (lift p₁ p₂).left ≫ (lift (fst A' T) (snd A' T ≫ x)).left ≫ φ₂ =
      (lift (fst X.A T₀) (snd X.A T₀ ≫ x₀)).left := by
    have e : (lift p₁ p₂).left ≫ (lift (fst A' T) (snd A' T ≫ x)).left = (lift p₁ (p₂ ≫ x)).left := by
      rw [← Over.comp_left]; congr 1; simp
    rw [← Category.assoc, e]
    apply pullback.hom_ext
    · have h1 := hsq.1
      rw [Over.fst_left] at h1
      rw [Category.assoc, h1, ← Category.assoc, ← Over.comp_left, lift_fst, hp₁, ← Over.fst_left,
        ← Over.comp_left, lift_fst]
    · have h2 := hsq.2
      rw [Over.snd_left] at h2
      rw [Category.assoc, h2, ← Category.assoc, ← Over.comp_left, lift_snd, ← Over.snd_left,
        ← Over.comp_left, lift_snd, Over.comp_left, Over.comp_left, Category.assoc]
      rfl
  have hgen₀ : HasGen ((X.P c).pull (lift (fst X.A T₀) (snd X.A T₀ ≫ x₀)).left) :=
    hasGen_pull_pull_comp (X.isLB c) φ₂ _ (lift p₁ p₂).left _ key hgen
  have h₀ : x₀ ≫ X.rm.act a = 1 := X.ker c T₀ x₀ hgen₀ a ha
  have inj : ∀ {y z : T ⟶ A'}, pushPt hφ.1.w y = pushPt hφ.1.w z → y = z := fun {y z} h =>
    Over.OverMorphism.ext (hφ.1.hom_ext (congrArg (fun q => q.left) h) (by rw [Over.w, Over.w]))
  apply inj
  have hpa : pushPt hφ.1.w (x ≫ rm'.act a) = x₀ ≫ X.rm.act a :=
    Over.OverMorphism.ext (by
      show (x.left ≫ (rm'.act a).left) ≫ φ = (x.left ≫ φ) ≫ (X.rm.act a).left
      rw [Category.assoc, hact, Category.assoc])
  rw [hpa, h₀]
  exact (map_one (pushHom hφ T)).symm

end GlobalTheory.PolKerPull
