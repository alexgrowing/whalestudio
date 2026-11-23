import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOverArtinFibreProductIsPushoutStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackPowersCartesianGroupSquare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PinchHom

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {f : S' ⟶ S} {β : G'.left ⟶ G.left}

theorem sq_fst (hp : IsPullback β G'.hom G.hom f) :
    (lift (pushPt hp.w (fst G' G')) (pushPt hp.w (snd G' G'))).left ≫ (fst G G).left = (fst G' G').left ≫ β := by
  rw [← Over.comp_left, lift_fst]; rfl

theorem sq_snd (hp : IsPullback β G'.hom G.hom f) :
    (lift (pushPt hp.w (fst G' G')) (pushPt hp.w (snd G' G'))).left ≫ (snd G G).left = (snd G' G').left ≫ β := by
  rw [← Over.comp_left, lift_snd]; rfl

theorem sq_hom_ext (G : Over S) {X : Scheme.{0}} {a b : X ⟶ (G ⊗ G).left}
    (h₁ : a ≫ (fst G G).left = b ≫ (fst G G).left) (h₂ : a ≫ (snd G G).left = b ≫ (snd G G).left) : a = b :=
  GlobalTheory.Mum.PowCart.square_over_hom_ext G fun i => by fin_cases i; exacts [h₁, h₂]

theorem sq_mul [GrpObj G] [GrpObj G'] (hp : IsGrpPullback G' G f β) :
    (lift (pushPt hp.1.w (fst G' G')) (pushPt hp.1.w (snd G' G'))).left ≫ (MonObj.mul : G ⊗ G ⟶ G).left =
      (MonObj.mul : G' ⊗ G' ⟶ G').left ≫ β := by
  have h := hp.2 (G' ⊗ G') (fst G' G') (snd G' G') (pushPt hp.1.w (fst G' G')) (pushPt hp.1.w (snd G' G')) rfl rfl
  rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp, Over.comp_left] at h
  exact h

theorem main : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (A' A : Over (Spec P)) [GrpObj A'] [GrpObj A] (A₁ : Over (Spec R₁)) (A₂ : Over (Spec R₂)) (A₀ : Over (Spec R₀)) [GrpObj A₁] [GrpObj A₂] [GrpObj A₀] (j₁ : A₁.left ⟶ A'.left) (j₂ : A₂.left ⟶ A'.left) (k₁ : A₁.left ⟶ A.left) (k₂ : A₂.left ⟶ A.left) (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₀.left ⟶ A₂.left) (φ : A'.left ⟶ A.left), Flat A'.hom → IsGrpPullback A₁ A' (Spec.map f₁) j₁ → IsGrpPullback A₂ A' (Spec.map f₂) j₂ → IsGrpPullback A₁ A (Spec.map f₁) k₁ → IsGrpPullback A₂ A (Spec.map f₂) k₂ → IsGrpPullback A₀ A₁ (Spec.map g₁) i₁ → IsGrpPullback A₀ A₂ (Spec.map g₂) i₂ → i₁ ≫ j₁ = i₂ ≫ j₂ → IsPullback φ A'.hom A.hom (𝟙 _) → j₁ ≫ φ = k₁ → j₂ ≫ φ = k₂ → IsGrpPullback A' A (𝟙 _) φ := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂ A' A _ _ A₁ A₂ A₀ _ _ _ j₁ j₂ k₁ k₂ i₁ i₂ φ hfl hj₁ hj₂ hk₁ hk₂
    hi₁ hi₂ hij hφ hjk₁ hjk₂
  have hY : Flat (A' ⊗ A').hom := by
    haveI := hfl
    exact GlobalTheory.ExtUnique.flat_tensorObj A' A'
  have hw : φ ≫ A.hom = A'.hom := by simpa using hφ.w
  let Φ : A' ⟶ A := Over.homMk φ hw
  let L : A' ⊗ A' ⟶ A ⊗ A := lift (fst A' A' ≫ Φ) (snd A' A' ≫ Φ)

  have hcomp : (lift (pushPt hi₁.1.w (fst A₀ A₀)) (pushPt hi₁.1.w (snd A₀ A₀))).left ≫
      (lift (pushPt hj₁.1.w (fst A₁ A₁)) (pushPt hj₁.1.w (snd A₁ A₁))).left =
      (lift (pushPt hi₂.1.w (fst A₀ A₀)) (pushPt hi₂.1.w (snd A₀ A₀))).left ≫
      (lift (pushPt hj₂.1.w (fst A₂ A₂)) (pushPt hj₂.1.w (snd A₂ A₂))).left := by
    apply sq_hom_ext A'
    · rw [Category.assoc, sq_fst hj₁.1, reassoc_of% (sq_fst hi₁.1), Category.assoc, sq_fst hj₂.1,
        reassoc_of% (sq_fst hi₂.1), hij]
    · rw [Category.assoc, sq_snd hj₁.1, reassoc_of% (sq_snd hi₁.1), Category.assoc, sq_snd hj₂.1,
        reassoc_of% (sq_snd hi₂.1), hij]
  have po := GlobalTheory.T.flat_over_artinFibreProduct_isPushout P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂ (A' ⊗ A') (A₁ ⊗ A₁) (A₂ ⊗ A₂) (A₀ ⊗ A₀) _ _ _ _
    hY (GlobalTheory.Mum.PowCart.isPullback_two hj₁.1) (GlobalTheory.Mum.PowCart.isPullback_two hj₂.1)
    (GlobalTheory.Mum.PowCart.isPullback_two hi₁.1) hcomp (GlobalTheory.Mum.PowCart.isPullback_two hi₂.1).w

  have hL : ∀ {R : CommRingCat.{0}} {g : P ⟶ R} {B : Over (Spec R)} [GrpObj B] {j k : B.left ⟶ _}
      (hj : IsGrpPullback B A' (Spec.map g) j) (hk : IsGrpPullback B A (Spec.map g) k), j ≫ φ = k →
      (lift (pushPt hj.1.w (fst B B)) (pushPt hj.1.w (snd B B))).left ≫ (MonObj.mul : A' ⊗ A' ⟶ A').left ≫ φ =
      (lift (pushPt hj.1.w (fst B B)) (pushPt hj.1.w (snd B B))).left ≫ L.left ≫ (MonObj.mul : A ⊗ A ⟶ A).left := by
    intro R g B _ j k hj hk hjk
    have e : (lift (pushPt hj.1.w (fst B B)) (pushPt hj.1.w (snd B B))).left ≫ L.left =
        (lift (pushPt hk.1.w (fst B B)) (pushPt hk.1.w (snd B B))).left := by
      apply sq_hom_ext A
      · rw [Category.assoc, ← Over.comp_left _ _ _ L, lift_fst, sq_fst hk.1, Over.comp_left, ← Category.assoc,
          sq_fst hj.1, Category.assoc, ← hjk]
        rfl
      · rw [Category.assoc, ← Over.comp_left _ _ _ L, lift_snd, sq_snd hk.1, Over.comp_left, ← Category.assoc,
          sq_snd hj.1, Category.assoc, ← hjk]
        rfl
    rw [← Category.assoc, sq_mul hj, ← Category.assoc, e, sq_mul hk, Category.assoc, hjk]
  have hE : (MonObj.mul : A' ⊗ A' ⟶ A').left ≫ φ = L.left ≫ (MonObj.mul : A ⊗ A ⟶ A).left :=
    po.hom_ext (hL hj₁ hk₁ hjk₁) (hL hj₂ hk₂ hjk₂)
  have hE' : (MonObj.mul : A' ⊗ A' ⟶ A') ≫ Φ = L ≫ MonObj.mul := Over.OverMorphism.ext hE
  have hxy : ∀ (T : Over (Spec P)) (x y : T ⟶ A'), (x * y) ≫ Φ = (x ≫ Φ) * (y ≫ Φ) := by
    intro T x y
    rw [Hom.mul_def, Hom.mul_def, Category.assoc, hE', ← Category.assoc]
    congr 1
    simp [L]
  refine ⟨hφ, fun T x y x₀ y₀ hx hy => ?_⟩
  let k : Over.mk (T.hom ≫ 𝟙 (Spec P)) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = k ≫ x ≫ Φ := Over.OverMorphism.ext (by simp [k, Φ, hx])
  have ey : y₀ = k ≫ y ≫ Φ := Over.OverMorphism.ext (by simp [k, Φ, hy])
  rw [ex, ey, ← MonObj.comp_mul, ← hxy]
  simp [k, Φ]

end GlobalTheory.PinchHom
