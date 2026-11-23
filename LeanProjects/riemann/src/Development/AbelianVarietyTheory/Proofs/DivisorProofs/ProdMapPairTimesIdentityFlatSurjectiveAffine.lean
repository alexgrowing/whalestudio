import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMapPairTimesIdentitySnd
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false

namespace GlobalTheory.CharKer.PmapTwo

variable {S : Scheme.{0}}

theorem isPullback_whiskerLeft_left (W : Over S) {G B : Over S} (p : G ⟶ B) :
    IsPullback (W ◁ p).left (snd W G).left (snd W B).left p.left := by
  have h1 : IsPullback (fst W B).left (snd W B).left W.hom B.hom := IsPullback.of_hasPullback W.hom B.hom
  have h2 : IsPullback (fst W G).left (snd W G).left W.hom G.hom := IsPullback.of_hasPullback W.hom G.hom
  refine IsPullback.of_right ?_ ?_ h1
  · rw [← Over.comp_left, whiskerLeft_fst, Over.w p]; exact h2
  · rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]

theorem isPullback_whiskerRight_left {G B : Over S} (p : G ⟶ B) (W : Over S) :
    IsPullback (p ▷ W).left (fst G W).left (fst B W).left p.left := by
  have h1 : IsPullback (snd B W).left (fst B W).left W.hom B.hom :=
    (IsPullback.of_hasPullback B.hom W.hom).flip
  have h2 : IsPullback (snd G W).left (fst G W).left W.hom G.hom := (IsPullback.of_hasPullback G.hom W.hom).flip
  refine IsPullback.of_right ?_ ?_ h1
  · rw [← Over.comp_left, whiskerRight_snd, Over.w p]; exact h2
  · rw [← Over.comp_left, ← Over.comp_left, whiskerRight_fst]

theorem prodMapPairTimesIdentity_eq_comp_whiskers {A A' : Over S} (q : A ⟶ A') (T : Over S) :
    pmap2 q T = (q ▷ (A ⊗ T)) ≫ (A' ◁ (q ▷ T)) := by
  ext <;> simp [pmap2, pmap]

end GlobalTheory.CharKer.PmapTwo

open GlobalTheory.CharKer.PmapTwo in

theorem GlobalTheory.CharKer.pmap2_flat_surjective_isAffineHom :
    ∀ (S : Scheme.{0}) (A A' T : Over S) (q : A ⟶ A'), Flat q.left → Surjective q.left → IsAffineHom q.left →
      Flat (pmap2 q T).left ∧ Surjective (pmap2 q T).left ∧ IsAffineHom (pmap2 q T).left := by
  intro S A A' T q h1 h2 h3
  have hR := (isPullback_whiskerRight_left q (A ⊗ T)).flip
  have hL := (isPullback_whiskerLeft_left A' (q ▷ T)).flip
  have hR' := (isPullback_whiskerRight_left q T).flip
  have a1 : Flat (q ▷ (A ⊗ T)).left := MorphismProperty.of_isPullback hR h1
  have a2 : Surjective (q ▷ (A ⊗ T)).left := MorphismProperty.of_isPullback hR h2
  have a3 : IsAffineHom (q ▷ (A ⊗ T)).left := MorphismProperty.of_isPullback hR h3
  have b1 : Flat (q ▷ T).left := MorphismProperty.of_isPullback hR' h1
  have b2 : Surjective (q ▷ T).left := MorphismProperty.of_isPullback hR' h2
  have b3 : IsAffineHom (q ▷ T).left := MorphismProperty.of_isPullback hR' h3
  have c1 : Flat (A' ◁ (q ▷ T)).left := MorphismProperty.of_isPullback hL b1
  have c2 : Surjective (A' ◁ (q ▷ T)).left := MorphismProperty.of_isPullback hL b2
  have c3 : IsAffineHom (A' ◁ (q ▷ T)).left := MorphismProperty.of_isPullback hL b3
  rw [prodMapPairTimesIdentity_eq_comp_whiskers, Over.comp_left]
  exact ⟨inferInstance, inferInstance, inferInstance⟩
