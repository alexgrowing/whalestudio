import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsAdditiveLineBundleFamiliesUniqueIso
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.Pinch

variable {S : Scheme.{0}}

theorem isPullback_fst_whiskerRight {X Y : Over S} (f : X ⟶ Y) (W : Over S) :
    IsPullback (fst X W) (f ▷ W) f (fst Y W) := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => lift s.fst (s.snd ≫ snd _ _)) (fun s => by simp)
    (fun s => ?_) fun s l h1 h2 => ?_⟩⟩
  · ext1
    · simp [s.condition]
    · simp
  · ext1
    · simp [← h1]
    · simp [← h2]

theorem isPullback_snd_whiskerLeft (W : Over S) {X Y : Over S} (f : X ⟶ Y) :
    IsPullback (snd W X) (W ◁ f) f (snd W Y) := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => lift (s.snd ≫ fst _ _) s.fst) (fun s => by simp)
    (fun s => ?_) fun s l h1 h2 => ?_⟩⟩
  · ext1
    · simp
    · simp [s.condition]
  · ext1
    · simp [← h2]
    · simp [← h1]

theorem rep_cmp (S : Scheme.{0}) (A B' S' C Z : Over S) [GrpObj A] (b' : B' ⟶ S') (P' : LB (A ⊗ B').left)
    (e : C ⟶ Z) (Q : LB (A ⊗ C).left) (h₁ : Rep A b' P') (h₂ : Rep A e Q) :
    ∃ q : B' ⊗ Z ⟶ C, q ≫ e = snd B' Z ∧ IsPullback q.left (fst B' Z ≫ b').left C.hom S'.hom ∧
      Same A P' Q (fst B' Z) q := by
  have r₁ := Rep.baseChange S A B' S' (S' ⊗ Z) (B' ⊗ Z) b' P' (fst S' Z) (fst B' Z) (b' ▷ Z) h₁
    (isPullback_fst_whiskerRight b' Z)
  have r₂ := Rep.baseChange S A C Z (S' ⊗ Z) (S' ⊗ C) e Q (snd S' Z) (snd S' C) (S' ◁ e) h₂
    (isPullback_snd_whiskerLeft S' e)
  obtain ⟨ε, hε, hs⟩ := rep_unique S A (B' ⊗ Z) (S' ⊗ C) (S' ⊗ Z) (b' ▷ Z) _ (S' ◁ e) _ r₁ r₂
  have hf : ε.hom.left ≫ (fst S' C).left = (fst B' Z ≫ b').left := by
    rw [← Over.comp_left, ← whiskerLeft_fst S' e, reassoc_of% hε, whiskerRight_fst]
  refine ⟨ε.hom ≫ snd S' C, ?_, ?_, ?_⟩
  · rw [Category.assoc, ← whiskerLeft_snd, reassoc_of% hε, whiskerRight_snd]
  · have hpb : IsPullback (snd S' C).left (fst S' C).left C.hom S'.hom :=
      (IsPullback.of_hasPullback S'.hom C.hom).flip
    have : IsIso ε.hom.left := ⟨⟨ε.inv.left, by rw [← Over.comp_left, ε.hom_inv_id, Over.id_left],
      by rw [← Over.comp_left, ε.inv_hom_id, Over.id_left]⟩⟩
    have hiso : IsPullback ε.hom.left (fst B' Z ≫ b').left (fst S' C).left (𝟙 S'.left) :=
      IsPullback.of_horiz_isIso ⟨by rw [hf, Category.comp_id]⟩
    have := hiso.paste_horiz hpb
    rwa [Category.id_comp, ← Over.comp_left] at this
  · rw [same_iff h₁.fam.isLB h₂.fam.isLB]
    rw [same_iff r₁.fam.isLB r₂.fam.isLB, evc_ev h₁.fam.isLB, evc_ev h₂.fam.isLB] at hs
    simpa [lift_fst, lift_snd_assoc] using hs

end GlobalTheory.Pinch
