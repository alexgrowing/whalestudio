import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentOfEqualisedProperCoverNormalStatement

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.GrpDescent

section Pt
variable {S X : Scheme.{0}} (G' : Over S) (f : X ⟶ S)

def ptOf {T : Over X} (a : T.left ⟶ G'.left) (ha : a ≫ G'.hom = T.hom ≫ f) : T ⟶ (Over.pullback f).obj G' :=
  Over.homMk (pullback.lift a T.hom ha) (pullback.lift_snd _ _ _)

theorem ptOf_fst {T : Over X} (a : T.left ⟶ G'.left) (ha : a ≫ G'.hom = T.hom ≫ f) :
    (ptOf G' f a ha).left ≫ pullback.fst G'.hom f = a := pullback.lift_fst _ _ _

theorem ptOf_mul [GrpObj G'] {T : Over X} (w : T.left ⟶ (G' ⊗ G').left) (hw : w ≫ (G' ⊗ G').hom = T.hom ≫ f)
    (h₁ : (w ≫ (fst G' G').left) ≫ G'.hom = T.hom ≫ f) (h₂ : (w ≫ (snd G' G').left) ≫ G'.hom = T.hom ≫ f) :
    (ptOf G' f _ h₁ * ptOf G' f _ h₂).left ≫ pullback.fst G'.hom f = w ≫ μ[G'].left := by
  let U : Over.mk (T.hom ≫ f) ⟶ G' ⊗ G' := Over.homMk w hw
  have e := (isGrpPullback_pullback G' f).2 T (ptOf G' f _ h₁) (ptOf G' f _ h₂) (U ≫ fst G' G') (U ≫ snd G' G')
    (ptOf_fst G' f _ h₁).symm (ptOf_fst G' f _ h₂).symm
  rw [← e, ← MonObj.comp_mul, Hom.mul_def, lift_fst_snd, Category.id_comp]
  rfl

end Pt

theorem mul_descends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] (G : Over (Sp R)) (β : G'.left ⟶ G.left), Smooth G.hom → IsPullback β G'.hom G.hom π → ∀ φ : (Over.pullback (pullback.fst π π)).obj G' ≅ (Over.pullback (pullback.snd π π)).obj G', IsMonHom φ.hom → pullback.fst G'.hom (pullback.fst π π) ≫ β = φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β → ∃ m : G ⊗ G ⟶ G, ∀ (T : Over S) (x y : T ⟶ G') (x₀ y₀ : Over.mk (T.hom ≫ π) ⟶ G), x₀.left = x.left ≫ β → y₀.left = y.left ≫ β → (lift x₀ y₀ ≫ m).left = (x * y).left ≫ β := by
  intro R _ _ _ _ S π hprop hsurj hint G' _ G β hsm hβ φ hφ hdat
  haveI := hsm
  haveI : Smooth (G ⊗ G).hom := inferInstanceAs (Smooth (pullback.fst G.hom G.hom ≫ G.hom))
  have hflat : Flat (G ⊗ G).hom := inferInstance
  let Z' : Over (Sp R) := Over.mk ((G' ⊗ G').hom ≫ π)
  let u : Z' ⟶ G := Over.homMk ((fst G' G').left ≫ β) (by
    show ((fst G' G').left ≫ β) ≫ G.hom = (G' ⊗ G').hom ≫ π
    rw [Category.assoc, hβ.w, ← Category.assoc, Over.w])
  let v : Z' ⟶ G := Over.homMk ((snd G' G').left ≫ β) (by
    show ((snd G' G').left ≫ β) ≫ G.hom = (G' ⊗ G').hom ≫ π
    rw [Category.assoc, hβ.w, ← Category.assoc, Over.w])
  let p : (G' ⊗ G').left ⟶ (G ⊗ G).left := (lift u v).left
  have hp1 : p ≫ (fst G G).left = (fst G' G').left ≫ β := by
    show (lift u v ≫ fst G G).left = _
    rw [lift_fst]; rfl
  have hp2 : p ≫ (snd G G).left = (snd G' G').left ≫ β := by
    show (lift u v ≫ snd G G).left = _
    rw [lift_snd]; rfl
  have hA : IsPullback (fst G' G').left (snd G' G').left G'.hom G'.hom := IsPullback.of_hasPullback _ _
  have hB : IsPullback (fst G G).left (snd G G).left G.hom G.hom := IsPullback.of_hasPullback _ _
  have htop : IsPullback p (snd G' G').left (snd G G).left β := by
    refine IsPullback.of_right (h₁₂ := (fst G G).left) (h₂₂ := G.hom) ?_ hp2 hB
    rw [hp1, hβ.w]
    exact hA.paste_horiz hβ
  have hpb : IsPullback p (G' ⊗ G').hom (G ⊗ G).hom π := by
    have h := htop.paste_vert hβ
    rwa [Over.w (snd G' G'), Over.w (snd G G)] at h

  have hepi : ∀ {W : Scheme.{0}} (a b : (G ⊗ G).left ⟶ W), p ≫ a = p ≫ b → a = b := by
    intro W a b hab
    obtain ⟨c, -, hc⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S _ _ W π _ p _ hprop hsurj hint hflat hpb (p ≫ a)
      (by rw [← Category.assoc, pullback.condition, Category.assoc])
    exact (hc a rfl).trans (hc b hab.symm).symm

  have heq : pullback.fst p p ≫ μ[G'].left ≫ β = pullback.snd p p ≫ μ[G'].left ≫ β := by
    set f₁ := pullback.fst p p
    set f₂ := pullback.snd p p
    have hf : f₁ ≫ p = f₂ ≫ p := pullback.condition
    have hs : (f₁ ≫ (G' ⊗ G').hom) ≫ π = (f₂ ≫ (G' ⊗ G').hom) ≫ π := by
      rw [Category.assoc, Category.assoc, ← hpb.w, ← Category.assoc, hf, Category.assoc]
    let σ := pullback.lift _ _ hs
    let T₀ : Over (pullback π π) := Over.mk σ
    have hw₁ : f₁ ≫ (G' ⊗ G').hom = T₀.hom ≫ pullback.fst π π := (pullback.lift_fst _ _ hs).symm
    have hw₂ : f₂ ≫ (G' ⊗ G').hom = T₀.hom ≫ pullback.snd π π := (pullback.lift_snd _ _ hs).symm

    have htr : ∀ (a₁ a₂ : T₀.left ⟶ G'.left) (h₁ : a₁ ≫ G'.hom = T₀.hom ≫ pullback.fst π π)
        (h₂ : a₂ ≫ G'.hom = T₀.hom ≫ pullback.snd π π), a₁ ≫ β = a₂ ≫ β →
        ptOf G' (pullback.fst π π) a₁ h₁ ≫ φ.hom = ptOf G' (pullback.snd π π) a₂ h₂ := by
      intro a₁ a₂ h₁ h₂ hb
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · apply hβ.hom_ext
        · rw [Over.comp_left, Category.assoc, Category.assoc, ← hdat, ← Category.assoc, ptOf_fst, ptOf_fst, hb]
        · rw [Category.assoc, pullback.condition, ptOf_fst, h₂, ← Category.assoc]
          exact congrArg (· ≫ pullback.snd π π) (Over.w (ptOf G' (pullback.fst π π) a₁ h₁ ≫ φ.hom))
      · exact (Over.w (ptOf G' (pullback.fst π π) a₁ h₁ ≫ φ.hom)).trans (Over.w (ptOf G' (pullback.snd π π) a₂ h₂)).symm
    have hb₁ : (f₁ ≫ (fst G' G').left) ≫ β = (f₂ ≫ (fst G' G').left) ≫ β := by
      rw [Category.assoc, Category.assoc, ← hp1, ← Category.assoc, hf, Category.assoc]
    have hb₂ : (f₁ ≫ (snd G' G').left) ≫ β = (f₂ ≫ (snd G' G').left) ≫ β := by
      rw [Category.assoc, Category.assoc, ← hp2, ← Category.assoc, hf, Category.assoc]
    have k₁ : (f₁ ≫ (fst G' G').left) ≫ G'.hom = T₀.hom ≫ pullback.fst π π := by rw [Category.assoc, Over.w, hw₁]
    have k₂ : (f₁ ≫ (snd G' G').left) ≫ G'.hom = T₀.hom ≫ pullback.fst π π := by rw [Category.assoc, Over.w, hw₁]
    have l₁ : (f₂ ≫ (fst G' G').left) ≫ G'.hom = T₀.hom ≫ pullback.snd π π := by rw [Category.assoc, Over.w, hw₂]
    have l₂ : (f₂ ≫ (snd G' G').left) ≫ G'.hom = T₀.hom ≫ pullback.snd π π := by rw [Category.assoc, Over.w, hw₂]
    have e₁ := ptOf_mul G' (pullback.fst π π) (T := T₀) f₁ hw₁ k₁ k₂
    have e₂ := ptOf_mul G' (pullback.snd π π) (T := T₀) f₂ hw₂ l₁ l₂
    have hAB : (ptOf G' (pullback.fst π π) (T := T₀) _ k₁ * ptOf G' (pullback.fst π π) (T := T₀) _ k₂) ≫ φ.hom =
        ptOf G' (pullback.snd π π) (T := T₀) _ l₁ * ptOf G' (pullback.snd π π) (T := T₀) _ l₂ := by
      refine ((IsMonHom.monoidHom φ.hom T₀).map_mul _ _).trans ?_
      show (ptOf G' (pullback.fst π π) (T := T₀) _ k₁ ≫ φ.hom) * (ptOf G' (pullback.fst π π) (T := T₀) _ k₂ ≫ φ.hom) = _
      rw [htr _ _ k₁ l₁ hb₁, htr _ _ k₂ l₂ hb₂]
    rw [← Category.assoc f₁, ← e₁, ← Category.assoc f₂, ← e₂, ← hAB, Over.comp_left]
    simp only [Category.assoc]
    rw [hdat]
  obtain ⟨h₀, hh₀, -⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S _ _ _ π _ p _ hprop hsurj hint hflat hpb (μ[G'].left ≫ β) heq
  have hover : h₀ ≫ G.hom = (G ⊗ G).hom := by
    apply hepi
    rw [← Category.assoc, hh₀, Category.assoc, hβ.w, ← Category.assoc, Over.w μ[G'], hpb.w]
  refine ⟨Over.homMk h₀ hover, fun T x y x₀ y₀ hx hy => ?_⟩
  have hl : (lift x₀ y₀).left = (lift x y).left ≫ p := by
    apply hB.hom_ext
    · rw [Category.assoc, hp1, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst, hx]
    · rw [Category.assoc, hp2, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd, hy]
  rw [Over.comp_left, hl]
  change ((lift x y).left ≫ p) ≫ h₀ = _
  rw [Category.assoc, hh₀, Hom.mul_def, Over.comp_left, Category.assoc]

end GlobalTheory.GrpDescent
