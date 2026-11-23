import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.CoverLowOfCov
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

namespace UpperTheory.Gal.G3.BaseChangeTowers

private noncomputable def cmp {X A B C : Scheme.{0}} (p : X ⟶ A) (a : B ⟶ A) (ab : C ⟶ A) (b : C ⟶ B) (h : b ≫ a = ab) :
    pullback p ab ⟶ pullback p a :=
  pullback.lift (pullback.fst p ab) (pullback.snd p ab ≫ b)
    (by rw [pullback.condition, Category.assoc, h])

private theorem cmp_fst {X A B C : Scheme.{0}} (p : X ⟶ A) (a : B ⟶ A) (ab : C ⟶ A) (b : C ⟶ B) (h : b ≫ a = ab) :
    cmp p a ab b h ≫ pullback.fst p a = pullback.fst p ab := pullback.lift_fst _ _ _

private theorem cmp_snd {X A B C : Scheme.{0}} (p : X ⟶ A) (a : B ⟶ A) (ab : C ⟶ A) (b : C ⟶ B) (h : b ≫ a = ab) :
    cmp p a ab b h ≫ pullback.snd p a = pullback.snd p ab ≫ b := pullback.lift_snd _ _ _

private theorem cmp_isPullback {X A B C : Scheme.{0}} (p : X ⟶ A) (a : B ⟶ A) (ab : C ⟶ A) (b : C ⟶ B) (h : b ≫ a = ab) :
    IsPullback (cmp p a ab b h) (pullback.snd p ab) (pullback.snd p a) b := by
  refine IsPullback.of_right (h₁₂ := pullback.fst p a) (h₂₂ := a) (v₁₃ := p) ?_ (cmp_snd p a ab b h)
    (IsPullback.of_hasPullback p a)
  rw [cmp_fst, h]
  exact IsPullback.of_hasPullback p ab

private theorem cmp_bcMap {X Y A B C : Scheme.{0}} (p : X ⟶ A) (q : Y ⟶ A) (f : Y ⟶ X) (hf : f ≫ p = q)
    (a : B ⟶ A) (ab : C ⟶ A) (b : C ⟶ B) (h : b ≫ a = ab) :
    cmp q a ab b h ≫ bcMap a f hf = bcMap ab f hf ≫ cmp p a ab b h := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, bcMap_fst, cmp_fst, bcMap_fst, ← Category.assoc, cmp_fst]
  · rw [Category.assoc, Category.assoc, bcMap_snd, cmp_snd, cmp_snd, ← Category.assoc, bcMap_snd]

private theorem cmp_bcMap_isPullback {X Y A B C : Scheme.{0}} (p : X ⟶ A) (q : Y ⟶ A) (f : Y ⟶ X) (hf : f ≫ p = q)
    (a : B ⟶ A) (ab : C ⟶ A) (b : C ⟶ B) (h : b ≫ a = ab) :
    IsPullback (cmp q a ab b h) (bcMap ab f hf) (bcMap a f hf) (cmp p a ab b h) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd p ab) (v₂₂ := pullback.snd p a) (h₃₁ := b) ?_
    (cmp_bcMap p q f hf a ab b h) (cmp_isPullback p a ab b h)
  rw [bcMap_snd, bcMap_snd]
  exact cmp_isPullback q a ab b h

end UpperTheory.Gal.G3.BaseChangeTowers

open UpperTheory.Gal.G3.BaseChangeTowers in
theorem UpperTheory.Gal.G3.jBCTower :
    UpperTheory.Gal.Seam.NiceBc → PositivityTheory.AutomorphicGaloisHodgeTate.G8.BCTower := by
  intro hN k K F _ _ _ τ φ H hH
  refine ⟨hN k K τ H hH, ⟨?_⟩⟩
  have hab : Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom τ) =
      Spec.map (CommRingCat.ofHom (φ.comp τ)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let a := Spec.map (CommRingCat.ofHom τ)
  let ab := Spec.map (CommRingCat.ofHom (φ.comp τ))
  let b := Spec.map (CommRingCat.ofHom φ)
  have hz : IsPullback (cmp H.q a ab b hab) (UpperTheory.Gal.Int.Geo.bcAlong H (φ.comp τ)).q
      (UpperTheory.Gal.Int.Geo.bcAlong H τ).q b := cmp_isPullback H.q a ab b hab
  refine
    { z := cmp H.q a ab b hab
      hz := hz
      y := fun j => cmp (H.s j ≫ H.q) a ab b hab
      hs := fun j => ?_
      ht := fun j => ?_ }
  · exact cmp_bcMap_isPullback H.q (H.s j ≫ H.q) (H.s j) rfl a ab b hab
  · exact cmp_bcMap H.q (H.s j ≫ H.q) (H.t j) (H.comm j) a ab b hab
