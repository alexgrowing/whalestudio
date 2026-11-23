import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem comp_hom_apply_pointOfLocal {a b c d : CommRingCat.{0}} (A : a ⟶ b) (B : b ⟶ c) (D : a ⟶ c) (T : c ⟶ d)
    (e : A ≫ B = D) (s : a) : (B ≫ T).hom (A.hom s) = (D ≫ T).hom s := by
  subst e
  simp

theorem genMap_apply_of_specializes_pointOfLocal {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (p q : Cpt ξ) (h : p.1 ⤳ q.1) (s : X.presheaf.stalk q.1) :
    genMap ξ p ((X.presheaf.stalkSpecializes h).hom s) = genMap ξ q s := by
  have e : X.presheaf.stalkSpecializes h ≫ X.presheaf.stalkSpecializes p.2 =
      X.presheaf.stalkSpecializes q.2 := TopCat.Presheaf.stalkSpecializes_comp _ _ _
  unfold genMap
  exact comp_hom_apply_pointOfLocal _ _ _ _ e s

theorem exists_unique_point_of_local (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (hξ : IsCptGen ξ) (p : Cpt ξ) (R : Type) [CommRing R] [IsLocalRing R] (φ : regAt ξ p →+* R)
    (hφ : IsLocalHom φ) :
    ∃! z : Spec (CommRingCat.of R) ⟶ X, centre z = p.1 ∧ ∀ a : regAt ξ p, ValAt ξ z (a : Ω) (φ a) := by
  let e : X.presheaf.stalk p.1 →+* regAt ξ p := (genMap ξ p).rangeRestrict
  have he : ∀ s, ((e s : regAt ξ p) : Ω) = genMap ξ p s := fun s => rfl
  have einj : Function.Injective e := fun s t h => hξ.inj p (by rw [← he, ← he, h])
  have esurj : Function.Surjective e := (genMap ξ p).rangeRestrict_surjective
  let ψ : X.presheaf.stalk p.1 ⟶ CommRingCat.of R := CommRingCat.ofHom (φ.comp e)
  have hψ : ∀ s, ψ.hom s = φ (e s) := fun s => rfl
  have hloc : IsLocalHom ψ.hom := by
    refine ⟨fun s hs => ?_⟩
    have h1 : IsUnit (e s) := hφ.map_nonunit _ (by rwa [hψ] at hs)
    obtain ⟨b, hb⟩ := h1.exists_right_inv
    obtain ⟨t, rfl⟩ := esurj b
    have : s * t = 1 := einj (by rw [map_mul, hb, map_one])
    exact IsUnit.of_mul_eq_one t this
  let w : Σ x, { f : X.presheaf.stalk x ⟶ CommRingCat.of R // IsLocalHom f.hom } := ⟨p.1, ψ, hloc⟩
  let E := SpecToEquivOfLocalRing X (CommRingCat.of R)
  have key : ∀ y : Spec (CommRingCat.of R) ⟶ X, ∀ hc : centre y = p.1,
      (∀ s : X.presheaf.stalk (centre y),
        (Scheme.stalkClosedPointTo y).hom s =
          ψ.hom ((X.presheaf.stalkSpecializes (specializes_of_eq hc.symm)).hom s)) → y = E.symm w := by
    intro y hc h
    rw [Equiv.eq_symm_apply]
    refine SpecToEquivOfLocalRing_eq_iff.mpr ⟨hc, ?_⟩
    ext s
    exact h s
  refine ⟨E.symm w, ?_, ?_⟩
  · have hs := E.apply_symm_apply w
    obtain ⟨hc, hT⟩ := SpecToEquivOfLocalRing_eq_iff.mp hs
    have hc' : centre (E.symm w) = p.1 := hc
    refine ⟨hc', fun a => ?_⟩
    obtain ⟨s, hsa⟩ := a.2
    have hsa' : e s = a := Subtype.ext hsa
    have hg : genPt ξ ⤳ centre (E.symm w) := hc'.symm ▸ p.2
    refine ⟨hg, (X.presheaf.stalkSpecializes (specializes_of_eq hc')).hom s, ?_, ?_⟩
    · exact (genMap_apply_of_specializes_pointOfLocal ξ ⟨_, hg⟩ p (specializes_of_eq hc') s).trans hsa
    · have h1 := congrArg (fun f => f.hom ((X.presheaf.stalkSpecializes (specializes_of_eq hc')).hom s)) hT
      have h1' : (Scheme.stalkClosedPointTo (E.symm w)).hom
          ((X.presheaf.stalkSpecializes (specializes_of_eq hc')).hom s) =
          ψ.hom ((X.presheaf.stalkSpecializes (specializes_of_eq hc.symm)).hom
            ((X.presheaf.stalkSpecializes (specializes_of_eq hc')).hom s)) := h1
      have h2 : (X.presheaf.stalkSpecializes (specializes_of_eq hc.symm)).hom
          ((X.presheaf.stalkSpecializes (specializes_of_eq hc')).hom s) = s := by
        have h3 : X.presheaf.stalkSpecializes (specializes_of_eq hc') ≫
            X.presheaf.stalkSpecializes (specializes_of_eq hc.symm) = 𝟙 _ := by
          rw [TopCat.Presheaf.stalkSpecializes_comp]
          exact TopCat.Presheaf.stalkSpecializes_refl _ _
        have h4 := congrArg (fun f => f.hom s) h3
        exact h4
      rw [h2, hψ, hsa'] at h1'
      exact h1'
  · rintro y ⟨hc, hv⟩
    refine key y hc fun s => ?_
    obtain ⟨s0, hs0⟩ : ∃ s0, s0 = (X.presheaf.stalkSpecializes (specializes_of_eq hc.symm)).hom s := ⟨_, rfl⟩
    obtain ⟨hg, s1, hs1, hr⟩ := hv (e s0)
    have h1 : s1 = s := by
      apply hξ.inj ⟨_, hg⟩
      rw [hs1, he, hs0]
      exact genMap_apply_of_specializes_pointOfLocal ξ p ⟨_, hg⟩ (specializes_of_eq hc.symm) s
    rw [← hs0, hψ, ← hr, h1]

end GlobalTheory.CompanionTheory.Ar
