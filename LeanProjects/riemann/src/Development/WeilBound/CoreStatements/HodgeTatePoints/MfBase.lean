import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.MemEigSpOfMemHtDual
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFullLevelAt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIsLocalRingIsFractionRingStalk
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueLiftSpecOfIsLocalizationAway
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InjectiveOfApplyEqGenericPoint

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

noncomputable section

namespace PositivityTheory.HtPt.Mf

set_option maxHeartbeats 1000000 in

theorem xr_normal : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → (∀ q : X, GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ q) → IsIntegral X ∧ (Flat.NormalCpt ξ ↔ IsNormalScheme X) := by
  intro X Ω _ ξ hgen hall
  have hdom : ∀ x : X, IsDomain (X.presheaf.stalk x) := fun x =>
    Function.Injective.isDomain (genMap ξ ⟨x, hall x⟩) (hgen.inj ⟨x, hall x⟩)
  haveI : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    haveI := hdom x
    infer_instance
  haveI : AlgebraicGeometry.IsReduced X := isReduced_of_isReduced_stalk X
  haveI : IrreducibleSpace X := by
    rw [irreducibleSpace_def]
    have hcl : closure {GlobalTheory.CompanionTheory.Ar.genPt ξ} = (Set.univ : Set X) :=
      Set.eq_univ_of_forall fun q => specializes_iff_mem_closure.mp (hall q)
    rw [Set.top_eq_univ, ← hcl]
    exact isIrreducible_singleton.closure
  haveI hI : AlgebraicGeometry.IsIntegral X := isIntegral_of_irreducibleSpace_of_isReduced X
  refine ⟨hI, ?_⟩
  have key : ∀ p : Cpt ξ, IsIntegrallyClosedIn (regAt ξ p) Ω ↔ IsIntegrallyClosed (X.presheaf.stalk p.1) := by
    intro p
    let ψ : X.functionField →+* Ω :=
      (X.presheaf.stalkSpecializes (hall (genericPoint X)) ≫ Scheme.stalkClosedPointTo ξ).hom
    letI : Algebra (X.presheaf.stalk p.1) Ω := (genMap ξ p).toAlgebra
    have hcomm : ∀ r : X.presheaf.stalk p.1, ψ (algebraMap _ X.functionField r) = algebraMap _ Ω r := by
      intro r
      have hc : X.presheaf.stalkSpecializes (genericPoint_specializes p.1) ≫
          X.presheaf.stalkSpecializes (hall (genericPoint X)) = X.presheaf.stalkSpecializes p.2 :=
        TopCat.Presheaf.stalkSpecializes_comp _ _ _
      have h1 : algebraMap (X.presheaf.stalk p.1) X.functionField r =
          (X.presheaf.stalkSpecializes (genericPoint_specializes p.1)).hom r := rfl
      have h2 : algebraMap (X.presheaf.stalk p.1) Ω r =
          (X.presheaf.stalkSpecializes p.2 ≫ Scheme.stalkClosedPointTo ξ).hom r := rfl
      rw [h1, h2]
      have h3 := congrArg (fun φ => (φ ≫ Scheme.stalkClosedPointTo ξ).hom r) hc
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h3
      simp only [ψ, CommRingCat.hom_comp, RingHom.comp_apply]
      exact h3
    have hsurj : Function.Surjective ψ := by
      intro a
      obtain ⟨g, rfl⟩ := hgen.bij.2 a
      refine ⟨(X.presheaf.stalkSpecializes (genericPoint_specializes (GlobalTheory.CompanionTheory.Ar.genPt ξ))).hom g, ?_⟩
      have hc2 : X.presheaf.stalkSpecializes (genericPoint_specializes (GlobalTheory.CompanionTheory.Ar.genPt ξ)) ≫
          X.presheaf.stalkSpecializes (hall (genericPoint X)) = 𝟙 _ :=
        (TopCat.Presheaf.stalkSpecializes_comp _ _ _).trans (TopCat.Presheaf.stalkSpecializes_refl _ _)
      have h3 := congrArg (fun φ => (φ ≫ Scheme.stalkClosedPointTo ξ).hom g) hc2
      simp only [Category.id_comp, CommRingCat.hom_comp, RingHom.comp_apply] at h3
      simp only [ψ, CommRingCat.hom_comp, RingHom.comp_apply]
      exact h3
    let e : X.functionField ≃ₐ[X.presheaf.stalk p.1] Ω :=
      AlgEquiv.ofBijective { ψ with commutes' := hcomm } ⟨ψ.injective, hsurj⟩
    rw [isIntegrallyClosed_iff_isIntegrallyClosedIn X.functionField, e.isIntegrallyClosedIn]
    letI : Algebra (X.presheaf.stalk p.1) (regAt ξ p) := (genMap ξ p).rangeRestrict.toAlgebra
    haveI : IsScalarTower (X.presheaf.stalk p.1) (regAt ξ p) Ω :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI : Algebra.IsIntegral (X.presheaf.stalk p.1) (regAt ξ p) :=
      Algebra.isIntegral_of_surjective (genMap ξ p).rangeRestrict_surjective
    rw [Subring.isIntegrallyClosedIn_iff, isIntegrallyClosedIn_iff]
    constructor
    · intro h
      refine ⟨hgen.inj p, fun {x} hx => ?_⟩
      exact RingHom.mem_range.mp (h hx.tower_top)
    · rintro ⟨-, h⟩ x hx
      exact RingHom.mem_range.mpr (h (isIntegral_trans x hx))
  constructor
  · intro h x
    exact ⟨inferInstance, (key ⟨x, hall x⟩).mp
      (Subring.isIntegrallyClosedIn_iff.mpr (fun a ha => h ⟨x, hall x⟩ a ha))⟩
  · intro h p a ha
    exact Subring.isIntegrallyClosedIn_iff.mp ((key p).mpr (h p.1).2) ha

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem bijective_iff_isIso_stalkMap (ξ : Sp Ω ⟶ X) (x : Sp Ω) :
    Function.Bijective (Scheme.stalkClosedPointTo ξ).hom ↔ IsIso (ξ.stalkMap x) := by
  obtain rfl : x = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
  rw [← isIso_comp_right_iff (ξ.stalkMap _) (AlgebraicGeometry.stalkClosedPointIso (CommRingCat.of Ω)).hom]
  exact (ConcreteCategory.isIso_iff_bijective _).symm

def push {W : Scheme.{0}} (ξ : Sp Ω ⟶ W) (f : W ⟶ X) (q : Cpt ξ) : Cpt (ξ ≫ f) :=
  ⟨f q.1, q.2.map f.continuous⟩

theorem genMap_push {W : Scheme.{0}} (ξ : Sp Ω ⟶ W) (f : W ⟶ X) (q : Cpt ξ) :
    genMap (ξ ≫ f) (push ξ f q) = (genMap ξ q).comp (f.stalkMap q.1).hom := by
  show (X.presheaf.stalkSpecializes _ ≫ Scheme.stalkClosedPointTo (ξ ≫ f)).hom =
    (W.presheaf.stalkSpecializes q.2 ≫ Scheme.stalkClosedPointTo ξ).hom.comp (f.stalkMap q.1).hom
  rw [← CommRingCat.hom_comp]
  congr 1
  rw [Scheme.stalkClosedPointTo_comp]
  exact Scheme.Hom.stalkSpecializes_stalkMap_assoc f _ q.1 q.2 _

theorem regAt_push {W : Scheme.{0}} (ξ : Sp Ω ⟶ W) (f : W ⟶ X) [SurjectiveOnStalks f] (q : Cpt ξ) :
    regAt (ξ ≫ f) (push ξ f q) = regAt ξ q := by
  ext a
  simp only [regAt, genMap_push, RingHom.mem_range, RingHom.comp_apply]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := f.stalkMap_surjective q.1 y
    exact ⟨x, rfl⟩

theorem isCptGen_of_comp {W : Scheme.{0}} (ξ : Sp Ω ⟶ W) (f : W ⟶ X) [SurjectiveOnStalks f]
    (h : IsCptGen (ξ ≫ f)) : IsCptGen ξ := by
  have key : ∀ {A B C : Type} (g : B → C) (s : A → B), Function.Injective (g ∘ s) →
      Function.Surjective s → Function.Injective g := by
    intro A B C g s hi hs y y' hy
    obtain ⟨x, rfl⟩ := hs y
    obtain ⟨x', rfl⟩ := hs y'
    exact congrArg s (hi hy)
  have hb : Function.Bijective ((Scheme.stalkClosedPointTo ξ).hom ∘ (f.stalkMap (ξ (closedPoint Ω))).hom) := by
    have hb0 := h.bij
    rw [Scheme.stalkClosedPointTo_comp] at hb0
    exact hb0
  refine ⟨⟨key _ _ hb.1 (f.stalkMap_surjective _), Function.Surjective.of_comp hb.2⟩, fun p => ?_⟩
  have hi : Function.Injective ((genMap ξ p) ∘ (f.stalkMap p.1).hom) := by
    have hi0 := h.inj (push ξ f p)
    rw [genMap_push] at hi0
    exact hi0
  exact key _ _ hi (f.stalkMap_surjective p.1)

end PositivityTheory.HtPt.Mf
