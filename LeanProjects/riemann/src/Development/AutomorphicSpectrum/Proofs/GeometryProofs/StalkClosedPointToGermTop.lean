import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ZmodTorsorBaseChangeTransportPoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkSpecializes
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.ConstReg

theorem stalkClosedPointTo_germ_top {X : Scheme.{0}} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (t : Γ(X, ⊤)) :
    (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.germ ⊤ (genPt ξ) trivial).hom t) =
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom (ξ.appTop.hom t) := by
  have h : X.presheaf.germ ⊤ (genPt ξ) trivial ≫ Scheme.stalkClosedPointTo ξ =
      ξ.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom := by
    refine (Scheme.germ_stalkClosedPointTo ξ ⊤ trivial).trans ?_
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Scheme.Hom.appTop]
    congr 1
  exact congrArg (fun q => q.hom t) h

theorem genMap_germ_const {X : Scheme.{0}} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) {O : Type} [CommRing O] [Algebra O Ω]
    (s : X ⟶ Spec (CommRingCat.of O))
    (hs : ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω))) (p : Cpt ξ) (o : O) :
    genMap ξ p ((X.presheaf.germ ⊤ p.1 trivial).hom
        (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) = algebraMap O Ω o := by
  have h1 : genMap ξ p ((X.presheaf.germ ⊤ p.1 trivial).hom
        (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) =
      (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.germ ⊤ (genPt ξ) trivial).hom
        (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) :=
    congrArg (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ_stalkSpecializes_apply (show p.1 ∈ (⊤ : X.Opens) from trivial) p.2 _)
  rw [h1, stalkClosedPointTo_germ_top]
  have h2 : ξ.appTop.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o)) =
      (Spec.map (CommRingCat.ofHom (algebraMap O Ω))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o) := by
    rw [← hs]; simp only [Scheme.Hom.comp_appTop]; rfl
  rw [h2]
  have h3 := congrArg (fun q => q.hom o)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap O Ω)))
  have h3' : (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (algebraMap O Ω o) =
      (Spec.map (CommRingCat.ofHom (algebraMap O Ω))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o) := h3
  rw [← h3']
  simp

theorem isUnit_germ_const_iff {X : Scheme.{0}} {O : Type} [CommRing O]
    (s : X ⟶ Spec (CommRingCat.of O)) (x : X) (o : O) :
    IsUnit ((X.presheaf.germ ⊤ x trivial).hom
        (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) ↔ o ∉ (s x).asIdeal := by
  rw [← Scheme.mem_basicOpen_top, ← Scheme.preimage_basicOpen_top, Scheme.Hom.mem_preimage,
    basicOpen_eq_of_affine (R := CommRingCat.of O) o]
  exact Iff.rfl

theorem regular_const : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)), ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → ∀ (p : Cpt ξ) (o : O), algebraMap O Ω o ∈ regAt ξ p ∧ (IsCptGen ξ → (unitAt ξ p (algebraMap O Ω o) ↔ o ∉ (s p.1).asIdeal)) := by
  intro X Ω _ ξ O _ _ _ s hs p o
  have hg := genMap_germ_const ξ s hs p o
  refine ⟨⟨_, hg⟩, fun hc => ?_⟩
  rw [← isUnit_germ_const_iff s p.1 o]
  constructor
  · intro hu
    obtain ⟨u, hu, e⟩ := (unitAt_iff_of_isCptGen ξ hc p _).1 hu
    rwa [← hc.inj p (e.trans hg.symm)]
  · intro hu
    rw [← hg]
    exact RegAtMono.unitAt_of_isUnit ξ p hu

end GlobalTheory.CompanionTheory.Ar.Flat.ConstReg
