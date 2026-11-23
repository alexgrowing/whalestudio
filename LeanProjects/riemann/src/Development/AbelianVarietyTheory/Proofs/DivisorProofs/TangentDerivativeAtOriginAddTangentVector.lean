import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingDualNumber
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin

noncomputable section

namespace GlobalTheory.CoordsOrigin.OriginCoordinatesAdd

theorem isLocalRing_tsz (S M : Type) [CommRing S] [IsLocalRing S] [AddCommGroup M] [Module S M] [Module Sᵐᵒᵖ M]
    [IsCentralScalar S M] : IsLocalRing (TrivSqZeroExt S M) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst with h | h
    · exact Or.inl ((TrivSqZeroExt.isUnit_iff_isUnit_fst).2 h)
    · exact Or.inr ((TrivSqZeroExt.isUnit_iff_isUnit_fst).2 (by simpa using h))

theorem isLocalHom_map {S M N : Type} [CommRing S] [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
    [Module Sᵐᵒᵖ M] [IsCentralScalar S M] [Module Sᵐᵒᵖ N] [IsCentralScalar S N] (L : M →ₗ[S] N) :
    IsLocalHom ((TrivSqZeroExt.map L : TrivSqZeroExt S M →ₐ[S] TrivSqZeroExt S N) : TrivSqZeroExt S M →+* TrivSqZeroExt S N) :=
  ⟨fun a ha => (TrivSqZeroExt.isUnit_iff_isUnit_fst).2 (by
    simpa using (TrivSqZeroExt.isUnit_iff_isUnit_fst).1 ha)⟩

variable {X : Scheme.{0}}

def valAt {A : Type} [CommRing A] [IsLocalRing A] (x : Sp A ⟶ X) (p : X) (h : x (IsLocalRing.closedPoint A) = p) :
    X.presheaf.stalk p →+* A :=
  ((X.presheaf.stalkCongr (Inseparable.of_eq h.symm)).hom ≫
    Scheme.stalkClosedPointTo (R := CommRingCat.of A) x).hom

theorem valAt_comp {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] (g : A →+* B)
    [IsLocalHom g] (x : Sp A ⟶ X) (p : X) (hx : x (IsLocalRing.closedPoint A) = p)
    (hy : (spMap g ≫ x) (IsLocalRing.closedPoint B) = p) (f : X.presheaf.stalk p) :
    valAt (spMap g ≫ x) p hy f = g (valAt x p hx f) := by
  subst hx
  let ψ : X.presheaf.stalk (x (IsLocalRing.closedPoint A)) ⟶ CommRingCat.of B :=
    Scheme.stalkClosedPointTo (R := CommRingCat.of A) x ≫ CommRingCat.ofHom g
  have hψl : IsLocalHom ψ.hom := by
    show IsLocalHom (g.comp (Scheme.stalkClosedPointTo (R := CommRingCat.of A) x).hom)
    infer_instance
  have e1 : Spec.map ψ ≫ X.fromSpecStalk _ = spMap g ≫ x := by
    simp only [ψ, Spec.map_comp, Category.assoc]
    rw [Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  have e2 := congrArg (SpecToEquivOfLocalRing X (CommRingCat.of B)) e1
  have e3 : (SpecToEquivOfLocalRing X (CommRingCat.of B)) (Spec.map ψ ≫ X.fromSpecStalk _) = ⟨_, ψ, hψl⟩ :=
    (SpecToEquivOfLocalRing X (CommRingCat.of B)).apply_symm_apply ⟨_, ψ, hψl⟩
  rw [e3] at e2
  obtain ⟨h1, h2⟩ := SpecToEquivOfLocalRing_eq_iff.1 e2.symm
  dsimp only [SpecToEquivOfLocalRing, Equiv.coe_fn_mk] at h2
  have h2' : Scheme.stalkClosedPointTo (R := CommRingCat.of B) (spMap g ≫ x) =
      (X.presheaf.stalkCongr (Inseparable.of_eq hy.symm)).inv ≫ ψ := h2
  simp only [valAt, h2', Iso.hom_inv_id_assoc]
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp, ψ]
  rfl

theorem valAt_congr {A : Type} [CommRing A] [IsLocalRing A] {x x' : Sp A ⟶ X} (e : x = x') (p : X)
    (h : x (IsLocalRing.closedPoint A) = p) (h' : x' (IsLocalRing.closedPoint A) = p) :
    valAt x p h = valAt x' p h' := by
  subst e; rfl

end GlobalTheory.CoordsOrigin.OriginCoordinatesAdd

namespace GlobalTheory.CoordsOrigin

open GlobalTheory.CoordsOrigin.OriginCoordinatesAdd

theorem tanDer_add : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (u v : TanM (𝟙 (Sp R)) G) (f : G.left.presheaf.stalk (origin G)),
    tanDer G (u + v) f = tanDer G u f + tanDer G v f := by
  intro R _ _ G _ _ u v f
  haveI : IsLocalRing (TrivSqZeroExt R (R × R)) := isLocalRing_tsz R (R × R)
  let P : overAt (𝟙 (Sp R)) (TrivSqZeroExt R (R × R)) ⟶ G :=
    (homAt (𝟙 (Sp R)) (tm (LinearMap.inl R R R)) ≫ tv u) * (homAt (𝟙 (Sp R)) (tm (LinearMap.inr R R R)) ≫ tv v)
  have hz : (0 : R →ₗ[R] R) = (0 : R) • (LinearMap.id : R →ₗ[R] R) := by simp
  have hid : ∀ w : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ G,
      homAt (𝟙 (Sp R)) (tm (LinearMap.id : R →ₗ[R] R)) ≫ w = w := by
    intro w
    simp only [tm]
    rw [TrivSqZeroExt.map_id, homAt_id, Category.id_comp]
  have hfst : homAt (𝟙 (Sp R)) (tm (LinearMap.fst R R R)) ≫ P = tv u := by
    simp only [P]
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp,
      ← TrivSqZeroExt.map_comp_map, ← TrivSqZeroExt.map_comp_map, LinearMap.fst_comp_inl, LinearMap.fst_comp_inr, hz]
    change _ * smT (𝟙 (Sp R)) 0 (tv v) = _
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem, _root_.mul_one, hid]
  have hsnd : homAt (𝟙 (Sp R)) (tm (LinearMap.snd R R R)) ≫ P = tv v := by
    simp only [P]
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp,
      ← TrivSqZeroExt.map_comp_map, ← TrivSqZeroExt.map_comp_map, LinearMap.snd_comp_inl, LinearMap.snd_comp_inr, hz]
    change smT (𝟙 (Sp R)) 0 (tv u) * _ = _
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem, _root_.one_mul, hid]
  have hsum : homAt (𝟙 (Sp R)) (tm (LinearMap.coprod (LinearMap.id : R →ₗ[R] R) LinearMap.id)) ≫ P = tv (u + v) := by
    simp only [P]
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp,
      ← TrivSqZeroExt.map_comp_map, ← TrivSqZeroExt.map_comp_map, LinearMap.coprod_inl, LinearMap.coprod_inr,
      hid, hid, ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_add]
  have hP : P.left (IsLocalRing.closedPoint (TrivSqZeroExt R (R × R))) = origin G := by
    have e : spMap ((tm (LinearMap.fst R R R) : TrivSqZeroExt R (R × R) →ₐ[R] DualNumber R) :
        TrivSqZeroExt R (R × R) →+* DualNumber R) ≫ P.left = (tv u).left := congrArg (fun q => q.left) hfst
    haveI := isLocalHom_map (LinearMap.fst R R R)
    have e0 : spMap ((tm (LinearMap.fst R R R) : TrivSqZeroExt R (R × R) →ₐ[R] DualNumber R) :
        TrivSqZeroExt R (R × R) →+* DualNumber R) (IsLocalRing.closedPoint (DualNumber R)) =
        IsLocalRing.closedPoint (TrivSqZeroExt R (R × R)) :=
      Spec_closedPoint (f := CommRingCat.ofHom _)
    rw [← e0, ← tv_closedPoint G u, ← e]
    rfl
  have key : ∀ (L : R × R →ₗ[R] R) (w : TanM (𝟙 (Sp R)) G), homAt (𝟙 (Sp R)) (tm L) ≫ P = tv w →
      tanDer G w f = L (valAt P.left (origin G) hP f).snd := by
    intro L w hw
    haveI := isLocalHom_map L
    have e : (tv w).left = spMap ((tm L : TrivSqZeroExt R (R × R) →ₐ[R] DualNumber R) :
        TrivSqZeroExt R (R × R) →+* DualNumber R) ≫ P.left := (congrArg (fun q => q.left) hw).symm
    have hy : (spMap ((tm L : TrivSqZeroExt R (R × R) →ₐ[R] DualNumber R) :
        TrivSqZeroExt R (R × R) →+* DualNumber R) ≫ P.left) (IsLocalRing.closedPoint (DualNumber R)) = origin G :=
      e ▸ tv_closedPoint G w
    rw [tanDer_eq]
    change (valAt (tv w).left (origin G) (tv_closedPoint G w) f).snd = _
    rw [valAt_congr e (origin G) _ hy, valAt_comp _ P.left (origin G) hP hy]
    simp [tm]
  rw [key _ _ hsum, key _ _ hfst, key _ _ hsnd]
  simp

end GlobalTheory.CoordsOrigin
