import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulCoeEqZero
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory Formalism.L2.Pj GlobalTheory.Serre GlobalTheory.RayEv GlobalTheory.ExpUniqCh0

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExpCancel

theorem isLocalRing_tsze {S : Type} [Field S] (M : Type) [AddCommGroup M] [Module S M] [Module Sᵐᵒᵖ M]
    [IsCentralScalar S M] : IsLocalRing (TrivSqZeroExt S M) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
    exact IsLocalRing.isUnit_or_isUnit_one_sub_self _

theorem isLocalHom_incl {S : Type} [Field S] {A : Type} [CommRing A] [Algebra S A] [IsLocalRing A]
    (J : Ideal A) [Module Sᵐᵒᵖ J] [IsCentralScalar S J] (hJ : J ^ 2 = ⊥) :
    IsLocalHom (incl (S := S) J hJ).toRingHom := by
  constructor
  intro x hx
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
  by_contra h0
  have hf : x.fst = 0 := by
    by_contra hne; exact h0 (isUnit_iff_ne_zero.mpr hne)
  have e : (incl (S := S) J hJ).toRingHom x = (x.snd : A) := by
    show incl (S := S) J hJ x = _
    rw [incl_apply, hf, map_zero, zero_add]
  rw [e] at hx
  have h2 : (x.snd : A) * (x.snd : A) = 0 := mul_coe_eq_zero J hJ x.snd x.snd
  obtain ⟨w, hw⟩ := hx.exists_left_inv
  have : (1 : A) = 0 := by
    calc (1 : A) = (w * w) * ((x.snd : A) * (x.snd : A)) := by
          rw [show (w * w) * ((x.snd : A) * (x.snd : A)) = (w * (x.snd : A)) * (w * (x.snd : A)) by ring, hw, _root_.one_mul]
      _ = 0 := by rw [h2, mul_zero]
  exact one_ne_zero this

theorem ext_of_local {B C : Type} [CommRing B] [CommRing C] [IsLocalRing B] [IsLocalRing C]
    (d : B →+* C) [IsLocalHom d] (hd : Function.Injective d)
    {X : Scheme.{0}} (a b : Sp B ⟶ X) (h1 : spMap d ≫ a = spMap d ≫ b) : a = b := by
  obtain ⟨⟨x, f, hf⟩, rfl⟩ := (SpecToEquivOfLocalRing X (CommRingCat.of B)).symm.surjective a
  obtain ⟨⟨y, g, hg⟩, rfl⟩ := (SpecToEquivOfLocalRing X (CommRingCat.of B)).symm.surjective b
  have l1 : ∀ (z : X) (φ : X.presheaf.stalk z ⟶ CommRingCat.of B),
      IsLocalHom φ.hom → IsLocalHom (φ ≫ CommRingCat.ofHom d).hom := by
    intro z φ _
    rw [CommRingCat.hom_comp]; exact RingHom.isLocalHom_comp d φ.hom
  have k1 : (⟨x, f ≫ CommRingCat.ofHom d, l1 x f hf⟩ :
      Σ z : X, {φ : X.presheaf.stalk z ⟶ CommRingCat.of C // IsLocalHom φ.hom}) =
        ⟨y, g ≫ CommRingCat.ofHom d, l1 y g hg⟩ := by
    apply (SpecToEquivOfLocalRing X (CommRingCat.of C)).symm.injective
    simpa [SpecToEquivOfLocalRing] using h1
  obtain rfl : x = y := congrArg Sigma.fst k1
  have h5 : f ≫ CommRingCat.ofHom d = g ≫ CommRingCat.ofHom d :=
    congrArg Subtype.val (eq_of_heq (Sigma.mk.inj k1).2)
  obtain rfl : f = g := by
    ext s
    exact hd (congrArg (fun k => k.hom s) h5)
  rfl

end GlobalTheory.ExpCancel

theorem GlobalTheory.ExpCancel.cancel_incl : ∀ {X : Scheme.{0}} {G : Over X} {S : Type} [Field S] (x0 : Sp S ⟶ X)
    {A : Type} [CommRing A] [Algebra S A] [IsLocalRing A] (J : Ideal A) [Module Sᵐᵒᵖ J] [IsCentralScalar S J]
    (hJ : J ^ 2 = ⊥), Function.Injective (incl (S := S) J hJ) →
    ∀ u v : overAt x0 (TrivSqZeroExt S J) ⟶ G, Formalism.L2.Pj.homAt x0 (incl (S := S) J hJ) ≫ u = Formalism.L2.Pj.homAt x0 (incl (S := S) J hJ) ≫ v → u = v := by
  intro X G S _ x0 A _ _ _ J _ _ hJ hinj u v h
  letI := GlobalTheory.ExpCancel.isLocalRing_tsze (S := S) J
  haveI := GlobalTheory.ExpCancel.isLocalHom_incl (S := S) J hJ
  ext1
  have h' := congrArg CommaMorphism.left h
  simp only [Over.comp_left] at h'
  exact GlobalTheory.ExpCancel.ext_of_local (incl (S := S) J hJ).toRingHom hinj u.left v.left h'
