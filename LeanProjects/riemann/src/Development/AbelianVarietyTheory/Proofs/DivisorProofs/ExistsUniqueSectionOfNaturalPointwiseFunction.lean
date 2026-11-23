import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PtAlgSpOver
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NaturalPointwiseCochainConstOfGlobalSectionsBase

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.NatSec

theorem nat_of_comp (R : Type) [CommRing R] (Y : Over (Sp R)) (U : Y.left.Opens) (t : Fn0 Y)
    (ht : ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : E →ₐ[R] E')
      (z : Pt Y E), ⊤ ≤ z.left ⁻¹ᵁ U → t E' (spOver ψ ≫ z) = ψ (t E z))
    (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →+* D')
    (x : Pt Y D) (x' : Pt Y D') (hx : ⊤ ≤ x.left ⁻¹ᵁ U) (h : spMap φ ≫ x.left = x'.left) :
    t D' x' = φ (t D x) := by
  have h1 : x.left ≫ Y.hom = spMap (algebraMap R D) := Over.w x
  have h2 : x'.left ≫ Y.hom = spMap (algebraMap R D') := Over.w x'
  have h3 : CommRingCat.ofHom (algebraMap R D) ≫ CommRingCat.ofHom φ = CommRingCat.ofHom (algebraMap R D') := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    change spMap φ ≫ spMap _ = spMap _
    rw [← h1, ← h2, ← h, Category.assoc]
  let ψ : D →ₐ[R] D' := ⟨φ, fun r ↦ congrArg (fun f ↦ CommRingCat.Hom.hom f r) h3⟩
  have h4 := ht D D' ψ x hx
  have h5 : spOver ψ ≫ x = x' := Over.OverMorphism.ext h
  rw [h5] at h4
  exact h4

theorem fromSpecStalk_top {X : Scheme.{0}} (x : X) (U : X.Opens) (hx : x ∈ U) :
    ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ U := by
  intro z _
  have hz : X.fromSpecStalk x z ⤳ x := by
    have : X.fromSpecStalk x z ∈ Set.range (X.fromSpecStalk x) := ⟨z, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  exact hz.mem_open U.2 hx

theorem fromSpecStalk_appLE {X : Scheme.{0}} (x : X) (U : X.Opens) (hx : x ∈ U) :
    (X.fromSpecStalk x).appLE U ⊤ (fromSpecStalk_top x U hx) =
      X.presheaf.germ U x hx ≫ (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv := by
  rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
  simp only [Category.assoc, ← Functor.map_comp]
  have e : ((homOfLE le_top).op ≫ (homOfLE (fromSpecStalk_top x U hx)).op :
      Opposite.op (⊤ : (Spec (X.presheaf.stalk x)).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ := rfl
  rw [e, CategoryTheory.Functor.map_id, Category.comp_id]

theorem ext_of_evU (R : Type) [CommRing R] (Y : Over (Sp R)) (U : Y.left.Opens) (a a' : Γ(Y.left, U))
    (h : ∀ (E : Type) [CommRing E] [Algebra R E] (z : Pt Y E), ⊤ ≤ z.left ⁻¹ᵁ U →
      evU z.left U a = evU z.left U a') : a = a' := by
  refine TopCat.Presheaf.section_ext Y.left.sheaf U a a' fun y hy ↦ ?_
  let S : CommRingCat.{0} := Y.left.presheaf.stalk y
  letI al : Algebra R S := (Spec.preimage (R := CommRingCat.of R) (Y.left.fromSpecStalk y ≫ Y.hom)).hom.toAlgebra
  let z : Pt Y S := Over.homMk (Y.left.fromSpecStalk y)
    (Spec.map_preimage (R := CommRingCat.of R) (Y.left.fromSpecStalk y ≫ Y.hom)).symm
  have hz : ⊤ ≤ z.left ⁻¹ᵁ U := fromSpecStalk_top y U hy
  have e := h S z hz
  unfold evU at e
  rw [dif_pos hz, dif_pos hz] at e
  unfold evalAt at e
  change (Scheme.ΓSpecIso S).hom ((Y.left.fromSpecStalk y).appLE U ⊤ hz a) =
    (Scheme.ΓSpecIso S).hom ((Y.left.fromSpecStalk y).appLE U ⊤ hz a') at e
  rw [fromSpecStalk_appLE y U hy] at e
  simp only [CommRingCat.comp_apply] at e
  change (Scheme.ΓSpecIso (Y.left.presheaf.stalk y)).hom _ = (Scheme.ΓSpecIso (Y.left.presheaf.stalk y)).hom _ at e
  simp only [Iso.inv_hom_id_apply] at e
  exact e

theorem exists_unique_section : ∀ (R : Type) [CommRing R] (Y : Over (Sp R)) (U : Y.left.Opens) (t : Fn0 Y), (∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : E →ₐ[R] E') (z : Pt Y E), ⊤ ≤ z.left ⁻¹ᵁ U → t E' (spOver ψ ≫ z) = ψ (t E z)) → ∃! a : Γ(Y.left, U), ∀ (E : Type) [CommRing E] [Algebra R E] (z : Pt Y E), ⊤ ≤ z.left ⁻¹ᵁ U → evU z.left U a = t E z := by
  intro R _ Y U t ht
  let Z : Scheme.{0} := U.toScheme
  let al : ∀ (D : CommRingCat.{0}) (x : Spec D ⟶ Z), Algebra R D := fun D x ↦
    (Spec.preimage (R := CommRingCat.of R) (x ≫ U.ι ≫ Y.hom)).hom.toAlgebra
  let pt : ∀ (D : CommRingCat.{0}) (x : Spec D ⟶ Z), @Pt R _ Y D _ (al D x) := fun D x ↦
    Over.homMk (x ≫ U.ι) (by rw [Category.assoc]; exact (Spec.map_preimage (R := CommRingCat.of R) (x ≫ U.ι ≫ Y.hom)).symm)
  have hin : ∀ (D : CommRingCat.{0}) (x : Spec D ⟶ Z), ⊤ ≤ (x ≫ U.ι) ⁻¹ᵁ U := by
    intro D x p _
    exact (x p).2
  let κ : ∀ D : CommRingCat.{0}, (Spec D ⟶ Z) → D := fun D x ↦ @t D _ (al D x) (pt D x)
  obtain ⟨s, hs⟩ := NatConst.exists_section Z (fun _ : Unit ↦ (⊤ : Z.Opens)) (by simp) κ
    fun D D' φ x _ ↦ @NatSec.nat_of_comp R _ Y U t ht D _ (al D x) D' _ (al D' (Spec.map φ ≫ x)) φ.hom
      (pt D x) (pt D' _) (hin D x) (by change Spec.map φ ≫ x ≫ U.ι = (Spec.map φ ≫ x) ≫ U.ι; rw [Category.assoc])
  have hex : ∀ (E : Type) [CommRing E] [Algebra R E] (z : Pt Y E), ⊤ ≤ z.left ⁻¹ᵁ U →
      evU z.left U (U.topIso.hom s) = t E z := by
    intro E _ inst z hz
    have hr : Set.range z.left ⊆ Set.range U.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨q, rfl⟩
      exact hz (Set.mem_univ q)
    let w : Spec (CommRingCat.of E) ⟶ Z := IsOpenImmersion.lift U.ι z.left hr
    have hw : w ≫ U.ι = z.left := IsOpenImmersion.lift_fac U.ι z.left hr
    have h1 : κ (CommRingCat.of E) w = t E z := by
      refine (@NatSec.nat_of_comp R _ Y U t ht E _ inst E _ (al (CommRingCat.of E) w) (RingHom.id E) z
        (pt (CommRingCat.of E) w) hz ?_)
      change Spec.map (CommRingCat.ofHom (RingHom.id E)) ≫ z.left = w ≫ U.ι
      rw [hw, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    rw [← h1, hs (CommRingCat.of E) w ⟨(), le_top⟩]
    unfold evU
    rw [dif_pos hz]
    unfold evalAt
    simp only [RingHom.comp_apply]
    congr 1
    have key : ∀ (g : Spec (CommRingCat.of E) ⟶ Y.left) (_ : w ≫ U.ι = g) (h : ⊤ ≤ g ⁻¹ᵁ U),
        g.appLE U ⊤ h = U.ι.appLE U ⊤ (by simp) ≫ w.appLE ⊤ ⊤ le_top := by
      rintro _ rfl h
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    rw [key _ hw hz, CommRingCat.comp_apply, Scheme.Opens.ι_appLE]
    have hid : ∀ (f : Opposite.op U ⟶ Opposite.op (U.ι ''ᵁ ⊤)) (g : Opposite.op (U.ι ''ᵁ ⊤) ⟶ Opposite.op U)
        (x : Γ(Y.left, U.ι ''ᵁ ⊤)), Y.left.presheaf.map f (Y.left.presheaf.map g x) = x := by
      intro f g x
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, Subsingleton.elim (g ≫ f) (𝟙 _),
        CategoryTheory.Functor.map_id]
      rfl
    rw [Scheme.Opens.topIso_hom]
    erw [hid]
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  refine ⟨U.topIso.hom s, hex, fun a ha ↦ ?_⟩
  exact NatSec.ext_of_evU R Y U a _ fun E _ _ z hz ↦ (ha E z hz).trans (hex E z hz).symm

end GlobalTheory.PtExt.NatSec
