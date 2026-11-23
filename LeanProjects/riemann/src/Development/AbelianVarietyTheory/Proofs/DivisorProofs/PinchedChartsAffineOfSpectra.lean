import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.Pinch.Aff

theorem pinched_of_iso (g : ℕ) {S S' Z B' C Y B₂ C₂ Y₂ : Scheme.{0}} {s' : S' ⟶ S} {z : Z ⟶ S}
    {b' : B' ⟶ S'} {e : C ⟶ Z} {i : Y ⟶ B'} {q : Y ⟶ C}
    {b₂ : B₂ ⟶ S'} {e₂ : C₂ ⟶ Z} {i₂ : Y₂ ⟶ B₂} {q₂ : Y₂ ⟶ C₂}
    (eB : B' ≅ B₂) (eC : C ≅ C₂) (eY : Y ≅ Y₂)
    (hb : b' = eB.hom ≫ b₂) (he : e = eC.hom ≫ e₂) (hi : i ≫ eB.hom = eY.hom ≫ i₂)
    (hq : q ≫ eC.hom = eY.hom ≫ q₂) (x : B') (h : Pinched g s' z b₂ e₂ i₂ q₂ (eB.hom x)) :
    Pinched g s' z b' e i q x := by
  obtain ⟨U, U', V, u, p, j, n, k, hu, hp, hj, hx, hn, hl⟩ := h
  refine ⟨U, U', V, u, p, j ≫ eB.inv, n, k ≫ eC.inv, hu, ?_, inferInstance, ?_, ?_, ?_⟩
  · simpa [hb] using hp
  · obtain ⟨t, ht⟩ := hx
    refine ⟨t, ?_⟩
    simp [ht]
  · simpa [he] using hn
  · intro T a a' h
    obtain ⟨y, hy1, hy2⟩ := hl T a a' h
    refine ⟨y ≫ eY.inv, ?_, ?_⟩
    · have : eY.inv ≫ i = i₂ ≫ eB.inv := by
        rw [Iso.inv_comp_eq, ← Category.assoc, ← hi]; simp
      rw [Category.assoc, this, ← Category.assoc, hy1, Category.assoc]
    · have : eY.inv ≫ q = q₂ ≫ eC.inv := by
        rw [Iso.inv_comp_eq, ← Category.assoc, ← hq]; simp
      rw [Category.assoc, this, ← Category.assoc, hy2, Category.assoc]

theorem isPushout_of_isPullback_Spec {A B C D : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C} {h : B ⟶ D}
    {k : C ⟶ D} (H : IsPullback (Spec.map h) (Spec.map k) (Spec.map f) (Spec.map g)) :
    IsPushout f g h k := by
  have w : k.op ≫ g.op = h.op ≫ f.op := by
    apply Quiver.Hom.unop_inj
    simp only [unop_comp, Quiver.Hom.unop_op]
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp]
    exact H.w.symm
  exact (IsPullback.of_map Scheme.Spec w H.flip).unop

end GlobalTheory.Pinch.Aff

namespace GlobalTheory.Pinch.Aff

theorem pinched_affine_of_spec : (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (R' : Type) [CommRing R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (g : ℕ) (C' D E : Type) [CommRing C'] [CommRing D] [CommRing E] (φ : R' →+* C') (δ : R ⧸ c →+* D) (π : C' →+* E) (ψ : D →+* E), φ.Smooth → δ.IsStandardSmoothOfRelativeDimension g → IsPushout (CommRingCat.ofHom (φ.comp (algebraMap R R'))) (CommRingCat.ofHom (Ideal.Quotient.mk c)) (CommRingCat.ofHom π) (CommRingCat.ofHom (ψ.comp δ)) → IsPushout (CommRingCat.ofHom (δ.comp (Ideal.Quotient.mk c))) (CommRingCat.ofHom (algebraMap R R')) (CommRingCat.ofHom ψ) (CommRingCat.ofHom (π.comp φ)) → ∀ y : Sp E, GlobalTheory.Pinch.Pinched g (spMap (algebraMap R R')) (spMap (Ideal.Quotient.mk c)) (spMap φ) (spMap δ) (spMap π) (spMap ψ) (spMap π y)) → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (R' : Type) [CommRing R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (g : ℕ) (B' C Y : Scheme.{0}) (b' : B' ⟶ Sp R') (e : C ⟶ Sp (R ⧸ c)) (i : Y ⟶ B') (q : Y ⟶ C), IsAffine B' → IsAffine C → Smooth b' → e.appTop.hom.IsStandardSmoothOfRelativeDimension g → IsPullback i (q ≫ e) (b' ≫ spMap (algebraMap R R')) (spMap (Ideal.Quotient.mk c)) → IsPullback q (i ≫ b') (e ≫ spMap (Ideal.Quotient.mk c)) (spMap (algebraMap R R')) → ∀ y : Y, GlobalTheory.Pinch.Pinched g (spMap (algebraMap R R')) (spMap (Ideal.Quotient.mk c)) b' e i q (i y) := by
  intro H R _ _ R' _ _ _ hinj c hc g B' C Y b' e i q hB hC hsm hss h1 h2 y
  haveI : IsAffine Y := IsAffine.of_isPullback h1
  haveI := hsm
  set φc : CommRingCat.of R' ⟶ Γ(B', ⊤) := Spec.preimage (B'.isoSpec.inv ≫ b') with hφc
  set δc : CommRingCat.of (R ⧸ c) ⟶ Γ(C, ⊤) := Spec.preimage (C.isoSpec.inv ≫ e) with hδc
  set πc : Γ(B', ⊤) ⟶ Γ(Y, ⊤) := Spec.preimage (Y.isoSpec.inv ≫ i ≫ B'.isoSpec.hom) with hπc
  set ψc : Γ(C, ⊤) ⟶ Γ(Y, ⊤) := Spec.preimage (Y.isoSpec.inv ≫ q ≫ C.isoSpec.hom) with hψc
  have eφ : spMap φc.hom = B'.isoSpec.inv ≫ b' := by simp [spMap, φc]
  have eδ : spMap δc.hom = C.isoSpec.inv ≫ e := by simp [spMap, δc]
  have eπ : spMap πc.hom = Y.isoSpec.inv ≫ i ≫ B'.isoSpec.hom := by simp [spMap, πc]
  have eψ : spMap ψc.hom = Y.isoSpec.inv ≫ q ≫ C.isoSpec.hom := by simp [spMap, ψc]
  have hφs : φc.hom.Smooth := by
    rw [← HasRingHomProperty.Spec_iff (P := @Smooth), hφc, Spec.map_preimage]
    infer_instance
  have hδ : δc = (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ c))).inv ≫ e.appTop := by
    apply Spec.map_injective
    rw [hδc, Spec.map_preimage, Spec.map_comp, Iso.inv_comp_eq, ← Category.assoc,
      Scheme.isoSpec_hom_naturality, Category.assoc, Scheme.isoSpec_Spec_hom, ← Spec.map_comp,
      Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  have hδs : δc.hom.IsStandardSmoothOfRelativeDimension g := by
    rw [hδ, CommRingCat.hom_comp]
    exact (RingHom.isStandardSmoothOfRelativeDimension_respectsIso.cancel_left_isIso _ _).mpr hss
  have hp1 : IsPushout (CommRingCat.ofHom (φc.hom.comp (algebraMap R R'))) (CommRingCat.ofHom (Ideal.Quotient.mk c))
      (CommRingCat.ofHom πc.hom) (CommRingCat.ofHom (ψc.hom.comp δc.hom)) := by
    apply isPushout_of_isPullback_Spec
    simp only [CommRingCat.ofHom_comp, Spec.map_comp]
    change IsPullback (spMap πc.hom) (spMap ψc.hom ≫ spMap δc.hom) (spMap φc.hom ≫ spMap (algebraMap R R'))
      (spMap (Ideal.Quotient.mk c))
    rw [eφ, eδ, eπ, eψ]
    refine IsPullback.of_iso h1 Y.isoSpec B'.isoSpec (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp
  have hp2 : IsPushout (CommRingCat.ofHom (δc.hom.comp (Ideal.Quotient.mk c))) (CommRingCat.ofHom (algebraMap R R'))
      (CommRingCat.ofHom ψc.hom) (CommRingCat.ofHom (πc.hom.comp φc.hom)) := by
    apply isPushout_of_isPullback_Spec
    simp only [CommRingCat.ofHom_comp, Spec.map_comp]
    change IsPullback (spMap ψc.hom) (spMap πc.hom ≫ spMap φc.hom) (spMap δc.hom ≫ spMap (Ideal.Quotient.mk c))
      (spMap (algebraMap R R'))
    rw [eφ, eδ, eπ, eψ]
    refine IsPullback.of_iso h2 Y.isoSpec C.isoSpec (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp
  have hP := H R R' hinj c hc g Γ(B', ⊤) Γ(C, ⊤) Γ(Y, ⊤) φc.hom δc.hom πc.hom ψc.hom hφs hδs hp1 hp2
    (Y.isoSpec.hom y)
  have hpt : spMap πc.hom (Y.isoSpec.hom y) = B'.isoSpec.hom (i y) := by
    rw [eπ]; simp
  rw [hpt] at hP
  refine pinched_of_iso g B'.isoSpec C.isoSpec Y.isoSpec ?_ ?_ ?_ ?_ (i y) hP
  · rw [eφ]; simp
  · rw [eδ]; simp
  · rw [eπ]; simp
  · rw [eψ]; simp

end GlobalTheory.Pinch.Aff
