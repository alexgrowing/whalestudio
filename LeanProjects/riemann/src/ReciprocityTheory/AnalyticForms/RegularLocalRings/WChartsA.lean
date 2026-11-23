import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjBCompl

namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

theorem mem_nonZeroDivisors_of_bijective {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hb : Function.Bijective φ) {a : R} (ha : a ∈ nonZeroDivisors R) : φ a ∈ nonZeroDivisors S := by
  have key : ∀ x : S, x * φ a = 0 → x = 0 := by
    intro x hx
    obtain ⟨z, rfl⟩ := hb.2 x
    have hz : z * a = 0 := hb.1 (by rw [map_mul, map_zero]; exact hx)
    rw [(mem_nonZeroDivisors_iff.mp ha).2 z hz, map_zero]
  exact mem_nonZeroDivisors_iff.mpr ⟨fun x hx => key x (by rwa [mul_comm] at hx), key⟩

theorem isAffineOpen_of_iso {W : Scheme.{0}} (V : W.Opens) {A : CommRingCat.{0}}
    (e : V.toScheme ≅ Spec A) : IsAffineOpen V :=
  IsAffine.of_isIso e.hom

theorem sec_mem_nonZeroDivisors {W : Scheme.{0}} (V : W.Opens) {A : CommRingCat.{0}}
    (e : V.toScheme ≅ Spec A) {a : A} (ha : a ∈ nonZeroDivisors A) :
    V.topIso.hom (e.hom.appTop ((Scheme.ΓSpecIso A).inv a)) ∈ nonZeroDivisors Γ(W, V) := by
  have : IsIso e.hom.appTop := inferInstanceAs (IsIso (e.hom.app ⊤))
  have hb : Function.Bijective ((V.topIso.hom.hom).comp ((e.hom.appTop).hom.comp
      (Scheme.ΓSpecIso A).inv.hom)) :=
    (ConcreteCategory.bijective_of_isIso V.topIso.hom).comp
      ((ConcreteCategory.bijective_of_isIso e.hom.appTop).comp
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).inv))
  exact mem_nonZeroDivisors_of_bijective _ hb ha

theorem sec_algebraMap_of_iso {X W : Scheme.{0}} (π : W ⟶ X) (U : X.affineOpens) (V : W.Opens)
    (hV : V ≤ π ⁻¹ᵁ U.1) (A : Type) [CommRing A] [Algebra Γ(X, U.1) A]
    (e : V.toScheme ≅ Spec (.of A))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) A)) ≫ U.2.fromSpec = V.ι ≫ π)
    (r : Γ(X, U.1)) :
    V.topIso.hom (e.hom.appTop ((Scheme.ΓSpecIso (.of A)).inv (algebraMap _ A r))) = π.appLE _ V hV r := by
  have hVa := isAffineOpen_of_iso V e
  have h1 := IsAffineOpen.SpecMap_appLE_fromSpec π U.2 hVa hV
  have : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  have : Mono U.2.fromSpec := IsOpenImmersion.mono _
  have h3 : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) A)) =
      hVa.isoSpec.hom ≫ Spec.map (π.appLE _ V hV) := by
    rw [← cancel_mono U.2.fromSpec, Category.assoc, he, Category.assoc, h1, ← Category.assoc,
      IsAffineOpen.isoSpec_hom_fromSpec]
  have n1 : (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) A))).appTop
      ((Scheme.ΓSpecIso _).inv r) = (Scheme.ΓSpecIso (.of A)).inv (algebraMap _ A r) := by
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    rfl
  have n2 : (Spec.map (π.appLE _ V hV)).appTop ((Scheme.ΓSpecIso _).inv r) =
      (Scheme.ΓSpecIso _).inv (π.appLE _ V hV r) := by
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  have n3 : ∀ x : Γ(W, V), hVa.isoSpec.hom.appTop ((Scheme.ΓSpecIso _).inv x) = V.topIso.inv x := by
    intro x
    rw [IsAffineOpen.isoSpec_hom_appTop, CommRingCat.comp_apply, ← CommRingCat.comp_apply
      (Scheme.ΓSpecIso _).inv, Iso.inv_hom_id, CommRingCat.id_apply]
  calc V.topIso.hom (e.hom.appTop ((Scheme.ΓSpecIso (.of A)).inv (algebraMap _ A r)))
      = V.topIso.hom ((e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) A))).appTop
          ((Scheme.ΓSpecIso _).inv r)) := by
        rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, n1]
    _ = V.topIso.hom ((hVa.isoSpec.hom ≫ Spec.map (π.appLE _ V hV)).appTop
          ((Scheme.ΓSpecIso _).inv r)) := by rw [h3]; rfl
    _ = π.appLE _ V hV r := by
        rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
        erw [n2, n3]
        rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

theorem germ_mem_nonZeroDivisors {W : Scheme.{0}} {V : W.Opens} (hV : IsAffineOpen V) {a : Γ(W, V)}
    (ha : a ∈ nonZeroDivisors Γ(W, V)) (w : W) (hw : w ∈ V) :
    W.presheaf.germ V w hw a ∈ nonZeroDivisors (W.presheaf.stalk w) := by
  let := TopCat.Presheaf.algebra_section_stalk W.presheaf ⟨w, hw⟩
  have := hV.isLocalization_stalk ⟨w, hw⟩
  have h := IsLocalization.map_nonZeroDivisors_le (hV.primeIdealOf ⟨w, hw⟩).asIdeal.primeCompl
    (W.presheaf.stalk w) (Submonoid.mem_map_of_mem (algebraMap Γ(W, V) (W.presheaf.stalk w)) ha)
  exact h

theorem res_mem_nonZeroDivisors {W : Scheme.{0}} {V O : W.Opens} (h : O ≤ V) (hV : IsAffineOpen V)
    {a : Γ(W, V)} (ha : a ∈ nonZeroDivisors Γ(W, V)) :
    W.presheaf.map (homOfLE h).op a ∈ nonZeroDivisors Γ(W, O) := by
  have key : ∀ x : Γ(W, O), x * W.presheaf.map (homOfLE h).op a = 0 → x = 0 := by
    intro x hx
    refine TopCat.Presheaf.section_ext W.sheaf O x 0 (fun w hw => ?_)
    have hg := germ_mem_nonZeroDivisors hV ha w (h hw)
    have h1 : W.presheaf.germ O w hw x * W.presheaf.germ V w (h hw) a = 0 := by
      rw [← W.presheaf.germ_res_apply (homOfLE h) w hw a, ← map_mul, hx, map_zero]
    change W.presheaf.germ O w hw x = W.presheaf.germ O w hw 0
    rw [(mem_nonZeroDivisors_iff.mp hg).2 _ h1, map_zero]
  exact mem_nonZeroDivisors_iff.mpr ⟨fun x hx => key x (by rwa [mul_comm] at hx), key⟩

end

end ReciprocityTheory.AnForm.R
