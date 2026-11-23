import Mathlib
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory

theorem spec_local_point_descends {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] {T : Type} [CommRing T] [IsLocalRing T]
    (v : Spec (CommRingCat.of T) ⟶ X) :
    ∃ s : Finset T, ∀ (S : Type) [CommRing S] (φ : S →+* T), Function.Injective φ →
      (↑s : Set T) ⊆ Set.range φ → ∃ w : Spec (CommRingCat.of S) ⟶ X,
        Spec.map (CommRingCat.ofHom φ) ≫ w = v := by
  classical
  obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
    (show v (IsLocalRing.closedPoint T) ∈ (⊤ : X.Opens) from trivial)
  have hU' : IsAffineOpen U := hU
  have hr : Set.range v ⊆ Set.range hU'.fromSpec := by
    rw [hU'.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint y).map v.continuous).mem_open U.isOpen hxU
  have hv₁ := IsOpenImmersion.lift_fac hU'.fromSpec v hr
  rw [← Spec.map_preimage (IsOpenImmersion.lift hU'.fromSpec v hr)] at hv₁
  set g := Spec.preimage (IsOpenImmersion.lift hU'.fromSpec v hr) with hg

  have hft₁ : (f.appLE ⊤ U le_top).hom.FiniteType :=
    LocallyOfFiniteType.finiteType_appLE f (isAffineOpen_top _) hU' le_top
  have hft₀ : (algebraMap ℤ Γ(Spec (CommRingCat.of R), ⊤)).FiniteType := by
    have h1 : (algebraMap ℤ R).FiniteType := RingHom.finiteType_algebraMap.2 inferInstance
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.surjective
    have := h2.comp h1
    convert this using 1
    exact RingHom.ext_int _ _
  have hftU : (algebraMap ℤ Γ(X, U)).FiniteType := by
    have := hft₁.comp hft₀
    convert this using 1
    exact RingHom.ext_int _ _
  have hftA : Algebra.FiniteType ℤ Γ(X, U) := RingHom.finiteType_algebraMap.1 hftU
  obtain ⟨t, ht⟩ := hftA.out
  refine ⟨t.image g.hom, fun S _ φ hφ hs => ?_⟩
  have hmem : ∀ a : Γ(X, U), g.hom a ∈ φ.range := by
    intro a
    have ha : a ∈ Algebra.adjoin ℤ (t : Set Γ(X, U)) := by rw [ht]; exact Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem b hb =>
      obtain ⟨c, hc⟩ := hs (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hb))
      exact ⟨c, hc⟩
    | algebraMap n => exact ⟨(n : S), by simp⟩
    | add b c _ _ hb hc => rw [map_add]; exact φ.range.add_mem hb hc
    | mul b c _ _ hb hc => rw [map_mul]; exact φ.range.mul_mem hb hc
  let e : S ≃+* φ.range := RingEquiv.ofBijective φ.rangeRestrict
    ⟨fun a b h => hφ (congrArg Subtype.val h), φ.rangeRestrict_surjective⟩
  let g' : Γ(X, U) →+* S := (e.symm : φ.range →+* S).comp (g.hom.codRestrict φ.range hmem)
  have hcomp : φ.comp g' = g.hom := by
    ext a
    exact congrArg Subtype.val (e.apply_symm_apply (g.hom.codRestrict φ.range hmem a))
  refine ⟨Spec.map (CommRingCat.ofHom g') ≫ hU'.fromSpec, ?_⟩
  rw [← hv₁, ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext a
  exact congrArg (fun h : Γ(X, U) →+* T => h a) hcomp

end GlobalTheory
