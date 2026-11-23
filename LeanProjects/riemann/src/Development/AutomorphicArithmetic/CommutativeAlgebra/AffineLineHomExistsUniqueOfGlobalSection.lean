import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC UpperTheory.Pbf

private theorem comp_gamma {T : Scheme.{0}} (φ : Polynomial ℤ →+* Γ(T, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℤ))).inv ≫
      (T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)).appTop = CommRingCat.ofHom φ := by
  rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
  erw [Scheme.ΓSpecIso_naturality]
  exact Iso.inv_hom_id_assoc _ _

theorem UpperTheory.affineLine_hom_existsUnique_of_globalSection :
    ∀ (T : Scheme.{0}) (a : Γ(T, ⊤)), ∃! s : T ⟶ A1, s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℤ))).inv.hom Polynomial.X) = a := by
  intro T a
  have key : ∀ s : T ⟶ A1, s = T.toSpecΓ ≫
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℤ))).inv ≫ s.appTop) := by
    intro s
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  let φ : Polynomial ℤ →+* Γ(T, ⊤) := Polynomial.eval₂RingHom (Int.castRingHom _) a
  refine ⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ), ?_, ?_⟩
  · have h : ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℤ))).inv ≫
        (T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)).appTop).hom Polynomial.X = a := by
      rw [comp_gamma]
      simp [φ]
    rw [CommRingCat.hom_comp, RingHom.comp_apply] at h
    exact h
  · intro s hs
    suffices e : (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℤ))).inv ≫ s.appTop =
        CommRingCat.ofHom φ by
      rw [key s, e]
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext'
    · exact RingHom.ext_int _ _
    · rw [CommRingCat.hom_comp, RingHom.comp_apply, hs]
      simp [φ]
