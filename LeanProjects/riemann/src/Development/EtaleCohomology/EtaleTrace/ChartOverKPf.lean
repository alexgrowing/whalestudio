import Development.EtaleCohomology.EtaleTrace.GenOutChartPfGen

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

theorem sect_eq_of_alg (X : Scheme.{0}) [IsIntegral X] (U : X.Opens) (s t : Γ(X, U))
    (h : ∀ (y : X) (hy : y ∈ U), algebraMap (X.presheaf.stalk y) X.functionField (X.presheaf.germ U y hy s) =
      algebraMap (X.presheaf.stalk y) X.functionField (X.presheaf.germ U y hy t)) : s = t := by
  apply TopCat.Presheaf.section_ext X.sheaf
  intro y hy
  have : Nonempty U := ⟨⟨y, hy⟩⟩
  have hst : s = t := by
    apply Scheme.germToFunctionField_injective X U
    have := h y hy
    rwa [Scheme.algebraMap_germ_eq_germToFunctionField, Scheme.algebraMap_germ_eq_germToFunctionField] at this
  rw [hst]

theorem fromZero_eq_mk {k : Type} [Field k] {N : ℕ} (i : Fin (N + 1))
    (hx : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 1) (c : k)
    (hg : (C c : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k (0 • 1)) :
    HomogeneousLocalization.fromZeroRingHom (homogeneousSubmodule (Fin (N + 1)) k) (Submonoid.powers (MvPolynomial.X i))
      (algebraMap k (homogeneousSubmodule (Fin (N + 1)) k 0) c) = HomogeneousLocalization.Away.mk _ hx 0 (C c) hg := by
  apply HomogeneousLocalization.val_injective
  simp [HomogeneousLocalization.fromZeroRingHom]
  rfl

theorem chart_key {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField) (i : Fin (N + 1)) (U : X.Opens)
  (hx : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 1)
  (φ : HomogeneousLocalization.Away (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) →+* Γ(X, U))
  (hφ : ∀ (y : X) (hy : y ∈ U) (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k)
      (hg : g ∈ homogeneousSubmodule (Fin (N + 1)) k (m • 1)),
      algebraMap (X.presheaf.stalk y) X.functionField
        (X.presheaf.germ U y hy (φ (HomogeneousLocalization.Away.mk _ hx m g hg))) = eval₂ (kHom p) w g / w i ^ m) :
  (CommRingCat.ofHom (algebraMap k (homogeneousSubmodule (Fin (N + 1)) k 0)) ≫
      CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom (homogeneousSubmodule (Fin (N + 1)) k)
        (Submonoid.powers (MvPolynomial.X i)))) ≫ CommRingCat.ofHom ((U.topIso.inv.hom).comp φ) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (U.ι ≫ p).appTop := by
  ext c
  have hg : (C c : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k (0 • 1) :=
    (mem_homogeneousSubmodule _ _).2 (by simpa using isHomogeneous_C (Fin (N + 1)) c)
  have hsec : φ (HomogeneousLocalization.Away.mk _ hx 0 (C c) hg) =
      X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op (p.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)) := by
    apply sect_eq_of_alg X
    intro y hy
    rw [hφ, TopCat.Presheaf.germ_res_apply]
    have : Nonempty (⊤ : X.Opens) := ⟨⟨y, trivial⟩⟩
    rw [Scheme.algebraMap_germ_eq_germToFunctionField]
    simp [kHom]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
  rw [fromZero_eq_mk i hx c hg, hsec]
  simp only [Scheme.Hom.comp_appTop, Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv, CommRingCat.hom_comp,
    RingHom.comp_apply]
  erw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem ChartOverK_of : ChartOverK := by
  intro k _ X _ p N w i hi U hx φ hφ
  have hR : U.ι ≫ p = U.toScheme.toSpecΓ ≫ Spec.map ((U.ι ≫ p).appTop) ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv := by
    rw [← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have key := chart_key p N w i U hx φ hφ
  rw [hR]
  unfold chartMor PNto
  simp only [Category.assoc]
  rw [Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp, ← key]
  simp only [Spec.map_comp, Category.assoc]
  rfl

end LateralTheory.EtaleTrace.Cov
