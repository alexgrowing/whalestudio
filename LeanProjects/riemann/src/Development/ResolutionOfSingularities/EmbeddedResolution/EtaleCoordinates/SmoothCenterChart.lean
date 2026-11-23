import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateSubscheme
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.LocalNormalForm
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem algebraMap_quotient_map_mk {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    (I : Ideal R) (r : R) :
    algebraMap (R ⧸ I) (A ⧸ Ideal.map (algebraMap R A) I) (Ideal.Quotient.mk I r)
      = Ideal.Quotient.mk (Ideal.map (algebraMap R A) I) (algebraMap R A r) := rfl

private theorem algebraMap_quotient_apply {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    (I : Ideal R) (a : k) :
    algebraMap k (R ⧸ I) a = Ideal.Quotient.mk I (algebraMap k R a) := rfl

private theorem formallySmooth_quotient_map_of_isLocalization (k : Type u) [CommRing k] {R : Type u} [CommRing R]
    [Algebra k R] (M : Submonoid R) (A : Type u) [CommRing A] [Algebra R A] [IsLocalization M A]
    [Algebra k A] [IsScalarTower k R A] (I : Ideal R)
    (h : Algebra.FormallySmooth k (R ⧸ I)) :
    Algebra.FormallySmooth k (A ⧸ Ideal.map (algebraMap R A) I) := by
  have := h
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) M)
      (A ⧸ Ideal.map (algebraMap R A) I) := inferInstance
  have : Algebra.FormallyEtale (R ⧸ I) (A ⧸ Ideal.map (algebraMap R A) I) :=
    Algebra.FormallyEtale.of_isLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) M)
  have : IsScalarTower k (R ⧸ I) (A ⧸ Ideal.map (algebraMap R A) I) := by
    refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
    rw [algebraMap_quotient_apply I a, algebraMap_quotient_map_mk I (algebraMap k R a),
      algebraMap_quotient_apply (Ideal.map (algebraMap R A) I) a, IsScalarTower.algebraMap_apply k R A]
  exact Algebra.FormallySmooth.comp k (R ⧸ I) (A ⧸ Ideal.map (algebraMap R A) I)

private theorem map_algebraMap_eq_map_map_of_algEquiv {R L M : Type u} [CommRing R] [CommRing L]
    [CommRing M] [Algebra R L] [Algebra R M] (e : L ≃ₐ[R] M) (J : Ideal R) :
    Ideal.map (algebraMap R M) J
      = Ideal.map e.toAlgHom.toRingHom (Ideal.map (algebraMap R L) J) := by
  rw [Ideal.map_map]
  refine congrArg (fun φ : R →+* M => Ideal.map φ J) ?_
  exact RingHom.ext fun r => (e.commutes r).symm

private theorem ι_appLE_eq_topIso_inv {X : Scheme.{u}} (U : X.Opens)
    (e : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U) : U.ι.appLE U ⊤ e = U.topIso.inv := by
  rw [Scheme.Opens.ι_appLE U U ⊤ e, Scheme.Opens.topIso_inv]
  refine congrArg (fun h => X.presheaf.map h) ?_
  exact Quiver.Hom.unop_inj (Subsingleton.elim _ _)

private theorem ofIdealTop_ideal_top {Y : Scheme.{u}} (J : Ideal Γ(Y, ⊤))
    (hY : IsAffineOpen (⊤ : Y.Opens)) :
    (Scheme.IdealSheafData.ofIdealTop J).ideal ⟨⊤, hY⟩ = J := by
  rw [Scheme.IdealSheafData.ofIdealTop_ideal]
  have h1 : (homOfLE (le_refl (⊤ : Y.Opens)) : (⊤ : Y.Opens) ⟶ ⊤) = 𝟙 _ := rfl
  rw [h1, op_id, CategoryTheory.Functor.map_id]
  exact Ideal.map_id J

private theorem affineSpaceGlobalSectionsHom_eq_eval₂Hom (k : Type u) [Field k] (m : ℕ) :
    affineSpaceGlobalSectionsHom k m =
      MvPolynomial.eval₂Hom
        (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (affineSpaceFinToSpec k m).appTop).hom)
        (fun i : ULift.{u} (Fin m) => AffineSpace.coord (Spec (CommRingCat.of k)) i) := by
  show ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).inv ≫
      (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).hom.appTop).hom = _
  rw [AffineSpace.SpecIso_hom_appTop, ← Category.assoc, Iso.inv_hom_id, Category.id_comp,
    CommRingCat.hom_ofHom]

private theorem affineSpaceGlobalSectionsHom_X (k : Type u) [Field k] (m : ℕ) (i : ULift.{u} (Fin m)) :
    affineSpaceGlobalSectionsHom k m (MvPolynomial.X i) = AffineSpace.coord (Spec (CommRingCat.of k)) i := by
  rw [affineSpaceGlobalSectionsHom_eq_eval₂Hom, MvPolynomial.eval₂Hom_X']

private theorem affineSpaceGlobalSectionsHom_C (k : Type u) [Field k] (m : ℕ) (b : k) :
    affineSpaceGlobalSectionsHom k m (MvPolynomial.C b) =
      (affineSpaceFinToSpec k m).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom b) := by
  rw [affineSpaceGlobalSectionsHom_eq_eval₂Hom, MvPolynomial.eval₂Hom_C]
  rfl

private def affineSpaceGlobalSectionsEquiv (k : Type u) [Field k] (m : ℕ) :
    MvPolynomial (ULift.{u} (Fin m)) k ≃+* Γ(affineSpaceFin k m, ⊤) where
  toFun := affineSpaceGlobalSectionsHom k m
  invFun := fun z =>
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).hom.hom
      ((AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).inv.appTop.hom z)
  left_inv := by
    intro x
    have e : (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).inv ≫
        ((AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).hom.appTop ≫
          (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).inv.appTop) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).hom = 𝟙 _ := by
      rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id, Scheme.Hom.id_appTop, Category.id_comp,
        Iso.inv_hom_id]
    exact congrArg
      (fun φ : CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k) ⟶
        CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k) => φ.hom x) e
  right_inv := by
    intro z
    have e : (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).inv.appTop ≫
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).hom ≫
          (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).inv) ≫
        (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).hom.appTop = 𝟙 _ := by
      rw [Iso.hom_inv_id, Category.id_comp, ← Scheme.Hom.comp_appTop, Iso.hom_inv_id,
        Scheme.Hom.id_appTop]
    exact congrArg
      (fun φ : Γ(affineSpaceFin k m, ⊤) ⟶ Γ(affineSpaceFin k m, ⊤) => φ.hom z) e
  map_mul' := (affineSpaceGlobalSectionsHom k m).map_mul
  map_add' := (affineSpaceGlobalSectionsHom k m).map_add

theorem sectionsAlgebraMap_apply_eq (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) (a : k) :
    sectionsAlgebraMap k p U a =
      (p.appLE ⊤ U (le_preimage_top k p U)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a) := by
  rw [sectionsAlgebraMap_eq]
  rfl

private theorem appLE_top_comp_app (k : Type u) [CommRing k] {X W : Scheme.{u}}
    (f : W ⟶ X) (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) :
    p.appLE ⊤ U (le_preimage_top k p U) ≫ f.app U
      = (f ≫ p).appLE ⊤ (f ⁻¹ᵁ U) (le_preimage_top k (f ≫ p) (f ⁻¹ᵁ U)) := by
  have hn := f.c.naturality (homOfLE (le_preimage_top k p U)).op
  show (p.app ⊤ ≫ X.presheaf.map (homOfLE (le_preimage_top k p U)).op) ≫ f.app U
      = (f ≫ p).app ⊤ ≫ W.presheaf.map (homOfLE (le_preimage_top k (f ≫ p) (f ⁻¹ᵁ U))).op
  rw [Category.assoc]
  exact congrArg (fun t => p.app ⊤ ≫ t) hn

private theorem app_sectionsAlgebraMap (k : Type u) [CommRing k] {X W : Scheme.{u}}
    (f : W ⟶ X) (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) (a : k) :
    (f.app U).hom (sectionsAlgebraMap k p U a)
      = sectionsAlgebraMap k (f ≫ p) (f ⁻¹ᵁ U) a := by
  rw [sectionsAlgebraMap_apply_eq, sectionsAlgebraMap_apply_eq]
  exact congrArg
    (fun φ : Γ(Spec (CommRingCat.of k), ⊤) ⟶ Γ(W, f ⁻¹ᵁ U) =>
      φ.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a)) (appLE_top_comp_app k f p U)

theorem mem_basicOpen_of_notMem_primeIdealOf {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) (g : Γ(X, U))
    (hg : g ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal) : x ∈ X.basicOpen g := by
  have h1 : hU.fromSpec.base (hU.primeIdealOf ⟨x, hx⟩) = x := hU.fromSpec_primeIdealOf ⟨x, hx⟩
  have h2 : hU.fromSpec ⁻¹ᵁ (X.basicOpen g) = PrimeSpectrum.basicOpen g :=
    hU.fromSpec_preimage_basicOpen g
  have h3 : hU.primeIdealOf ⟨x, hx⟩ ∈ hU.fromSpec ⁻¹ᵁ (X.basicOpen g) := by
    rw [h2]
    exact (PrimeSpectrum.mem_basicOpen g _).mpr hg
  have h4 : hU.fromSpec.base (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen g := h3
  rwa [h1] at h4

theorem ideal_le_primeIdealOf {X : Scheme.{u}} (Z : X.IdealSheafData) {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) (hxZ : x ∈ Z.support) :
    Z.ideal ⟨U, hU⟩ ≤ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have h : x ∈ X.zeroLocus (↑(Z.ideal ⟨U, hU⟩) : Set Γ(X, U)) :=
    (Scheme.IdealSheafData.mem_support_iff_of_mem (I := Z) (U := ⟨U, hU⟩) hx).mp hxZ
  intro f hf
  by_contra hfp
  have hx' : x ∈ X.basicOpen f := mem_basicOpen_of_notMem_primeIdealOf hU hx f hfp
  rw [Scheme.mem_zeroLocus_iff] at h
  exact h f hf hx'

theorem restrictIdeal_eq_coordIdeal_of_ideal_eq_span {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} (hU : IsAffineOpen U) {m : ℕ}
    (c : EtaleChart p U m) (Z : X.IdealSheafData) (S : Finset (Fin m))
    (h : Z.ideal ⟨U, hU⟩ = Ideal.span (c.coord '' (S : Set (Fin m)))) :
    restrictIdeal Z U = c.coordIdeal S := by
  have : IsAffine U.toScheme := hU
  have hTop : IsAffineOpen (⊤ : U.toScheme.Opens) := isAffineOpen_top U.toScheme
  have e : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U := fun z _ => z.2
  have hsets : (U.topIso.inv.hom) '' (c.coord '' (S : Set (Fin m)))
      = (c.map.appTop.hom) ''
        ((fun i : Fin m => AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i)) ''
          (S : Set (Fin m))) := by
    rw [Set.image_image, Set.image_image]
    refine congrArg (fun g : Fin m → Γ(U.toScheme, ⊤) => g '' (S : Set (Fin m))) ?_
    funext j
    rw [EtaleChart.coord_def]
    exact Iso.hom_inv_id_apply U.topIso _
  rw [restrictIdeal_eq_comap_ι, c.coordIdeal_eq_comap_coordSubspaceIdeal, coordSubspaceIdeal_eq_ofIdealTop_span_coord]
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE Z U.ι ⟨U, hU⟩ ⟨⊤, hTop⟩ e,
    Scheme.IdealSheafData.comap_ideal_top_eq_map_appTop, ofIdealTop_ideal_top, h,
    ι_appLE_eq_topIso_inv, Ideal.map_span, Ideal.map_span]
  exact congrArg Ideal.span hsets

theorem etale_homOfVector_of_ringHom_etale {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) {U : X.Opens} (hU : IsAffineOpen U) {m : ℕ}
    (y : ULift.{u} (Fin m) → Γ(X, U))
    (f : MvPolynomial (ULift.{u} (Fin m)) k →+* Γ(X, U))
    (hC : ∀ a : k, f (MvPolynomial.C a) = sectionsAlgebraMap k p U a)
    (hX : ∀ i : ULift.{u} (Fin m), f (MvPolynomial.X i) = y i)
    (hf : f.Etale) :
    AlgebraicGeometry.Etale
      (AffineSpace.homOfVector (U.ι ≫ p) (fun i => U.topIso.inv.hom (y i))) := by
  have : IsAffine U.toScheme := hU
  have hresp : RingHom.RespectsIso @RingHom.Etale :=
    (AlgebraicGeometry.HasRingHomProperty.isLocal_ringHomProperty
      (P := @AlgebraicGeometry.Etale)).respectsIso
  have hover : AffineSpace.homOfVector (U.ι ≫ p) (fun i => U.topIso.inv.hom (y i)) ≫
      affineSpaceFinToSpec k m = U.ι ≫ p := by simp
  have e1 : (affineSpaceFinToSpec k m).appTop ≫
      (AffineSpace.homOfVector (U.ι ≫ p) (fun i => U.topIso.inv.hom (y i))).appTop
        = (U.ι ≫ p).appTop := by
    rw [← Scheme.Hom.comp_appTop, hover]
  have e2 : p.appLE ⊤ U (le_preimage_top k p U) ≫ U.topIso.inv = (U.ι ≫ p).appTop :=
    appLE_top_comp_topIso_inv p U (le_preimage_top k p U)
  have key : ((AffineSpace.homOfVector (U.ι ≫ p)
        (fun i => U.topIso.inv.hom (y i))).appTop.hom).comp (affineSpaceGlobalSectionsHom k m)
      = (U.topIso.inv.hom).comp f := by
    apply MvPolynomial.ringHom_ext
    · intro b
      show (AffineSpace.homOfVector (U.ι ≫ p) (fun i => U.topIso.inv.hom (y i))).appTop.hom
          (affineSpaceGlobalSectionsHom k m (MvPolynomial.C b))
          = U.topIso.inv.hom (f (MvPolynomial.C b))
      rw [affineSpaceGlobalSectionsHom_C, hC, sectionsAlgebraMap_apply_eq]
      exact congrArg (fun φ : Γ(Spec (CommRingCat.of k), ⊤) ⟶ Γ(U.toScheme, ⊤) =>
        φ.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom b)) (e1.trans e2.symm)
    · intro i
      show (AffineSpace.homOfVector (U.ι ≫ p) (fun i => U.topIso.inv.hom (y i))).appTop.hom
          (affineSpaceGlobalSectionsHom k m (MvPolynomial.X i))
          = U.topIso.inv.hom (f (MvPolynomial.X i))
      rw [affineSpaceGlobalSectionsHom_X, hX]
      exact AffineSpace.homOfVector_appTop_coord (U.ι ≫ p)
        (fun i => U.topIso.inv.hom (y i)) i
  have hA : (AffineSpace.homOfVector (U.ι ≫ p) (fun i => U.topIso.inv.hom (y i))).appTop.hom
      = ((U.topIso.inv.hom).comp f).comp (affineSpaceGlobalSectionsEquiv k m).symm.toRingHom := by
    refine RingHom.ext fun z => ?_
    have h1 := DFunLike.congr_fun key ((affineSpaceGlobalSectionsEquiv k m).symm z)
    simp only [RingHom.comp_apply] at h1 ⊢
    rw [show affineSpaceGlobalSectionsHom k m ((affineSpaceGlobalSectionsEquiv k m).symm z) = z from
      (affineSpaceGlobalSectionsEquiv k m).apply_symm_apply z] at h1
    exact h1
  rw [AlgebraicGeometry.HasRingHomProperty.iff_of_isAffine (P := @AlgebraicGeometry.Etale), hA]
  exact hresp.right _ (affineSpaceGlobalSectionsEquiv k m).symm
    (hresp.left f U.topIso.commRingCatIsoToRingEquiv.symm hf)

theorem exists_etaleChart_coord_eq {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) {U : X.Opens} (hU : IsAffineOpen U) {m : ℕ}
    (y : ULift.{u} (Fin m) → Γ(X, U))
    (f : MvPolynomial (ULift.{u} (Fin m)) k →+* Γ(X, U))
    (hC : ∀ a : k, f (MvPolynomial.C a) = sectionsAlgebraMap k p U a)
    (hX : ∀ i : ULift.{u} (Fin m), f (MvPolynomial.X i) = y i)
    (hf : f.Etale) :
    ∃ c : EtaleChart p U m, ∀ j : Fin m, c.coord j = y (ULift.up j) := by
  refine ⟨EtaleChart.ofCoords p U (fun i => U.topIso.inv.hom (y i))
      (etale_homOfVector_of_ringHom_etale p hU y f hC hX hf), fun j => ?_⟩
  rw [EtaleChart.coord_def, EtaleChart.ofCoords_map, AffineSpace.homOfVector_appTop_coord]
  exact Iso.inv_hom_id_apply U.topIso (y (ULift.up j))

theorem exists_chart_ideal_eq_span_coord {X : Scheme.{u}} {k : Type u} [Field k] [CharZero k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (Z : X.IdealSheafData)
    [AlgebraicGeometry.Smooth (Z.subschemeι ≫ p)] (x : X) (hx : x ∈ Z.support) :
    ∃ (U : X.Opens) (hU : IsAffineOpen U) (m : ℕ) (c : EtaleChart p U m) (S : Finset (Fin m)),
      x ∈ U ∧ Z.ideal ⟨U, hU⟩ = Ideal.span (c.coord '' (S : Set (Fin m))) := by
  obtain ⟨U₀, m, hxU₀, hU₀, ⟨c⟩⟩ := exists_etaleChart p x
  let _ : Algebra k Γ(X, U₀) := sectionsAlgebra k p U₀
  have hk : (algebraMap k Γ(X, U₀)) = sectionsAlgebraMap k p U₀ :=
    algebraMap_sectionsAlgebra k p U₀
  let _ : Algebra (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U₀) := c.algebra
  have : IsScalarTower k (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U₀) := c.isScalarTower
  have : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U₀) :=
    c.algebra_formallyEtale hU₀
  have : IsNoetherianRing Γ(X, U₀) := isNoetherianRing_sections k p ⟨U₀, hU₀⟩ hk
  have : DecidableEq (ULift.{u} (Fin m)) := Classical.decEq _
  let P : PrimeSpectrum Γ(X, U₀) := hU₀.primeIdealOf ⟨x, hxU₀⟩
  have hIq : Z.ideal ⟨U₀, hU₀⟩ ≤ P.asIdeal := ideal_le_primeIdealOf Z hU₀ hxU₀ hx
  have : IsNoetherianRing (Localization.AtPrime P.asIdeal) :=
    IsLocalization.isNoetherianRing P.asIdeal.primeCompl
      (Localization.AtPrime P.asIdeal) inferInstance
  have hVaff : IsAffineOpen (Z.subschemeι ⁻¹ᵁ U₀) := isAffineOpen_preimage_subschemeι Z hU₀
  let _ : Algebra k Γ(Z.subscheme, Z.subschemeι ⁻¹ᵁ U₀) :=
    sectionsAlgebra k (Z.subschemeι ≫ p) (Z.subschemeι ⁻¹ᵁ U₀)
  have : Algebra.FormallySmooth k Γ(Z.subscheme, Z.subschemeι ⁻¹ᵁ U₀) :=
    formallySmooth_sections k (Z.subschemeι ≫ p) (Z.subschemeι ⁻¹ᵁ U₀) hVaff
      (algebraMap_sectionsAlgebra k (Z.subschemeι ≫ p) (Z.subschemeι ⁻¹ᵁ U₀))
  have hker : RingHom.ker (Z.subschemeι.app U₀).hom = Z.ideal ⟨U₀, hU₀⟩ :=
    Z.ker_subschemeι_app ⟨U₀, hU₀⟩
  have hsurj : Function.Surjective ⇑((Z.subschemeι.app U₀).hom) :=
    Z.subschemeι_app_surjective ⟨U₀, hU₀⟩
  let Φ : Γ(X, U₀) →ₐ[k] Γ(Z.subscheme, Z.subschemeι ⁻¹ᵁ U₀) :=
    { (Z.subschemeι.app U₀).hom with
      commutes' := fun a => app_sectionsAlgebraMap k Z.subschemeι p U₀ a }
  have hΦsurj : Function.Surjective ⇑Φ := hsurj
  have hkerΦ : RingHom.ker (Φ : Γ(X, U₀) →+* Γ(Z.subscheme, Z.subschemeι ⁻¹ᵁ U₀))
      = Z.ideal ⟨U₀, hU₀⟩ := hker
  have hfs : Algebra.FormallySmooth k (Γ(X, U₀) ⧸ Z.ideal ⟨U₀, hU₀⟩) := by
    have e1 : (Γ(X, U₀) ⧸ Z.ideal ⟨U₀, hU₀⟩) ≃ₐ[k]
        (Γ(X, U₀) ⧸ RingHom.ker (Φ : Γ(X, U₀) →+* Γ(Z.subscheme, Z.subschemeι ⁻¹ᵁ U₀))) :=
      Ideal.quotientEquivAlgOfEq k hkerΦ.symm
    have e2 : (Γ(X, U₀) ⧸ RingHom.ker (Φ : Γ(X, U₀) →+* Γ(Z.subscheme, Z.subschemeι ⁻¹ᵁ U₀)))
        ≃ₐ[k] Γ(Z.subscheme, Z.subschemeι ⁻¹ᵁ U₀) :=
      Ideal.quotientKerAlgEquivOfSurjective hΦsurj
    exact Algebra.FormallySmooth.of_equiv (e1.trans e2).symm
  have : Algebra.FormallySmooth k
      ((Localization.AtPrime P.asIdeal) ⧸
        Ideal.map (algebraMap Γ(X, U₀) (Localization.AtPrime P.asIdeal))
          (Z.ideal ⟨U₀, hU₀⟩)) :=
    formallySmooth_quotient_map_of_isLocalization k P.asIdeal.primeCompl
      (Localization.AtPrime P.asIdeal) (Z.ideal ⟨U₀, hU₀⟩) hfs
  obtain ⟨g, w, T, hgq, hwI, hspanmap, hcoords, hfe⟩ :=
    EtaleCoordinates.exists_away_ideal_eq_span_and_formallyEtale k (ULift.{u} (Fin m)) Γ(X, U₀)
      (Z.ideal ⟨U₀, hU₀⟩) P.asIdeal (Localization.AtPrime P.asIdeal) hIq
  have hxU : x ∈ X.basicOpen g := mem_basicOpen_of_notMem_primeIdealOf hU₀ hxU₀ g hgq
  let _ : Algebra k Γ(X, X.basicOpen g) := sectionsAlgebra k p (X.basicOpen g)
  let _ : Algebra (MvPolynomial (ULift.{u} (Fin m)) k) (Localization.Away g) :=
    RingHom.toAlgebra (MvPolynomial.eval₂Hom
      ((algebraMap Γ(X, U₀) (Localization.Away g)).comp (algebraMap k Γ(X, U₀)))
      (fun j : ULift.{u} (Fin m) => algebraMap Γ(X, U₀) (Localization.Away g) (w j)))
  have : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m)) k) (Localization.Away g) := hfe
  let _ : Algebra (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, X.basicOpen g) :=
    RingHom.toAlgebra (MvPolynomial.eval₂Hom
      ((algebraMap Γ(X, U₀) Γ(X, X.basicOpen g)).comp (algebraMap k Γ(X, U₀)))
      (fun j : ULift.{u} (Fin m) => algebraMap Γ(X, U₀) Γ(X, X.basicOpen g) (w j)))
  have : IsLocalization.Away g Γ(X, X.basicOpen g) := hU₀.isLocalization_basicOpen g
  let e : Localization.Away g ≃ₐ[Γ(X, U₀)] Γ(X, X.basicOpen g) :=
    IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g) Γ(X, X.basicOpen g)
  have hcomm : (e.toAlgHom.toRingHom).comp
      (MvPolynomial.eval₂Hom
        ((algebraMap Γ(X, U₀) (Localization.Away g)).comp (algebraMap k Γ(X, U₀)))
        (fun j : ULift.{u} (Fin m) => algebraMap Γ(X, U₀) (Localization.Away g) (w j)))
      = MvPolynomial.eval₂Hom
        ((algebraMap Γ(X, U₀) Γ(X, X.basicOpen g)).comp (algebraMap k Γ(X, U₀)))
        (fun j : ULift.{u} (Fin m) => algebraMap Γ(X, U₀) Γ(X, X.basicOpen g) (w j)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      exact e.commutes _
    · intro i
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      exact e.commutes _
  let E : Localization.Away g ≃ₐ[MvPolynomial (ULift.{u} (Fin m)) k] Γ(X, X.basicOpen g) :=
    AlgEquiv.ofRingEquiv (f := e.toRingEquiv)
      (fun z => congrArg
        (fun φ : MvPolynomial (ULift.{u} (Fin m)) k →+* Γ(X, X.basicOpen g) => φ z) hcomm)
  have : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, X.basicOpen g) :=
    Algebra.FormallyEtale.of_equiv E
  have : Algebra.FiniteType k Γ(X, X.basicOpen g) :=
    finiteType_sections k p ⟨X.basicOpen g, hU₀.basicOpen g⟩
      (algebraMap_sectionsAlgebra k p (X.basicOpen g))
  have : IsScalarTower k (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, X.basicOpen g) := by
    refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
    have h1 : algebraMap (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, X.basicOpen g)
        (algebraMap k (MvPolynomial (ULift.{u} (Fin m)) k) a)
        = algebraMap Γ(X, U₀) Γ(X, X.basicOpen g) (algebraMap k Γ(X, U₀) a) := by
      rw [MvPolynomial.algebraMap_eq]
      exact MvPolynomial.eval₂Hom_C _ _ a
    rw [h1]
    exact (sectionsAlgebraMap_restrict_apply k p (X.basicOpen_le g) a).symm
  have : Algebra.FiniteType (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, X.basicOpen g) :=
    Algebra.FiniteType.of_restrictScalars_finiteType k
      (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, X.basicOpen g)
  have : Algebra.FinitePresentation (MvPolynomial (ULift.{u} (Fin m)) k)
      Γ(X, X.basicOpen g) := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.Etale (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, X.basicOpen g) := by
    constructor <;> infer_instance
  have hC : ∀ a : k, (MvPolynomial.eval₂Hom
      ((algebraMap Γ(X, U₀) Γ(X, X.basicOpen g)).comp (algebraMap k Γ(X, U₀)))
      (fun j : ULift.{u} (Fin m) => algebraMap Γ(X, U₀) Γ(X, X.basicOpen g) (w j)))
        (MvPolynomial.C a) = sectionsAlgebraMap k p (X.basicOpen g) a := by
    intro a
    rw [MvPolynomial.eval₂Hom_C]
    exact sectionsAlgebraMap_restrict_apply k p (X.basicOpen_le g) a
  have hX : ∀ i : ULift.{u} (Fin m), (MvPolynomial.eval₂Hom
      ((algebraMap Γ(X, U₀) Γ(X, X.basicOpen g)).comp (algebraMap k Γ(X, U₀)))
      (fun j : ULift.{u} (Fin m) => algebraMap Γ(X, U₀) Γ(X, X.basicOpen g) (w j)))
        (MvPolynomial.X i) = algebraMap Γ(X, U₀) Γ(X, X.basicOpen g) (w i) :=
    fun i => MvPolynomial.eval₂Hom_X' _ _ i
  have hf : (MvPolynomial.eval₂Hom
      ((algebraMap Γ(X, U₀) Γ(X, X.basicOpen g)).comp (algebraMap k Γ(X, U₀)))
      (fun j : ULift.{u} (Fin m) =>
        algebraMap Γ(X, U₀) Γ(X, X.basicOpen g) (w j))).Etale :=
    ‹Algebra.Etale (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, X.basicOpen g)›
  obtain ⟨c', hc'⟩ := exists_etaleChart_coord_eq p (hU₀.basicOpen g)
    (fun i : ULift.{u} (Fin m) => algebraMap Γ(X, U₀) Γ(X, X.basicOpen g) (w i))
    (MvPolynomial.eval₂Hom
      ((algebraMap Γ(X, U₀) Γ(X, X.basicOpen g)).comp (algebraMap k Γ(X, U₀)))
      (fun j : ULift.{u} (Fin m) => algebraMap Γ(X, U₀) Γ(X, X.basicOpen g) (w j)))
    hC hX hf
  refine ⟨X.basicOpen g, hU₀.basicOpen g, m, c', T.image ULift.down, hxU, ?_⟩
  have hmap : Ideal.map (algebraMap Γ(X, U₀) Γ(X, X.basicOpen g)) (Z.ideal ⟨U₀, hU₀⟩)
      = Z.ideal ⟨X.basicOpen g, hU₀.basicOpen g⟩ := Z.map_ideal_basicOpen ⟨U₀, hU₀⟩ g
  have htrans : Ideal.map (algebraMap Γ(X, U₀) Γ(X, X.basicOpen g))
        (Ideal.span (w '' (↑T : Set (ULift.{u} (Fin m)))))
      = Ideal.map (algebraMap Γ(X, U₀) Γ(X, X.basicOpen g)) (Z.ideal ⟨U₀, hU₀⟩) := by
    rw [map_algebraMap_eq_map_map_of_algEquiv e, map_algebraMap_eq_map_map_of_algEquiv e, hspanmap]
  have hSset : ((T.image ULift.down : Finset (Fin m)) : Set (Fin m))
      = ULift.down '' (↑T : Set (ULift.{u} (Fin m))) := Finset.coe_image
  have himg : (fun i : ULift.{u} (Fin m) => algebraMap Γ(X, U₀) Γ(X, X.basicOpen g) (w i))
      = c'.coord ∘ ULift.down := by
    funext i
    show algebraMap Γ(X, U₀) Γ(X, X.basicOpen g) (w i) = c'.coord i.down
    rw [hc' i.down]
  rw [← hmap, ← htrans, Ideal.map_span]
  refine congrArg Ideal.span ?_
  rw [Set.image_image, hSset, ← Set.image_comp]
  exact congrArg (fun h : ULift.{u} (Fin m) → Γ(X, X.basicOpen g) =>
    h '' (↑T : Set (ULift.{u} (Fin m)))) himg

theorem exists_chart_restrictIdeal_eq_coordIdeal {X : Scheme.{u}} {k : Type u} [Field k]
    [CharZero k] (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (Z : X.IdealSheafData) [AlgebraicGeometry.Smooth (Z.subschemeι ≫ p)] (x : X)
    (hx : x ∈ Z.support) :
    ∃ (U : X.Opens) (m : ℕ) (c : EtaleChart p U m) (S : Finset (Fin m)),
      x ∈ U ∧ IsAffineOpen U ∧ restrictIdeal Z U = c.coordIdeal S := by
  obtain ⟨U, hU, m, c, S, hxU, hspan⟩ := exists_chart_ideal_eq_span_coord p Z x hx
  exact ⟨U, m, c, S, hxU, hU, restrictIdeal_eq_coordIdeal_of_ideal_eq_span hU c Z S hspan⟩

theorem hasStrictNormalCrossingsWith_nil_of_smooth {X : Scheme.{u}} {k : Type u} [Field k] [CharZero k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (Z : X.IdealSheafData)
    [AlgebraicGeometry.Smooth (Z.subschemeι ≫ p)] :
    HasStrictNormalCrossingsWith p Z [] := by
  unfold HasStrictNormalCrossingsWith
  intro x hx
  obtain ⟨U, m, c, S, hxU, hU, hres⟩ := exists_chart_restrictIdeal_eq_coordIdeal p Z x hx
  refine ⟨U, hxU, m, c, fun _ => none, S, ?_, ?_, ?_, hres⟩
  · intro i hi
    simp at hi
  · intro i hi
    simp at hi
  · intro i hi
    simp at hi

end FunctorialResolution.EmbeddedResolution
