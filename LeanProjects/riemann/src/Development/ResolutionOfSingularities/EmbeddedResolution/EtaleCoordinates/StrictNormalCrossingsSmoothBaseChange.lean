import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartAlgebra
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateSubscheme
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.PolynomialCoordinateExtension
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCenterChart
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothEtaleChart
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafSmoothPullback
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace FunctorialResolution.EmbeddedResolution

variable {k : Type u} [Field k] {X Y : Scheme.{u}}

private theorem topIso_hom_inv_apply {Z : Scheme.{u}} (V : Z.Opens) (x : Γ(Z, V)) :
    V.topIso.hom.hom (V.topIso.inv.hom x) = x :=
  V.topIso.commRingCatIsoToRingEquiv.right_inv x

private theorem ι_appLE_self_top_eq_topIso_inv {Z : Scheme.{u}} (V : Z.Opens) :
    V.ι.appLE V ⊤ (by simp) = V.topIso.inv := by
  simp
  apply Scheme.presheaf_map_eq_of_parallel

private theorem appLE_eq_map_comp_appLE (f : Y ⟶ X) {U W : X.Opens} {V : Y.Opens} (hWU : W ≤ U)
    (e : V ≤ f ⁻¹ᵁ W) (hVU : V ≤ f ⁻¹ᵁ U) :
    f.appLE U V hVU = X.presheaf.map (homOfLE hWU).op ≫ f.appLE W V e := by
  rw [Scheme.Hom.map_appLE]

private theorem etale_comp_ringEquiv {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : B →+* C) (e : A ≃+* B) (hf : f.Etale) : (f.comp e.toRingHom).Etale :=
  RingHom.Etale.respectsIso.2 f e hf

private def uliftFinAddEquivSum (m d : ℕ) :
    ULift.{u} (Fin (m + d)) ≃ ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d) :=
  Equiv.ulift.trans (finSumFinEquiv.symm.trans (Equiv.sumCongr Equiv.ulift.symm Equiv.ulift.symm))

private theorem sumEquiv_castAdd_eq_inl (m d : ℕ) (j : Fin m) :
    uliftFinAddEquivSum m d (ULift.up (Fin.castAdd d j)) = Sum.inl (ULift.up j) := by
  simp [uliftFinAddEquivSum]

private theorem etale_of_formallyEtale_of_finitePresentation {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (h1 : @Algebra.FormallyEtale A B _ _ f.toAlgebra)
    (h2 : @Algebra.FinitePresentation A B _ _ f.toAlgebra) : f.Etale :=
  @Algebra.Etale.mk A B _ _ f.toAlgebra h1 h2

private theorem ideal_eq_top_of_map_eq_top_of_leftInverse {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (g : B →+* A) (hgf : ∀ x, g (f x) = x) (I : Ideal A) (hI : Ideal.map f I = ⊤) : I = ⊤ := by
  have h2 : Ideal.map g (Ideal.map f I) = I := by
    rw [Ideal.map_map]
    have hc : g.comp f = RingHom.id A := RingHom.ext hgf
    rw [hc, Ideal.map_id]
  rw [hI, Ideal.map_top] at h2
  exact h2.symm

private theorem restrictIdeal_eq_top_of_ideal_eq_top {Z : Scheme.{u}} {V : Z.Opens}
    (hV : IsAffineOpen V) (D : Z.IdealSheafData) (hD : D.ideal ⟨V, hV⟩ = ⊤) :
    restrictIdeal D V = ⊤ := by
  have : IsAffine V.toScheme := hV
  have e1 : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := by simp
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [restrictIdeal_eq_comap_ι,
    Scheme.IdealSheafData.comap_ideal_eq_map_appLE D V.ι ⟨V, hV⟩
      ⟨⊤, isAffineOpen_top V.toScheme⟩ e1,
    hD, Ideal.map_top]
  simp

private theorem ideal_affineOpen_eq_top_of_restrictIdeal_eq_top {Z : Scheme.{u}} {V : Z.Opens}
    (hV : IsAffineOpen V) (D : Z.IdealSheafData) (hD : restrictIdeal D V = ⊤) :
    D.ideal ⟨V, hV⟩ = ⊤ := by
  have : IsAffine V.toScheme := hV
  have e1 : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := by simp
  have h1 : Ideal.map (V.ι.appLE V ⊤ e1).hom (D.ideal ⟨V, hV⟩) = ⊤ := by
    rw [← Scheme.IdealSheafData.comap_ideal_eq_map_appLE D V.ι ⟨V, hV⟩
      ⟨⊤, isAffineOpen_top V.toScheme⟩ e1, ← restrictIdeal_eq_comap_ι, hD]
    simp
  rw [ι_appLE_self_top_eq_topIso_inv] at h1
  exact ideal_eq_top_of_map_eq_top_of_leftInverse _ V.topIso.hom.hom (topIso_hom_inv_apply V) _ h1

private theorem finiteType_sectionsAlgebra_of_isAffineOpen (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] (h : Y ⟶ X)
    [Smooth h] {V : Y.Opens} (hV : IsAffineOpen V) :
    @Algebra.FiniteType k Γ(Y, V) _ _ (sectionsAlgebra k (h ≫ p) V) :=
  @finiteType_sections k _ Y (h ≫ p) _ ⟨V, hV⟩ (sectionsAlgebra k (h ≫ p) V)
    (algebraMap_sectionsAlgebra k (h ≫ p) V)

private theorem exists_etale_mvPolynomialHom_castAdd_coord (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] (h : Y ⟶ X) [Smooth h]
    {W : X.Opens} (hW : IsAffineOpen W) {m : ℕ} (cW : EtaleChart p W m)
    {V : Y.Opens} (hV : IsAffineOpen V) (e : V ≤ h ⁻¹ᵁ W) {d : ℕ}
    (g : V.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) W.toScheme) (hgE : Etale g)
    (hg : g ≫ (AffineSpace (ULift.{u} (Fin d)) W.toScheme ↘ W.toScheme) = h.resLE W V e) :
    ∃ ψ : MvPolynomial (ULift.{u} (Fin (m + d))) k →+* Γ(Y, V),
      ψ.Etale ∧ (∀ a : k, ψ (MvPolynomial.C a) = sectionsAlgebraMap k (h ≫ p) V a) ∧
        ∀ j : Fin m, ψ (MvPolynomial.X (ULift.up (Fin.castAdd d j)))
          = (h.appLE W V e).hom (cW.coord j) := by
  have := hgE
  let _ : Algebra k Γ(X, W) := sectionsAlgebra k p W
  let _ : Algebra (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, W) := cW.algebra
  have : IsScalarTower k (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, W) := cW.isScalarTower
  have : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, W) :=
    cW.algebra_formallyEtale hW
  let _ : Algebra (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V) := chartAlgebra hW g
  have : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V) :=
    chartAlgebra_formallyEtale hW hV g
  set χ : MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k →+* Γ(Y, V) :=
    (chartEvalHom hW g).comp
      (EtaleCoordinates.sumEval k (ULift.{u} (Fin m)) (ULift.{u} (Fin d)) Γ(X, W)).toRingHom
    with hχdef
  let _ : Algebra (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k) Γ(Y, V) := χ.toAlgebra
  let _ := EtaleCoordinates.sumEvalAlgebra k (ULift.{u} (Fin m)) (ULift.{u} (Fin d)) Γ(X, W)
  have : IsScalarTower (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k)
      (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V) :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      rw [EtaleCoordinates.algebraMap_eq_sumEval]
      rfl)
  have : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k)
      Γ(Y, V) :=
    EtaleCoordinates.formallyEtale_trans k (ULift.{u} (Fin m)) (ULift.{u} (Fin d)) Γ(X, W)
      Γ(Y, V)
  have hCval : ∀ a : k, χ (MvPolynomial.C a) = sectionsAlgebraMap k (h ≫ p) V a := by
    intro a
    have hc := (EtaleCoordinates.sumEval k (ULift.{u} (Fin m)) (ULift.{u} (Fin d))
      Γ(X, W)).commutes a
    rw [MvPolynomial.algebraMap_eq] at hc
    have h1 : EtaleCoordinates.sumEval k (ULift.{u} (Fin m)) (ULift.{u} (Fin d)) Γ(X, W)
        (MvPolynomial.C a) = MvPolynomial.C (sectionsAlgebraMap k p W a) := by
      rw [hc, MvPolynomial.algebraMap_apply, algebraMap_sectionsAlgebra]
    rw [hχdef]
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [h1, chartEvalHom_C hW h e g hg, sectionsAlgebraMap_appLE_apply]
  have hXval : ∀ j : Fin m, χ (MvPolynomial.X (Sum.inl (ULift.up j)))
      = (h.appLE W V e).hom (cW.coord j) := by
    intro j
    have h1 : EtaleCoordinates.sumEval k (ULift.{u} (Fin m)) (ULift.{u} (Fin d)) Γ(X, W)
        (MvPolynomial.X (Sum.inl (ULift.up j)))
        = MvPolynomial.C (EtaleCoordinates.coord k (ULift.{u} (Fin m)) Γ(X, W)
            (ULift.up j)) := by
      rw [← EtaleCoordinates.algebraMap_eq_sumEval]
      exact EtaleCoordinates.algebraMap_X_inl k (ULift.{u} (Fin m)) (ULift.{u} (Fin d))
        Γ(X, W) (ULift.up j)
    rw [hχdef]
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [h1, cW.etaleCoordinates_coord j, chartEvalHom_C hW h e g hg]
  let _ : Algebra k Γ(Y, V) := sectionsAlgebra k (h ≫ p) V
  have : Algebra.FiniteType k Γ(Y, V) := finiteType_sectionsAlgebra_of_isAffineOpen p h hV
  have : IsScalarTower k (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k) Γ(Y, V) :=
    IsScalarTower.of_algebraMap_eq (fun a => by
      rw [algebraMap_sectionsAlgebra, MvPolynomial.algebraMap_eq]
      exact (hCval a).symm)
  have : Algebra.FiniteType (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k) Γ(Y, V) :=
    Algebra.FiniteType.of_restrictScalars_finiteType k
      (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k) Γ(Y, V)
  have : IsNoetherianRing (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k) :=
    inferInstance
  have : Algebra.FinitePresentation (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k)
      Γ(Y, V) := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hχE : χ.Etale := etale_of_formallyEtale_of_finitePresentation χ inferInstance inferInstance
  refine ⟨χ.comp (MvPolynomial.renameEquiv k (uliftFinAddEquivSum m d)).toRingEquiv.toRingHom,
    etale_comp_ringEquiv χ (MvPolynomial.renameEquiv k (uliftFinAddEquivSum m d)).toRingEquiv hχE,
    ?_, ?_⟩
  · intro a
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      AlgEquiv.coe_ringEquiv, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_C]
    exact hCval a
  · intro j
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      AlgEquiv.coe_ringEquiv, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X]
    rw [sumEquiv_castAdd_eq_inl]
    exact hXval j

private theorem exists_etaleChart_comap_restrictIdeal_eq_coordIdeal (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] (h : Y ⟶ X)
    [Smooth h] {U : X.Opens} {m : ℕ} (c : EtaleChart p U m) (y : Y) (hy : h.base y ∈ U) :
    ∃ (V : Y.Opens) (d : ℕ) (c' : EtaleChart (h ≫ p) V (m + d)) (hVU : V ≤ h ⁻¹ᵁ U),
      IsAffineOpen V ∧ y ∈ V ∧
      (∀ j : Fin m, c'.coord (Fin.castAdd d j) = (h.appLE U V hVU).hom (c.coord j)) ∧
      (∀ D : X.IdealSheafData, restrictIdeal D U = ⊤ → restrictIdeal (D.comap h) V = ⊤) ∧
      (∀ (D : X.IdealSheafData) (S : Finset (Fin m)), restrictIdeal D U = c.coordIdeal S →
        restrictIdeal (D.comap h) V = c'.coordIdeal (S.map (Fin.castAddEmb d))) := by
  obtain ⟨W, V, d, e, hW, hV, hyV, hWU, -, g, hgE, hgc⟩ :=
    SmoothEtaleChart.exists_isAffineOpen_etale_resLE_le h y U hy ⊤ (by trivial)
  obtain ⟨ψ, hψE, hψC, hψX⟩ := exists_etale_mvPolynomialHom_castAdd_coord p h hW (c.restrict hWU) hV e g hgE hgc
  have hVU : V ≤ h ⁻¹ᵁ U := fun z hz => hWU (e hz)
  set v : ULift.{u} (Fin (m + d)) → Γ(V.toScheme, ⊤) :=
    fun i => V.topIso.inv.hom (ψ (MvPolynomial.X i)) with hvdef
  have hEt : Etale (AffineSpace.homOfVector (V.ι ≫ (h ≫ p)) v) :=
    etale_homOfVector_of_ringHom_etale (h ≫ p) hV ψ hψC hψE
      (y := fun i => ψ (MvPolynomial.X i)) (hX := fun _ => rfl)
  have hcoordEq : ∀ j : Fin m,
      (EtaleChart.ofCoords (h ≫ p) V v hEt).coord (Fin.castAdd d j)
        = ψ (MvPolynomial.X (ULift.up (Fin.castAdd d j))) := by
    intro j
    rw [EtaleChart.coord_def, EtaleChart.ofCoords_map,
      show (AffineSpace.homOfVector (V.ι ≫ (h ≫ p)) v).appTop.hom
          (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up (Fin.castAdd d j)))
          = v (ULift.up (Fin.castAdd d j)) from
        AffineSpace.homOfVector_appTop_coord _ _ _]
    rw [hvdef]
    exact topIso_hom_inv_apply V _
  refine ⟨V, d, EtaleChart.ofCoords (h ≫ p) V v hEt, hVU, hV, hyV, ?_, ?_, ?_⟩
  · intro j
    refine (hcoordEq j).trans ((hψX j).trans ?_)
    rw [EtaleChart.coord_restrict c hWU j]
    have h5 := congrArg (fun φ : Γ(X, U) ⟶ Γ(Y, V) => φ.hom (c.coord j))
      (appLE_eq_map_comp_appLE h hWU e hVU)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h5
    exact h5.symm
  · intro D hD
    have h1 : restrictIdeal D W = ⊤ := restrictIdeal_eq_top_of_le D hWU hD
    have h2 : D.ideal ⟨W, hW⟩ = ⊤ := ideal_affineOpen_eq_top_of_restrictIdeal_eq_top hW D h1
    have h3 : (D.comap h).ideal ⟨V, hV⟩ = ⊤ := by
      rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE D h ⟨W, hW⟩ ⟨V, hV⟩ e, h2, Ideal.map_top]
    exact restrictIdeal_eq_top_of_ideal_eq_top hV (D.comap h) h3
  · intro D S hD
    have h1 : restrictIdeal D W = (c.restrict hWU).coordIdeal S :=
      restrictIdeal_eq_restrict_coordIdeal_of_le hWU c D S hD
    have h2 : D.ideal ⟨W, hW⟩
        = Ideal.span ((c.restrict hWU).coord '' (S : Set (Fin m))) :=
      EtaleChart.ideal_eq_span_coord (c.restrict hWU) hW D S h1
    apply restrictIdeal_eq_coordIdeal_of_ideal_eq_span hV
    rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE D h ⟨W, hW⟩ ⟨V, hV⟩ e, h2, Ideal.map_span]
    congr 1
    rw [Finset.coe_map, Set.image_image, Set.image_image]
    have hEq : ∀ i : Fin m, (h.appLE W V e).hom ((c.restrict hWU).coord i)
        = (EtaleChart.ofCoords (h ≫ p) V v hEt).coord (Fin.castAddEmb d i) := by
      intro i
      rw [Fin.castAddEmb_apply]
      exact ((hcoordEq i).trans (hψX i)).symm
    exact Set.image_congr (fun i _ => hEq i)

theorem exists_etaleChart_comap_coord_eq (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p]
    (h : Y ⟶ X) [Smooth h] {U : X.Opens} {m : ℕ} (c : EtaleChart p U m) (y : Y)
    (hy : h.base y ∈ U) :
    ∃ (V : Y.Opens) (hVU : V ≤ h ⁻¹ᵁ U) (d : ℕ) (c' : EtaleChart (h ≫ p) V (m + d)),
      IsAffineOpen V ∧ y ∈ V ∧
        ∀ j : Fin m,
          c'.coord (Fin.castAdd d j) = (h.appLE U V hVU).hom (c.coord j) := by
  obtain ⟨V, d, c', hVU, hV, hyV, hcoord, -, -⟩ := exists_etaleChart_comap_restrictIdeal_eq_coordIdeal p h c y hy
  exact ⟨V, hVU, d, c', hV, hyV, hcoord⟩

theorem isSmoothDivisor_comap_of_mem_inStrictNormalCrossingPosition (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p]
    (h : Y ⟶ X) [Smooth h] (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E)
    (D : X.IdealSheafData) (hD : D ∈ E) :
    IsSmoothDivisor (h ≫ p) (D.comap h) := by
  obtain ⟨i, hi, hEi⟩ := List.mem_iff_getElem.1 hD
  refine isSmoothDivisor_of_locally_coordIdeal (D.comap h) ?_
  intro y
  obtain ⟨U, hxU, m, c, a, _, hnone, hsome⟩ := ((inStrictNormalCrossingPosition_iff p E).1 hE).2 (h.base y)
  obtain ⟨V, d, c', _, _, hyV, _, htop, hcid⟩ := exists_etaleChart_comap_restrictIdeal_eq_coordIdeal p h c y hxU
  refine ⟨V, hyV, m + d, c', ?_⟩
  cases hai : a i with
  | none =>
      left
      have h1 := hnone i hi hai
      rw [hEi] at h1
      exact htop D h1
  | some t =>
      right
      refine ⟨Fin.castAdd d t, ?_⟩
      have h1 := hsome i hi t hai
      rw [hEi] at h1
      have h2 := hcid D {t} h1
      rw [Finset.map_singleton, Fin.castAddEmb_apply] at h2
      exact h2

private theorem strictNormalCrossings_chart_conditions_comap (p : X ⟶ Spec (CommRingCat.of k)) (h : Y ⟶ X)
    (E : List X.IdealSheafData) {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    (a : ℕ → Option (Fin m))
    (hinj : ∀ i < E.length, ∀ j < E.length, ∀ t : Fin m, a i = some t → a j = some t → i = j)
    (hnone : ∀ (i : ℕ) (hi : i < E.length), a i = none → restrictIdeal E[i] U = ⊤)
    (hsome : ∀ (i : ℕ) (hi : i < E.length) (t : Fin m), a i = some t →
      restrictIdeal E[i] U = c.coordIdeal {t})
    {V : Y.Opens} {d : ℕ} (c' : EtaleChart (h ≫ p) V (m + d))
    (htop : ∀ D : X.IdealSheafData, restrictIdeal D U = ⊤ → restrictIdeal (D.comap h) V = ⊤)
    (hcid : ∀ (D : X.IdealSheafData) (S : Finset (Fin m)), restrictIdeal D U = c.coordIdeal S →
      restrictIdeal (D.comap h) V = c'.coordIdeal (S.map (Fin.castAddEmb d))) :
    (∀ i < (E.map (fun D => D.comap h)).length, ∀ j < (E.map (fun D => D.comap h)).length,
        ∀ t : Fin (m + d), Option.map (Fin.castAdd d) (a i) = some t →
          Option.map (Fin.castAdd d) (a j) = some t → i = j) ∧
      (∀ (i : ℕ) (hi : i < (E.map (fun D => D.comap h)).length),
          Option.map (Fin.castAdd d) (a i) = none →
          restrictIdeal (E.map (fun D => D.comap h))[i] V = ⊤) ∧
      (∀ (i : ℕ) (hi : i < (E.map (fun D => D.comap h)).length) (t : Fin (m + d)),
          Option.map (Fin.castAdd d) (a i) = some t →
          restrictIdeal (E.map (fun D => D.comap h))[i] V = c'.coordIdeal {t}) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi j hj t h1 h2
    have hi' : i < E.length := by simpa using hi
    have hj' : j < E.length := by simpa using hj
    cases hai : a i with
    | none => rw [hai] at h1; simp at h1
    | some t₁ =>
      cases haj : a j with
      | none => rw [haj] at h2; simp at h2
      | some t₂ =>
        rw [hai] at h1
        rw [haj] at h2
        have e1 : Fin.castAdd d t₁ = t := Option.some.inj h1
        have e2 : Fin.castAdd d t₂ = t := Option.some.inj h2
        have ht : t₁ = t₂ := (Fin.castAddEmb d).injective (by
          rw [Fin.castAddEmb_apply, Fin.castAddEmb_apply, e1, e2])
        exact hinj i hi' j hj' t₁ hai (by rw [haj, ht])
  · intro i hi hni
    have hi' : i < E.length := by simpa using hi
    have hgi : (E.map (fun D => D.comap h))[i]'hi = (E[i]'hi').comap h := by simp
    rw [hgi]
    cases hai : a i with
    | none => exact htop _ (hnone i hi' hai)
    | some _ => rw [hai] at hni; simp at hni
  · intro i hi t h1
    have hi' : i < E.length := by simpa using hi
    have hgi : (E.map (fun D => D.comap h))[i]'hi = (E[i]'hi').comap h := by simp
    rw [hgi]
    cases hai : a i with
    | none => rw [hai] at h1; simp at h1
    | some t₁ =>
      rw [hai] at h1
      have e1 : Fin.castAdd d t₁ = t := Option.some.inj h1
      have h2 := hcid _ {t₁} (hsome i hi' t₁ hai)
      rw [Finset.map_singleton, Fin.castAddEmb_apply, e1] at h2
      exact h2

theorem inStrictNormalCrossingPosition_comap (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] (h : Y ⟶ X) [Smooth h]
    (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E) :
    InStrictNormalCrossingPosition (h ≫ p) (E.map (fun D => D.comap h)) := by
  rw [inStrictNormalCrossingPosition_iff]
  refine ⟨?_, ?_⟩
  · intro D hD
    rw [List.mem_map] at hD
    obtain ⟨D₀, hD₀, rfl⟩ := hD
    exact isSmoothDivisor_comap_of_mem_inStrictNormalCrossingPosition p h E hE D₀ hD₀
  · intro y
    obtain ⟨U, hxU, m, c, a, hinj, hnone, hsome⟩ := ((inStrictNormalCrossingPosition_iff p E).1 hE).2 (h.base y)
    obtain ⟨V, d, c', _, _, hyV, _, htop, hcid⟩ := exists_etaleChart_comap_restrictIdeal_eq_coordIdeal p h c y hxU
    have hL := strictNormalCrossings_chart_conditions_comap p h E c a hinj hnone hsome c' htop hcid
    exact ⟨V, hyV, m + d, c', fun i => Option.map (Fin.castAdd d) (a i),
      hL.1, hL.2.1, hL.2.2⟩

theorem inStrictNormalCrossingPosition_comap_singleton (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p]
    (h : Y ⟶ X) [Smooth h] (H : X.IdealSheafData) (hH : InStrictNormalCrossingPosition p [H]) :
    InStrictNormalCrossingPosition (h ≫ p) [H.comap h] := by
  have hcomp := inStrictNormalCrossingPosition_comap p h [H] hH
  rw [List.map_cons, List.map_nil] at hcomp
  exact hcomp

private theorem base_mem_support_of_mem_support_comap (f : Y ⟶ X) (I : X.IdealSheafData) (y : Y)
    (hy : y ∈ (I.comap f).support) : f.base y ∈ I.support := by
  rw [AlgebraicGeometry.Scheme.IdealSheafData.support_comap] at hy
  exact hy

theorem hasStrictNormalCrossingsWith_comap (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] (h : Y ⟶ X) [Smooth h]
    (Z : X.IdealSheafData) (E : List X.IdealSheafData) (hZ : HasStrictNormalCrossingsWith p Z E) :
    HasStrictNormalCrossingsWith (h ≫ p) (Z.comap h) (E.map (fun D => D.comap h)) := by
  intro y hy
  have hxZ : h.base y ∈ Z.support := base_mem_support_of_mem_support_comap h Z y hy
  obtain ⟨U, hxU, m, c, a, S, hinj, hnone, hsome, hZU⟩ := hZ (h.base y) hxZ
  obtain ⟨V, d, c', _, _, hyV, _, htop, hcid⟩ := exists_etaleChart_comap_restrictIdeal_eq_coordIdeal p h c y hxU
  have hL := strictNormalCrossings_chart_conditions_comap p h E c a hinj hnone hsome c' htop hcid
  exact ⟨V, hyV, m + d, c', fun i => Option.map (Fin.castAdd d) (a i), S.map (Fin.castAddEmb d),
    hL.1, hL.2.1, hL.2.2, hcid Z S hZU⟩

end FunctorialResolution.EmbeddedResolution
