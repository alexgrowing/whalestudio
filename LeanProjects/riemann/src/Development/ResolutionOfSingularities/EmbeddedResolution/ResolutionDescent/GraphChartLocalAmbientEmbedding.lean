import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupCoproduct
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AffineSpaceCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCoordinateCodimension
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCoordinateCodimensionPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceZeroSection
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceProduct
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SmoothPullbackLocalAmbientEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceChartPresentation
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.GraphChart
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceLinearEmbeddings
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem appTop_comp_hom_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (s : ↑(Z.presheaf.obj (Opposite.op ⊤))) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (f ≫ g))) s
      = (ConcreteCategory.hom (Scheme.Hom.appTop f))
        ((ConcreteCategory.hom (Scheme.Hom.appTop g)) s) := by
  have h : Scheme.Hom.appTop (f ≫ g) = Scheme.Hom.appTop g ≫ Scheme.Hom.appTop f := by
    simp [Scheme.Hom.appTop]
  rw [h]
  rfl

theorem graphMorphismToAffineSpace_comp_projLeft (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (D : (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).Opens) :
    graphMorphismToAffineSpace k M n q F D ≫ projLeft k M q = D.ι ≫ projLeft k M n := by
  refine AffineSpace.hom_ext ?_ ?_
  · rw [Category.assoc, projLeft_comp_affineSpaceIndexedByToSpec, Category.assoc, projLeft_comp_affineSpaceIndexedByToSpec, graphMorphismToAffineSpace_comp_affineSpaceIndexedByToSpec]
  · intro i
    obtain ⟨a⟩ := i
    show (ConcreteCategory.hom (Scheme.Hom.appTop (graphMorphismToAffineSpace k M n q F D ≫ projLeft k M q)))
          (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} a))
        = (ConcreteCategory.hom (Scheme.Hom.appTop (D.ι ≫ projLeft k M n)))
          (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} a))
    rw [appTop_comp_hom_apply, appTop_comp_hom_apply, projLeft_appTop_coord, projLeft_appTop_coord,
      graphMorphismToAffineSpace_appTop_coord_inl]

private theorem smooth_of_smooth_comp_isOpenImmersion {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (i : Y ⟶ Z) [IsOpenImmersion i] (h : Smooth (f ≫ i)) : Smooth f := by
  have hsq : f ≫ i = 𝟙 X ≫ (f ≫ i) := by simp
  have hp : IsPullback f (𝟙 X) i (f ≫ i) := by
    refine IsPullback.of_isLimit (c := Limits.PullbackCone.mk f (𝟙 X) hsq) ?_
    refine Limits.PullbackCone.IsLimit.mk _ (fun s => s.snd) (fun s => ?_) (fun s => ?_)
      (fun s m h₁ h₂ => ?_)
    · have hc : s.fst ≫ i = (s.snd ≫ f) ≫ i := by
        rw [Category.assoc]; exact s.condition
      exact ((cancel_mono i).mp hc).symm
    · simp
    · simpa using h₂
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hp.flip h

private theorem ker_subschemeι_app {Z : Scheme.{u}} (I : Z.IdealSheafData)
    (V : Z.affineOpens) :
    RingHom.ker (Scheme.Hom.app I.subschemeι (V : Z.Opens)).hom = I.ideal V := by
  have hinj : Function.Injective ⇑((I.subschemeObjIso V).inv.hom) := by
    intro a b hab
    have h1 : ((I.subschemeObjIso V).inv ≫ (I.subschemeObjIso V).hom).hom a
        = ((I.subschemeObjIso V).inv ≫ (I.subschemeObjIso V).hom).hom b := by
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, hab]
    simpa using h1
  rw [Scheme.IdealSheafData.subschemeι_app]
  ext x
  simp only [CommRingCat.hom_comp, RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom]
  rw [← map_zero ((I.subschemeObjIso V).inv.hom), hinj.eq_iff, Ideal.Quotient.eq_zero_iff_mem]

private theorem ideal_top_ofIdealTop_eq {Z : Scheme.{u}} [IsAffine Z]
    (J : Ideal Γ(Z, ⊤)) :
    (Scheme.IdealSheafData.ofIdealTop J).ideal ⟨⊤, isAffineOpen_top Z⟩ = J := by
  have h := (Scheme.IdealSheafData.equivOfIsAffine (X := Z)).apply_symm_apply J
  rw [Scheme.IdealSheafData.equivOfIsAffine_symm_apply,
    Scheme.IdealSheafData.equivOfIsAffine_apply] at h
  exact h

private theorem eq_of_ideal_top_eq {Z : Scheme.{u}} [IsAffine Z] {I J : Z.IdealSheafData}
    (h : I.ideal ⟨⊤, isAffineOpen_top Z⟩ = J.ideal ⟨⊤, isAffineOpen_top Z⟩) : I = J := by
  have hI := (Scheme.IdealSheafData.equivOfIsAffine (X := Z)).symm_apply_apply I
  have hJ := (Scheme.IdealSheafData.equivOfIsAffine (X := Z)).symm_apply_apply J
  rw [Scheme.IdealSheafData.equivOfIsAffine_apply,
    Scheme.IdealSheafData.equivOfIsAffine_symm_apply] at hI hJ
  rw [← hI, ← hJ, h]

private theorem ofIdealTop_sup {Z : Scheme.{u}} [IsAffine Z] (I J : Ideal Γ(Z, ⊤)) :
    Scheme.IdealSheafData.ofIdealTop (I ⊔ J) =
      Scheme.IdealSheafData.ofIdealTop I ⊔ Scheme.IdealSheafData.ofIdealTop J := by
  refine eq_of_ideal_top_eq ?_
  simp only [Scheme.IdealSheafData.ideal_sup, Pi.sup_apply, ideal_top_ofIdealTop_eq]

private theorem comap_ofIdealTop_span {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (s : Set Γ(Y, ⊤)) :
    (Scheme.IdealSheafData.ofIdealTop (Ideal.span s)).comap f =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.span (⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop f)) '' s)) := by
  rw [Scheme.IdealSheafData.comap_ofIdealTop, Ideal.map_span]

private theorem coordSubspaceIdeal_univ_eq_ofIdealTop (k : Type u) [Field k] (m : ℕ) :
    coordSubspaceIdeal k m Finset.univ =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.span (Set.range (fun i : Fin m =>
          AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} i)))) := by
  rw [coordSubspaceIdeal_eq_ofIdealTop_span_coord, Finset.coe_univ, Set.image_univ]

private theorem ker_eq_ofIdealTop_ker_appTop {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [IsClosedImmersion f] :
    Scheme.Hom.ker f =
      Scheme.IdealSheafData.ofIdealTop
        (RingHom.ker (CommRingCat.Hom.hom (Scheme.Hom.appTop f))) := by
  have : IsIso (Scheme.Hom.toImage f) := inferInstance
  have hc : Scheme.Hom.toImage f ≫ (Scheme.Hom.ker f).subschemeι = f :=
    Scheme.Hom.toImage_imageι f
  have h2 : ∀ z, (CommRingCat.Hom.hom (Scheme.Hom.appTop (inv (Scheme.Hom.toImage f))))
      ((CommRingCat.Hom.hom (Scheme.Hom.appTop (Scheme.Hom.toImage f))) z) = z := by
    intro z
    have hz := (appTop_comp_hom_apply (inv (Scheme.Hom.toImage f))
      (Scheme.Hom.toImage f) z).symm
    rw [IsIso.inv_hom_id] at hz
    simpa using hz
  have hinj : Function.Injective
      ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop (Scheme.Hom.toImage f))) := by
    intro a b hab
    have ha := h2 a
    rw [hab, h2 b] at ha
    exact ha.symm
  have happ : ∀ z, (CommRingCat.Hom.hom (Scheme.Hom.appTop f)) z
      = (CommRingCat.Hom.hom (Scheme.Hom.appTop (Scheme.Hom.toImage f)))
        ((CommRingCat.Hom.hom (Scheme.Hom.appTop ((Scheme.Hom.ker f).subschemeι))) z) := by
    intro z
    conv_lhs => rw [← hc]
    rw [appTop_comp_hom_apply]
  have hkers : RingHom.ker (CommRingCat.Hom.hom (Scheme.Hom.appTop f)) =
      RingHom.ker (CommRingCat.Hom.hom
        (Scheme.Hom.appTop ((Scheme.Hom.ker f).subschemeι))) := by
    ext z
    simp only [RingHom.mem_ker]
    rw [happ z]
    constructor
    · intro hz
      apply hinj
      rw [hz, map_zero]
    · intro hz
      rw [hz, map_zero]
  refine eq_of_ideal_top_eq ?_
  rw [ideal_top_ofIdealTop_eq,
    ← ker_subschemeι_app (Scheme.Hom.ker f) ⟨⊤, isAffineOpen_top Y⟩]
  exact hkers.symm

private theorem coordSubspaceIdeal_univ_comap_affineSpaceIsoOfEquiv (k : Type u) [Field k] (c q : ℕ) :
    (coordSubspaceIdeal k (c + q) Finset.univ).comap
        (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} c q) (Spec (CommRingCat.of k))).hom
      = (coordSubspaceIdeal k c Finset.univ).comap (projLeft k c q)
        ⊔ (coordSubspaceIdeal k q Finset.univ).comap (projRight k c q) := by
  have h1 : ∀ i : ULift.{u, 0} (Fin (c + q)),
      (CommRingCat.Hom.hom (Scheme.Hom.appTop
        (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} c q) (Spec (CommRingCat.of k))).hom))
          (AffineSpace.coord (Spec (CommRingCat.of k)) i)
        = AffineSpace.coord (Spec (CommRingCat.of k)) ((uliftFinSumEquiv.{u} c q).symm i) := by
    intro i
    simp [affineSpaceIsoOfEquiv]
  have h2 : ∀ a : Fin c,
      (CommRingCat.Hom.hom (Scheme.Hom.appTop (projLeft k c q)))
          (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} a))
        = AffineSpace.coord (Spec (CommRingCat.of k))
            (ULift.up.{u, 0} (Sum.inl a) : ULift.{u, 0} (Fin c ⊕ Fin q)) := by
    intro a
    simp
  have h3 : ∀ b : Fin q,
      (CommRingCat.Hom.hom (Scheme.Hom.appTop (projRight k c q)))
          (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} b))
        = AffineSpace.coord (Spec (CommRingCat.of k))
            (ULift.up.{u, 0} (Sum.inr b) : ULift.{u, 0} (Fin c ⊕ Fin q)) := by
    intro b
    simp
  have hset :
      ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop
          (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} c q) (Spec (CommRingCat.of k))).hom)) ''
        Set.range (fun i : Fin (c + q) =>
          AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} i))
      = (⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop (projLeft k c q))) ''
          Set.range (fun a : Fin c =>
            AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} a)))
        ∪ (⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop (projRight k c q))) ''
          Set.range (fun b : Fin q =>
            AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} b))) := by
    ext x
    simp only [Set.mem_image, Set.mem_range, Set.mem_union]
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      rw [h1]
      rcases hcase : ((uliftFinSumEquiv.{u} c q).symm (ULift.up.{u, 0} i)).down with a | b
      · refine Or.inl ⟨_, ⟨a, rfl⟩, ?_⟩
        rw [h2]
        have hEq : ULift.up.{u, 0} (Sum.inl a : Fin c ⊕ Fin q)
            = (uliftFinSumEquiv.{u} c q).symm (ULift.up.{u, 0} i) := by
          rw [← hcase]
        rw [hEq]
      · refine Or.inr ⟨_, ⟨b, rfl⟩, ?_⟩
        rw [h3]
        have hEq : ULift.up.{u, 0} (Sum.inr b : Fin c ⊕ Fin q)
            = (uliftFinSumEquiv.{u} c q).symm (ULift.up.{u, 0} i) := by
          rw [← hcase]
        rw [hEq]
    · rintro (⟨y, ⟨a, rfl⟩, rfl⟩ | ⟨y, ⟨b, rfl⟩, rfl⟩)
      · refine ⟨_, ⟨((uliftFinSumEquiv.{u} c q) (ULift.up.{u, 0} (Sum.inl a))).down, rfl⟩, ?_⟩
        rw [h1, h2]
        congr 1
        rw [ULift.up_down, Equiv.symm_apply_apply]
      · refine ⟨_, ⟨((uliftFinSumEquiv.{u} c q) (ULift.up.{u, 0} (Sum.inr b))).down, rfl⟩, ?_⟩
        rw [h1, h3]
        congr 1
        rw [ULift.up_down, Equiv.symm_apply_apply]
  rw [coordSubspaceIdeal_univ_eq_ofIdealTop, coordSubspaceIdeal_univ_eq_ofIdealTop,
    coordSubspaceIdeal_univ_eq_ofIdealTop, comap_ofIdealTop_span, comap_ofIdealTop_span,
    comap_ofIdealTop_span, ← ofIdealTop_sup, ← Ideal.span_union, hset]

theorem hasSmoothCoordCodim_add_of_smooth_graphMorphism (hsm : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k]
    {A A' : Scheme.{u}} [IsAffine A] [IsAffine A'] (M c n q : ℕ)
    (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [IsClosedImmersion ρ]
    (hρ : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))) ρ c)
    (g : A' ⟶ A)
    (ρ' : A' ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))) [IsClosedImmersion ρ']
    (hcomm : ρ' ≫ projLeft k M n = g ≫ ρ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (Δ : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (hker : RingHom.ker (CommRingCat.Hom.hom (Scheme.Hom.appTop ρ')) =
      Ideal.map (CommRingCat.Hom.hom (Scheme.Hom.appTop (projLeft k M n)))
          (RingHom.ker (CommRingCat.Hom.hom (Scheme.Hom.appTop ρ))) ⊔
        Ideal.span (Set.range F))
    (hD : ρ' ⁻¹ᵁ ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ) = ⊤)
    (hsmooth : Smooth (graphMorphismToAffineSpace k M n q F
      ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ))) :
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin n))) ρ' (c + q) := by
  classical
  have hDaff : IsAffine
      (((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ).toScheme) :=
    (isAffineOpen_top (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n)))).basicOpen Δ
  have hker' : Scheme.Hom.ker ρ' =
      (Scheme.Hom.ker ρ).comap (projLeft k M n) ⊔
        Scheme.IdealSheafData.ofIdealTop (Ideal.span (Set.range F)) := by
    rw [ker_eq_ofIdealTop_ker_appTop ρ', hker, ofIdealTop_sup,
      ker_eq_ofIdealTop_ker_appTop ρ, Scheme.IdealSheafData.comap_ofIdealTop]
  have hcomapEq : (coordSubspaceIdeal k q Finset.univ).comap
        (graphMorphismToAffineSpace k M n q F ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ)
          ≫ projRight k M q)
      = (Scheme.IdealSheafData.ofIdealTop (Ideal.span (Set.range F))).comap
          ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ).ι := by
    have hset :
        ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop
            (graphMorphismToAffineSpace k M n q F
              ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ)
              ≫ projRight k M q))) ''
          Set.range (fun j : Fin q =>
            AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} j))
        = ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop
            ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ).ι)) ''
          Set.range F := by
      rw [← Set.range_comp, ← Set.range_comp]
      refine congrArg Set.range (funext fun j => ?_)
      show (ConcreteCategory.hom (Scheme.Hom.appTop
            (graphMorphismToAffineSpace k M n q F
              ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ)
              ≫ projRight k M q)))
            (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} j))
          = (ConcreteCategory.hom (Scheme.Hom.appTop
              ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ).ι)) (F j)
      rw [appTop_comp_hom_apply, projRight_appTop_coord, graphMorphismToAffineSpace_appTop_coord_inr]
    rw [coordSubspaceIdeal_univ_eq_ofIdealTop, comap_ofIdealTop_span,
      comap_ofIdealTop_span, hset]
  intro x
  obtain ⟨U₀, hU₀, q₀, hq₀s, hq₀o, hq₀k⟩ := hρ (g.base x)
  have := hq₀s
  have hmem1 : (projLeft k M n).base (ρ'.base x) ∈ U₀ := by
    have hb : (ρ' ≫ projLeft k M n).base x = (g ≫ ρ).base x := by rw [hcomm]
    simpa using (hb ▸ hU₀ : _)
  have hmem2 : ρ'.base x ∈
      (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ := by
    have hx : x ∈ ρ' ⁻¹ᵁ ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ) := by
      rw [hD]; trivial
    exact hx
  set U : (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).Opens :=
    (projLeft k M n ⁻¹ᵁ U₀) ⊓
      ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ) with hUdef
  have hUD : U ≤ (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ := by
    rw [hUdef]; exact inf_le_right
  set G : U.toScheme ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin q)) :=
    (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).homOfLE hUD ≫
      graphMorphismToAffineSpace k M n q F ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen Δ)
    with hGdef
  have hGproj : G ≫ projLeft k M q = U.ι ≫ projLeft k M n := by
    rw [hGdef, Category.assoc, graphMorphismToAffineSpace_comp_projLeft, ← Category.assoc, Scheme.homOfLE_ι]
  have hsub : Set.range ⇑G.base ⊆ Set.range ⇑(projLeft k M q ⁻¹ᵁ U₀).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro y ⟨z, rfl⟩
    have hz : (G ≫ projLeft k M q).base z = (U.ι ≫ projLeft k M n).base z := by rw [hGproj]
    have hz' : (projLeft k M q).base (G.base z) = (projLeft k M n).base (U.ι.base z) := by
      simpa using hz
    show (projLeft k M q).base (G.base z) ∈ U₀
    rw [hz']
    have hzU : U.ι.base z ∈ U := z.2
    exact hzU.1
  set L : U.toScheme ⟶ (projLeft k M q ⁻¹ᵁ U₀).toScheme :=
    IsOpenImmersion.lift (projLeft k M q ⁻¹ᵁ U₀).ι G hsub with hLdef
  have hLfac : L ≫ (projLeft k M q ⁻¹ᵁ U₀).ι = G :=
    IsOpenImmersion.lift_fac _ _ hsub
  have hGsmooth : Smooth G := by
    rw [hGdef]
    have := hsmooth
    infer_instance
  have hLsmooth : Smooth L := by
    refine smooth_of_smooth_comp_isOpenImmersion L (projLeft k M q ⁻¹ᵁ U₀).ι ?_
    rw [hLfac]; exact hGsmooth
  set P : (projLeft k M q ⁻¹ᵁ U₀).toScheme ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin c ⊕ Fin q)) :=
    prodMapOnPreimage k M q c U₀ q₀ with hPdef
  have hPsmooth : Smooth P := smooth_prodMapOnPreimage hsm k M q c U₀ q₀ hq₀o
  set chart : U.toScheme ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin (c + q))) :=
    L ≫ P ≫ (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} c q) (Spec (CommRingCat.of k))).hom
    with hchartdef
  refine ⟨U, ⟨hmem1, hmem2⟩, chart, ?_, ?_, ?_⟩
  · have := hLsmooth
    have := hPsmooth
    rw [hchartdef]
    infer_instance
  · rw [hchartdef, Category.assoc, Category.assoc,
      affineSpaceIsoOfEquiv_hom_comp_toSpec, hPdef, prodMapOnPreimage_comp_affineSpaceIndexedByToSpec, ← Category.assoc,
      hLfac, hGdef, Category.assoc, graphMorphismToAffineSpace_comp_affineSpaceIndexedByToSpec, ← Category.assoc, Scheme.homOfLE_ι]
  · have hA : (coordSubspaceIdeal k c Finset.univ).comap (L ≫ P ≫ projLeft k c q)
        = (Scheme.Hom.ker ρ).comap (U.ι ≫ projLeft k M n) := by
      rw [hPdef, ← morphismRestrict_projLeft_comp k M q c U₀ q₀ hq₀o,
        Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, ← hq₀k,
        restrictIdeal_eq_comap_ι, ← Scheme.IdealSheafData.comap_comp,
        ← Scheme.IdealSheafData.comap_comp, Category.assoc, morphismRestrict_ι,
        ← Category.assoc, hLfac, hGproj]
    have hB : (coordSubspaceIdeal k q Finset.univ).comap (L ≫ P ≫ projRight k c q)
        = (Scheme.IdealSheafData.ofIdealTop (Ideal.span (Set.range F))).comap U.ι := by
      rw [hPdef, prodMapOnPreimage_comp_projRight, ← Category.assoc, hLfac, hGdef, Category.assoc,
        Scheme.IdealSheafData.comap_comp, hcomapEq, ← Scheme.IdealSheafData.comap_comp,
        Scheme.homOfLE_ι]
    have key : (coordSubspaceIdeal k (c + q) Finset.univ).comap chart
        = (coordSubspaceIdeal k c Finset.univ).comap (L ≫ P ≫ projLeft k c q)
          ⊔ (coordSubspaceIdeal k q Finset.univ).comap (L ≫ P ≫ projRight k c q) := by
      rw [hchartdef, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp,
        coordSubspaceIdeal_univ_comap_affineSpaceIsoOfEquiv, Scheme.IdealSheafData.comap_sup,
        Scheme.IdealSheafData.comap_sup]
      simp only [← Scheme.IdealSheafData.comap_comp]
    have key2 : restrictIdeal (Scheme.Hom.ker ρ') U
        = (Scheme.Hom.ker ρ).comap (U.ι ≫ projLeft k M n)
          ⊔ (Scheme.IdealSheafData.ofIdealTop (Ideal.span (Set.range F))).comap U.ι := by
      rw [restrictIdeal_eq_comap_ι, hker', Scheme.IdealSheafData.comap_sup,
        ← Scheme.IdealSheafData.comap_comp]
    rw [key2, key, hA, hB]

theorem smoothPullbackHasLocalAmbientEmbedding_of_hasGraphChart (hsm : AffineSpaceIsSmooth.{u})
    (hgr : SmoothPullbackHasGraphChart.{u}) : SmoothPullbackHasLocalAmbientEmbedding.{u} := by
  intro k _ _ X Y A pX pY pA _ _ _ _ i _ hi M c ρ _ hρ hρc r h _ hh y
  obtain ⟨V, hyV, hVaff, A', pA', hA'aff, hA'sm, hA'ft, hA'qc, g, hgsm, hgpA, j, hjci,
    hjpb, n, q, hnqr, σ, hσci, hσcomm, F, Δ, hkerσ, hDtop, hgrsm⟩ :=
      hgr k X Y A pX pY pA i hi M ρ hρ r h hh y
  have := hA'aff
  have := hσci
  refine ⟨V, hyV, hVaff, A', pA', hA'aff, hA'sm, hA'ft, hA'qc, g, hgsm, hgpA, j, hjci, hjpb,
    n, by omega, ?_⟩
  intro N hN
  obtain ⟨p, rfl⟩ : ∃ p, N = n + p := ⟨N - n, by omega⟩
  rw [show M + (n + p) = M + n + p from by omega,
    show c + (n + p - r) = c + q + p from by omega]
  have hcc : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin n)))
      σ (c + q) :=
    hasSmoothCoordCodim_add_of_smooth_graphMorphism hsm k M c n q ρ hρc g σ hσcomm F Δ hkerσ hDtop hgrsm
  have hcc1 : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (M + n))))
      (σ ≫ (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} M n) (Spec (CommRingCat.of k))).hom)
      (c + q) :=
    HasSmoothCoordCodim.comp_iso_hom hcc
      (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} M n) (Spec (CommRingCat.of k)))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (M + n))))
      (affineSpaceIsoOfEquiv_hom_comp_toSpec k (uliftFinSumEquiv.{u} M n))
  have : IsClosedImmersion
      (σ ≫ (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} M n) (Spec (CommRingCat.of k))).hom) :=
    inferInstance
  have hpad := HasSmoothCoordCodim.comp_affineSpaceInl_affineSpaceIsoOfEquiv hsm k
      (σ ≫ (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} M n) (Spec (CommRingCat.of k))).hom) p hcc1
  refine ⟨(σ ≫ (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} M n) (Spec (CommRingCat.of k))).hom) ≫
      affineSpaceInl k (M + n) p ≫
        (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} (M + n) p) (Spec (CommRingCat.of k))).hom,
    inferInstance, ?_, hpad⟩
  have hstruct : affineSpaceInl k (M + n) p ≫
      (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} (M + n) p) (Spec (CommRingCat.of k))).hom ≫
        affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (M + n + p)))
      = affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (M + n))) := by
    rw [affineSpaceIsoOfEquiv_hom_comp_toSpec, affineSpaceInl_comp_affineSpaceIndexedByToSpec]
  simp only [Category.assoc]
  rw [hstruct, affineSpaceIsoOfEquiv_hom_comp_toSpec, ← projLeft_comp_affineSpaceIndexedByToSpec, ← Category.assoc,
    hσcomm, Category.assoc, hρ, hgpA]

end FunctorialResolution.EmbeddedResolution

end
