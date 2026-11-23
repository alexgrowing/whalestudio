import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.PowerContainmentAndOrderLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IdealSheafFlatComapInjective
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DescentHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.StrictPullbackBlowupSeq
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u v

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

variable {A B C : Scheme.{u}}

def rangeOpens (γ : A ⟶ B) (W : A.Opens) (h : IsOpenImmersion (W.ι ≫ γ)) : B.Opens :=
  ⟨Set.range ⇑(W.ι ≫ γ).base, by
    have := h
    exact IsOpenImmersion.isOpen_range _⟩

theorem mem_rangeOpens_iff (γ : A ⟶ B) (W : A.Opens) (h : IsOpenImmersion (W.ι ≫ γ))
    (b : ↥B) : b ∈ rangeOpens γ W h ↔ ∃ w : W.toScheme, (W.ι ≫ γ).base w = b :=
  Iff.rfl

theorem range_ι_comp_eq_range_rangeOpens_ι (γ : A ⟶ B) (W : A.Opens) (h : IsOpenImmersion (W.ι ≫ γ)) :
    Set.range ⇑(W.ι ≫ γ).base = Set.range ⇑(rangeOpens γ W h).ι.base :=
  (Scheme.Opens.range_ι (rangeOpens γ W h)).symm

noncomputable def isoRangeOpens (γ : A ⟶ B) (W : A.Opens) (h : IsOpenImmersion (W.ι ≫ γ)) :
    W.toScheme ≅ (rangeOpens γ W h).toScheme :=
  letI : IsOpenImmersion (W.ι ≫ γ) := h
  IsOpenImmersion.isoOfRangeEq (W.ι ≫ γ) (rangeOpens γ W h).ι (range_ι_comp_eq_range_rangeOpens_ι γ W h)

theorem isoRangeOpens_hom_ι (γ : A ⟶ B) (W : A.Opens) (h : IsOpenImmersion (W.ι ≫ γ)) :
    (isoRangeOpens γ W h).hom ≫ (rangeOpens γ W h).ι = W.ι ≫ γ := by
  have : IsOpenImmersion (W.ι ≫ γ) := h
  have hsub : Set.range ⇑(W.ι ≫ γ).base ⊆ Set.range ⇑(rangeOpens γ W h).ι.base := by
    intro x hx
    rw [← range_ι_comp_eq_range_rangeOpens_ι γ W h]
    exact hx
  exact IsOpenImmersion.lift_fac (rangeOpens γ W h).ι (W.ι ≫ γ) hsub

theorem isoRangeOpens_inv_comp (γ : A ⟶ B) (W : A.Opens) (h : IsOpenImmersion (W.ι ≫ γ)) :
    (isoRangeOpens γ W h).inv ≫ W.ι ≫ γ = (rangeOpens γ W h).ι := by
  have : IsOpenImmersion (W.ι ≫ γ) := h
  show (IsOpenImmersion.isoOfRangeEq (W.ι ≫ γ) (rangeOpens γ W h).ι
      (range_ι_comp_eq_range_rangeOpens_ι γ W h)).inv ≫ W.ι ≫ γ = (rangeOpens γ W h).ι
  simp

theorem isoRangeOpens_hom_ι_assoc (γ : A ⟶ B) (W : A.Opens) (h : IsOpenImmersion (W.ι ≫ γ))
    (f : B ⟶ C) :
    (isoRangeOpens γ W h).hom ≫ (rangeOpens γ W h).ι ≫ f = W.ι ≫ γ ≫ f := by
  rw [← Category.assoc, isoRangeOpens_hom_ι, Category.assoc]

theorem isoRangeOpens_inv_comp_assoc (γ : A ⟶ B) (W : A.Opens) (h : IsOpenImmersion (W.ι ≫ γ))
    (f : B ⟶ C) :
    (isoRangeOpens γ W h).inv ≫ W.ι ≫ γ ≫ f = (rangeOpens γ W h).ι ≫ f := by
  have key : (isoRangeOpens γ W h).inv ≫ W.ι ≫ γ = (rangeOpens γ W h).ι := by
    rw [← isoRangeOpens_hom_ι γ W h, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hassoc : (isoRangeOpens γ W h).inv ≫ W.ι ≫ γ ≫ f
      = ((isoRangeOpens γ W h).inv ≫ W.ι ≫ γ) ≫ f := by
    simp only [Category.assoc]
  rw [hassoc, key]

theorem exists_mem_rangeOpens (γ : A ⟶ B)
    (hγ : MaxContactFunctoriality.IsLocalIsomorphism γ) [AlgebraicGeometry.Surjective γ]
    (b : ↥B) :
    ∃ (U : A.Opens) (hU : IsOpenImmersion (U.ι ≫ γ)), b ∈ rangeOpens γ U hU := by
  obtain ⟨a, ha⟩ := AlgebraicGeometry.Surjective.surj (f := γ) b
  obtain ⟨U, haU, hU⟩ := hγ a
  have hmem : a ∈ Set.range ⇑U.ι.base := by
    rw [Scheme.Opens.range_ι]
    exact haU
  obtain ⟨w, hw⟩ := hmem
  refine ⟨U, hU, (mem_rangeOpens_iff γ U hU b).mpr ⟨w, ?_⟩⟩
  have h1 : (U.ι ≫ γ).base w = γ.base (U.ι.base w) := by simp
  rw [h1, hw, ha]

private theorem le_of_map_le_of_leftInverse {R S : Type u} [CommRing R] [CommRing S]
    (ψ : R →+* S) (ψ' : S →+* R) (hinv : ∀ x, ψ' (ψ x) = x) {A C : Ideal R}
    (hle : A.map ψ ≤ C.map ψ) : A ≤ C := by
  intro a ha
  have h1 : ψ a ∈ C.map ψ := hle (Ideal.mem_map_of_mem ψ ha)
  have h2 : ψ' (ψ a) ∈ (C.map ψ).map ψ' := Ideal.mem_map_of_mem ψ' h1
  rw [hinv a, Ideal.map_map] at h2
  have h3 : ψ'.comp ψ = RingHom.id R := RingHom.ext hinv
  rw [h3, Ideal.map_id] at h2
  exact h2

private theorem span_eq_top_of_forall_mem_basicOpen {X : Scheme.{u}} {V : X.Opens}
    (hV : IsAffineOpen V) (S : Set Γ(X, V))
    (hcov : ∀ x : ↥X, x ∈ V → ∃ f ∈ S, x ∈ X.basicOpen f) :
    Ideal.span S = ⊤ := by
  rw [← hV.iSup_basicOpen_eq_self_iff]
  refine le_antisymm (iSup_le fun f => X.basicOpen_le (f : Γ(X, V))) ?_
  intro x hx
  obtain ⟨f, hfS, hxf⟩ := hcov x hx
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨f, hfS⟩, hxf⟩

private theorem comap_ι_le_comap_ι_of_le {X : Scheme.{u}} {I J : X.IdealSheafData}
    {V W : X.Opens} (hVW : V ≤ W) (hIJ : I.comap W.ι ≤ J.comap W.ι) :
    I.comap V.ι ≤ J.comap V.ι := by
  have hsub : Set.range ⇑V.ι.base ⊆ Set.range ⇑W.ι.base := by
    rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    exact hVW
  have hfac : IsOpenImmersion.lift W.ι V.ι hsub ≫ W.ι = V.ι :=
    IsOpenImmersion.lift_fac W.ι V.ι hsub
  have h1 : (I.comap W.ι).comap (IsOpenImmersion.lift W.ι V.ι hsub) = I.comap V.ι := by
    rw [← Scheme.IdealSheafData.comap_comp, hfac]
  have h2 : (J.comap W.ι).comap (IsOpenImmersion.lift W.ι V.ι hsub) = J.comap V.ι := by
    rw [← Scheme.IdealSheafData.comap_comp, hfac]
  rw [← h1, ← h2]
  exact Scheme.IdealSheafData.comap_mono _ hIJ

private theorem ideal_le_ideal_of_comap_ι_le {X : Scheme.{u}} {I J : X.IdealSheafData}
    (V : X.affineOpens)
    (hc : I.comap (V : X.Opens).ι ≤ J.comap (V : X.Opens).ι) :
    I.ideal V ≤ J.ideal V := by
  have : IsAffine (V : X.Opens).toScheme := V.2
  have haffine : IsAffineOpen ((V : X.Opens).ι ''ᵁ (⊤ : (V : X.Opens).toScheme.Opens)) := by
    rw [Scheme.Opens.ι_image_top]
    exact V.2
  have e : (⊤ : (V : X.Opens).toScheme.Opens)
      ≤ (V : X.Opens).ι ⁻¹ᵁ ((V : X.Opens).ι ''ᵁ (⊤ : (V : X.Opens).toScheme.Opens)) :=
    fun x hx => ⟨x, hx, rfl⟩
  have hV : V = (⟨(V : X.Opens).ι ''ᵁ (⊤ : (V : X.Opens).toScheme.Opens), haffine⟩ : X.affineOpens) :=
    Subtype.ext (Scheme.Opens.ι_image_top _).symm
  have hI := Scheme.IdealSheafData.comap_ideal_eq_map_appLE I (V : X.Opens).ι
      ⟨(V : X.Opens).ι ''ᵁ (⊤ : (V : X.Opens).toScheme.Opens), haffine⟩
      ⟨⊤, isAffineOpen_top (V : X.Opens).toScheme⟩ e
  have hJ := Scheme.IdealSheafData.comap_ideal_eq_map_appLE J (V : X.Opens).ι
      ⟨(V : X.Opens).ι ''ᵁ (⊤ : (V : X.Opens).toScheme.Opens), haffine⟩
      ⟨⊤, isAffineOpen_top (V : X.Opens).toScheme⟩ e
  have hle : (I.comap (V : X.Opens).ι).ideal ⟨⊤, isAffineOpen_top (V : X.Opens).toScheme⟩
      ≤ (J.comap (V : X.Opens).ι).ideal ⟨⊤, isAffineOpen_top (V : X.Opens).toScheme⟩ :=
    hc ⟨⊤, isAffineOpen_top (V : X.Opens).toScheme⟩
  rw [hI, hJ] at hle
  have happ : ((V : X.Opens).ι).appLE
        ((V : X.Opens).ι ''ᵁ (⊤ : (V : X.Opens).toScheme.Opens))
        (⊤ : (V : X.Opens).toScheme.Opens) e
      = (((V : X.Opens).ι).appIso (⊤ : (V : X.Opens).toScheme.Opens)).hom :=
    (Scheme.Hom.appIso_hom' _ _).symm
  rw [happ] at hle
  rw [hV]
  refine le_of_map_le_of_leftInverse _
    ((((V : X.Opens).ι).appIso (⊤ : (V : X.Opens).toScheme.Opens)).inv.hom) ?_ hle
  intro x
  have hxx : ((V : X.Opens).ι.appIso (⊤ : (V : X.Opens).toScheme.Opens)).hom ≫
      ((V : X.Opens).ι.appIso (⊤ : (V : X.Opens).toScheme.Opens)).inv = 𝟙 _ :=
    Iso.hom_inv_id _
  have h2 : (((V : X.Opens).ι.appIso (⊤ : (V : X.Opens).toScheme.Opens)).hom ≫
      ((V : X.Opens).ι.appIso (⊤ : (V : X.Opens).toScheme.Opens)).inv).hom x = x := by
    rw [hxx]; simp
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2
  exact h2

private theorem exists_pow_smul_mem_of_map_mem {X : Scheme.{u}} (V : X.affineOpens)
    (C : Ideal Γ(X, (V : X.Opens))) (f a : Γ(X, (V : X.Opens)))
    (hmem : (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom a ∈
      Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom C) :
    ∃ n : ℕ, f ^ n • a ∈ C := by
  have : IsLocalization.Away f Γ(X, X.basicOpen f) := V.2.isLocalization_basicOpen f
  have halg : (algebraMap Γ(X, (V : X.Opens)) Γ(X, X.basicOpen f))
      = (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom := rfl
  rw [← halg] at hmem
  rw [IsLocalization.mem_map_algebraMap_iff (Submonoid.powers f)] at hmem
  obtain ⟨⟨⟨c, hc⟩, ⟨m, hm⟩⟩, heq⟩ := hmem
  obtain ⟨k, hk⟩ := hm
  have hk' : f ^ k = m := hk
  have heq' : (algebraMap Γ(X, (V : X.Opens)) Γ(X, X.basicOpen f)) (a * m)
      = (algebraMap Γ(X, (V : X.Opens)) Γ(X, X.basicOpen f)) c := by
    simpa using heq
  obtain ⟨d, hd⟩ :=
    (IsLocalization.eq_iff_exists (Submonoid.powers f) Γ(X, X.basicOpen f)).mp heq'
  obtain ⟨j, hj⟩ := d.2
  have hj' : f ^ j = (d : Γ(X, (V : X.Opens))) := hj
  refine ⟨j + k, ?_⟩
  have hmul : f ^ (j + k) * a = (d : Γ(X, (V : X.Opens))) * c := by
    rw [pow_add, hj', hk', mul_assoc, mul_comm m a]
    exact hd
  rw [smul_eq_mul, hmul]
  exact Ideal.mul_mem_left _ _ hc

theorem le_of_forall_comap_ι_le {ι : Type v} (U : ι → B.Opens)
    (hU : ∀ b : ↥B, ∃ i, b ∈ U i) (J K : B.IdealSheafData)
    (h : ∀ i, J.comap (U i).ι ≤ K.comap (U i).ι) : J ≤ K := by
  show ∀ V : B.affineOpens, J.ideal V ≤ K.ideal V
  intro V a ha
  have hVaff : IsAffineOpen (V : B.Opens) := V.2
  have hspan : Ideal.span {f : Γ(B, (V : B.Opens)) | ∃ i, B.basicOpen f ≤ U i} = ⊤ := by
    refine span_eq_top_of_forall_mem_basicOpen hVaff _ ?_
    intro x hx
    obtain ⟨i, hi⟩ := hU x
    obtain ⟨f, hfle, hxf⟩ :=
      AlgebraicGeometry.IsAffineOpen.exists_basicOpen_le hVaff (⟨x, hi⟩ : ↥(U i)) hx
    exact ⟨f, ⟨i, hfle⟩, hxf⟩
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem (K.ideal V) _ hspan a ?_
  rintro ⟨f, i, hfle⟩
  have hcomap : J.comap (B.basicOpen f).ι ≤ K.comap (B.basicOpen f).ι :=
    comap_ι_le_comap_ι_of_le hfle (h i)
  have hideal : J.ideal (B.affineBasicOpen f) ≤ K.ideal (B.affineBasicOpen f) :=
    ideal_le_ideal_of_comap_ι_le (B.affineBasicOpen f) hcomap
  have ha' : (B.presheaf.map (homOfLE (B.basicOpen_le f)).op).hom a
      ∈ J.ideal (B.affineBasicOpen f) := by
    rw [← J.map_ideal_basicOpen V f]
    exact Ideal.mem_map_of_mem _ ha
  have ha'' := hideal ha'
  rw [← K.map_ideal_basicOpen V f] at ha''
  exact exists_pow_smul_mem_of_map_mem V (K.ideal V) f a ha''

private theorem comap_inv_comap_hom {X Y : Scheme.{u}} (e : X ≅ Y) (I : Y.IdealSheafData) :
    (I.comap e.hom).comap e.inv = I := by
  rw [← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id, Scheme.IdealSheafData.comap_id]

theorem le_of_comap_le (γ : A ⟶ B)
    (hγ : MaxContactFunctoriality.IsLocalIsomorphism γ) [AlgebraicGeometry.Surjective γ]
    (J K : B.IdealSheafData) (h : J.comap γ ≤ K.comap γ) : J ≤ K := by
  refine le_of_forall_comap_ι_le
    (fun p : { U : A.Opens // IsOpenImmersion (U.ι ≫ γ) } => rangeOpens γ p.1 p.2) ?_ J K ?_
  · intro b
    obtain ⟨U, hU, hb⟩ := exists_mem_rangeOpens γ hγ b
    exact ⟨⟨U, hU⟩, hb⟩
  · rintro ⟨W, hW⟩
    show J.comap (rangeOpens γ W hW).ι ≤ K.comap (rangeOpens γ W hW).ι
    have key : ∀ L : B.IdealSheafData,
        (L.comap (rangeOpens γ W hW).ι).comap (isoRangeOpens γ W hW).hom
          = (L.comap γ).comap W.ι := by
      intro L
      rw [← Scheme.IdealSheafData.comap_comp, isoRangeOpens_hom_ι,
        ← Scheme.IdealSheafData.comap_comp]
    have h1 : (J.comap (rangeOpens γ W hW).ι).comap (isoRangeOpens γ W hW).hom
        ≤ (K.comap (rangeOpens γ W hW).ι).comap (isoRangeOpens γ W hW).hom := by
      rw [key J, key K]
      exact Scheme.IdealSheafData.comap_mono W.ι h
    have h2 : ((J.comap (rangeOpens γ W hW).ι).comap (isoRangeOpens γ W hW).hom).comap
          (isoRangeOpens γ W hW).inv
        ≤ ((K.comap (rangeOpens γ W hW).ι).comap (isoRangeOpens γ W hW).hom).comap
          (isoRangeOpens γ W hW).inv :=
      Scheme.IdealSheafData.comap_mono (isoRangeOpens γ W hW).inv h1
    rwa [comap_inv_comap_hom, comap_inv_comap_hom] at h2

private theorem smooth_ι_comp {X Y : Scheme.{u}} (U : X.Opens) (g : X ⟶ Y)
    (hg : AlgebraicGeometry.Smooth g) : AlgebraicGeometry.Smooth (U.ι ≫ g) := by
  have : AlgebraicGeometry.Smooth g := hg
  infer_instance

private theorem smooth_of_smooth_iso_hom_comp {X Y Z : Scheme.{u}} (e : X ≅ Y) (k : Y ⟶ Z)
    (hk : AlgebraicGeometry.Smooth (e.hom ≫ k)) : AlgebraicGeometry.Smooth k := by
  have : AlgebraicGeometry.Smooth (e.hom ≫ k) := hk
  have h2 : AlgebraicGeometry.Smooth (e.inv ≫ e.hom ≫ k) := inferInstance
  rwa [← Category.assoc, e.inv_hom_id, Category.id_comp] at h2

theorem smooth_of_smooth_comp_of_isLocalIsomorphism {S : Scheme.{u}} (γ : A ⟶ B) (f : B ⟶ S)
    [IsZariskiLocalAtSource (@AlgebraicGeometry.Smooth.{u})]
    [AlgebraicGeometry.Surjective γ]
    (hγ : MaxContactFunctoriality.IsLocalIsomorphism γ)
    (h : AlgebraicGeometry.Smooth (γ ≫ f)) : AlgebraicGeometry.Smooth f := by
  choose U hU hmem using fun b : ↥B => exists_mem_rangeOpens γ hγ b
  have htop : (⨆ b : ↥B, rangeOpens γ (U b) (hU b)) = ⊤ := by
    refine le_antisymm le_top ?_
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hmem x⟩
  have hsm : ∀ b : ↥B, AlgebraicGeometry.Smooth ((rangeOpens γ (U b) (hU b)).ι ≫ f) := by
    intro b
    refine smooth_of_smooth_iso_hom_comp (isoRangeOpens γ (U b) (hU b))
      ((rangeOpens γ (U b) (hU b)).ι ≫ f) ?_
    rw [isoRangeOpens_hom_ι_assoc γ (U b) (hU b) f]
    exact smooth_ι_comp (U b) (γ ≫ f) h
  exact IsZariskiLocalAtSource.of_iSup_eq_top _ htop hsm

private theorem isLocalIsomorphism_pullback_snd {X Y W : Scheme.{u}} (g : X ⟶ Y)
    (hg : MaxContactFunctoriality.IsLocalIsomorphism g) (t : W ⟶ Y) :
    MaxContactFunctoriality.IsLocalIsomorphism (Limits.pullback.snd g t) := by
  intro x
  obtain ⟨V, hxV, hV⟩ := hg ((Limits.pullback.fst g t).base x)
  have : IsOpenImmersion (V.ι ≫ g) := hV
  refine ⟨(Limits.pullback.fst g t) ⁻¹ᵁ V, hxV, ?_⟩
  have hsq : CategoryTheory.IsPullback
      (Limits.pullback.fst g t ∣_ V)
      (((Limits.pullback.fst g t) ⁻¹ᵁ V).ι ≫ Limits.pullback.snd g t)
      (V.ι ≫ g) t :=
    (AlgebraicGeometry.isPullback_morphismRestrict (Limits.pullback.fst g t) V).paste_vert
      (CategoryTheory.IsPullback.of_hasPullback g t)
  rw [← hsq.isoPullback_hom_snd]
  infer_instance

theorem smooth_subschemeι_comp_of_smooth_comap_comp {S : Scheme.{u}} (γ : A ⟶ B) (f : B ⟶ S)
    (Z : B.IdealSheafData)
    [IsZariskiLocalAtSource (@AlgebraicGeometry.Smooth.{u})]
    [AlgebraicGeometry.Surjective γ]
    (hγ : MaxContactFunctoriality.IsLocalIsomorphism γ)
    (h : AlgebraicGeometry.Smooth ((Z.comap γ).subschemeι ≫ γ ≫ f)) :
    AlgebraicGeometry.Smooth (Z.subschemeι ≫ f) := by
  have h1 : AlgebraicGeometry.Smooth (Limits.pullback.fst γ Z.subschemeι ≫ γ ≫ f) := by
    refine smooth_of_smooth_iso_hom_comp (Z.comapIso γ)
      (Limits.pullback.fst γ Z.subschemeι ≫ γ ≫ f) ?_
    rw [← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst Z γ]
    exact h
  have h2 : AlgebraicGeometry.Smooth
      (Limits.pullback.snd γ Z.subschemeι ≫ Z.subschemeι ≫ f) := by
    rw [← Category.assoc, ← Limits.pullback.condition, Category.assoc]
    exact h1
  exact smooth_of_smooth_comp_of_isLocalIsomorphism (Limits.pullback.snd γ Z.subschemeι) (Z.subschemeι ≫ f)
    (isLocalIsomorphism_pullback_snd γ hγ Z.subschemeι) h2

private theorem isoRangeOpens_inv_comp_map_comp_affineSpaceFinToSpec {X Y : Scheme.{u}} {k : Type u} [Field k]
    (q : Y ⟶ Spec (CommRingCat.of k)) (γ : X ⟶ Y) {V W : X.Opens} (hWV : W ≤ V)
    (hW : IsOpenImmersion (W.ι ≫ γ)) {m : ℕ} (c : EtaleChart (γ ≫ q) V m) :
    ((isoRangeOpens γ W hW).inv ≫ X.homOfLE hWV ≫ c.map) ≫ affineSpaceFinToSpec k m
      = (rangeOpens γ W hW).ι ≫ q := by
  have h1 : (X.homOfLE hWV ≫ c.map) ≫ affineSpaceFinToSpec k m = W.ι ≫ γ ≫ q := by
    calc (X.homOfLE hWV ≫ c.map) ≫ affineSpaceFinToSpec k m
        = X.homOfLE hWV ≫ c.map ≫ affineSpaceFinToSpec k m := Category.assoc _ _ _
      _ = X.homOfLE hWV ≫ V.ι ≫ γ ≫ q := by rw [c.comp_struct]
      _ = (X.homOfLE hWV ≫ V.ι) ≫ γ ≫ q := (Category.assoc _ _ _).symm
      _ = W.ι ≫ γ ≫ q := by rw [Scheme.homOfLE_ι]
  calc ((isoRangeOpens γ W hW).inv ≫ X.homOfLE hWV ≫ c.map) ≫ affineSpaceFinToSpec k m
      = (isoRangeOpens γ W hW).inv ≫ (X.homOfLE hWV ≫ c.map) ≫ affineSpaceFinToSpec k m := by
        simp only [Category.assoc]
    _ = (isoRangeOpens γ W hW).inv ≫ W.ι ≫ γ ≫ q := by rw [h1]
    _ = (rangeOpens γ W hW).ι ≫ q := isoRangeOpens_inv_comp_assoc γ W hW q

private theorem etale_isoRangeOpens_inv_comp_map {X Y : Scheme.{u}} {k : Type u} [Field k]
    (q : Y ⟶ Spec (CommRingCat.of k)) (γ : X ⟶ Y) {V W : X.Opens} (hWV : W ≤ V)
    (hW : IsOpenImmersion (W.ι ≫ γ)) {m : ℕ} (c : EtaleChart (γ ≫ q) V m) :
    AlgebraicGeometry.Etale ((isoRangeOpens γ W hW).inv ≫ X.homOfLE hWV ≫ c.map) := by
  have : AlgebraicGeometry.Etale c.map := c.isEtale
  have : IsOpenImmersion (isoRangeOpens γ W hW).inv := inferInstance
  infer_instance

private noncomputable def etaleChartOnRangeOpens {X Y : Scheme.{u}} {k : Type u} [Field k]
    (q : Y ⟶ Spec (CommRingCat.of k)) (γ : X ⟶ Y) {V W : X.Opens} (hWV : W ≤ V)
    (hW : IsOpenImmersion (W.ι ≫ γ)) {m : ℕ} (c : EtaleChart (γ ≫ q) V m) :
    EtaleChart q (rangeOpens γ W hW) m where
  map := (isoRangeOpens γ W hW).inv ≫ X.homOfLE hWV ≫ c.map
  comp_struct := isoRangeOpens_inv_comp_map_comp_affineSpaceFinToSpec q γ hWV hW c
  isEtale := etale_isoRangeOpens_inv_comp_map q γ hWV hW c

private theorem coordIdeal_etaleChartOnRangeOpens {X Y : Scheme.{u}} {k : Type u} [Field k]
    (q : Y ⟶ Spec (CommRingCat.of k)) (γ : X ⟶ Y) {V W : X.Opens} (hWV : W ≤ V)
    (hW : IsOpenImmersion (W.ι ≫ γ)) {m : ℕ} (c : EtaleChart (γ ≫ q) V m)
    (T : Finset (Fin m)) :
    (etaleChartOnRangeOpens q γ hWV hW c).coordIdeal T
      = ((c.coordIdeal T).comap (X.homOfLE hWV)).comap (isoRangeOpens γ W hW).inv := by
  have e1 : ((c.coordIdeal T).comap (X.homOfLE hWV)).comap (isoRangeOpens γ W hW).inv
      = (c.coordIdeal T).comap ((isoRangeOpens γ W hW).inv ≫ X.homOfLE hWV) := by
    rw [← Scheme.IdealSheafData.comap_comp]
  have e2 : (c.coordIdeal T).comap ((isoRangeOpens γ W hW).inv ≫ X.homOfLE hWV)
      = (coordSubspaceIdeal k m T).comap
          (((isoRangeOpens γ W hW).inv ≫ X.homOfLE hWV) ≫ c.map) := by
    rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, ← Scheme.IdealSheafData.comap_comp]
  have e3 : (coordSubspaceIdeal k m T).comap
        (((isoRangeOpens γ W hW).inv ≫ X.homOfLE hWV) ≫ c.map)
      = (etaleChartOnRangeOpens q γ hWV hW c).coordIdeal T :=
    congrArg (fun g => (coordSubspaceIdeal k m T).comap g)
      (Category.assoc (isoRangeOpens γ W hW).inv (X.homOfLE hWV) c.map)
  exact ((e1.trans e2).trans e3).symm

private theorem restrictIdeal_rangeOpens {X Y : Scheme.{u}} (γ : X ⟶ Y) {V W : X.Opens}
    (hWV : W ≤ V) (hW : IsOpenImmersion (W.ι ≫ γ)) (J : Y.IdealSheafData) :
    restrictIdeal J (rangeOpens γ W hW)
      = ((restrictIdeal (J.comap γ) V).comap (X.homOfLE hWV)).comap
          (isoRangeOpens γ W hW).inv := by
  have hcomp : (((isoRangeOpens γ W hW).inv ≫ X.homOfLE hWV) ≫ V.ι) ≫ γ
      = (rangeOpens γ W hW).ι := by
    calc (((isoRangeOpens γ W hW).inv ≫ X.homOfLE hWV) ≫ V.ι) ≫ γ
        = (isoRangeOpens γ W hW).inv ≫ (X.homOfLE hWV ≫ V.ι) ≫ γ := by
          simp only [Category.assoc]
      _ = (isoRangeOpens γ W hW).inv ≫ W.ι ≫ γ := by rw [Scheme.homOfLE_ι]
      _ = (rangeOpens γ W hW).ι := isoRangeOpens_inv_comp γ W hW
  have e1 : (((J.comap γ).comap V.ι).comap (X.homOfLE hWV)).comap (isoRangeOpens γ W hW).inv
      = ((J.comap γ).comap V.ι).comap ((isoRangeOpens γ W hW).inv ≫ X.homOfLE hWV) := by
    rw [← Scheme.IdealSheafData.comap_comp]
  have e2 : ((J.comap γ).comap V.ι).comap ((isoRangeOpens γ W hW).inv ≫ X.homOfLE hWV)
      = (J.comap γ).comap (((isoRangeOpens γ W hW).inv ≫ X.homOfLE hWV) ≫ V.ι) := by
    rw [← Scheme.IdealSheafData.comap_comp]
  have e3 : (J.comap γ).comap (((isoRangeOpens γ W hW).inv ≫ X.homOfLE hWV) ≫ V.ι)
      = J.comap ((((isoRangeOpens γ W hW).inv ≫ X.homOfLE hWV) ≫ V.ι) ≫ γ) := by
    rw [← Scheme.IdealSheafData.comap_comp]
  have e4 : J.comap ((((isoRangeOpens γ W hW).inv ≫ X.homOfLE hWV) ≫ V.ι) ≫ γ)
      = J.comap (rangeOpens γ W hW).ι := by rw [hcomp]
  show J.comap (rangeOpens γ W hW).ι
      = (((J.comap γ).comap V.ι).comap (X.homOfLE hWV)).comap (isoRangeOpens γ W hW).inv
  exact ((e1.trans e2).trans (e3.trans e4)).symm

theorem hasStrictNormalCrossingsWith_of_comap {k : Type u} [Field k] (p : B ⟶ Spec (CommRingCat.of k))
    (γ : A ⟶ B) [AlgebraicGeometry.Surjective γ]
    (hγ : MaxContactFunctoriality.IsLocalIsomorphism γ)
    (Z : B.IdealSheafData) (L : List B.IdealSheafData)
    (h : HasStrictNormalCrossingsWith (γ ≫ p) (Z.comap γ) (L.map (fun D => D.comap γ))) :
    HasStrictNormalCrossingsWith p Z L := by
  intro x hx
  obtain ⟨a, ha⟩ := AlgebraicGeometry.Surjective.surj (f := γ) x
  have haZ : a ∈ (Z.comap γ).support := by
    rw [← one_le_orderAt_iff_mem_support]
    refine le_trans ?_ (orderAt_le_orderAt_comap γ Z a)
    rw [ha]
    exact (one_le_orderAt_iff_mem_support Z x).mpr hx
  obtain ⟨V, haV, m, c, af, S, hinj, hnone, hsome, hZV⟩ := h a haZ
  obtain ⟨U0, haU0, hU0⟩ := hγ a
  have hU0γ : IsOpenImmersion (U0.ι ≫ γ) := hU0
  have hWV : V ⊓ U0 ≤ V := inf_le_left
  have hWU : V ⊓ U0 ≤ U0 := inf_le_right
  have haW : a ∈ V ⊓ U0 := ⟨haV, haU0⟩
  have hWι : (V ⊓ U0).ι ≫ γ = A.homOfLE hWU ≫ U0.ι ≫ γ := by
    calc (V ⊓ U0).ι ≫ γ = (A.homOfLE hWU ≫ U0.ι) ≫ γ := by rw [Scheme.homOfLE_ι]
      _ = A.homOfLE hWU ≫ U0.ι ≫ γ := Category.assoc _ _ _
  have hW : IsOpenImmersion ((V ⊓ U0).ι ≫ γ) := by
    rw [hWι]
    infer_instance
  have hmem : a ∈ Set.range ⇑(V ⊓ U0).ι.base := by
    rw [Scheme.Opens.range_ι]
    exact haW
  obtain ⟨w, hw⟩ := hmem
  have hxP : x ∈ rangeOpens γ (V ⊓ U0) hW := by
    refine (mem_rangeOpens_iff γ (V ⊓ U0) hW x).mpr ⟨w, ?_⟩
    have hc : ((V ⊓ U0).ι ≫ γ).base w = γ.base ((V ⊓ U0).ι.base w) := by simp
    rw [hc, hw, ha]
  have hlen : (L.map (fun D => D.comap γ)).length = L.length := by simp
  refine ⟨rangeOpens γ (V ⊓ U0) hW, hxP, m, etaleChartOnRangeOpens p γ hWV hW c, af, S,
    ?_, ?_, ?_, ?_⟩
  · intro i hi j hj t hti htj
    exact hinj i (by rw [hlen]; exact hi) j (by rw [hlen]; exact hj) t hti htj
  · intro i hi hni
    have hi' : i < (L.map (fun D => D.comap γ)).length := by rw [hlen]; exact hi
    have h2 : (L.map (fun D => D.comap γ))[i]'hi' = (L[i]'hi).comap γ := by simp
    have h1 := hnone i hi' hni
    rw [h2] at h1
    rw [restrictIdeal_rangeOpens γ hWV hW (L[i]'hi), h1, Scheme.IdealSheafData.comap_top,
      Scheme.IdealSheafData.comap_top]
  · intro i hi t hti
    have hi' : i < (L.map (fun D => D.comap γ)).length := by rw [hlen]; exact hi
    have h2 : (L.map (fun D => D.comap γ))[i]'hi' = (L[i]'hi).comap γ := by simp
    have h1 := hsome i hi' t hti
    rw [h2] at h1
    rw [restrictIdeal_rangeOpens γ hWV hW (L[i]'hi), h1, coordIdeal_etaleChartOnRangeOpens]
  · rw [restrictIdeal_rangeOpens γ hWV hW Z, hZV, coordIdeal_etaleChartOnRangeOpens]

private theorem smooth_markedBlowupSequenceData_projectionToBase_comp {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} [AlgebraicGeometry.Smooth p]
    (t : MarkedBlowupSequenceData p I m E) :
    ∀ i : ℕ, i ≤ t.length → AlgebraicGeometry.Smooth (t.proj i ≫ p) := by
  intro i
  induction i with
  | zero =>
      intro _
      rw [t.proj_zero]
      infer_instance
  | succ j ih =>
      intro hi
      have hj : j < t.length := hi
      have := ih (le_of_lt hj)
      have he : t.proj (j + 1) ≫ p = t.map j ≫ t.proj j ≫ p := by
        rw [t.proj_succ j, Category.assoc]
      rw [he]
      exact smooth_comp_of_isBlowupAlongIdealSheaf (t.center_snc j hj) (t.isBlowup j hj)

private theorem strictPullbackComparisonMap_comp_projectionToBase {k : Type u} [Field k] {X X' : Scheme.{u}}
    {q : X' ⟶ Spec (CommRingCat.of k)} {g : X' ⟶ X} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} {d : BlowupSequenceData X}
    (t : MarkedBlowupSequenceData q (I.comap g) m (E.map fun A => A.comap g))
    (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups) :
    ∀ (i : ℕ) (hi : i ≤ t.length), t.strictPullbackComparisonMap D i hi ≫ d.projectionToBase i = t.proj i ≫ g := by
  intro i
  induction i with
  | zero =>
      intro hi
      rw [BlowupSequenceData.projectionToBase_zero, t.proj_zero]
      exact t.strictPullbackComparisonMap_zero D
  | succ j ih =>
      intro hi
      have hj : j < t.length := hi
      have h1 : t.strictPullbackComparisonMap D (j + 1) hi ≫ d.map j = t.map j ≫ t.strictPullbackComparisonMap D j (le_of_lt hj) :=
        t.strictPullbackComparisonMap_comp_blowupMorphism D j hj
      have h2 : t.strictPullbackComparisonMap D j (le_of_lt hj) ≫ d.projectionToBase j = t.proj j ≫ g := ih (le_of_lt hj)
      calc t.strictPullbackComparisonMap D (j + 1) hi ≫ d.projectionToBase (j + 1)
          = t.strictPullbackComparisonMap D (j + 1) hi ≫ d.map j ≫ d.projectionToBase j := by rw [BlowupSequenceData.projectionToBase_succ]
        _ = (t.strictPullbackComparisonMap D (j + 1) hi ≫ d.map j) ≫ d.projectionToBase j := (Category.assoc _ _ _).symm
        _ = (t.map j ≫ t.strictPullbackComparisonMap D j (le_of_lt hj)) ≫ d.projectionToBase j := by rw [h1]
        _ = t.map j ≫ t.strictPullbackComparisonMap D j (le_of_lt hj) ≫ d.projectionToBase j := Category.assoc _ _ _
        _ = t.map j ≫ t.proj j ≫ g := by rw [h2]
        _ = (t.map j ≫ t.proj j) ≫ g := (Category.assoc _ _ _).symm
        _ = t.proj (j + 1) ≫ g := by rw [t.proj_succ j]

private theorem controlledTransform_le_center_pow {k : Type u} [Field k] [CharZero k] {X X' : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {g : X' ⟶ X}
    [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.Smooth g]
    [AlgebraicGeometry.Flat g] [AlgebraicGeometry.Surjective g]
    {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} {d : BlowupSequenceData X}
    (t : MarkedBlowupSequenceData (g ≫ p) (I.comap g) m (E.map fun A => A.comap g))
    (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups)
    (hcomp : ∀ (i : ℕ) (hi : i ≤ t.length),
      MaxContactFunctoriality.IsLocalIsomorphism (D.comp i (t.le_toSequenceOfBlowups_length hi)))
    (i : ℕ) (hi : i < t.length)
    (hmt : t.ideal i = (d.controlledTransform I m i).comap (t.strictPullbackComparisonMap D i (le_of_lt hi))) :
    d.controlledTransform I m i ≤ d.center i ^ m := by
  have : AlgebraicGeometry.Smooth (t.proj i ≫ g ≫ p) := smooth_markedBlowupSequenceData_projectionToBase_comp t i (le_of_lt hi)
  have hup : t.ideal i ≤ t.center i ^ m :=
    le_pow_of_hasStrictNormalCrossingsWith (t.proj i ≫ g ≫ p) (t.center i) (t.ideal i) (t.boundary i)
      (t.center_snc i hi) m (t.center_order i hi)
  have : AlgebraicGeometry.Surjective (t.strictPullbackComparisonMap D i (le_of_lt hi)) :=
    t.surjective_strictPullbackComparisonMap D i (le_of_lt hi)
  have hc : (d.center i).comap (t.strictPullbackComparisonMap D i (le_of_lt hi)) = t.center i :=
    (t.center_eq_comap_strictPullbackComparisonMap D i hi).symm
  refine le_of_comap_le (t.strictPullbackComparisonMap D i (le_of_lt hi)) (hcomp i (le_of_lt hi)) _ _ ?_
  calc (d.controlledTransform I m i).comap (t.strictPullbackComparisonMap D i (le_of_lt hi))
      = t.ideal i := hmt.symm
    _ ≤ t.center i ^ m := hup
    _ = ((d.center i).comap (t.strictPullbackComparisonMap D i (le_of_lt hi))) ^ m := by rw [hc]
    _ = (d.center i ^ m).comap (t.strictPullbackComparisonMap D i (le_of_lt hi)) :=
        (Scheme.IdealSheafData.comap_pow (d.center i) (t.strictPullbackComparisonMap D i (le_of_lt hi)) m).symm

private theorem ideal_eq_comap_controlledTransform {k : Type u} [Field k] [CharZero k] {X X' : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {g : X' ⟶ X}
    [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.Smooth g]
    [AlgebraicGeometry.Flat g] [AlgebraicGeometry.Surjective g]
    {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} {d : BlowupSequenceData X}
    (t : MarkedBlowupSequenceData (g ≫ p) (I.comap g) m (E.map fun A => A.comap g))
    (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups)
    (hNd : ∀ i ≤ d.length, IsLocallyNoetherian (d.obj i))
    (hcomp : ∀ (i : ℕ) (hi : i ≤ t.length),
      MaxContactFunctoriality.IsLocalIsomorphism (D.comp i (t.le_toSequenceOfBlowups_length hi))) :
    ∀ (i : ℕ) (hi : i ≤ t.length),
      t.ideal i = (d.controlledTransform I m i).comap (t.strictPullbackComparisonMap D i hi) := by
  have hlen : t.length = d.length := t.length_eq_of_strictPullbackBlowupSeq D
  intro i
  induction i with
  | zero =>
      intro hi
      have h0 : t.strictPullbackComparisonMap D 0 hi ≫ d.isoZero.hom = t.isoZero.hom ≫ g := t.strictPullbackComparisonMap_zero D
      calc t.ideal 0 = (I.comap g).comap t.isoZero.hom := t.ideal_zero
        _ = I.comap (t.isoZero.hom ≫ g) := by rw [← Scheme.IdealSheafData.comap_comp]
        _ = I.comap (t.strictPullbackComparisonMap D 0 hi ≫ d.isoZero.hom) := by rw [h0]
        _ = (I.comap d.isoZero.hom).comap (t.strictPullbackComparisonMap D 0 hi) := by
              rw [Scheme.IdealSheafData.comap_comp]
        _ = (d.controlledTransform I m 0).comap (t.strictPullbackComparisonMap D 0 hi) := by rw [BlowupSequenceData.controlledTransform_zero]
  | succ j ih =>
      intro hi
      have hj : j < t.length := hi
      have hmj : t.ideal j = (d.controlledTransform I m j).comap (t.strictPullbackComparisonMap D j (le_of_lt hj)) :=
        ih (le_of_lt hj)
      have hle : d.controlledTransform I m j ≤ d.center j ^ m :=
        controlledTransform_le_center_pow t D hcomp j hj hmj
      have hjd : j < d.length := by rw [← hlen]; exact hj
      have hjd1 : j + 1 ≤ d.length := hjd
      have : IsLocallyNoetherian (d.obj (j + 1)) := hNd (j + 1) hjd1
      obtain ⟨B, hB, -⟩ := existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf (d.map j) (d.center j)
        (d.controlledTransform I m j) m (d.isBlowup j hjd) hle
      have hdivj : Blowup.exceptionalIdeal (d.map j) (d.center j) ^ m * d.controlledTransform I m (j + 1)
          = (d.controlledTransform I m j).comap (d.map j) := d.pow_exceptionalIdeal_mul_controlledTransform_succ I m j ⟨B, hB⟩
      have hcm : t.strictPullbackComparisonMap D (j + 1) hi ≫ d.map j = t.map j ≫ t.strictPullbackComparisonMap D j (le_of_lt hj) :=
        t.strictPullbackComparisonMap_comp_blowupMorphism D j hj
      have hexc : Blowup.exceptionalIdeal (t.map j) (t.center j)
          = (Blowup.exceptionalIdeal (d.map j) (d.center j)).comap (t.strictPullbackComparisonMap D (j + 1) hi) :=
        t.exceptionalIdeal_eq_comap_strictPullbackComparisonMap D j hj
      have key : Blowup.exceptionalIdeal (t.map j) (t.center j) ^ m * t.ideal (j + 1)
          = Blowup.exceptionalIdeal (t.map j) (t.center j) ^ m *
              (d.controlledTransform I m (j + 1)).comap (t.strictPullbackComparisonMap D (j + 1) hi) := by
        calc Blowup.exceptionalIdeal (t.map j) (t.center j) ^ m * t.ideal (j + 1)
            = (t.ideal j).comap (t.map j) := t.ideal_succ j hj
          _ = ((d.controlledTransform I m j).comap (t.strictPullbackComparisonMap D j (le_of_lt hj))).comap (t.map j) := by
              rw [hmj]
          _ = (d.controlledTransform I m j).comap (t.map j ≫ t.strictPullbackComparisonMap D j (le_of_lt hj)) := by
              rw [← Scheme.IdealSheafData.comap_comp]
          _ = (d.controlledTransform I m j).comap (t.strictPullbackComparisonMap D (j + 1) hi ≫ d.map j) := by rw [hcm]
          _ = ((d.controlledTransform I m j).comap (d.map j)).comap (t.strictPullbackComparisonMap D (j + 1) hi) := by
              rw [Scheme.IdealSheafData.comap_comp]
          _ = (Blowup.exceptionalIdeal (d.map j) (d.center j) ^ m *
                d.controlledTransform I m (j + 1)).comap (t.strictPullbackComparisonMap D (j + 1) hi) := by rw [hdivj]
          _ = (Blowup.exceptionalIdeal (d.map j) (d.center j) ^ m).comap (t.strictPullbackComparisonMap D (j + 1) hi) *
                (d.controlledTransform I m (j + 1)).comap (t.strictPullbackComparisonMap D (j + 1) hi) :=
              Scheme.IdealSheafData.comap_mul _ _ _
          _ = ((Blowup.exceptionalIdeal (d.map j) (d.center j)).comap (t.strictPullbackComparisonMap D (j + 1) hi)) ^ m *
                (d.controlledTransform I m (j + 1)).comap (t.strictPullbackComparisonMap D (j + 1) hi) := by
              rw [Scheme.IdealSheafData.comap_pow]
          _ = Blowup.exceptionalIdeal (t.map j) (t.center j) ^ m *
                (d.controlledTransform I m (j + 1)).comap (t.strictPullbackComparisonMap D (j + 1) hi) := by rw [hexc]
      exact eq_of_isLocallyGeneratedByNonZeroDivisor_pow_mul_eq_mul
        (isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal (t.isBlowup j hj)) m key

private theorem isMarked_of_strictPullbackBlowupSeq {k : Type u} [Field k] [CharZero k]
    {X X' : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) (g : X' ⟶ X)
    [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.Smooth g]
    [AlgebraicGeometry.Flat g] [AlgebraicGeometry.Surjective g]
    [IsZariskiLocalAtSource (@AlgebraicGeometry.Smooth.{u})]
    (I : X.IdealSheafData) (m : ℕ) (E : List X.IdealSheafData) (d : BlowupSequenceData X)
    (t : MarkedBlowupSequenceData (g ≫ p) (I.comap g) m (E.map fun A => A.comap g))
    (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups)
    (hNd : ∀ i ≤ d.length, IsLocallyNoetherian (d.obj i))
    (hNt : ∀ i ≤ t.length, IsLocallyNoetherian (t.obj i))
    (hcomp : ∀ (i : ℕ) (hi : i ≤ t.length),
      MaxContactFunctoriality.IsLocalIsomorphism (D.comp i (t.le_toSequenceOfBlowups_length hi))) :
    d.IsMarked p I m E := by
  have hlen : t.length = d.length := t.length_eq_of_strictPullbackBlowupSeq D
  have hmatch : ∀ (i : ℕ) (hi : i ≤ t.length),
      t.ideal i = (d.controlledTransform I m i).comap (t.strictPullbackComparisonMap D i hi) :=
    ideal_eq_comap_controlledTransform t D hNd hcomp
  have hle : ∀ i : ℕ, i < t.length → d.controlledTransform I m i ≤ d.center i ^ m := by
    intro i hi
    exact controlledTransform_le_center_pow t D hcomp i hi (hmatch i (le_of_lt hi))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hid
    have hi : i < t.length := by rw [hlen]; exact hid
    have hid1 : i + 1 ≤ d.length := hid
    have : IsLocallyNoetherian (d.obj (i + 1)) := hNd (i + 1) hid1
    obtain ⟨B, hB, -⟩ := existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf (d.map i) (d.center i)
      (d.controlledTransform I m i) m (d.isBlowup i hid) (hle i hi)
    exact ⟨B, hB⟩
  · intro i hid
    have hi : i < t.length := by rw [hlen]; exact hid
    exact support_subset_orderAtLeastLocus_of_le_pow (d.center i) (d.controlledTransform I m i) m (hle i hi)
  · intro i hid
    have hi : i < t.length := by rw [hlen]; exact hid
    have : AlgebraicGeometry.Surjective (t.strictPullbackComparisonMap D i (le_of_lt hi)) :=
      t.surjective_strictPullbackComparisonMap D i (le_of_lt hi)
    refine smooth_subschemeι_comp_of_smooth_comap_comp (t.strictPullbackComparisonMap D i (le_of_lt hi)) (d.projectionToBase i ≫ p) (d.center i)
      (hcomp i (le_of_lt hi)) ?_
    have hc : (d.center i).comap (t.strictPullbackComparisonMap D i (le_of_lt hi)) = t.center i :=
      (t.center_eq_comap_strictPullbackComparisonMap D i hi).symm
    have hpr : t.strictPullbackComparisonMap D i (le_of_lt hi) ≫ d.projectionToBase i ≫ p = t.proj i ≫ g ≫ p := by
      rw [← Category.assoc, strictPullbackComparisonMap_comp_projectionToBase t D i (le_of_lt hi), Category.assoc]
    rw [hc, hpr]
    exact t.center_smooth i hi
  · intro i hid
    have hi : i < t.length := by rw [hlen]; exact hid
    have : AlgebraicGeometry.Surjective (t.strictPullbackComparisonMap D i (le_of_lt hi)) :=
      t.surjective_strictPullbackComparisonMap D i (le_of_lt hi)
    refine hasStrictNormalCrossingsWith_of_comap (d.projectionToBase i ≫ p) (t.strictPullbackComparisonMap D i (le_of_lt hi))
      (hcomp i (le_of_lt hi)) (d.center i) (d.boundaryFrom E i) ?_
    have hc : (d.center i).comap (t.strictPullbackComparisonMap D i (le_of_lt hi)) = t.center i :=
      (t.center_eq_comap_strictPullbackComparisonMap D i hi).symm
    have hb : (d.boundaryFrom E i).map (fun A => A.comap (t.strictPullbackComparisonMap D i (le_of_lt hi))) = t.boundary i :=
      (t.boundary_eq_comap_strictPullbackComparisonMap D hNd hNt i (le_of_lt hi)).symm
    have hpr : t.strictPullbackComparisonMap D i (le_of_lt hi) ≫ d.projectionToBase i ≫ p = t.proj i ≫ g ≫ p := by
      rw [← Category.assoc, strictPullbackComparisonMap_comp_projectionToBase t D i (le_of_lt hi), Category.assoc]
    rw [hc, hb, hpr]
    exact t.center_snc i hi

theorem isMarked_balancedTunedIdeal_of_isStrictPullbackBlowupSeq (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop)
    (Afam : ℕ → PrincipalizationAssignment.{u}) (T : MarkedIdealWithBoundary.{u})
    (h : MaxContactFunctoriality.OrderReductionHypotheses P T)
    [CharZero T.base]
    [AlgebraicGeometry.Smooth T.structMap]
    [AlgebraicGeometry.LocallyOfFiniteType T.structMap]
    [AlgebraicGeometry.Smooth (MaxContactCoverData.coverMap T h.valid)]
    [AlgebraicGeometry.Surjective (MaxContactCoverData.coverMap T h.valid)]
    [IsZariskiLocalAtSource (@AlgebraicGeometry.Smooth.{u})]
    (_hoi : MaxContactFunctoriality.IsLocalIsomorphism (MaxContactCoverData.coverMap T h.valid))
    (_hmult : 1 ≤ MaxContactCoverData.tunedMult T)
    (d : BlowupSequenceData T.scheme)
    (hpb : IsStrictPullbackBlowupSeq (MaxContactCoverData.coverMap T h.valid)
      (MaxContactFunctoriality.coverBlowupSequence hinv Afam T h.valid).toBlowupSequenceData.toSequenceOfBlowups d.toSequenceOfBlowups)
    (hNd : ∀ i ≤ d.length, IsLocallyNoetherian (d.obj i))
    (hNt : ∀ i ≤ (MaxContactFunctoriality.coverBlowupSequence hinv Afam T h.valid).length,
      IsLocallyNoetherian ((MaxContactFunctoriality.coverBlowupSequence hinv Afam T h.valid).obj i))
    (hcomp : ∀ D : StrictPullbackBlowupSeq (MaxContactCoverData.coverMap T h.valid)
        (MaxContactFunctoriality.coverBlowupSequence hinv Afam T h.valid).toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups,
      ∀ (i : ℕ) (hi : i ≤ (MaxContactFunctoriality.coverBlowupSequence hinv Afam T h.valid).length),
        MaxContactFunctoriality.IsLocalIsomorphism
          (D.comp i ((MaxContactFunctoriality.coverBlowupSequence hinv Afam T h.valid).le_toSequenceOfBlowups_length hi))) :
    d.IsMarked T.structMap (MaxContactCoverData.balancedTunedIdeal T h.valid)
      (MaxContactCoverData.tunedMult T) T.boundary := by
  have : AlgebraicGeometry.Flat (MaxContactCoverData.coverMap T h.valid) := inferInstance
  have D : StrictPullbackBlowupSeq (MaxContactCoverData.coverMap T h.valid)
      (MaxContactFunctoriality.coverBlowupSequence hinv Afam T h.valid).toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups :=
    hpb.toStrictPullbackBlowupSeq
  exact isMarked_of_strictPullbackBlowupSeq T.structMap (MaxContactCoverData.coverMap T h.valid)
    (MaxContactCoverData.balancedTunedIdeal T h.valid) (MaxContactCoverData.tunedMult T) T.boundary d
    (MaxContactFunctoriality.coverBlowupSequence hinv Afam T h.valid) D hNd hNt (hcomp D)

end FunctorialResolution.EmbeddedResolution
