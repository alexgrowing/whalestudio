import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
universe u v

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite

namespace FunctorialResolution.Blowup

private theorem eq_span_inv_of_map_eq_span {R S : CommRingCat.{u}} (φ : R ⟶ S) [IsIso φ]
    (J : Ideal R) (s : S) (h : J.map φ.hom = Ideal.span {s}) :
    J = Ideal.span {(CategoryTheory.inv φ).hom s} := by
  have hcomp : (CategoryTheory.inv φ).hom.comp φ.hom = RingHom.id R := by
    ext x
    simp
  calc J = (J.map φ.hom).map (CategoryTheory.inv φ).hom := by
        rw [Ideal.map_map, hcomp, Ideal.map_id]
    _ = (Ideal.span {s}).map (CategoryTheory.inv φ).hom := by rw [h]
    _ = Ideal.span {(CategoryTheory.inv φ).hom s} := by rw [Ideal.map_span, Set.image_singleton]

private theorem isIso_appLE_of_image_eq {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {W : X.Opens} {V : Y.Opens} (hV : f ''ᵁ W = V) (e : W ≤ f ⁻¹ᵁ V) :
    IsIso (f.appLE V W e) := by
  subst hV
  rw [← Scheme.Hom.appIso_hom']
  infer_instance

private theorem exists_affineOpen_mem_le {X : Scheme.{u}} (x : X) (W : X.Opens) (hx : x ∈ W) :
    ∃ V : X.affineOpens, x ∈ (V : X.Opens) ∧ (V : X.Opens) ≤ W := by
  obtain ⟨Vs, hVs, hxV, hVW⟩ :=
    (Scheme.isBasis_affineOpens X).exists_subset_of_mem_open
      (show x ∈ (W : Set X) from hx) W.isOpen
  obtain ⟨V, hVmem, rfl⟩ := hVs
  exact ⟨⟨V, hVmem⟩, hxV, fun y hy => hVW hy⟩

theorem IsLocallyGeneratedByNonZeroDivisor.comap_of_isOpenImmersion {X U : Scheme.{u}}
    {I : X.IdealSheafData} (hI : IsLocallyGeneratedByNonZeroDivisor I) (f : U ⟶ X) [IsOpenImmersion f] :
    IsLocallyGeneratedByNonZeroDivisor (I.comap f) := by
  intro x
  obtain ⟨V, g, hxV, hg, hVg⟩ := hI (f.base x)
  have hVa : IsAffineOpen (V : X.Opens) := V.2
  obtain ⟨W, hxW, hWle⟩ := exists_affineOpen_mem_le x (f ⁻¹ᵁ (V : X.Opens)) hxV
  have hWa : IsAffineOpen (W : U.Opens) := W.2
  have hximg : f.base x ∈ (f ''ᵁ (W : U.Opens)) := ⟨x, hxW, rfl⟩
  obtain ⟨r, hr1, hr2⟩ := hVa.exists_basicOpen_le (⟨f.base x, hximg⟩ : (f ''ᵁ (W : U.Opens))) hxV
  have hW'le : f ⁻¹ᵁ (X.basicOpen r) ≤ (W : U.Opens) := by
    rw [← Scheme.Hom.preimage_image_eq f (W : U.Opens)]
    exact fun y hy => hr1 hy
  have hbas : U.basicOpen ((f.appLE (V : X.Opens) (W : U.Opens) hWle).hom r)
      = f ⁻¹ᵁ (X.basicOpen r) := by
    rw [show (f.appLE (V : X.Opens) (W : U.Opens) hWle).hom r
          = (U.presheaf.map (homOfLE hWle).op).hom ((f.app (V : X.Opens)).hom r) from rfl,
      Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]
    exact inf_eq_right.mpr hW'le
  have hW'aff : IsAffineOpen (f ⁻¹ᵁ (X.basicOpen r)) := by
    rw [← hbas]
    exact hWa.basicOpen _
  have hBrange : X.basicOpen r ≤ f.opensRange := by
    intro y hy
    obtain ⟨z, _, hz⟩ := hr1 hy
    exact ⟨z, hz⟩
  have himg : f ''ᵁ (f ⁻¹ᵁ (X.basicOpen r)) = X.basicOpen r :=
    (f.image_preimage_eq_opensRange_inf (X.basicOpen r)).trans (inf_eq_right.mpr hBrange)
  have : IsIso (f.appLE (X.basicOpen r) (f ⁻¹ᵁ (X.basicOpen r)) le_rfl) :=
    isIso_appLE_of_image_eq f himg le_rfl
  have e1 : (I.ideal V).map (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
      = I.ideal ⟨X.basicOpen r, hVa.basicOpen r⟩ := I.map_ideal_basicOpen V r
  rw [hVg, Ideal.map_span, Set.image_singleton] at e1
  refine ⟨⟨f ⁻¹ᵁ (X.basicOpen r), hW'aff⟩,
    (f.appLE (X.basicOpen r) (f ⁻¹ᵁ (X.basicOpen r)) le_rfl).hom
      ((X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom g), hr2, ?_, ?_⟩
  · refine map_mem_nonZeroDivisors_of_iso
      (asIso (f.appLE (X.basicOpen r) (f ⁻¹ᵁ (X.basicOpen r)) le_rfl)) ?_
    have := hVa.isLocalization_basicOpen r
    exact IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers r) Γ(X, X.basicOpen r) hg
  · have hmap := I.comap_ideal_eq_map_appLE f ⟨X.basicOpen r, hVa.basicOpen r⟩
      ⟨f ⁻¹ᵁ (X.basicOpen r), hW'aff⟩ le_rfl
    rw [← e1, Ideal.map_span, Set.image_singleton] at hmap
    exact hmap

theorem IsLocallyGeneratedByNonZeroDivisor.of_isOpenImmersion_cover {X : Scheme.{u}} (I : X.IdealSheafData)
    {ι : Type v} (U : ι → Scheme.{u}) (f : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range ⇑(f i).base)
    (h : ∀ i, IsLocallyGeneratedByNonZeroDivisor (I.comap (f i))) :
    IsLocallyGeneratedByNonZeroDivisor I := by
  intro x
  obtain ⟨i, u, hu⟩ := hcover x
  obtain ⟨W, s, hxW, hs, hWs⟩ := h i u
  have hWa : IsAffineOpen (W : (U i).Opens) := W.2
  have hVaff : IsAffineOpen (f i ''ᵁ (W : (U i).Opens)) := hWa.image_of_isOpenImmersion (f i)
  have hpre : (f i) ⁻¹ᵁ (f i ''ᵁ (W : (U i).Opens)) = (W : (U i).Opens) :=
    Scheme.Hom.preimage_image_eq (f i) _
  have e : (W : (U i).Opens) ≤ (f i) ⁻¹ᵁ (f i ''ᵁ (W : (U i).Opens)) := hpre.ge
  have : IsIso ((f i).appLE (f i ''ᵁ (W : (U i).Opens)) (W : (U i).Opens) e) :=
    isIso_appLE_of_image_eq (f i) rfl e
  have key := I.comap_ideal_eq_map_appLE (f i) ⟨f i ''ᵁ (W : (U i).Opens), hVaff⟩ W e
  rw [hWs] at key
  refine ⟨⟨f i ''ᵁ (W : (U i).Opens), hVaff⟩,
    (CategoryTheory.inv ((f i).appLE (f i ''ᵁ (W : (U i).Opens)) (W : (U i).Opens) e)).hom s,
    ?_, ?_, ?_⟩
  · exact ⟨u, hxW, hu⟩
  · exact map_mem_nonZeroDivisors_of_iso
      (asIso (CategoryTheory.inv
        ((f i).appLE (f i ''ᵁ (W : (U i).Opens)) (W : (U i).Opens) e))) hs
  · exact eq_span_inv_of_map_eq_span _ _ _ key.symm

theorem IsBlowupAlongIdealSheaf.restrict {X X' : Scheme.{u}} {π : X' ⟶ X} {I : X.IdealSheafData}
    (h : IsBlowupAlongIdealSheaf π I) (U : X.Opens) :
    IsBlowupAlongIdealSheaf (π ∣_ U) (I.comap U.ι) := by
  have key : ∀ {W : Scheme.{u}} (g : W ⟶ U.toScheme),
      (I.comap U.ι).comap g = I.comap (g ≫ U.ι) := by
    intro W g
    rw [Scheme.IdealSheafData.comap_comp]
  constructor
  · rw [key (π ∣_ U), morphismRestrict_ι, Scheme.IdealSheafData.comap_comp]
    exact h.1.comap_of_isOpenImmersion (π ⁻¹ᵁ U).ι
  · intro W g hg
    rw [key g] at hg
    obtain ⟨k, hk, hk'⟩ := h.2 W (g ≫ U.ι) hg
    have hrange : Set.range ⇑k.base ⊆ Set.range ⇑(π ⁻¹ᵁ U).ι.base := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨w, rfl⟩
      show π.base (k.base w) ∈ U
      have h1 : (k ≫ π).base w = (g ≫ U.ι).base w := by rw [hk]
      have h2 : π.base (k.base w) = U.ι.base (g.base w) := h1
      rw [h2]
      exact (g.base w).2
    refine ⟨IsOpenImmersion.lift (π ⁻¹ᵁ U).ι k hrange, ?_, ?_⟩
    · show IsOpenImmersion.lift (π ⁻¹ᵁ U).ι k hrange ≫ π ∣_ U = g
      rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc,
        IsOpenImmersion.lift_fac]
      exact hk
    · intro y hy
      have hy' : y ≫ π ∣_ U = g := hy
      rw [← cancel_mono (π ⁻¹ᵁ U).ι, IsOpenImmersion.lift_fac]
      refine hk' _ ?_
      show (y ≫ (π ⁻¹ᵁ U).ι) ≫ π = g ≫ U.ι
      rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, hy']

private theorem exists_pullback_fst_base_eq {W U X : Scheme.{u}} (g : W ⟶ X) (f : U ⟶ X)
    [IsOpenImmersion f] (w : W) (hw : g.base w ∈ Set.range ⇑f.base) :
    ∃ z : ↥(pullback g f), (pullback.fst g f).base z = w := by
  have hrange : Set.range ⇑((g ⁻¹ᵁ f.opensRange).ι ≫ g).base ⊆ Set.range ⇑f.base := by
    rintro _ ⟨v, rfl⟩
    exact v.2
  have hl : IsOpenImmersion.lift f ((g ⁻¹ᵁ f.opensRange).ι ≫ g) hrange ≫ f
      = (g ⁻¹ᵁ f.opensRange).ι ≫ g := IsOpenImmersion.lift_fac _ _ _
  have hm := pullback.lift_fst (g ⁻¹ᵁ f.opensRange).ι
    (IsOpenImmersion.lift f ((g ⁻¹ᵁ f.opensRange).ι ≫ g) hrange) hl.symm
  refine ⟨(pullback.lift (g ⁻¹ᵁ f.opensRange).ι
    (IsOpenImmersion.lift f ((g ⁻¹ᵁ f.opensRange).ι ≫ g) hrange) hl.symm).base
      ⟨w, show w ∈ g ⁻¹ᵁ f.opensRange from hw⟩, ?_⟩
  have h3 := congrArg (fun t : (g ⁻¹ᵁ f.opensRange).toScheme ⟶ W => t.base
    ⟨w, show w ∈ g ⁻¹ᵁ f.opensRange from hw⟩) hm
  exact h3

private noncomputable def pullbackOpenCoverOfCovers {X W : Scheme.{u}} {ι : Type v} (U : ι → Scheme.{u})
    (f : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range ⇑(f i).base) (g : W ⟶ X) : W.OpenCover :=
  Scheme.Cover.mkOfCovers ι (fun i => pullback g (f i)) (fun i => pullback.fst g (f i))
    (fun w => by
      obtain ⟨i, hi⟩ := hcover (g.base w)
      obtain ⟨z, hz⟩ := exists_pullback_fst_base_eq g (f i) w hi
      exact ⟨i, z, hz⟩)
    (fun i => inferInstance)

private theorem hom_ext_of_isOpenImmersion_cover {X W T : Scheme.{u}} {ι : Type v}
    (U : ι → Scheme.{u}) (f : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range ⇑(f i).base) (g : W ⟶ X) {a b : W ⟶ T}
    (h : ∀ i, pullback.fst g (f i) ≫ a = pullback.fst g (f i) ≫ b) : a = b := by
  refine Scheme.Cover.hom_ext (pullbackOpenCoverOfCovers U f hcover g) a b (fun i => ?_)
  exact h i

private theorem exists_hom_of_isOpenImmersion_cover {X W T : Scheme.{u}} {ι : Type v}
    (U : ι → Scheme.{u}) (f : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range ⇑(f i).base) (g : W ⟶ X)
    (k : ∀ i, pullback g (f i) ⟶ T)
    (hk : ∀ i j, pullback.fst (pullback.fst g (f i)) (pullback.fst g (f j)) ≫ k i
        = pullback.snd (pullback.fst g (f i)) (pullback.fst g (f j)) ≫ k j) :
    ∃ φ : W ⟶ T, ∀ i, pullback.fst g (f i) ≫ φ = k i := by
  have hk' : ∀ i j,
      pullback.fst ((pullbackOpenCoverOfCovers U f hcover g).f i) ((pullbackOpenCoverOfCovers U f hcover g).f j) ≫ k i
        = pullback.snd ((pullbackOpenCoverOfCovers U f hcover g).f i)
            ((pullbackOpenCoverOfCovers U f hcover g).f j) ≫ k j :=
    fun i j => hk i j
  refine ⟨Scheme.Cover.glueMorphisms (pullbackOpenCoverOfCovers U f hcover g) k hk', fun i => ?_⟩
  exact Scheme.Cover.ι_glueMorphisms (pullbackOpenCoverOfCovers U f hcover g) k hk' i

private theorem eq_of_comp_eq_of_isBlowupAlongIdealSheaf_openCover {X X' T : Scheme.{u}} (π : X' ⟶ X)
    (I : X.IdealSheafData)
    {ι : Type v} (U : ι → Scheme.{u}) (f : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range ⇑(f i).base)
    (h : ∀ i, IsBlowupAlongIdealSheaf (pullback.snd π (f i)) (I.comap (f i)))
    {a b : T ⟶ X'} (hab : a ≫ π = b ≫ π) (hc : IsLocallyGeneratedByNonZeroDivisor (I.comap (a ≫ π))) :
    a = b := by
  refine hom_ext_of_isOpenImmersion_cover U f hcover (a ≫ π) fun i => ?_
  have hcond : pullback.fst (a ≫ π) (f i) ≫ (a ≫ π) = pullback.snd (a ≫ π) (f i) ≫ f i :=
    pullback.condition
  have ha' : (pullback.fst (a ≫ π) (f i) ≫ a) ≫ π = pullback.snd (a ≫ π) (f i) ≫ f i := by
    rw [Category.assoc]; exact hcond
  have hb' : (pullback.fst (a ≫ π) (f i) ≫ b) ≫ π = pullback.snd (a ≫ π) (f i) ≫ f i := by
    rw [Category.assoc, ← hab]; exact hcond
  have hEC : IsLocallyGeneratedByNonZeroDivisor ((I.comap (f i)).comap (pullback.snd (a ≫ π) (f i))) := by
    rw [← Scheme.IdealSheafData.comap_comp, ← hcond, Scheme.IdealSheafData.comap_comp]
    exact hc.comap_of_isOpenImmersion _
  have hAB := (h i).hom_ext_of_comp_eq hEC
    (pullback.lift_snd (pullback.fst (a ≫ π) (f i) ≫ a) (pullback.snd (a ≫ π) (f i)) ha')
    (pullback.lift_snd (pullback.fst (a ≫ π) (f i) ≫ b) (pullback.snd (a ≫ π) (f i)) hb')
  have h1 := pullback.lift_fst (pullback.fst (a ≫ π) (f i) ≫ a) (pullback.snd (a ≫ π) (f i)) ha'
  have h2 := pullback.lift_fst (pullback.fst (a ≫ π) (f i) ≫ b) (pullback.snd (a ≫ π) (f i)) hb'
  rw [← h1, ← h2, hAB]

theorem IsBlowupAlongIdealSheaf.of_comap_of_isOpenImmersion_cover {X X' : Scheme.{u}} (π : X' ⟶ X)
    (I : X.IdealSheafData) {ι : Type v} (U : ι → Scheme.{u}) (f : ∀ i, U i ⟶ X)
    [∀ i, IsOpenImmersion (f i)]
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range ⇑(f i).base)
    (h : ∀ i, IsBlowupAlongIdealSheaf (pullback.snd π (f i)) (I.comap (f i))) :
    IsBlowupAlongIdealSheaf π I := by
  constructor
  · refine IsLocallyGeneratedByNonZeroDivisor.of_isOpenImmersion_cover (I.comap π) (fun i => pullback π (f i))
      (fun i => pullback.fst π (f i)) (fun x' => ?_) ?_
    · obtain ⟨i, hi⟩ := hcover (π.base x')
      obtain ⟨z, hz⟩ := exists_pullback_fst_base_eq π (f i) x' hi
      exact ⟨i, z, hz⟩
    · intro i
      have hq : (I.comap π).comap (pullback.fst π (f i))
          = (I.comap (f i)).comap (pullback.snd π (f i)) := by
        rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
          pullback.condition]
      rw [hq]
      exact (h i).1
  · intro W g hg
    have hEC : ∀ i, IsLocallyGeneratedByNonZeroDivisor ((I.comap (f i)).comap (pullback.snd g (f i))) := by
      intro i
      have hq : (I.comap (f i)).comap (pullback.snd g (f i))
          = (I.comap g).comap (pullback.fst g (f i)) := by
        rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
          pullback.condition]
      rw [hq]
      exact hg.comap_of_isOpenImmersion _
    choose k hk1 _ using fun i => (h i).2 (pullback g (f i)) (pullback.snd g (f i)) (hEC i)
    have hapi : ∀ i, k i ≫ pullback.fst π (f i) ≫ π = pullback.fst g (f i) ≫ g := by
      intro i
      rw [pullback.condition, ← Category.assoc, hk1 i, ← pullback.condition]
    have hglue : ∀ i j, pullback.fst (pullback.fst g (f i)) (pullback.fst g (f j)) ≫
          (k i ≫ pullback.fst π (f i))
        = pullback.snd (pullback.fst g (f i)) (pullback.fst g (f j)) ≫
          (k j ≫ pullback.fst π (f j)) := by
      intro i j
      refine eq_of_comp_eq_of_isBlowupAlongIdealSheaf_openCover π I U f hcover h ?_ ?_
      · simp only [Category.assoc]
        rw [hapi i, hapi j, ← Category.assoc, ← Category.assoc, pullback.condition]
      · have heq : (pullback.fst (pullback.fst g (f i)) (pullback.fst g (f j)) ≫
              (k i ≫ pullback.fst π (f i))) ≫ π
            = (pullback.fst (pullback.fst g (f i)) (pullback.fst g (f j)) ≫
              pullback.fst g (f i)) ≫ g := by
          rw [Category.assoc, Category.assoc, hapi i, ← Category.assoc]
        rw [heq, Scheme.IdealSheafData.comap_comp]
        exact hg.comap_of_isOpenImmersion _
    obtain ⟨φ, hφ⟩ :=
      exists_hom_of_isOpenImmersion_cover U f hcover g
        (fun i => k i ≫ pullback.fst π (f i)) hglue
    have hφπ : φ ≫ π = g := by
      refine hom_ext_of_isOpenImmersion_cover U f hcover g fun i => ?_
      rw [← Category.assoc, hφ i, Category.assoc, hapi i]
    refine ⟨φ, hφπ, fun y hy => ?_⟩
    have hy' : y ≫ π = g := hy
    refine eq_of_comp_eq_of_isBlowupAlongIdealSheaf_openCover π I U f hcover h (by rw [hy', hφπ]) ?_
    rw [hy']
    exact hg

end FunctorialResolution.Blowup
