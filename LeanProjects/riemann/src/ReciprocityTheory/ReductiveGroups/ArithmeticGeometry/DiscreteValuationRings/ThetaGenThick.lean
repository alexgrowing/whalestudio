import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenFlat

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

noncomputable section

variable {R : Type} [CommRing R]

lemma toW_res {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) {V W : X.Opens} (h : W ≤ V) (r : R) :
    (X.presheaf.map (homOfLE h).op).hom (toW p V r) = toW p W r := by
  simp only [toW, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

lemma app_toW {X Y : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) (f : Y ⟶ X) (W : X.Opens) (r : R) :
    (f.app W).hom (toW p W r) = toW (f ≫ p) (f ⁻¹ᵁ W) r := by
  simp only [toW, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE]
  erw [Scheme.Hom.appLE_comp_appLE]

lemma toW_congr {X : Scheme.{0}} {p p' : X ⟶ Spec (CommRingCat.of R)} (h : p = p') (W : X.Opens) (r : R) :
    toW p W r = toW p' W r := by subst h; rfl

lemma app_res {X Y : Scheme.{0}} (f : Y ⟶ X) {V W : X.Opens} (h : W ≤ V) (x : Γ(X, V)) :
    (Y.presheaf.map (homOfLE (f.preimage_mono h)).op).hom ((f.app V).hom x) =
      (f.app W).hom ((X.presheaf.map (homOfLE h).op).hom x) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
  rfl

variable [IsDomain R]

theorem exists_div {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) [Flat p] {a : R} (ha : a ≠ 0)
    {J : Ideal R} (hJ : J ≤ Ideal.span {a})
    (V : X.Opens) (x : Γ(X, V)) (hx : (pullback.fst p (tq J)).app V x = 0) :
    ∃ g : Γ(X, V), x = toW p V a * g := by
  classical
  set π := pullback.fst p (tq J)
  let ι := {W : X.affineOpens // (W : X.Opens) ≤ V}
  let U : ι → X.Opens := fun W => W.1
  have hloc : ∀ W : ι, ∃ g : Γ(X, U W), (X.presheaf.map (homOfLE W.2).op).hom x = toW p (U W) a * g := by
    intro W
    have h0 : (π.app (U W)).hom ((X.presheaf.map (homOfLE W.2).op).hom x) = 0 := by
      rw [← app_res, hx, map_zero]
    have hm := Ideal.map_mono hJ ((app_fst_tq p J (U W) W.1.2).2 _ h0)
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hm
    obtain ⟨g, hg⟩ := hm
    exact ⟨g, by rw [← hg, mul_comm]⟩
  choose g hg using hloc
  have hcover : V ≤ iSup U := by
    intro y hy
    obtain ⟨W, hW, hyW, hWV⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨W, hW⟩, hWV⟩, hyW⟩
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 U g := by
    intro i j
    show (X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op).hom (g i) =
      (X.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op).hom (g j)
    rw [← sub_eq_zero]
    apply toW_mul_eq_zero p _ ha
    rw [mul_sub]
    have e1 := congrArg (X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op).hom (hg i)
    have e2 := congrArg (X.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op).hom (hg j)
    rw [map_mul, toW_res, ← CommRingCat.comp_apply, ← Functor.map_comp] at e1 e2
    rw [sub_eq_zero]
    exact e1.symm.trans e2
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf U V (fun i => homOfLE i.2) hcover g hcompat
  refine ⟨s, ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq' X.sheaf U V (fun i => homOfLE i.2) hcover
  intro i
  show (X.presheaf.map (homOfLE i.2).op).hom x = (X.presheaf.map (homOfLE i.2).op).hom (toW p V a * (show Γ(X, V) from s))
  rw [hg i, map_mul, toW_res]
  exact congrArg _ (hs i).symm

end

end ReciprocityTheory.ChartRestriction.G.DVR.TG

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

noncomputable section

variable {R : Type} [CommRing R]

lemma app_toW_of_mem {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) (J : Ideal R) (W : X.Opens)
    {r : R} (hr : r ∈ J) : (pullback.fst p (tq J)).app W (toW p W r) = 0 := by
  have e1 : (pullback.fst p (tq J)).app W (toW p W r) =
      ((pullback.snd p (tq J) ≫ tq J).appLE ⊤ (pullback.fst p (tq J) ⁻¹ᵁ W) le_top).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
    rw [toW, RingHom.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE]
    erw [Scheme.Hom.appLE_comp_appLE]
    rw [appLE_of_eq pullback.condition]
  have e2 : (pullback.snd p (tq J) ≫ tq J).appLE ⊤ (pullback.fst p (tq J) ⁻¹ᵁ W) le_top =
      (tq J).appLE ⊤ (tq J ⁻¹ᵁ ⊤) le_rfl ≫
        (pullback.snd p (tq J)).appLE (tq J ⁻¹ᵁ ⊤) (pullback.fst p (tq J) ⁻¹ᵁ W) le_top := by
    erw [Scheme.Hom.appLE_comp_appLE]
  have e3 : (tq J).appLE ⊤ (tq J ⁻¹ᵁ ⊤) le_rfl =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).inv := by
    rw [Scheme.Hom.appLE_eq_app, ← Scheme.Hom.appTop,
      (Iso.eq_comp_inv _).2 (Scheme.ΓSpecIso_naturality _), Category.assoc]
  have eR : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = r := by
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id]; rfl
  have e4 : ((Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).inv).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = 0 := by
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply, eR]
    erw [Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]
  rw [e1, e2, CommRingCat.comp_apply, e3]
  erw [e4, map_zero]

variable [IsDomain R]

set_option maxHeartbeats 400000 in

theorem vanish_of_mul {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) [Flat p] {a : R} (ha : a ≠ 0)
    (e : ℕ) {J₁ J₂ : Ideal R} (h1 : J₁ ≤ Ideal.span {a ^ (e + 2)}) (h2 : a ^ (e + 1) ∈ J₂)
    (ι : pullback p (tq J₂) ⟶ pullback p (tq J₁)) (hι : ι ≫ pullback.fst p (tq J₁) = pullback.fst p (tq J₂))
    (V : (pullback p (tq J₁)).Opens) (y : Γ(pullback p (tq J₁), V))
    (hy : toW (pullback.fst p (tq J₁) ≫ p) V a * y = 0) :
    (ι.app V) y = 0 := by
  set π₁ := pullback.fst p (tq J₁)
  set π₂ := pullback.fst p (tq J₂)
  have : IsClosedImmersion (tq J₁) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : IsClosedImmersion π₁ := inferInstance
  refine TopCat.Presheaf.section_ext (pullback p (tq J₂)).sheaf _ _ 0 fun z hz => ?_

  have hemb : Topology.IsEmbedding π₁.base := π₁.isClosedEmbedding.isEmbedding
  obtain ⟨V₀, hV₀, hV₀e⟩ := hemb.isInducing.isOpen_iff.1 V.isOpen
  have hz0 : π₁.base (ι.base z) ∈ V₀ := by
    have : ι.base z ∈ (π₁.base ⁻¹' V₀) := by rw [hV₀e]; exact hz
    exact this
  obtain ⟨W, hW, hzW, hWV₀⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show π₁.base (ι.base z) ∈ (⟨V₀, hV₀⟩ : X.Opens) from hz0)
  have hWV : π₁ ⁻¹ᵁ W ≤ V := by
    intro u hu
    have : u ∈ π₁.base ⁻¹' V₀ := hWV₀ hu
    rw [hV₀e] at this; exact this

  obtain ⟨hs, hk⟩ := app_fst_tq p J₁ W hW
  obtain ⟨yt, hyt⟩ := hs (((pullback p (tq J₁)).presheaf.map (homOfLE hWV).op).hom y)
  have hay : π₁.app W (toW p W a * yt) = 0 := by
    rw [map_mul, hyt, app_toW, ← toW_res (π₁ ≫ p) hWV, ← map_mul, hy, map_zero]
  have hm := Ideal.map_mono h1 (hk _ hay)
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hm
  obtain ⟨c, hc⟩ := hm
  have hyt' : yt = toW p W (a ^ (e + 1)) * c := by
    apply sub_eq_zero.1
    apply toW_mul_eq_zero p W ha
    rw [mul_sub, ← hc, map_pow, map_pow, pow_succ' _ (e + 1)]
    ring

  have hW2 : π₂ ⁻¹ᵁ W ≤ ι ⁻¹ᵁ V := by
    intro u hu
    apply hWV
    show π₁.base (ι.base u) ∈ W
    rw [← Scheme.Hom.comp_apply, hι]; exact hu
  have hW2' : π₂ ⁻¹ᵁ W ≤ ι ⁻¹ᵁ (π₁ ⁻¹ᵁ W) := by
    intro u hu
    show π₁.base (ι.base u) ∈ W
    rw [← Scheme.Hom.comp_apply, hι]; exact hu
  have hzW2 : z ∈ π₂ ⁻¹ᵁ W := by
    show π₂.base z ∈ W
    rw [← hι, Scheme.Hom.comp_apply]; exact hzW
  have e5 : ((pullback p (tq J₂)).presheaf.map (homOfLE hW2).op).hom ((ι.app V) y) = (π₂.app W) yt := by
    have a1 : ((pullback p (tq J₂)).presheaf.map (homOfLE hW2).op).hom ((ι.app V) y) =
        (ι.appLE V (π₂ ⁻¹ᵁ W) hW2) y := by
      rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply]
      erw [Scheme.Hom.appLE_map]
    have a2 : (ι.appLE V (π₂ ⁻¹ᵁ W) hW2) y =
        (ι.appLE (π₁ ⁻¹ᵁ W) (π₂ ⁻¹ᵁ W) hW2') (((pullback p (tq J₁)).presheaf.map (homOfLE hWV).op).hom y) := by
      rw [← CommRingCat.comp_apply]
      erw [Scheme.Hom.map_appLE]
    have a3 : (ι.appLE (π₁ ⁻¹ᵁ W) (π₂ ⁻¹ᵁ W) hW2') ((π₁.app W) yt) = (π₂.app W) yt := by
      rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply]
      erw [Scheme.Hom.appLE_comp_appLE]
      rw [appLE_of_eq hι, Scheme.Hom.app_eq_appLE]
    rw [a1, a2, ← hyt, a3]
  have hzero : ((pullback p (tq J₂)).presheaf.map (homOfLE hW2).op).hom ((ι.app V) y) = 0 := by
    rw [e5, hyt', map_mul, app_toW_of_mem p J₂ W h2, zero_mul]
  show (pullback p (tq J₂)).presheaf.germ _ z hz ((ι.app V) y) = (pullback p (tq J₂)).presheaf.germ _ z hz 0
  rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE hW2) z hzW2, hzero, map_zero, map_zero]

end

end ReciprocityTheory.ChartRestriction.G.DVR.TG
