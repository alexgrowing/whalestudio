import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenImmersionSpMapOfIsDiscreteValuationRing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.CompatCrit

theorem section_open {G X V : Scheme.{0}} [IsReduced G] (p : G ⟶ X) [IsSeparated p] (s : V ⟶ G)
    [IsDominant s] [IsOpenImmersion (s ≫ p)] :
    IsOpenImmersion s ∧ ∀ x : G, p x ∈ Set.range (s ≫ p) → x ∈ Set.range s := by
  let t : V ⟶ pullback p (s ≫ p) := pullback.lift s (𝟙 V) (by simp)
  have h1 : t ≫ pullback.fst p (s ≫ p) = s := pullback.lift_fst _ _ _
  have h2 : t ≫ pullback.snd p (s ≫ p) = 𝟙 V := pullback.lift_snd _ _ _
  have : IsClosedImmersion (t ≫ pullback.snd p (s ≫ p)) := by rw [h2]; infer_instance
  have : IsClosedImmersion t := IsClosedImmersion.of_comp t (pullback.snd p (s ≫ p))
  have : IsDominant (t ≫ pullback.fst p (s ≫ p)) := by rw [h1]; infer_instance
  have : IsDominant t := IsDominant.of_comp_of_isOpenImmersion t (pullback.fst p (s ≫ p))
  have : Surjective t := surjective_of_isDominant_of_isClosed_range t t.isClosedEmbedding.isClosed_range
  have : IsReduced (pullback p (s ≫ p)) := isReduced_of_isOpenImmersion (pullback.fst p (s ≫ p))
  have : IsIso t := isIso_of_isClosedImmersion_of_surjective t
  refine ⟨by rw [← h1]; infer_instance, fun x hx => ?_⟩
  have hx' : x ∈ Set.range (pullback.fst p (s ≫ p)) := by
    rw [Scheme.Pullback.range_fst]; exact hx
  obtain ⟨y, rfl⟩ := hx'
  obtain ⟨v, rfl⟩ := t.surjective y
  exact ⟨v, by rw [← Scheme.Hom.comp_apply, h1]⟩

theorem isOpenImmersion_of_sections {G X : Scheme.{0}} [IsReduced G] (p : G ⟶ X) [IsSeparated p]
    (h : ∀ x : G, ∃ (V : Scheme.{0}) (s : V ⟶ G), IsDominant s ∧ IsOpenImmersion (s ≫ p) ∧ x ∈ Set.range s) :
    IsOpenImmersion p := by
  refine IsOpenImmersion.of_forall_source_exists p (fun x y hxy => ?_) (fun x => ?_)
  · obtain ⟨V, s, _, _, u, rfl⟩ := h x
    obtain ⟨v, rfl⟩ := (section_open p s).2 y ⟨u, by rw [← hxy, Scheme.Hom.comp_apply]⟩
    have : u = v := (s ≫ p).isOpenEmbedding.injective (by simpa using hxy)
    rw [this]
  · obtain ⟨V, s, _, _, hx⟩ := h x
    exact ⟨V, s, (section_open p s).1, hx, inferInstance⟩

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A : Over (Sp K)}

theorem isPullback_j (M : Model R A) : IsPullback M.j A.hom M.Y.hom (spMap (algebraMap R K)) := by
  have : IsIso M.e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map M.e.inv))
  have h : IsPullback M.e.inv.left A.hom (pullback.snd M.Y.hom (spMap (algebraMap R K))) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simpa using Over.w M.e.inv⟩
  simpa [Model.j] using h.paste_horiz (IsPullback.of_hasPullback M.Y.hom (spMap (algebraMap R K)))

theorem exists_model (M : Model R A) {G : Scheme.{0}} (p : G ⟶ M.Y.left) [IsOpenImmersion p]
    [QuasiCompact p] (i : A.left ⟶ G) (hi : i ≫ p = M.j) :
    ∃ e : (Over.pullback (spMap (algebraMap R K))).obj (Over.mk (p ≫ M.Y.hom)) ≅ A,
      e.inv.left ≫ pullback.fst (p ≫ M.Y.hom) (spMap (algebraMap R K)) = i := by
  have h : IsPullback i (𝟙 _) p M.j := IsPullback.of_vert_isIso_mono ⟨by simp [hi]⟩
  have h' := h.paste_vert (isPullback_j M)
  rw [Category.id_comp] at h'
  exact ⟨(Over.isoMk h'.isoPullback (by simp)).symm, by simp⟩

theorem mem_range_j [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] (M : Model R A)
    (y : M.Y.left) (hy : y ∉ M.sp) : y ∈ Set.range M.j := by
  have h1 : (M.Y.hom y : PrimeSpectrum R) ∈ Set.range (PrimeSpectrum.comap (algebraMap R K)) := by
    rw [PrimeSpectrum.localization_comap_range K (nonZeroDivisors R)]
    have hb : (M.Y.hom y : PrimeSpectrum R).asIdeal = ⊥ := by
      by_contra hb
      exact hy (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal
        ((M.Y.hom y : PrimeSpectrum R).isPrime.isMaximal hb)))
    show Disjoint _ _
    rw [hb, Set.disjoint_left]
    intro a ha ha'
    exact nonZeroDivisors.ne_zero ha ha'
  obtain ⟨t, ht⟩ := h1
  obtain ⟨a, ha, -⟩ := Scheme.exists_preimage_of_isPullback (isPullback_j M) y t ht.symm
  exact ⟨a, ha⟩

end GlobalTheory.SS.CompatCrit

namespace GlobalTheory.SS
open CompatCrit

theorem compat_of_isoAt_closure : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [IsIntegral A.left] (M N : Model R A) (δ : A.left ⟶ (M.Y ⊗ N.Y).left), δ ≫ (fst M.Y N.Y).left = M.j → δ ≫ (snd M.Y N.Y).left = N.j → (∀ z ∈ closure (Set.range δ), IsClosed {z} → (fst M.Y N.Y).left z ∈ M.sp → IsoAt M N (𝟙 A) ((fst M.Y N.Y).left z)) → Compat M N := by
  intro R K _ _ _ _ _ ⟨hD, _, _, hF⟩ A _ M N δ h₁ h₂ H
  have := M.smooth; have := M.sep; have := M.qc; have := N.smooth; have := N.sep; have := N.qc
  have : IsOpenImmersion (spMap (algebraMap R K)) := isOpenImmersion_spMap_of_isDiscreteValuationRing R K
  have : IsSchemeTheoreticallyDominant (spMap (algebraMap R K)) :=
    (schemeDominant_specMap_iff _).2 (IsFractionRing.injective R K)
  have jM : IsOpenImmersion M.j := MorphismProperty.of_isPullback (isPullback_j M).flip ‹_›
  have jN : IsOpenImmersion N.j := MorphismProperty.of_isPullback (isPullback_j N).flip ‹_›
  have qM : QuasiCompact M.j := MorphismProperty.of_isPullback (P := @QuasiCompact) (isPullback_j M).flip inferInstance
  have dM : IsSchemeTheoreticallyDominant M.j := .of_isPullback (isPullback_j M).flip
  have s₁ : IsSeparated (fst M.Y N.Y).left := inferInstanceAs (IsSeparated (pullback.fst M.Y.hom N.Y.hom))
  have s₂ : IsSeparated (snd M.Y N.Y).left := inferInstanceAs (IsSeparated (pullback.snd M.Y.hom N.Y.hom))
  have c₁ : QuasiCompact (fst M.Y N.Y).left := inferInstanceAs (QuasiCompact (pullback.fst M.Y.hom N.Y.hom))
  have : QuasiCompact (δ ≫ (fst M.Y N.Y).left) := by rw [h₁]; infer_instance
  have qδ : QuasiCompact δ := QuasiCompact.of_comp δ (fst M.Y N.Y).left
  have : IsReduced δ.image := IsSchemeTheoreticallyDominant.isReduced δ.toImage
  let p := δ.imageι ≫ (fst M.Y N.Y).left
  let q := δ.imageι ≫ (snd M.Y N.Y).left
  have hp : δ.toImage ≫ p = M.j := (δ.toImage_imageι_assoc _).trans h₁
  have hq : δ.toImage ≫ q = N.j := (δ.toImage_imageι_assoc _).trans h₂
  have : CompactSpace M.Y.left := QuasiCompact.compactSpace_of_compactSpace M.Y.hom
  have : CompactSpace δ.image := QuasiCompact.compactSpace_of_compactSpace p
  let S : Set δ.image := {x | ∃ (V : Scheme.{0}) (s : V ⟶ δ.image), IsDominant s ∧ IsOpenImmersion (s ≫ p) ∧
    IsOpenImmersion (s ≫ q) ∧ x ∈ Set.range s}
  have hSo : IsOpen S := by
    refine isOpen_iff_forall_mem_open.2 ?_
    rintro x ⟨V, s, a, b, c, hx⟩
    have := (section_open p s).1
    exact ⟨Set.range s, fun y hy => ⟨V, s, a, b, c, hy⟩, s.isOpenEmbedding.isOpen_range, hx⟩
  have hS : ∀ x, x ∈ S := by
    by_contra hne
    obtain ⟨x, hx, hc⟩ := hSo.isClosed_compl.exists_closed_singleton (not_forall.1 hne)
    apply hx
    by_cases hsp : p x ∈ M.sp
    · have hz : δ.imageι x ∈ closure (Set.range δ) := by
        have h := image_closure_subset_closure_image δ.imageι.continuous
          ⟨x, δ.toImage.denseRange x, rfl⟩
        refine closure_mono ?_ h
        rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
        exact ⟨a, by rw [← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι]⟩
      have hcz : IsClosed {δ.imageι x} := by
        simpa using δ.imageι.isClosedEmbedding.isClosedMap _ hc
      obtain ⟨U, g, hU, ⟨e₁, e₂⟩, hg⟩ := H _ hz hcz hsp
      let t : U.toScheme ⟶ (M.Y ⊗ N.Y).left := pullback.lift U.ι g e₁.symm
      have t₁ : t ≫ (fst M.Y N.Y).left = U.ι := pullback.lift_fst _ _ _
      have t₂ : t ≫ (snd M.Y N.Y).left = g := pullback.lift_snd _ _ _
      have : IsSchemeTheoreticallyDominant (M.j ∣_ U) := .of_isPullback (isPullback_morphismRestrict M.j U).flip
      have hw : (M.j ∣_ U) ≫ t = (M.j ⁻¹ᵁ U).ι ≫ δ := by
        refine pullback.hom_ext ?_ ?_
        · change ((M.j ∣_ U) ≫ t) ≫ (fst M.Y N.Y).left = (_ ≫ δ) ≫ (fst M.Y N.Y).left
          rw [Category.assoc, Category.assoc, t₁, h₁, morphismRestrict_ι]
        · change ((M.j ∣_ U) ≫ t) ≫ (snd M.Y N.Y).left = (_ ≫ δ) ≫ (snd M.Y N.Y).left
          rw [Category.assoc, Category.assoc, t₂, h₂, e₂]; simp
      let s := closureLift δ t (M.j ∣_ U) _ hw
      have sp : s ≫ p = U.ι := (closureLift_imageι_assoc δ t _ _ hw _).trans t₁
      have sq : s ≫ q = g := (closureLift_imageι_assoc δ t _ _ hw _).trans t₂
      have : IsDominant (M.j ⁻¹ᵁ U).ι := ⟨by
        rw [DenseRange, Scheme.Opens.range_ι]
        refine (M.j ⁻¹ᵁ U).isOpen.dense ?_
        obtain ⟨a, ha⟩ := M.j.denseRange.exists_mem_open U.isOpen ⟨_, hU⟩
        exact ⟨a, ha⟩⟩
      have : IsDominant ((M.j ∣_ U) ≫ s) := by
        simp only [s, comp_closureLift]; infer_instance
      have ds : IsDominant s := IsDominant.of_comp (M.j ∣_ U) s
      have op : IsOpenImmersion (s ≫ p) := by rw [sp]; infer_instance
      refine ⟨_, s, ds, op, by rw [sq]; exact hg, (section_open p s).2 x ?_⟩
      rw [sp, Scheme.Opens.range_ι]
      exact hU
    · have op : IsOpenImmersion (δ.toImage ≫ p) := by rw [hp]; exact jM
      refine ⟨_, δ.toImage, inferInstance, op, by rw [hq]; exact jN, (section_open p _).2 x ?_⟩
      rw [hp]
      exact mem_range_j M _ hsp
  have op : IsOpenImmersion p := isOpenImmersion_of_sections p fun x => by
    obtain ⟨V, s, a, b, -, hx⟩ := hS x
    exact ⟨V, s, a, b, hx⟩
  have oq : IsOpenImmersion q := isOpenImmersion_of_sections q fun x => by
    obtain ⟨V, s, a, -, c, hx⟩ := hS x
    exact ⟨V, s, a, c, hx⟩
  obtain ⟨e, he⟩ := exists_model M p δ.toImage hp
  let W : Model R A := ⟨Over.mk (p ≫ M.Y.hom), e, inferInstanceAs (Smooth (p ≫ M.Y.hom)),
    inferInstanceAs (IsSeparated (p ≫ M.Y.hom)), inferInstanceAs (QuasiCompact (p ≫ M.Y.hom))⟩
  have hW : W.j = δ.toImage := he
  let i : W.Y ⟶ M.Y ⊗ N.Y := Over.homMk δ.imageι (by simp [W, p])
  refine ⟨W, i ≫ fst _ _, i ≫ snd _ _, op, oq, ?_, ?_, ?_⟩
  · rw [hW]; exact hp
  · rw [hW]; exact hq
  · rw [lift_comp_fst_snd]
    exact inferInstanceAs (IsClosedImmersion δ.imageι)

end GlobalTheory.SS
