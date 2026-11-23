import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.GlueNear

theorem isSeparated_of_surjective {X Y S : Scheme.{0}} (j : X ⟶ Y) (f : Y ⟶ S)
    [Surjective j] [UniversallyClosed j] [IsSeparated (j ≫ f)] : IsSeparated f := by
  let m : pullback (j ≫ f) (j ≫ f) ⟶ pullback f f :=
    pullback.map (j ≫ f) (j ≫ f) f f j j (𝟙 S) (by simp) (by simp)
  have hm : UniversallyClosed m :=
    MorphismProperty.pullbackMap (P := @UniversallyClosed) ‹_› ‹_› rfl rfl
  have e : j ≫ pullback.diagonal f = pullback.diagonal (j ≫ f) ≫ m := by
    apply pullback.hom_ext <;> simp [m, pullback.map, pullback.lift_fst, pullback.lift_snd]
  have : UniversallyClosed (j ≫ pullback.diagonal f) := by rw [e]; infer_instance
  have : UniversallyClosed (pullback.diagonal f) := UniversallyClosed.of_comp_surjective j _
  exact ⟨IsClosedImmersion.of_isPreimmersion _ (pullback.diagonal f).isClosedMap.isClosed_range⟩

theorem isPullback_iSup {Y X S S' : Scheme.{0}} (π : Y ⟶ X) (q : X ⟶ S) (t : Y ⟶ S') (f : S' ⟶ S)
    {I : Type} (V : I → X.Opens)
    (h : ∀ i, IsPullback (π ∣_ V i) ((π ⁻¹ᵁ V i).ι ≫ t) ((V i).ι ≫ q) f) :
    IsPullback (π ∣_ (⨆ i, V i)) ((π ⁻¹ᵁ (⨆ i, V i)).ι ≫ t) ((⨆ i, V i).ι ≫ q) f := by
  refine Scheme.isPullback_of_openCover _ _ _ _ (Scheme.Opens.iSupOpenCover V) fun (i : I) => ?_
  have e : V i ≤ ⨆ i, V i := le_iSup V i
  have sq : IsPullback (Y.homOfLE (π.preimage_mono e)) (π ∣_ V i) (π ∣_ (⨆ i, V i)) (X.homOfLE e) := by
    refine IsPullback.of_right (h₁₂ := (π ⁻¹ᵁ (⨆ i, V i)).ι) (h₂₂ := (⨆ i, V i).ι) (v₁₃ := π) ?_ ?_
      (isPullback_morphismRestrict π _).flip
    · simpa using (isPullback_morphismRestrict π (V i)).flip
    · rw [← cancel_mono (⨆ i, V i).ι]; simp
  refine (h i).of_iso sq.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (Category.comp_id _).trans sq.isoPullback_hom_snd.symm
  · refine (Category.comp_id _).trans ?_
    refine Eq.trans ?_ (Category.assoc _ _ _)
    erw [sq.isoPullback_hom_fst]
    simp
  · change _ = 𝟙 _ ≫ X.homOfLE e ≫ _
    simp
  · simp

theorem smooth_iSup {X S : Scheme.{0}} (q : X ⟶ S) {I : Type} (V : I → X.Opens)
    (h : ∀ i, Smooth ((V i).ι ≫ q)) : Smooth ((⨆ i, V i).ι ≫ q) := by
  have : IsZariskiLocalAtSource @Smooth := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_openCover (P := @Smooth) (Scheme.Opens.iSupOpenCover V) fun (i : I) => ?_
  change Smooth (X.homOfLE (le_iSup V i) ≫ _)
  simpa using h i

theorem exists_near {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} (f : S ⟶ Sp R) [IsFinite f] [Surjective f]
    (G : Over S) [IsSeparated G.hom] (H : G.left.Opens)
    (hcl : ∀ g : G.left, f (G.hom g) = closedPoint R → g ∈ H) (hc : IsCompact (H : Set G.left))
    (X : Over (Sp R)) (π : H.toScheme ⟶ X.left)
    (hloc : ∀ x : H.toScheme, f (G.hom (H.ι x)) = closedPoint R → ∃ V : X.left.Opens, π x ∈ V ∧ IsAffineOpen V ∧
      Smooth (V.ι ≫ X.hom) ∧ IsPullback (π ∣_ V) ((π ⁻¹ᵁ V).ι ≫ H.ι ≫ G.hom) (V.ι ≫ X.hom) f) :
    ∃ N : Near f G, ∀ (α : G.left ⟶ G.left) (β : S ⟶ S) (hα : H ≤ α ⁻¹ᵁ H), α ≫ G.hom = G.hom ≫ β →
      α.resLE H H hα ≫ π = π →
      ∀ (T : Scheme.{0}) (s : T ⟶ S) (u : T ⟶ N.U.left) (x : T ⟶ G.left), N.Pt s u x → N.Pt (s ≫ β) u (x ≫ α) := by
  classical
  have : CompactSpace H.toScheme := isCompact_iff_compactSpace.mp hc
  let Z : Set H.toScheme := {x | f (G.hom (H.ι x)) = closedPoint R}
  have hZ : IsCompact Z := by
    refine IsClosed.isCompact ?_
    exact (isClosed_singleton_closedPoint R).preimage
      (f.continuous.comp (G.hom.continuous.comp H.ι.continuous))
  choose V hV hVa hVs hVp using fun x : Z => hloc x.1 x.2
  obtain ⟨t, ht⟩ := hZ.elim_finite_subcover (fun x : Z => ((π ⁻¹ᵁ V x : H.toScheme.Opens) : Set H.toScheme))
    (fun x => (π ⁻¹ᵁ V x).isOpen) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hV ⟨x, hx⟩⟩)
  let W : t → X.left.Opens := fun i => V i.1
  have P := isPullback_iSup π X.hom (H.ι ≫ G.hom) f W fun i => hVp i.1
  have hS := smooth_iSup X.hom W fun i => hVs i.1
  have hC : IsCompact ((⨆ i, W i : X.left.Opens) : Set X.left) := by
    rw [TopologicalSpace.Opens.coe_iSup]
    exact isCompact_iUnion fun i => (hVa i.1).isCompact
  have hA : ∀ x ∈ Z, π x ∈ ⨆ i, W i := by
    intro x hx
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.1 (ht hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, hi⟩, hx⟩
  generalize (⨆ i, W i) = U at P hS hC hA
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hC
  have hq : QuasiCompact (U.ι ≫ X.hom) := (quasiCompact_iff_compactSpace _).2 inferInstance
  have hsep : IsSeparated (U.ι ≫ X.hom) := by
    have h₁ : IsFinite (π ∣_ U) := MorphismProperty.of_isPullback (P := @IsFinite) P.flip inferInstance
    have h₂ : Surjective (π ∣_ U) := MorphismProperty.of_isPullback (P := @Surjective) P.flip inferInstance
    have h₃ : IsSeparated (π ∣_ U ≫ U.ι ≫ X.hom) := by rw [P.w]; infer_instance
    exact isSeparated_of_surjective (π ∣_ U) _
  let N : Near f G :=
    { U := Over.mk (U.ι ≫ X.hom)
      smooth := hS
      separated := hsep
      quasiCompact := hq
      u := P.isoPullback.inv ≫ (π ⁻¹ᵁ U).ι ≫ H.ι
      isOpen := inferInstanceAs (IsOpenImmersion (P.isoPullback.inv ≫ (π ⁻¹ᵁ U).ι ≫ H.ι))
      u_over := (Category.assoc _ _ _).trans
        ((congrArg (P.isoPullback.inv ≫ ·) (Category.assoc _ _ _)).trans P.isoPullback_inv_snd)
      all := by
        intro g hg
        refine ⟨P.isoPullback.hom ⟨⟨g, hcl g hg⟩, hA ⟨g, hcl g hg⟩ hg⟩, ?_⟩
        change (P.isoPullback.hom ≫ P.isoPullback.inv ≫ (π ⁻¹ᵁ U).ι ≫ H.ι) _ = g
        rw [Iso.hom_inv_id_assoc]
        rfl }
  have pt : ∀ {T : Scheme.{0}} (s : T ⟶ S) (u : T ⟶ U.toScheme) (x : T ⟶ G.left), N.Pt s u x ↔
      ∃ y : T ⟶ (π ⁻¹ᵁ U).toScheme, y ≫ π ∣_ U = u ∧ y ≫ (π ⁻¹ᵁ U).ι ≫ H.ι ≫ G.hom = s ∧
        y ≫ (π ⁻¹ᵁ U).ι ≫ H.ι = x := by
    intro T s u x
    constructor
    · rintro ⟨x₀, h₁, h₂, h₃⟩
      refine ⟨x₀ ≫ P.isoPullback.inv, ?_, ?_, ?_⟩
      · exact (Category.assoc _ _ _).trans ((congrArg (x₀ ≫ ·) P.isoPullback_inv_fst).trans h₁)
      · exact (Category.assoc _ _ _).trans ((congrArg (x₀ ≫ ·) P.isoPullback_inv_snd).trans h₂)
      · exact (Category.assoc _ _ _).trans h₃
    · rintro ⟨y, h₁, h₂, h₃⟩
      refine ⟨y ≫ P.isoPullback.hom, ?_, ?_, ?_⟩
      · exact (Category.assoc _ _ _).trans ((congrArg (y ≫ ·) P.isoPullback_hom_fst).trans h₁)
      · exact (Category.assoc _ _ _).trans ((congrArg (y ≫ ·) P.isoPullback_hom_snd).trans h₂)
      · exact (Category.assoc _ _ _).trans ((congrArg (y ≫ ·) (P.isoPullback.hom_inv_id_assoc _)).trans h₃)
  refine ⟨N, fun α β hα hαβ hπ T s u x hx => ?_⟩
  obtain ⟨y, rfl, rfl, rfl⟩ := (pt s u x).1 hx
  have Q := isPullback_morphismRestrict π U
  let δ : (π ⁻¹ᵁ U).toScheme ⟶ (π ⁻¹ᵁ U).toScheme :=
    Q.lift (π ∣_ U) ((π ⁻¹ᵁ U).ι ≫ α.resLE H H hα) (by rw [Category.assoc, hπ, Q.w])
  have hδ : δ ≫ (π ⁻¹ᵁ U).ι ≫ H.ι = (π ⁻¹ᵁ U).ι ≫ H.ι ≫ α := by
    rw [Q.lift_snd_assoc, Category.assoc, Scheme.Hom.resLE_comp_ι]
  refine (pt _ _ _).2 ⟨y ≫ δ, ?_, ?_, ?_⟩
  · rw [Category.assoc, Q.lift_fst]
  · simp only [Category.assoc]
    rw [reassoc_of% hδ, hαβ]
  · simp only [Category.assoc]
    rw [hδ]

theorem glue_near : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∀ (H : G'.left.Opens) (hH : ∀ σ, a.act σ ⁻¹ᵁ H = H), (∀ g : G'.left, spMap ρ (G'.hom g) = closedPoint R → g ∈ H) → IsCompact (H : Set G'.left) → ∀ (X : Over (Sp R)) (π : H.toScheme ⟶ X.left) (hX : π ≫ X.hom = H.ι ≫ G'.hom ≫ spMap ρ), IsAffineHom π → Surjective π → (∀ σ, (a.act σ).resLE H H (hH σ).ge ≫ π = π) → (∀ x y : H.toScheme, π x = π y → ∃ σ, a.act σ (H.ι x) = H.ι y) → (∀ V : X.left.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(H.toScheme, π ⁻¹ᵁ V), (∀ σ (h : π ⁻¹ᵁ V ≤ ((a.act σ).resLE H H (hH σ).ge) ⁻¹ᵁ (π ⁻¹ᵁ V)), (((a.act σ).resLE H H (hH σ).ge).appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → (∀ x : H.toScheme, spMap ρ (G'.hom (H.ι x)) = closedPoint R → ∃ V : X.left.Opens, π x ∈ V ∧ IsAffineOpen V ∧ Smooth (V.ι ≫ X.hom) ∧ IsIso (pullback.lift (π.resLE V (π ⁻¹ᵁ V) le_rfl) ((π ⁻¹ᵁ V).ι ≫ H.ι ≫ G'.hom) (by rw [Scheme.Hom.resLE_comp_ι_assoc, hX]; simp only [Category.assoc]) : (π ⁻¹ᵁ V).toScheme ⟶ pullback (V.ι ≫ X.hom) (spMap ρ))) → ∃ N : Near (spMap ρ) G', (∀ σ (T : Scheme.{0}) (s : T ⟶ Sp R') (u : T ⟶ N.U.left) (x : T ⟶ G'.left), N.Pt s u x → N.Pt (s ≫ spMap (Gal.hom σ)) u (x ≫ a.act σ)) := by
  intro R _ _ _ _ R' _ _ _ ρ hρ _ D D' hD A' G' _ _ hG U' a H hH hcl hc X π hX _ _ hπ _ _ hloc
  have := hG.separated
  have : IsFinite (spMap ρ) := (IsFinite.SpecMap_iff _).2 hρ.2.2
  have : Surjective (spMap ρ) := ⟨RingHom.IsIntegral.comap_surjective hρ.2.2.to_isIntegral hρ.2.1⟩
  obtain ⟨N, hN⟩ := exists_near (spMap ρ) G' H hcl hc X π fun x hx => by
    obtain ⟨V, h₁, h₂, h₃, h₄⟩ := hloc x hx
    refine ⟨V, h₁, h₂, h₃, ?_⟩
    rw [← Scheme.Hom.resLE_eq_morphismRestrict]
    refine IsPullback.of_iso_pullback ⟨?_⟩ (@asIso _ _ _ _ _ h₄) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    rw [Scheme.Hom.resLE_comp_ι_assoc, hX]
    simp only [Category.assoc]
  exact ⟨N, fun σ => hN (a.act σ) _ (hH σ).ge (a.cart σ).1.w (hπ σ)⟩

end GlobalTheory.Mum.GlueNear
