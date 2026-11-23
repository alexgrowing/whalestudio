import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GroupSchemeMorphismDescends
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGrpSchemeDescendsToFgSubring

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.ModelDescent

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {f : A →+* B} {g : B →+* C}
    {h : A →+* C} (e : g.comp f = h) : spMap g ≫ spMap f = spMap h := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, e]

theorem exists_factor {T L C : Type} [CommRing T] [CommRing L] [CommRing C] (f : T →+* C) (i : L →+* C)
    (hi : Function.Injective i) (h : ∀ t, f t ∈ i.range) : ∃ g : T →+* L, i.comp g = f := by
  let e : L ≃+* i.range := RingEquiv.ofBijective i.rangeRestrict
    ⟨fun x y hxy => hi (congrArg Subtype.val hxy), i.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp (f.codRestrict i.range h), RingHom.ext fun t => ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply ⟨f t, h t⟩)

theorem exists_hom_descent {R₀ K C : Type} [CommRing R₀] [CommRing K] [CommRing C] (a : R₀ →+* C) (b : K →+* C)
    {X X₀ Y : Scheme.{0}} (f : X ⟶ Sp C) (f₀ : X₀ ⟶ Sp R₀) (q : Y ⟶ Sp K) [QuasiCompact f₀] [QuasiSeparated f₀]
    [LocallyOfFinitePresentation q] (π : X ⟶ X₀) (φ : X ⟶ Y) (hp : IsPullback π f f₀ (spMap a))
    (hφ : φ ≫ q = f ≫ spMap b) :
    ∃ S : Finset C, ∀ (L : Type) [CommRing L] (i : L →+* C) (a' : R₀ →+* L) (b' : K →+* L),
      Function.Injective i → i.comp a' = a → i.comp b' = b → (∀ x ∈ S, x ∈ i.range) →
      ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp L) (π₁ : X₁ ⟶ X₀) (j : X ⟶ X₁), π₁ ≫ f₀ = f₁ ≫ spMap a' → j ≫ π₁ = π →
        j ≫ f₁ = f ≫ spMap i → ∃ ψ : X₁ ⟶ Y, j ≫ ψ = φ ∧ ψ ≫ q = f₁ ≫ spMap b' := by
  let k : Subring C := a.range ⊔ b.range
  let a₀ : R₀ →+* k := a.codRestrict k fun x => (le_sup_left : _ ≤ k) ⟨x, rfl⟩
  let b₀ : K →+* k := b.codRestrict k fun x => (le_sup_right : _ ≤ k) ⟨x, rfl⟩
  have ea : spMap (algebraMap k C) ≫ spMap a₀ = spMap a := spMap_comp_eq rfl
  have eb : spMap (algebraMap k C) ≫ spMap b₀ = spMap b := spMap_comp_eq rfl
  let π' : X ⟶ pullback f₀ (spMap a₀) :=
    pullback.lift π (f ≫ spMap (algebraMap k C)) (by rw [Category.assoc, ea, hp.w])
  have hπ₁ : π' ≫ pullback.fst _ _ = π := pullback.lift_fst _ _ _
  have hπ₂ : π' ≫ pullback.snd _ _ = f ≫ spMap (algebraMap k C) := pullback.lift_snd _ _ _
  have hp' : IsPullback π' f (pullback.snd f₀ (spMap a₀)) (spMap (algebraMap k C)) := by
    refine IsPullback.of_right (h₁₂ := pullback.fst f₀ (spMap a₀)) (v₁₃ := f₀) (h₂₂ := spMap a₀) ?_ hπ₂
      (.of_hasPullback _ _)
    rw [hπ₁, ea]
    exact hp
  let φ' : X ⟶ pullback q (spMap b₀) :=
    pullback.lift φ (f ≫ spMap (algebraMap k C)) (by rw [Category.assoc, eb, hφ])
  have hφ₁ : φ' ≫ pullback.fst _ _ = φ := pullback.lift_fst _ _ _
  have hφ₂ : φ' ≫ pullback.snd _ _ = f ≫ spMap (algebraMap k C) := pullback.lift_snd _ _ _
  obtain ⟨T, ψ, ⟨s, rfl⟩, h₁, h₂⟩ := Spread.exists_fg_comp_eq (A := C) (pullback.snd f₀ (spMap a₀))
    (pullback.snd q (spMap b₀)) (hp'.isoPullback.inv ≫ φ')
    (by rw [Category.assoc, hφ₂, ← hπ₂, hp'.isoPullback_inv_fst_assoc])
  refine ⟨s, fun L _ i a' b' hi ha hb hs X₁ f₁ π₁ j w hj₁ hj₂ => ?_⟩
  have hk : k ≤ i.range := by
    refine sup_le ?_ ?_ <;> rintro _ ⟨x, rfl⟩
    · exact ⟨a' x, RingHom.congr_fun ha x⟩
    · exact ⟨b' x, RingHom.congr_fun hb x⟩
  obtain ⟨g, hg⟩ := exists_factor (Algebra.adjoin k (s : Set C)).val.toRingHom i hi (by
    rintro ⟨x, hx⟩
    change x ∈ i.range
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact hs x hx
    | algebraMap r => exact hk r.2
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy)
  have hga : spMap g ≫ spMap (algebraMap k _) ≫ spMap a₀ = spMap a' := by
    rw [spMap_comp_eq rfl]
    exact spMap_comp_eq (RingHom.ext fun x => hi ((RingHom.congr_fun hg _).trans (RingHom.congr_fun ha x).symm))
  have hgb : spMap g ≫ spMap (algebraMap k _) ≫ spMap b₀ = spMap b' := by
    rw [spMap_comp_eq rfl]
    exact spMap_comp_eq (RingHom.ext fun x => hi ((RingHom.congr_fun hg _).trans (RingHom.congr_fun hb x).symm))
  have hg' := spMap_comp_eq hg
  let m₀ : X₁ ⟶ pullback f₀ (spMap a₀) :=
    pullback.lift π₁ (f₁ ≫ spMap g ≫ spMap (algebraMap k _)) (by
      rw [Category.assoc, Category.assoc, hga, w])
  have n₁ : m₀ ≫ pullback.fst _ _ = π₁ := pullback.lift_fst _ _ _
  have n₂ : m₀ ≫ pullback.snd _ _ = f₁ ≫ spMap g ≫ spMap (algebraMap k _) := pullback.lift_snd _ _ _
  let m : X₁ ⟶ pullback (pullback.snd f₀ (spMap a₀)) (spMap (algebraMap k (Algebra.adjoin k (s : Set C)))) :=
    pullback.lift m₀ (f₁ ≫ spMap g) (by rw [Category.assoc, n₂])
  have hm₁ : m ≫ pullback.fst _ _ = m₀ := pullback.lift_fst _ _ _
  have hm₂ : m ≫ pullback.snd _ _ = f₁ ≫ spMap g := pullback.lift_snd _ _ _
  have hjm₀ : j ≫ m₀ = π' := by
    apply pullback.hom_ext
    · rw [Category.assoc, n₁, hj₁, hπ₁]
    · rw [Category.assoc, n₂, reassoc_of% hj₂, reassoc_of% hg', Spread.spMap_algHom_comp, hπ₂]
  have hjm : j ≫ m = hp'.isoPullback.hom ≫ Spread.bcMap _ (Algebra.adjoin k (s : Set C)).val := by
    apply pullback.hom_ext
    · rw [Category.assoc, hm₁, hjm₀, Category.assoc, Spread.bcMap_fst, hp'.isoPullback_hom_fst]
    · rw [Category.assoc, hm₂, reassoc_of% hj₂, hg', Category.assoc, Spread.bcMap_snd,
        hp'.isoPullback_hom_snd_assoc]
  refine ⟨m ≫ ψ ≫ pullback.fst _ _, ?_, ?_⟩
  · rw [reassoc_of% hjm, reassoc_of% h₂, Iso.hom_inv_id_assoc, hφ₁]
  · rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% h₁, reassoc_of% hm₁, reassoc_of% n₂, hgb]

set_option backward.isDefEq.respectTransparency.types false in

theorem exists_iso_of_cover {S S' S'' : Scheme.{0}} (b : S' ⟶ S) (i : S'' ⟶ S') [Flat i] [Surjective i]
    [QuasiCompact i] [IsSchemeTheoreticallyDominant i] (A : Over S) [GrpObj A] [IsSeparated A.hom] (H : Over S')
    [GrpObj H] [Flat H.hom] (H' : Over S'') [GrpObj H'] (j : H'.left ⟶ H.left) (ψ : H.left ⟶ A.left)
    (hj : IsGrpPullback H' H i j) (h : IsGrpPullback H' A (i ≫ b) (j ≫ ψ)) (w : ψ ≫ A.hom = H.hom ≫ b) :
    ∃ e : H ≅ (Over.pullback b).obj A, IsMonHom e.hom := by
  let u : H ⟶ (Over.pullback b).obj A := Over.homMk (pullback.lift ψ H.hom w) (pullback.lift_snd _ _ _)
  have hu : u.left ≫ pullback.fst A.hom b = ψ := pullback.lift_fst _ _ _
  have hs : IsSeparated ((Over.pullback b).obj A).hom := by
    change IsSeparated (pullback.snd A.hom b)
    infer_instance
  have h₁ : IsGrpPullback H' ((Over.pullback b).obj A) i (j ≫ u.left) :=
    (isGrpPullback_pullback A b).cancel (h.congr rfl (by rw [Category.assoc, hu]))
      (by rw [Category.assoc, Over.w]; exact hj.1.w)
  have h₂ : IsMonHom u :=
    ExtUnique.isMonHom_of_isGrpPullback hj h₁ (𝟙 _) u (by rw [Over.id_left, Category.id_comp])
  have h₃ : IsPullback j (𝟙 _) u.left (j ≫ u.left) := by
    refine IsPullback.of_bot ?_ (Category.id_comp _).symm h₁.1
    rw [Category.id_comp, Over.w]
    exact hj.1
  have hq : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) (j ≫ u.left) :=
    ⟨⟨MorphismProperty.of_isPullback (P := @Surjective) h₁.1.flip ‹_›,
      MorphismProperty.of_isPullback (P := @Flat) h₁.1.flip ‹_›⟩,
      MorphismProperty.of_isPullback (P := @QuasiCompact) h₁.1.flip ‹_›⟩
  have h₄ : IsIso u.left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := MorphismProperty.isomorphisms Scheme.{0}) h₃.flip hq
      (MorphismProperty.isomorphisms.infer_property _)
  have h₅ : IsIso ((Over.forget _).map u) := h₄
  have h₆ : IsIso u := isIso_of_reflects_iso u (Over.forget _)
  exact ⟨asIso u, h₂⟩

theorem surjective_spMap {W R : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CommRing R] [IsDomain R]
    [IsLocalRing R] (f : W →+* R) (hf : Function.Injective f) [IsLocalHom f] : Surjective (spMap f) := by
  refine ⟨fun p => ?_⟩
  by_cases hp : p.asIdeal = ⊥
  · refine ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R), PrimeSpectrum.ext ?_⟩
    rw [hp]
    exact Ideal.comap_bot_of_injective f hf
  · refine ⟨IsLocalRing.closedPoint R, (IsLocalRing.comap_closedPoint f).trans (PrimeSpectrum.ext ?_)⟩
    exact (IsLocalRing.eq_maximalIdeal (p.isPrime.isMaximal hp)).symm

theorem exists_fraction_maps {V K W L R K' : Type} [CommRing V] [IsDomain V] [Field K] [Algebra V K]
    [IsFractionRing V K] [CommRing W] [IsDomain W] [Field L] [Algebra W L] [IsFractionRing W L] [CommRing R]
    [Field K'] [Algebra R K'] [IsFractionRing R K'] (v : V →+* W) (w : W →+* R) (hw : Function.Injective w)
    (a : K →+* K') (hc : (algebraMap R K').comp (w.comp v) = a.comp (algebraMap V K)) :
    ∃ (b : K →+* L) (i : L →+* K'), (algebraMap W L).comp v = b.comp (algebraMap V K) ∧
      i.comp (algebraMap W L) = (algebraMap R K').comp w ∧ i.comp b = a := by
  have iW : Function.Injective ((algebraMap R K').comp w) := (IsFractionRing.injective R K').comp hw
  let i : L →+* K' := IsFractionRing.lift iW
  have hi : i.comp (algebraMap W L) = (algebraMap R K').comp w :=
    RingHom.ext fun x => IsFractionRing.lift_algebraMap iW x
  have hiV : i.comp ((algebraMap W L).comp v) = a.comp (algebraMap V K) := by
    rw [← RingHom.comp_assoc, hi, ← hc]
    rfl
  have iV : Function.Injective ((algebraMap W L).comp v) := by
    refine Function.Injective.of_comp (f := i) ?_
    rw [← RingHom.coe_comp, hiV]
    exact a.injective.comp (IsFractionRing.injective V K)
  let b : K →+* L := IsFractionRing.lift iV
  have hb : b.comp (algebraMap V K) = (algebraMap W L).comp v :=
    RingHom.ext fun x => IsFractionRing.lift_algebraMap iV x
  refine ⟨b, i, hb.symm, hi, ?_⟩
  apply IsLocalization.ringHom_ext (nonZeroDivisors V)
  rw [RingHom.comp_assoc, hb, hiV]

theorem exists_iso_descent {R₀ K C : Type} [CommRing R₀] [CommRing K] [Field C] (a : R₀ →+* C) (b : K →+* C)
    (G₀ : Over (Sp R₀)) [GrpObj G₀] [Smooth G₀.hom] [IsSeparated G₀.hom] [QuasiCompact G₀.hom]
    (A : Over (Sp K)) [GrpObj A] [Smooth A.hom] [IsSeparated A.hom] (X : Over (Sp C)) [GrpObj X]
    (π : X.left ⟶ G₀.left) (φ : X.left ⟶ A.left) (hπ : IsGrpPullback X G₀ (spMap a) π)
    (hφ : IsGrpPullback X A (spMap b) φ) :
    ∃ S : Finset C, ∀ (L : Type) [Field L] (i : L →+* C) (a' : R₀ →+* L) (b' : K →+* L),
      i.comp a' = a → i.comp b' = b → (∀ x ∈ S, x ∈ i.range) →
      ∀ (H : Over (Sp L)) [GrpObj H] (π₁ : H.left ⟶ G₀.left), IsGrpPullback H G₀ (spMap a') π₁ →
        ∃ e : H ≅ (Over.pullback (spMap b')).obj A, IsMonHom e.hom := by
  obtain ⟨S, hS⟩ := exists_hom_descent a b X.hom G₀.hom A.hom π φ hπ.1 hφ.1.w
  refine ⟨S, fun L _ i a' b' ha hb hs H _ π₁ h₁ => ?_⟩
  have ea := spMap_comp_eq ha
  let j : X.left ⟶ H.left := h₁.1.lift π (X.hom ≫ spMap i) (by rw [Category.assoc, ea, hπ.1.w])
  have hj₁ : j ≫ π₁ = π := h₁.1.lift_fst _ _ _
  have hj₂ : j ≫ H.hom = X.hom ≫ spMap i := h₁.1.lift_snd _ _ _
  obtain ⟨ψ, hψ₁, hψ₂⟩ := hS L i a' b' i.injective ha hb hs H.left H.hom π₁ j h₁.1.w hj₁ hj₂
  have f₁ : Flat (spMap i) := by
    letI := i.toAlgebra
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact (inferInstance : Module.Flat L C)
  have f₂ : Surjective (spMap i) := ⟨fun _ => ⟨default, Subsingleton.elim _ _⟩⟩
  have f₃ : IsSchemeTheoreticallyDominant (spMap i) := .of_isDominant _
  have f₄ : Smooth H.hom := MorphismProperty.of_isPullback (P := @Smooth) h₁.1 ‹_›
  exact exists_iso_of_cover (spMap b') (spMap i) A H X j ψ (h₁.cancel (hπ.congr ea.symm hj₁.symm) hj₂)
    (hφ.congr (spMap_comp_eq hb).symm hψ₁.symm) hψ₂

theorem exists_smConn_level {R₀ W R : Type} [CommRing R₀] [CommRing W] [CommRing R] (c : R₀ →+* W) (w : W →+* R)
    [Surjective (spMap w)] (G₀ : Over (Sp R₀)) [GrpObj G₀] [IsCommMonObj G₀] [Smooth G₀.hom] [IsSeparated G₀.hom]
    [QuasiCompact G₀.hom] (G' : Over (Sp R)) [GrpObj G'] [GeometricallyConnected G'.hom] (φ₀ : G'.left ⟶ G₀.left)
    (hφ₀ : IsGrpPullback G' G₀ (spMap (w.comp c)) φ₀) :
    ∃ (G : Over (Sp W)) (_ : GrpObj G) (ε : (Over.pullback (spMap w)).obj G ≅ G') (π : G.left ⟶ G₀.left),
      SmConn G ∧ IsMonHom ε.hom ∧ IsGrpPullback G G₀ (spMap c) π := by
  have ec : spMap w ≫ spMap c = spMap (w.comp c) := spMap_comp_eq rfl
  let G := (Over.pullback (spMap c)).obj G₀
  have q₀ : IsGrpPullback G G₀ (spMap c) (pullback.fst G₀.hom (spMap c)) := isGrpPullback_pullback G₀ _
  let χ : G'.left ⟶ G.left := pullback.lift φ₀ (G'.hom ≫ spMap w) (by rw [Category.assoc, ec, hφ₀.1.w])
  have hχ₁ : χ ≫ pullback.fst G₀.hom (spMap c) = φ₀ := pullback.lift_fst _ _ _
  have hχ₂ : χ ≫ G.hom = G'.hom ≫ spMap w := pullback.lift_snd _ _ _
  have q₁ : IsGrpPullback G' G (spMap w) χ := q₀.cancel (hφ₀.congr ec.symm hχ₁.symm) hχ₂
  obtain ⟨ε, hε, -⟩ := grpPullback_iso (isGrpPullback_pullback G (spMap w)) q₁
  exact ⟨G, inferInstance, ε, _, ⟨inferInstance, MorphismProperty.of_isPullback (P := @Smooth) q₀.1 ‹_›,
    MorphismProperty.of_isPullback (P := @IsSeparated) q₀.1 ‹_›,
    MorphismProperty.of_isPullback (P := @QuasiCompact) q₀.1 ‹_›,
    GrpFlatDesc.geometricallyConnected_of_isPullback q₁.1⟩, hε, q₀⟩

end GlobalTheory.ModelDescent

namespace GlobalTheory

open ModelDescent

theorem smConn_model_descends : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (R K' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Algebra V R] [Field K'] [Algebra R K'] [IsFractionRing R K'] [Algebra K K'], (algebraMap R K').comp (algebraMap V R) = (algebraMap K K').comp (algebraMap V K) → ∀ (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (G' : Over (Sp R)) [GrpObj G'], SmConn G' → IsModel (L := K') A G' → ∃ s : Finset R, ∀ (W : Subalgebra V R) (_ : IsDiscreteValuationRing W), (↑s : Set R) ⊆ W → IsLocalHom W.val.toRingHom → ∃ (G : Over (Sp W)) (_ : GrpObj G) (_ : Algebra K (FractionRing W)) (ε : (Over.pullback (spMap W.val.toRingHom)).obj G ≅ G'), SmConn G ∧ IsMonHom ε.hom ∧ (algebraMap W (FractionRing W)).comp (algebraMap V W) = (algebraMap K (FractionRing W)).comp (algebraMap V K) ∧ IsModel (L := FractionRing W) A G := by
  intro V K _ _ _ _ _ _ R K' _ _ _ _ _ _ _ _ hc A _ hA G' _ ⟨hcomm, hsm, hsep, hqc, hgc⟩ ⟨e, he⟩
  classical
  obtain ⟨R₀, G₀, _, _, φ₀, -, ⟨t, ht⟩, s₁, s₂, s₃, hφ₀⟩ := GlobalTheory.smooth_grpScheme_descends_to_fg_subring R G' ∅ hsm hsep hqc
  have := hA.smooth
  have := hA.proper
  have p₁ := isGrpPullback_pullback G' (spMap (algebraMap R K'))
  have p₂ := ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback A (spMap (algebraMap K K')))).congr
    (Category.id_comp _) rfl
  have p₃ := (p₁.comp hφ₀).congr (spMap_comp_eq rfl) rfl
  obtain ⟨S, hS⟩ := exists_iso_descent _ (algebraMap K K') G₀ A _ _ _ p₃ p₂
  choose num den hden hnd using fun x : K' => IsFractionRing.div_surjective R x
  refine ⟨t.image Subtype.val ∪ (S.image num ∪ S.image den), fun W hW hs hloc => ?_⟩
  have hR₀ : ∀ x : R₀, R₀.subtype x ∈ W := by
    intro x
    have hx : x ∈ Algebra.adjoin ℤ (t : Set R₀) := ht ▸ Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact hs (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx))
    | algebraMap r => simp
    | add x y _ _ hx hy => exact map_add R₀.subtype x y ▸ add_mem hx hy
    | mul x y _ _ hx hy => exact map_mul R₀.subtype x y ▸ mul_mem hx hy
  let c : R₀ →+* W := R₀.subtype.codRestrict W hR₀
  have hsurj := surjective_spMap W.val.toRingHom Subtype.val_injective
  obtain ⟨G, iG, ε, π, hG, hε, hπ⟩ := exists_smConn_level c W.val.toRingHom G₀ G' φ₀ hφ₀
  obtain ⟨b, i, hb, hi, hib⟩ := exists_fraction_maps (L := FractionRing W) (algebraMap V W) W.val.toRingHom
    Subtype.val_injective (algebraMap K K') hc
  have hmem : ∀ x ∈ S, x ∈ i.range := by
    intro x hx
    have h₁ : num x ∈ W := hs (Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx)))
    have h₂ : den x ∈ W := hs (Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hx)))
    refine ⟨algebraMap W (FractionRing W) ⟨_, h₁⟩ / algebraMap W (FractionRing W) ⟨_, h₂⟩, ?_⟩
    rw [map_div₀]
    exact (congrArg₂ (· / ·) (RingHom.congr_fun hi _) (RingHom.congr_fun hi _)).trans (hnd x)
  have hm := hS (FractionRing W) i ((algebraMap W (FractionRing W)).comp c) b
    (by rw [← RingHom.comp_assoc, hi]; rfl) hib hmem _ _
    (((isGrpPullback_pullback G (spMap (algebraMap W (FractionRing W)))).comp hπ).congr (spMap_comp_eq rfl) rfl)
  exact ⟨G, iG, b.toAlgebra, ε, hG, hε, hb, hm⟩

end GlobalTheory
