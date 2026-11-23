import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendsToSemiAbelianAwayOfChartsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtensionHolds
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkGenerizationGermCompat
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullbackFactor

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem HasExt.of_comp {W V T : Scheme.{0}} (g : W ⟶ V) (e : V ⟶ T) (B : Over W) [GrpObj B] (h : HasExt (g ≫ e) B) :
    HasExt g B := by
  obtain ⟨G, _, φ, hG, hφ⟩ := h
  exact ⟨(Over.pullback e).obj G, inferInstance, _, IsSemiAbelian.pullback _ _ hG,
    ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor e g hφ⟩

theorem HasExt.of_dense {W V U : Scheme.{0}} [AlgebraicGeometry.IsNoetherian V]
    (hV : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme V) (l : W ⟶ V) [IsOpenImmersion l] [IsDominant l] (j : V ⟶ U)
    (A : Over V) [GrpObj A] (hA : IsSemiAbelian A) (B : Over W) [GrpObj B] (κ : B.left ⟶ A.left)
    (hκ : IsGrpPullback B A l κ) (h : HasExt (l ≫ j) B) : HasExt j A := by
  obtain ⟨G, _, φ, hG, hφ⟩ := h
  have h2 := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor j l hφ
  obtain ⟨e, ⟨he, -⟩, -⟩ := GlobalTheory.semiAbelianHomExtension_holds.existsUnique_iso_of_extensions hV hA
    (IsSemiAbelian.pullback j G hG) hκ h2
  exact ⟨G, inferInstance, e.hom.left ≫ pullback.fst _ _, hG,
    ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback G j)).congr (Category.id_comp _) rfl⟩

theorem etale_of_comp_bijective {B A R : Type} [CommRing B] [IsLocalRing B] [CommRing A] [IsLocalRing A]
    [CommRing R] [IsLocalRing R] (e : B →+* A) (he : Function.Bijective e) (φ : A →+* R)
    (h : IsEtaleCompletion (φ.comp e)) (h' : ((residue R).comp (φ.comp e)).FormallyUnramified) :
    IsEtaleCompletion φ ∧ ((residue R).comp φ).FormallyUnramified := by
  obtain ⟨h1, h2, h3⟩ := h
  let E := RingEquiv.ofBijective e he
  have hφ : φ = (φ.comp e).comp E.symm.toRingHom := by
    ext a
    exact congrArg φ (E.apply_symm_apply a).symm
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hφ]
    exact RingHom.Flat.comp (RingHom.Flat.of_bijective E.symm.bijective) h1
  · rw [← h2, ← Ideal.map_map, IsLocalRing.map_maximalIdeal_of_surjective e he.2]
  · exact RingHom.Finite.of_comp_finite (f := e) h3
  · exact RingHom.FormallyUnramified.of_comp (f := e) h'

theorem etale_of_comp_openImmersion {S S' : Scheme.{0}} (i : S' ⟶ S) [IsOpenImmersion i] {R : Type} [CommRing R]
    [IsLocalRing R] (ξ' : Sp R ⟶ S') (ξ : Sp R ⟶ S) (hξ : ξ' ≫ i = ξ)
    (h : IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom)
    (h' : ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified) :
    IsEtaleCompletion (Scheme.stalkClosedPointTo ξ').hom ∧
      ((residue R).comp (Scheme.stalkClosedPointTo ξ').hom).FormallyUnramified := by
  subst hξ
  have hiso : IsIso (i.stalkMap (ξ' (IsLocalRing.closedPoint (CommRingCat.of R)))) :=
    (IsOpenImmersion.iff_isIso_stalkMap.1 inferInstance).2 _
  have hb : Function.Bijective (i.stalkMap (ξ' (IsLocalRing.closedPoint (CommRingCat.of R)))).hom :=
    ConcreteCategory.bijective_of_isIso _
  rw [Scheme.stalkClosedPointTo_comp] at h h'
  exact etale_of_comp_bijective _ hb _ h h'

theorem generic_mem_of_flat {S : Scheme.{0}} {R : Type} [CommRing R] [IsLocalRing R] [IsDomain R] (ξ : Sp R ⟶ S)
    (h : (Scheme.stalkClosedPointTo ξ).hom.Flat) (U : S.Opens) (t : S) (ht : t ∈ U) (hs : t ⤳ ξ (closedPoint R))
    (z : Sp (FractionRing R)) : (jK R ≫ ξ) z ∈ U := by
  have hfl : Flat ξ := by
    rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of R) ξ]
    have : Flat (Spec.map (Scheme.stalkClosedPointTo ξ)) := (HasRingHomProperty.Spec_iff (P := @Flat)).2 h
    exact MorphismProperty.comp_mem @Flat _ _ this (GlobalTheory.LocalRingGeneralisation.flat_fromSpecStalk _ _)
  obtain ⟨p, -, hp⟩ := Flat.generalizingMap ξ hs
  have hz : jK R z ⤳ p := by
    refine (PrimeSpectrum.le_iff_specializes _ _).1 fun a ha => ?_
    have ha' : algebraMap R (FractionRing R) a ∈ z.asIdeal := ha
    have := z.isPrime
    rw [Ideal.eq_bot_of_prime z.asIdeal, Ideal.mem_bot, map_eq_zero_iff _ (IsFractionRing.injective R _)] at ha'
    rw [ha']
    exact zero_mem _
  exact (hz.map ξ.continuous).mem_open U.isOpen (by rw [hp]; exact ht)

theorem Chart.nonempty_restrict {X S X' S' : Scheme.{0}} [IrreducibleSpace S'] [Nonempty X'] (j : X ⟶ S) [Mono j]
    (j' : X' ⟶ S') [IsOpenImmersion j'] (i : S' ⟶ S) [IsOpenImmersion i] (k : X' ⟶ X) (w : k ≫ j = j' ≫ i)
    (A : Over X) [GrpObj A] (x : S') (C : Chart j A (i x)) : Nonempty (Chart j' ((Over.pullback k).obj A) x) := by
  have h1 : Set.range C.ξ ⊆ Set.range i := by
    rintro _ ⟨y, rfl⟩
    exact (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of C.R) C.ξ (U := i.opensRange)
      ⟨x, C.centre.symm⟩).ge (Set.mem_univ y)
  let ξ' : Sp C.R ⟶ S' := IsOpenImmersion.lift i C.ξ h1
  have hξ : ξ' ≫ i = C.ξ := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨he, hu⟩ := etale_of_comp_openImmersion i ξ' C.ξ hξ C.etc C.unr
  have hg : genericPoint S' ∈ j'.opensRange :=
    ((genericPoint_spec S').mem_open_set_iff j'.opensRange.isOpen).2 (by
      rw [Set.univ_inter]; exact Set.range_nonempty _)
  have h2 : Set.range (jK C.R ≫ ξ') ⊆ Set.range j' := by
    rintro _ ⟨z, rfl⟩
    exact generic_mem_of_flat ξ' he.1 j'.opensRange _ hg (genericPoint_specializes _) z
  let y' : Sp (FractionRing C.R) ⟶ X' := IsOpenImmersion.lift j' (jK C.R ≫ ξ') h2
  have hy' : y' ≫ j' = jK C.R ≫ ξ' := IsOpenImmersion.lift_fac _ _ _
  have hk : C.y = y' ≫ k := by
    rw [← cancel_mono j, Category.assoc, w, ← Category.assoc, hy', Category.assoc, hξ, C.hy]
  refine ⟨{ R := C.R, complete := C.complete, charZero := C.charZero, ξ := ξ', centre := ?_, etc := he, unr := hu,
            G := C.G, semi := C.semi, y := y', hy := hy', α := _,
            gen := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor k y' (C.gen.congr hk rfl) }⟩
  apply i.isOpenEmbedding.injective
  exact (congrArg (fun q => q (closedPoint C.R)) hξ).trans C.centre

theorem hasExt_opensRange (X S : Scheme.{0}) [AlgebraicGeometry.IsNoetherian S]
    (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) (j : X ⟶ S) [IsOpenImmersion j] [IsDominant j]
    (A : Over X) [GrpObj A] (hA : IsAbelianScheme A) (L : LB A.left) (hL : L.IsLB) (hamp : RelAmple A L)
    (hC : ∀ x : S, Nonempty (Chart j A x)) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] (i : Sp R ⟶ S) [IsOpenImmersion i] :
    HasExt (j ∣_ i.opensRange) ((Over.pullback (j ⁻¹ᵁ i.opensRange).ι).obj A) := by
  obtain ⟨x₀, p, hp⟩ := j.denseRange.exists_mem_open i.opensRange.isOpen (Set.range_nonempty i)
  obtain ⟨_, ⟨f : R, rfl⟩, hpf, hf⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (a := p) (u := (i ⁻¹ᵁ j.opensRange).1) ⟨x₀, hp.symm⟩ (i ⁻¹ᵁ j.opensRange).isOpen
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hpf (zero_mem _)
  have hrange : Set.range (awayMap f) = (PrimeSpectrum.basicOpen f).1 :=
    PrimeSpectrum.localization_away_comap_range (Localization.Away f) f
  have : IsOpenImmersion (awayMap f) := IsOpenImmersion.of_isLocalization f
  have hne : Nonempty (Sp (Localization.Away f)) := by
    obtain ⟨q, -⟩ : p ∈ Set.range (awayMap f) := hrange ▸ hpf
    exact ⟨q⟩
  have h1 : Set.range (awayMap f ≫ i) ⊆ Set.range j := by
    rintro _ ⟨z, rfl⟩
    exact hf (hrange.le (Set.mem_range_self z))
  let k : Sp (Localization.Away f) ⟶ X := IsOpenImmersion.lift j (awayMap f ≫ i) h1
  have hk : k ≫ j = awayMap f ≫ i := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (k ≫ j) := by rw [hk]; infer_instance
  have : IsOpenImmersion k := IsOpenImmersion.of_comp k j
  have hL' := pull_isLB hL (pullback.fst A.hom k)
  obtain ⟨u, hu⟩ := GlobalTheory.lbIso_refl hL'
  have hext : HasExt (awayMap f) ((Over.pullback k).obj A) :=
    GlobalTheory.T.extendsToSemiAbelian_away_of_charts R f hf0 _ (isAbelianScheme_pullback_obj k A hA) (L.pull (pullback.fst A.hom k)) hL'
      (relAmple_pull (isGrpPullback_pullback A k).1 hL hL' ((isGen_iff u).1 hu) k.opensRange
        (isAffineOpen_opensRange k) (fun y => ⟨y, rfl⟩) hamp)
      fun x => (hC (i x)).elim fun C => Chart.nonempty_restrict j (awayMap f) i k hk A x C
  have h2 : Set.range k ⊆ Set.range (j ⁻¹ᵁ i.opensRange).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact ⟨awayMap f z, (congrArg (fun q => q z) hk).symm⟩
  let l : Sp (Localization.Away f) ⟶ (j ⁻¹ᵁ i.opensRange).toScheme := IsOpenImmersion.lift _ k h2
  have hl : l ≫ (j ⁻¹ᵁ i.opensRange).ι = k := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (l ≫ (j ⁻¹ᵁ i.opensRange).ι) := by rw [hl]; infer_instance
  have : IsOpenImmersion l := IsOpenImmersion.of_comp l (j ⁻¹ᵁ i.opensRange).ι
  have hcomp : l ≫ (j ∣_ i.opensRange) ≫ i.isoOpensRange.inv = awayMap f := by
    rw [← cancel_mono i, Category.assoc, Category.assoc, i.isoOpensRange_inv_comp, morphismRestrict_ι, ← Category.assoc,
      hl, hk]
  have : IsDominant l := by
    have hd : Dense (Set.range (awayMap f)) :=
      (awayMap f).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)
    have hg := ((j ∣_ i.opensRange) ≫ i.isoOpensRange.inv).isOpenEmbedding
    refine ⟨(hd.preimage hg.isOpenMap).mono ?_⟩
    rintro y ⟨z, hz⟩
    exact ⟨z, hg.injective ((congrArg (fun q => q z) hcomp).trans hz)⟩
  have := GlobalTheory.IsNormalScheme.of_pred hS
  have : IsLocallyNoetherian (j ⁻¹ᵁ i.opensRange).toScheme :=
    isLocallyNoetherian_of_isOpenImmersion ((j ⁻¹ᵁ i.opensRange).ι ≫ j)
  have : TopologicalSpace.NoetherianSpace (j ⁻¹ᵁ i.opensRange).toScheme :=
    ((j ⁻¹ᵁ i.opensRange).ι ≫ j).isOpenEmbedding.isInducing.noetherianSpace
  have : AlgebraicGeometry.IsNoetherian (j ⁻¹ᵁ i.opensRange).toScheme := {}
  have : GlobalTheory.IsNormalScheme (j ⁻¹ᵁ i.opensRange).toScheme :=
    GlobalTheory.IsNormalScheme.of_isOpenImmersion ((j ⁻¹ᵁ i.opensRange).ι ≫ j)
  refine HasExt.of_dense (GlobalTheory.IsNormalScheme.pred _) l _ _
    (isSemiAbelian_of_isAbelianScheme _ (isAbelianScheme_pullback_obj _ A hA)) ((Over.pullback k).obj A) _
    (ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor _ l ((isGrpPullback_pullback A k).congr hl.symm rfl))
    (HasExt.of_comp _ i.isoOpensRange.inv _ ?_)
  rw [Category.assoc, hcomp]
  exact hext

theorem exists_hasExt_near : ∀ (X S : Scheme.{0}) [AlgebraicGeometry.IsNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ∀ (j : X ⟶ S) [IsOpenImmersion j], IsDominant j → ∀ (A : Over X) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → RelAmple A L → (∀ x : S, Nonempty (Chart j A x)) → ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ HasExt (j ∣_ U) ((Over.pullback (j ⁻¹ᵁ U).ι).obj A) := by
  intro X S _ hS j _ hj A _ hA L hL hamp hC s
  have := GlobalTheory.IsNormalScheme.of_pred hS
  let Z : S.Opens := GlobalTheory.IsNormalScheme.component ⟨_, irreducibleComponent_mem_irreducibleComponents s⟩
  obtain ⟨U, hU, hs, hle⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := Z) (x := s) mem_irreducibleComponent
  have : IrreducibleSpace U.toScheme := Subtype.irreducibleSpace
    ⟨⟨s, hs⟩, isIrreducible_irreducibleComponent.2.open_subset U.isOpen hle⟩
  have : IsIntegral U.toScheme := GlobalTheory.IsNormalScheme.isIntegral_of_irreducibleSpace _
  have : IsIntegral (Spec Γ(S, U)) := IsIntegral.of_isIso hU.isoSpec.hom
  have : IsDomain Γ(S, U) := (affine_isIntegral_iff _).1 this
  have : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : IsIntegrallyClosed Γ(S, U) := GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen hU
  let i : Sp Γ(S, U) ⟶ S := hU.fromSpec
  have : IsOpenImmersion i := inferInstanceAs (IsOpenImmersion hU.fromSpec)
  refine ⟨i.opensRange, ?_, hasExt_opensRange X S hS j A hA L hL hamp hC Γ(S, U) i⟩
  exact hU.range_fromSpec.ge hs

end GlobalTheory.Desc
