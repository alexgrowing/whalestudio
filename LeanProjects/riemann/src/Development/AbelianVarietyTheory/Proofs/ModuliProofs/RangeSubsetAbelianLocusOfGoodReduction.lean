import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GroupSchemeMorphismDescends
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsMonHomIffOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGrpSchemeDescendsToFgSubring
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomDescendsToFgIntermediateField

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.GoodVal

theorem exists_finset_factor {X : Scheme.{0}} (z : X ⟶ Sp ℤ) [LocallyOfFiniteType z] {V : Type} [CommRing V]
    [IsLocalRing V] (y : Sp V ⟶ X) :
    ∃ F : Finset V, ∀ R : Subring V, (F : Set V) ⊆ R → ∃ y₀ : Sp R ⟶ X, spMap R.subtype ≫ y₀ = y := by
  classical
  let i := X.affineOpenCover.idx (y (IsLocalRing.closedPoint V))
  let j := X.affineOpenCover.f i
  have hr : Set.range y ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    have h₁ : y x ⤳ y (IsLocalRing.closedPoint V) := (IsLocalRing.specializes_closedPoint x).map y.continuous
    exact h₁.mem_open j.isOpenEmbedding.isOpen_range (X.affineOpenCover.covers _)
  let a := Spec.preimage (IsOpenImmersion.lift j y hr)
  have ha : Spec.map a ≫ j = y := by rw [Spec.map_preimage, IsOpenImmersion.lift_fac]
  have hft : (Spec.preimage (j ≫ z)).hom.FiniteType := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), Spec.map_preimage]
    infer_instance
  have hft' : Algebra.FiniteType ℤ (X.affineOpenCover.X i) := by
    rw [← RingHom.finiteType_algebraMap]
    convert hft using 1
    exact RingHom.ext_int _ _
  obtain ⟨s, hs⟩ := hft'.out
  refine ⟨s.image a.hom, fun R hR => ?_⟩
  have hmem : ∀ x, a.hom x ∈ R := fun x => by
    have hx : x ∈ Algebra.adjoin ℤ (s : Set (X.affineOpenCover.X i)) := hs ▸ Algebra.mem_top
    have hle : Algebra.adjoin ℤ (s : Set (X.affineOpenCover.X i)) ≤ subalgebraOfSubring (R.comap a.hom) :=
      Algebra.adjoin_le fun t ht => hR (by simpa using ⟨t, ht, rfl⟩)
    exact hle hx
  refine ⟨Spec.map (CommRingCat.ofHom (a.hom.codRestrict R hmem)) ≫ j, ?_⟩
  rw [← ha, ← Category.assoc, ← Spec.map_comp]
  rfl

theorem exists_dvr_centre {R K L : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [Field L] [Algebra K L] [Algebra.EssFiniteType K L] (p : Ideal R) [p.IsPrime]
    (hp : p ≠ ⊥) : ∃ (T : ValuationSubring L) (_ : IsDiscreteValuationRing T) (g : R →+* T),
      (algebraMap T L).comp g = (algebraMap K L).comp (algebraMap R K) ∧
        (IsLocalRing.maximalIdeal T).comap g = p := by
  let S := Localization.subalgebra.ofField K p.primeCompl p.primeCompl_le_nonZeroDivisors
  have : IsLocalization.AtPrime S p := inferInstance
  have : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S p
  have : IsNoetherianRing S := IsLocalization.isNoetherianRing p.primeCompl S ‹_›
  have : IsFractionRing S K := inferInstance
  have : Algebra.EssFiniteType S K := Algebra.EssFiniteType.of_isLocalization K (nonZeroDivisors S)
  have : Algebra.EssFiniteType S L := Algebra.EssFiniteType.comp S K L
  have : FaithfulSMul S L := (faithfulSMul_iff_algebraMap_injective S L).2
    ((algebraMap K L).injective.comp Subtype.val_injective)
  have hS : ¬ IsField S := IsLocalization.AtPrime.not_isField R hp S
  obtain ⟨T, hT, h⟩ := exists_discreteValuationSubring_dominating_of_essFiniteType (L := L) hS
  obtain ⟨h₁, h₂⟩ := (localSubring_range_le_valuationSubring_iff_isLocalHom _ _).1 h
  refine ⟨T, hT, ((algebraMap S L).codRestrict T h₁).comp (algebraMap R S), rfl, ?_⟩
  rw [← Ideal.comap_comap, IsLocalRing.maximalIdeal_comap]
  exact IsLocalization.AtPrime.under_maximalIdeal S p

theorem fibre_of_range_subset {S S' A₀ A : Scheme.{0}} {g : A₀ ⟶ S} {f : A ⟶ S'} {φ : A ⟶ A₀} {s : S' ⟶ S}
    (h : IsPullback φ f g s) [IsProper f] [GeometricallyConnected f] {Ω : Type} [Field Ω] (p : Sp Ω ⟶ S)
    (hp : Set.range p ⊆ Set.range s) :
    IsProper (pullback.snd g p) ∧ GeometricallyConnected (pullback.snd g p) := by
  have : Subsingleton (Sp Ω) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  have x : Sp Ω := (default : PrimeSpectrum Ω)
  obtain ⟨x', hx'⟩ := hp ⟨x, rfl⟩
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := s) x x' hx'.symm
  let j := (pullback p s).fromSpecResidueField z
  let u := j ≫ pullback.fst p s
  let u' := j ≫ pullback.snd p s
  have e : u' ≫ s = u ≫ p := by simp only [u, u', Category.assoc, pullback.condition]
  have P := (IsPullback.of_hasPullback f u').paste_horiz h
  rw [e] at P
  have Q := IsPullback.of_hasPullback g p
  have P' := IsPullback.of_right (by rw [Q.lift_fst]; exact P) (Q.lift_snd _ _ (by simpa using P.w)) Q
  have : Surjective u := inferInstance
  have : Flat u := inferInstance
  exact ⟨GrpFlatDesc.isProper_of_isPullback P', GrpFlatDesc.geometricallyConnected_of_isPullback P'⟩

theorem isSemiAbelian_of_fibres {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B] [Smooth B.hom]
    [IsSeparated B.hom] [QuasiCompact B.hom]
    (h : ∀ (Ω : Type) [Field Ω] (p : Sp Ω ⟶ S),
      IsProper (pullback.snd B.hom p) ∧ GeometricallyConnected (pullback.snd B.hom p)) : IsSemiAbelian B := by
  refine ⟨‹_›, ‹_›, ‹_›, ‹_›, ⟨fun L _ y W a b hW => ?_⟩, fun Ω _ _ p => ⟨torusExtensionOfAbelian _
    ⟨inferInstance, inferInstanceAs (Smooth (pullback.snd B.hom p)), (h Ω p).1, (h Ω p).2⟩⟩⟩
  exact (h L y).2.geometrically_connectedSpace (K := L) (𝟙 _) hW.isoPullback.hom b
    (IsPullback.of_horiz_isIso ⟨by simp⟩)

theorem exists_fg_isGrpPullback {K C : Type} [Field K] [Field C] [Algebra K C] (A₁ B₁ : Over (Sp K)) [GrpObj A₁]
    [GrpObj B₁] [LocallyOfFiniteType A₁.hom] [QuasiCompact A₁.hom] [IsSeparated A₁.hom] [LocallyOfFiniteType B₁.hom]
    {A : Over (Sp C)} [GrpObj A] {φ : A.left ⟶ A₁.left} {ψ : A.left ⟶ B₁.left}
    (hφ : IsGrpPullback A A₁ (spMap (algebraMap K C)) φ) (hψ : IsGrpPullback A B₁ (spMap (algebraMap K C)) ψ) :
    ∃ (L : IntermediateField K C) (e : (Over.pullback (spMap (algebraMap K L))).obj A₁ ≅
      (Over.pullback (spMap (algebraMap K L))).obj B₁), L.FG ∧ IsMonHom e.hom := by
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso (isGrpPullback_pullback A₁ (spMap (algebraMap K C))) hφ
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso hψ (isGrpPullback_pullback B₁ (spMap (algebraMap K C)))
  obtain ⟨L, f₀, hL, hf₀, hf⟩ := GlobalTheory.hom_descends_to_fg_intermediateField K C A₁ B₁ (a ≪≫ b).hom ‹_› ‹_› ‹_› ‹_›
  have hc : spMap (algebraMap L C) ≫ spMap (algebraMap K L) = spMap (algebraMap K C) := by
    rw [← Spec.map_comp]; rfl
  have := FieldBaseChange.flat_spMap (algebraMap L C)
  have := FieldBaseChange.surjective_spMap (algebraMap L C)
  have key : ∀ (D : Over (Sp K)) [GrpObj D], ∃ i : pullback D.hom (spMap (algebraMap K C)) ⟶
      pullback D.hom (spMap (algebraMap K L)), i ≫ pullback.fst _ _ = pullback.fst _ _ ∧
      i ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (algebraMap L C) ∧
      IsGrpPullback ((Over.pullback (spMap (algebraMap K C))).obj D) ((Over.pullback (spMap (algebraMap K L))).obj D)
        (spMap (algebraMap L C)) i := fun D _ => by
    have w : pullback.fst D.hom (spMap (algebraMap K C)) ≫ D.hom =
        (pullback.snd _ _ ≫ spMap (algebraMap L C)) ≫ spMap (algebraMap K L) := by
      rw [Category.assoc, hc, pullback.condition]
    exact ⟨pullback.lift _ _ w, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _,
      (isGrpPullback_pullback D _).cancel ((isGrpPullback_pullback D _).congr hc.symm (pullback.lift_fst _ _ w).symm)
        (pullback.lift_snd _ _ _)⟩
  obtain ⟨i, hi₁, hi₂, hi⟩ := key A₁
  obtain ⟨k, hk₁, hk₂, hk⟩ := key B₁
  let g : (Over.pullback (spMap (algebraMap K L))).obj A₁ ⟶ (Over.pullback (spMap (algebraMap K L))).obj B₁ :=
    Over.homMk (pullback.lift f₀ (pullback.snd _ _) (hf₀.trans pullback.condition)) (pullback.lift_snd _ _ _)
  have hg₁ : g.left ≫ pullback.fst B₁.hom (spMap (algebraMap K L)) = f₀ := pullback.lift_fst _ _ _
  have hg : i ≫ g.left = (a ≪≫ b).hom.left ≫ k := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (i ≫ ·) hg₁).trans ((hf i hi₁ hi₂).trans
        ((congrArg ((a ≪≫ b).hom.left ≫ ·) hk₁.symm).trans (Category.assoc _ _ _).symm)))
    · refine (Category.assoc _ _ _).trans ((congrArg (i ≫ ·) (Over.w g)).trans (hi₂.trans ?_))
      refine Eq.symm ((Category.assoc _ _ _).trans ((congrArg ((a ≪≫ b).hom.left ≫ ·) hk₂).trans ?_))
      exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ spMap (algebraMap L C)) (Over.w (a ≪≫ b).hom))
  have hm : IsMonHom g := (FieldBaseChange.isMonHom_iff_of_isGrpPullback hi hk (a ≪≫ b).hom g hg).1
    (inferInstanceAs (IsMonHom (a.hom ≫ b.hom)))
  have hsq : IsPullback (a ≪≫ b).hom.left i k g.left :=
    IsPullback.of_bot (by rw [Over.w g, Over.w (a ≪≫ b).hom]; exact hi.1) hg hk.1 |>.flip
  have : Flat k := MorphismProperty.of_isPullback (P := @Flat) hk.1.flip ‹_›
  have : Surjective k := MorphismProperty.of_isPullback (P := @Surjective) hk.1.flip ‹_›
  have : QuasiCompact k := MorphismProperty.of_isPullback (P := @QuasiCompact) hk.1.flip inferInstance
  have hq : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) k := ⟨⟨‹_›, ‹_›⟩, ‹_›⟩
  have : IsIso g.left := MorphismProperty.of_isPullback_of_descendsAlong (P := .isomorphisms Scheme.{0}) hsq hq
    (inferInstanceAs (IsIso ((Over.forget _).map (a ≪≫ b).hom)))
  have : IsIso ((Over.forget _).map g) := ‹_›
  have : IsIso g := isIso_of_reflects_iso g (Over.forget _)
  exact ⟨L, asIso g, hL, hm⟩

theorem isSemiAbelian_pullback_of_range_subset {S S' T : Scheme.{0}} (A₀ : Over S) [GrpObj A₀] [IsCommMonObj A₀]
    [Smooth A₀.hom] [IsSeparated A₀.hom] [QuasiCompact A₀.hom] {A : Scheme.{0}} {f : A ⟶ S'} {φ : A ⟶ A₀.left}
    {s : S' ⟶ S} (h : IsPullback φ f A₀.hom s) [IsProper f] [GeometricallyConnected f] (g : T ⟶ S)
    (hg : Set.range g ⊆ Set.range s) :
    IsSemiAbelian ((Over.pullback g).obj A₀) ∧ ∀ x, x ∈ abLocus ((Over.pullback g).obj A₀) := by
  let B := (Over.pullback g).obj A₀
  have hfib : ∀ (Ω : Type) [Field Ω] (t : Sp Ω ⟶ T),
      IsProper (pullback.snd B.hom t) ∧ GeometricallyConnected (pullback.snd B.hom t) := fun Ω _ t => by
    obtain ⟨h₁, h₂⟩ := fibre_of_range_subset h (t ≫ g) (by
      rintro _ ⟨x, rfl⟩; exact hg ⟨t x, rfl⟩)
    have hp := (IsPullback.of_hasPullback B.hom t).paste_horiz (isGrpPullback_pullback A₀ g).1
    have hq : IsPullback hp.isoPullback.hom (pullback.snd B.hom t) (pullback.snd A₀.hom (t ≫ g)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [hp.isoPullback_hom_snd, Category.comp_id]⟩
    exact ⟨MorphismProperty.of_isPullback (P := @IsProper) hq h₁,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) hq h₂⟩
  have : Smooth B.hom := inferInstanceAs (Smooth (pullback.snd _ _))
  have : IsSeparated B.hom := inferInstanceAs (IsSeparated (pullback.snd _ _))
  have : QuasiCompact B.hom := inferInstanceAs (QuasiCompact (pullback.snd _ _))
  exact ⟨isSemiAbelian_of_fibres B hfib, fun _ Ω _ _ t _ => (hfib Ω t).1⟩

theorem exists_isGrpPullback_of_comp {S U W : Scheme.{0}} (D : Over S) [GrpObj D] {B : Over W} [GrpObj B] (t : U ⟶ S)
    (u : W ⟶ U) {ψ : B.left ⟶ D.left} (h : IsGrpPullback B D (u ≫ t) ψ) :
    ∃ ψ', IsGrpPullback B ((Over.pullback t).obj D) u ψ' := by
  have w : ψ ≫ D.hom = (B.hom ≫ u) ≫ t := by rw [h.1.w, Category.assoc]
  exact ⟨pullback.lift _ _ w, (isGrpPullback_pullback D t).cancel (h.congr rfl (pullback.lift_fst _ _ w).symm)
    (pullback.lift_snd _ _ _)⟩

theorem exists_iso_of_comp_eq {S U T W : Scheme.{0}} (D : Over S) [GrpObj D] {k : U ⟶ S} {l : W ⟶ U} {g : T ⟶ S}
    {j : W ⟶ T} (h : l ≫ k = j ≫ g) : ∃ e : (Over.pullback j).obj ((Over.pullback g).obj D) ≅
      (Over.pullback l).obj ((Over.pullback k).obj D), IsMonHom e.hom := by
  obtain ⟨a, ha, -⟩ := grpPullback_iso ((isGrpPullback_pullback _ j).comp (isGrpPullback_pullback D g))
    (((isGrpPullback_pullback _ l).comp (isGrpPullback_pullback D k)).congr h rfl)
  exact ⟨a, ha⟩

theorem range_subset_of_centre {V T : Type} [CommRing V] [IsDomain V] [CommRing T] [IsDomain T]
    [IsDiscreteValuationRing T] (R : Subring V) {g : R →+* T} (hg : Function.Injective g) (P : Sp V)
    (hcl : spMap g (IsLocalRing.closedPoint T) = spMap R.subtype P) :
    Set.range (spMap g) ⊆ Set.range (spMap R.subtype) := by
  rintro _ ⟨q, rfl⟩
  by_cases hq : PrimeSpectrum.asIdeal q = ⊥
  · refine ⟨(⊥ : PrimeSpectrum V), PrimeSpectrum.ext ?_⟩
    exact (Ideal.comap_bot_of_injective R.subtype Subtype.val_injective).trans
      ((congrArg (Ideal.comap g) hq).trans (Ideal.comap_bot_of_injective _ hg)).symm
  · have hq' : q = IsLocalRing.closedPoint T :=
      PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime hq q.isPrime))
    exact ⟨P, by rw [hq', hcl]⟩

theorem abLocus_subset_of_extends {T L : Type} [CommRing T] [Field L] [Algebra T L] [IsFractionRing T L]
    {B H : Over (Sp T)} [GrpObj B] [GrpObj H] (hB : IsSemiAbelian B) (hH : IsSemiAbelian H)
    (E : (Over.pullback (spMap (algebraMap T L))).obj B ≅ (Over.pullback (spMap (algebraMap T L))).obj H)
    (Φ : B ⟶ H) (Ψ : H ⟶ B) (hΦ : (Over.pullback (spMap (algebraMap T L))).map Φ = E.hom)
    (hΨ : (Over.pullback (spMap (algebraMap T L))).map Ψ = E.inv) : abLocus B ⊆ abLocus H := by
  obtain ⟨_, _⟩ := ExtUnique.flat_and_isSeparated_of_isSemiAbelian B hB
  obtain ⟨_, _⟩ := ExtUnique.flat_and_isSeparated_of_isSemiAbelian H hH
  obtain ⟨_, _⟩ := ExtUnique.spec_fractionRing T L
  have : IsIso Φ := ExtUnique.isIso_of_pullback (spMap (algebraMap T L)) E Φ Ψ hΦ hΨ
  have : IsIso Φ.left := inferInstanceAs (IsIso ((Over.forget _).map Φ))
  have hsq : IsPullback Φ.left B.hom H.hom (𝟙 _) := IsPullback.of_horiz_isIso ⟨by rw [Over.w, Category.comp_id]⟩
  exact fun x hx => (abLocus_pullback abLocusOne hH hsq x).2 hx

end GlobalTheory.GoodVal

namespace GlobalTheory

open GoodVal

set_option maxHeartbeats 800000 in

theorem range_subset_abLocus_of_goodReduction : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (X : Scheme.{0}) (z : X ⟶ Sp ℤ) (G : Over X) [GrpObj G] (V C : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [Algebra V C] [IsFractionRing V C] (y : Sp V ⟶ X) (𝒜 : Over (Sp V)) [GrpObj 𝒜] (A : Over (Sp C)) [GrpObj A] (φ₁ : A.left ⟶ 𝒜.left) (φ₂ : A.left ⟶ G.left), LocallyOfFiniteType z → IsSemiAbelian G → IsAbelianScheme 𝒜 → IsGrpPullback A 𝒜 (spMap (algebraMap V C)) φ₁ → IsGrpPullback A G (spMap (algebraMap V C) ≫ y) φ₂ → Set.range y ⊆ abLocus G := by
  intro hext X z G _ V C _ _ _ _ _ _ y 𝒜 _ A _ φ₁ φ₂ hz hG h𝒜 h₁ h₂
  obtain ⟨F, hF⟩ := exists_finset_factor z y
  have := h𝒜.comm
  have := h𝒜.proper
  have := h𝒜.geomConnected
  obtain ⟨R, A₀, _, _, φ, hFR, hR, _, _, _, hφ⟩ := GlobalTheory.smooth_grpScheme_descends_to_fg_subring V 𝒜 F h𝒜.smooth inferInstance inferInstance
  obtain ⟨y₀, rfl⟩ := hF R hFR
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  rintro _ ⟨P, rfl⟩
  let p : Ideal R := P.asIdeal.comap R.subtype
  have : p.IsPrime := Ideal.comap_isPrime _ _ (H := P.isPrime)
  have hinj : Function.Injective ((algebraMap V C).comp R.subtype) :=
    (IsFractionRing.injective V C).comp Subtype.val_injective
  by_cases hp : p = ⊥
  · have hpr : IsProper A.hom := MorphismProperty.of_isPullback (P := @IsProper) h₁.1 h𝒜.proper
    refine abLocusOne X G hG C _ (by rw [← h₂.1.isoPullback_inv_snd]; infer_instance) ⟨(⊥ : PrimeSpectrum C), ?_⟩
    change y₀ (spMap R.subtype (spMap (algebraMap V C) (⊥ : PrimeSpectrum C))) = y₀ (spMap R.subtype P)
    refine congrArg y₀ ?_
    exact PrimeSpectrum.ext ((Ideal.comap_comap _ _).trans ((Ideal.comap_bot_of_injective _ hinj).trans hp.symm))
  let K := FractionRing R
  letI : Algebra K C := (IsFractionRing.lift hinj).toAlgebra
  have hc : spMap (algebraMap K C) ≫ spMap (algebraMap R K) = spMap (algebraMap V C) ≫ spMap R.subtype := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext r
    exact IsFractionRing.lift_algebraMap hinj r
  obtain ⟨ψ₁, k₁⟩ := exists_isGrpPullback_of_comp A₀ (spMap (algebraMap R K)) _ ((h₁.comp hφ).congr hc.symm rfl)
  obtain ⟨ψ₂, k₂⟩ := exists_isGrpPullback_of_comp G (spMap (algebraMap R K) ≫ y₀) (spMap (algebraMap K C))
    (h₂.congr (by rw [← Category.assoc, ← hc, Category.assoc]) rfl)
  have := hG.smooth
  have : LocallyOfFiniteType ((Over.pullback (spMap (algebraMap R K))).obj A₀).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
  have : QuasiCompact ((Over.pullback (spMap (algebraMap R K))).obj A₀).hom :=
    inferInstanceAs (QuasiCompact (pullback.snd _ _))
  have : IsSeparated ((Over.pullback (spMap (algebraMap R K))).obj A₀).hom :=
    inferInstanceAs (IsSeparated (pullback.snd _ _))
  have : LocallyOfFiniteType ((Over.pullback (spMap (algebraMap R K) ≫ y₀)).obj G).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
  obtain ⟨L, e, hL, he⟩ := exists_fg_isGrpPullback _ _ k₁ k₂
  have : Algebra.EssFiniteType K L := IntermediateField.essFiniteType_iff.2 hL
  obtain ⟨T, _, g, hg, hgp⟩ := exists_dvr_centre (K := K) (L := L) p hp
  have hc' : spMap (algebraMap T L) ≫ spMap g = spMap (algebraMap K L) ≫ spMap (algebraMap R K) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hg
  have hginj : Function.Injective g := by
    refine Function.Injective.of_comp (f := algebraMap T L) ?_
    rw [← RingHom.coe_comp, hg]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  have hcl : spMap g (IsLocalRing.closedPoint T) = spMap R.subtype P := PrimeSpectrum.ext hgp
  obtain ⟨hB, hB'⟩ := isSemiAbelian_pullback_of_range_subset A₀ hφ.1 (spMap g) (range_subset_of_centre R hginj P hcl)
  have hH := IsSemiAbelian.pullback (spMap g ≫ y₀) G hG
  obtain ⟨a, ha⟩ := exists_iso_of_comp_eq A₀ hc'.symm
  obtain ⟨b, hb⟩ := exists_iso_of_comp_eq G (k := spMap g ≫ y₀) (l := spMap (algebraMap T L))
    (g := spMap (algebraMap R K) ≫ y₀) (j := spMap (algebraMap K L)) (by rw [← Category.assoc, hc', Category.assoc])
  have hE : IsMonHom (a ≪≫ e ≪≫ b).hom := inferInstanceAs (IsMonHom (a.hom ≫ e.hom ≫ b.hom))
  obtain ⟨Φ, ⟨-, hΦ⟩, -⟩ := hext T L _ _ hB hH (a ≪≫ e ≪≫ b).hom hE
  obtain ⟨Ψ, ⟨-, hΨ⟩, -⟩ := hext T L _ _ hH hB (a ≪≫ e ≪≫ b).inv inferInstance
  have hx := (abLocus_pullback abLocusOne hG (isGrpPullback_pullback G (spMap g ≫ y₀)).1
    (IsLocalRing.closedPoint T)).2 (abLocus_subset_of_extends hB hH _ Φ Ψ hΦ hΨ (hB' _))
  change y₀ (spMap g (IsLocalRing.closedPoint T)) ∈ abLocus G at hx
  rw [hcl] at hx
  exact hx

end GlobalTheory
