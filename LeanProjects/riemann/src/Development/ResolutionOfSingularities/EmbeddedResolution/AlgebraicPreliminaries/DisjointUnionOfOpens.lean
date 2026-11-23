import Mathlib
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

universe u

noncomputable abbrev sigmaOpens (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens) : Scheme.{u} :=
  ∐ fun i => (U i).toScheme

noncomputable abbrev sigmaOpensDesc (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens) :
    sigmaOpens Y U ⟶ Y :=
  Sigma.desc fun i => (U i).ι

theorem sigma_ι_sigmaOpensDesc (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens) (i : ι) :
    Sigma.ι (fun i => (U i).toScheme) i ≫ sigmaOpensDesc Y U = (U i).ι := by
  simp

theorem sigma_ι_sigmaOpensDesc_assoc (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens) (i : ι)
    {Z : Scheme.{u}} (h : Y ⟶ Z) :
    Sigma.ι (fun i => (U i).toScheme) i ≫ sigmaOpensDesc Y U ≫ h = (U i).ι ≫ h := by
  simp

theorem isAffine_sigmaOpens (Y : Scheme.{u}) {ι : Type u} [Finite ι] (U : ι → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) : IsAffine (sigmaOpens Y U) := by
  have : ∀ i, IsAffine (U i).toScheme := fun i => hU i
  exact inferInstanceAs (IsAffine (∐ fun i => (U i).toScheme))

private theorem isReduced_of_ringEquiv
    {A B : Type u} [CommRing A] [CommRing B] [_root_.IsReduced B] (e : A ≃+* B) :
    _root_.IsReduced A :=
  ⟨fun _ hx => e.injective (((hx.map e).eq_zero).trans (map_zero e).symm)⟩

private theorem isReduced_of_forall_isReduced_stalk (X : Scheme.{u})
    (h : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x)) : IsReduced X := by
  have := h
  exact isReduced_of_isReduced_stalk X

theorem isReduced_sigmaOpens (Y : Scheme.{u}) [IsReduced Y] {ι : Type u} (U : ι → Y.Opens) :
    IsReduced (sigmaOpens Y U) := by
  refine isReduced_of_forall_isReduced_stalk _ ?_
  intro x
  obtain ⟨⟨i, y⟩, hx⟩ := (sigmaMk fun i => (U i).toScheme).surjective x
  have hx' : (Sigma.ι (fun i => (U i).toScheme) i).base y = x := by simpa using hx
  subst hx'
  exact isReduced_of_ringEquiv
    (((asIso ((Sigma.ι (fun i => (U i).toScheme) i).stalkMap y)).commRingCatIsoToRingEquiv).trans
      ((asIso (((U i).ι).stalkMap y)).commRingCatIsoToRingEquiv.symm))

instance instIsReducedOpensCoprod (Y : Scheme.{u}) [IsReduced Y] {ι : Type u} (U : ι → Y.Opens) :
    IsReduced (sigmaOpens Y U) :=
  isReduced_sigmaOpens Y U

theorem etale_isZariskiLocalAtSource : IsZariskiLocalAtSource (@Etale.{u}) := by
  have hrh : HasRingHomProperty (@Etale.{u}) RingHom.Etale := inferInstance
  exact @HasRingHomProperty.instIsZariskiLocalAtSource (@Etale.{u}) _ hrh

theorem etale_sigmaDesc {ι : Type u} {X : ι → Scheme.{u}} {Z : Scheme.{u}}
    (f : ∀ i, X i ⟶ Z) (hf : ∀ i, Etale (f i)) : Etale (Sigma.desc f) := by
  have hloc : IsZariskiLocalAtSource (@Etale.{u}) := etale_isZariskiLocalAtSource
  exact IsZariskiLocalAtSource.sigmaDesc hf

theorem etale_sigmaOpensDesc (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens) :
    Etale (sigmaOpensDesc Y U) := by
  have hloc : IsZariskiLocalAtSource (@Etale.{u}) := etale_isZariskiLocalAtSource
  exact IsZariskiLocalAtSource.sigmaDesc fun i => inferInstance

instance instEtaleOpensCoprodDesc (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens) :
    Etale (sigmaOpensDesc Y U) :=
  etale_sigmaOpensDesc Y U

theorem locallyOfFiniteType_sigmaOpensDesc (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens) :
    LocallyOfFiniteType (sigmaOpensDesc Y U) := by
  have : Etale (sigmaOpensDesc Y U) := etale_sigmaOpensDesc Y U
  infer_instance

instance instLocallyOfFiniteTypeOpensCoprodDesc (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens) :
    LocallyOfFiniteType (sigmaOpensDesc Y U) :=
  locallyOfFiniteType_sigmaOpensDesc Y U

theorem surjective_sigmaOpensDesc (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens)
    (hU : iSup U = ⊤) : Surjective (sigmaOpensDesc Y U) := by
  constructor
  intro y
  have hy : y ∈ iSup U := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  refine ⟨(Sigma.ι (fun i => (U i).toScheme) i).base (⟨y, hi⟩ : ↥((U i).toScheme)), ?_⟩
  exact congrArg (fun f : (U i).toScheme ⟶ Y => f.base (⟨y, hi⟩ : ↥((U i).toScheme)))
    (sigma_ι_sigmaOpensDesc Y U i)

private theorem exists_isAffineOpen_mem (Y : Scheme.{u}) (x : Y) :
    ∃ U : Y.Opens, IsAffineOpen U ∧ x ∈ U := by
  refine ⟨(Y.affineOpenCover.3 (Y.affineOpenCover.4 x)).opensRange,
    isAffineOpen_opensRange _, ?_⟩
  exact Y.affineOpenCover.5 x

theorem exists_finite_affine_cover (Y : Scheme.{u}) [CompactSpace Y] :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → Y.Opens),
      (∀ i, IsAffineOpen (U i)) ∧ iSup U = ⊤ := by
  classical
  choose V hV hxV using exists_isAffineOpen_mem Y
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : Y => (V x : Set Y))
    (fun x => (V x).isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x, hxV x⟩)
  refine ⟨{ x : Y // x ∈ t }, inferInstance, fun i => V i.1, fun i => hV i.1, ?_⟩
  refine TopologicalSpace.Opens.ext ?_
  rw [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top]
  refine Set.eq_univ_of_univ_subset fun x _ => ?_
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hxy⟩

private theorem subsingleton_spec_of_field (k : Type u) [Field k] :
    Subsingleton ↥(Spec (CommRingCat.of k)) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum k))

theorem exists_affine_etale_cover_of_isReduced {k : Type u} [Field k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] [QuasiCompact p] [IsReduced Y] :
    ∃ (W : Scheme.{u}) (q : W ⟶ Spec (CommRingCat.of k)) (g : W ⟶ Y),
      IsAffine W ∧ IsReduced W ∧ LocallyOfFiniteType q ∧ QuasiCompact q ∧
        Etale g ∧ Surjective g ∧ g ≫ p = q := by
  have hsub : Subsingleton ↥(Spec (CommRingCat.of k)) := subsingleton_spec_of_field k
  have hcs : CompactSpace ↥(Spec (CommRingCat.of k)) := inferInstance
  have hcY : CompactSpace ↥Y := by
    constructor
    have h := (‹QuasiCompact p›).isCompact_preimage Set.univ isOpen_univ isCompact_univ
    rwa [Set.preimage_univ] at h
  obtain ⟨ι, hι, U, hUaff, hUsup⟩ := exists_finite_affine_cover Y
  have : Finite ι := hι
  have hW : IsAffine (sigmaOpens Y U) := isAffine_sigmaOpens Y U hUaff
  have : CompactSpace ↥(sigmaOpens Y U) := inferInstance
  refine ⟨sigmaOpens Y U, sigmaOpensDesc Y U ≫ p, sigmaOpensDesc Y U, hW,
    isReduced_sigmaOpens Y U, ?_, ?_, etale_sigmaOpensDesc Y U,
    surjective_sigmaOpensDesc Y U hUsup, rfl⟩
  · infer_instance
  · exact quasiCompact_of_compactSpace_of_subsingleton _

theorem smooth_isZariskiLocalAtSource : IsZariskiLocalAtSource (@Smooth.{u}) := by
  have hrh : HasRingHomProperty (@Smooth.{u}) RingHom.Smooth := inferInstance
  exact @HasRingHomProperty.instIsZariskiLocalAtSource (@Smooth.{u}) _ hrh

instance instIsZariskiLocalAtSourceSmooth : IsZariskiLocalAtSource (@Smooth.{u}) :=
  smooth_isZariskiLocalAtSource

theorem smooth_sigmaDesc {ι : Type u} {X : ι → Scheme.{u}} {Z : Scheme.{u}}
    (f : ∀ i, X i ⟶ Z) (hf : ∀ i, Smooth (f i)) : Smooth (Sigma.desc f) :=
  IsZariskiLocalAtSource.sigmaDesc hf

end FunctorialResolution.EmbeddedResolution
