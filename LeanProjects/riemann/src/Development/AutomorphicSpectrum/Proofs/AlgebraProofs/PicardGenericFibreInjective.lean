import Mathlib
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearIsIsoOfIsProperOfFinitePresentation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfFibres
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeneratorExtendsFromGenericFibreValuationRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulSecNonzeroOnSpecialFibre
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelExtensionOverDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymTranslate
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.StrictModelTranslatesTwistCompatible
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RigidifiedSymDescendToSubring

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.CompanionTheory.ValFibre

theorem isUnit_of_basicOpen_eq_top' {Y : Scheme.{0}} (a : Γ(Y, ⊤)) (h : Y.basicOpen a = ⊤) :
    IsUnit a := by
  have key : ∀ (g : Opposite.op (⊤ : Y.Opens) ⟶ Opposite.op (Y.basicOpen a))
      (g' : Opposite.op (Y.basicOpen a) ⟶ Opposite.op ⊤),
      (Y.presheaf.map g').hom ((Y.presheaf.map g).hom a) = a := by
    intro g g'
    rw [← CommRingCat.comp_apply, ← Functor.map_comp, Subsingleton.elim (g ≫ g') (𝟙 _),
      CategoryTheory.Functor.map_id, CommRingCat.id_apply]
  have u := (Y.toRingedSpace.isUnit_res_basicOpen a).map
    (Y.presheaf.map (homOfLE (le_of_eq h.symm)).op).hom
  convert u using 1
  exact (key _ _).symm

theorem point_cases (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Ring.DimensionLEOne R]
    (r : Sp R) : r.asIdeal = ⊥ ∨ r = IsLocalRing.closedPoint R := by
  by_cases h : r.asIdeal = ⊥
  · exact .inl h
  · refine .inr (PrimeSpectrum.ext ?_)
    have := Ring.DimensionLEOne.maximalOfPrime h r.isPrime
    exact IsLocalRing.eq_maximalIdeal this

theorem exists_factor (R C : Type) [CommRing R] [IsDomain R] [Field C] [Algebra R C] [IsFractionRing R C]
    {Y : Scheme.{0}} (f : Y ⟶ Sp R) (hf : ∀ y : Y, (f y).asIdeal = ⊥) :
    ∃ g : Y ⟶ Sp C, g ≫ spMap (algebraMap R C) = f := by
  let ψ : R →+* Γ(Y, ⊤) := (f.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  have hu : ∀ r : nonZeroDivisors R, IsUnit (ψ r) := by
    intro r
    refine isUnit_of_basicOpen_eq_top' _ (top_unique fun y _ => ?_)
    show y ∈ Y.basicOpen (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r.1))
    rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
    show r.1 ∉ (f y).asIdeal
    rw [hf y]
    exact nonZeroDivisors.ne_zero r.2
  let φ : C →+* Γ(Y, ⊤) := IsLocalization.lift (M := nonZeroDivisors R) hu
  have hφ : φ.comp (algebraMap R C) = ψ := IsLocalization.lift_comp hu
  refine ⟨Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ), ?_⟩
  have e : (Sp R).toSpecΓ = Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    rw [← Scheme.isoSpec_hom, Scheme.isoSpec_Spec_hom]
  have h1 : CommRingCat.ofHom (algebraMap R C) ≫ CommRingCat.ofHom φ =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop := by
    rw [← CommRingCat.ofHom_comp, hφ]
    rfl
  rw [Category.assoc, spMap, ← Spec.map_comp, h1, Spec.map_comp, ← Category.assoc,
    ← Scheme.toSpecΓ_naturality, Category.assoc, e, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.comp_id]

theorem geometricallyIntegral_open {X S : Scheme.{0}} (p : X ⟶ S) [GeometricallyIntegral p] (Y : X.Opens)
    (hY : ∀ s : S, ∃ y : X, y ∈ Y ∧ p y = s) : GeometricallyIntegral (Y.ι ≫ p) := by
  refine ⟨fun K _ y Z fst snd h => ?_⟩
  let g : Z ⟶ pullback p y := pullback.lift (fst ≫ Y.ι) snd (by simpa using h.w)
  have hg : IsPullback fst g Y.ι (pullback.fst p y) :=
    IsPullback.of_bot (by simpa [g] using h) (by simp [g]) (IsPullback.of_hasPullback p y)
  have : IsOpenImmersion g := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hg inferInstance
  have : IsIntegral (pullback p y) :=
    GeometricallyIntegral.geometrically_isIntegral y _ _ (IsPullback.of_hasPullback p y)
  have : Nonempty Z := by
    obtain ⟨x, hx, hxs⟩ := hY (y (IsLocalRing.closedPoint K))
    obtain ⟨z, hz, hz'⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := Y.ι ≫ p) (g := y) (⟨x, hx⟩ : Y) (IsLocalRing.closedPoint K) (by simpa using hxs)
    exact ⟨h.isoPullback.inv z⟩
  exact isIntegral_of_isOpenImmersion g

theorem eq_zero_of_pull_generic_eq_zero : ∀ (C : Type) [Field C] [IsAlgClosed C] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Ring.DimensionLEOne R]
    [Algebra R C] [IsFractionRing R C] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ Y : A.left.Opens, IsCompact (Y : Set A.left) →
    ∀ q : Pic Y.toScheme, pull (pullback.fst A.hom (spMap (algebraMap R C)) ∣_ Y) q = 0 → q = 0 := by
  intro C _ _ R _ _ _ _ _ _ A _ hA Y hY q hq
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have hGI : GeometricallyIntegral A.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hA.smooth hA.geomConnected
  have hsq : IsPullback (pullback.fst A.hom (spMap (algebraMap R C)) ∣_ Y)
      ((pullback.fst A.hom (spMap (algebraMap R C)) ⁻¹ᵁ Y).ι ≫ pullback.snd A.hom (spMap (algebraMap R C)))
      (Y.ι ≫ A.hom) (spMap (algebraMap R C)) :=
    IsPullback.paste_vert (isPullback_morphismRestrict _ _) (IsPullback.of_hasPullback _ _)
  by_cases hc : ∃ x : A.left, x ∈ Y ∧ A.hom x = IsLocalRing.closedPoint R
  · obtain ⟨x, hxY, hx⟩ := hc
    have hgen : ∀ r : Sp R, ∃ y : A.left, y ∈ Y ∧ A.hom y = r := by
      intro r
      have hs : r ⤳ A.hom x := by
        rw [hx]
        exact IsLocalRing.specializes_closedPoint r
      obtain ⟨y, hy, hyr⟩ := (Flat.generalizingMap A.hom) hs
      exact ⟨y, hy.mem_open Y.isOpen hxY, hyr⟩
    have : GeometricallyIntegral (Y.ι ≫ A.hom) := geometricallyIntegral_open _ _ hgen
    have : CompactSpace Y.toScheme := isCompact_iff_compactSpace.1 hY
    have : QuasiCompact (Y.ι ≫ A.hom) := (quasiCompact_iff_compactSpace _).2 inferInstance
    obtain ⟨M, hM, rfl⟩ := cls_surj q
    refine (cls_eq_zero_iff hM).2 ?_
    refine GlobalTheory.ValGenExtend.triv_of_triv_generic R C _ _ (Y.ι ≫ A.hom) _ _ hsq inferInstance inferInstance
      inferInstance M hM ?_
    exact (cls_eq_zero_iff (pull_isLB hM _)).1 hq
  · have hall : ∀ y : Y.toScheme, ((Y.ι ≫ A.hom) y).asIdeal = ⊥ := by
      intro y
      refine (point_cases R _).resolve_right fun h => hc ⟨y.1, y.2, ?_⟩
      simpa using h
    obtain ⟨g, hg⟩ := exists_factor R C (Y.ι ≫ A.hom) hall
    have e := hsq.lift_fst (𝟙 _) g (by simpa using hg.symm)
    have := pull_comp (hsq.lift (𝟙 _) g (by simpa using hg.symm))
      (pullback.fst A.hom (spMap (algebraMap R C)) ∣_ Y) q
    rw [e, pull_id, hq, map_zero] at this
    exact this

end GlobalTheory.CompanionTheory.ValFibre
