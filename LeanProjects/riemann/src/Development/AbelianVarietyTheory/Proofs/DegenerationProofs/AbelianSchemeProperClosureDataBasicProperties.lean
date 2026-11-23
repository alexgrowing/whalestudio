import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyTorusExtensionOfIsGt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem spMap_factor_jK {V Ω : Type} [CommRing V] [IsDomain V] [Field Ω] (φ : V →+* Ω)
    (hi : Function.Injective φ) : ∃ r, spMap φ = r ≫ Out.jK V := by
  refine ⟨spMap (IsFractionRing.lift (K := FractionRing V) hi), ?_⟩
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact (IsFractionRing.lift_algebraMap hi x).symm

theorem range_comp_ι_subset {X Y : Scheme.{0}} (U : Y.Opens) (f : X ⟶ U.toScheme) :
    Set.range (f ≫ U.ι) ⊆ U := by
  rintro _ ⟨x, rfl⟩
  exact (f x).2

theorem field_point_factor_dvr (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (Ω : Type) [Field Ω] (q : Sp Ω ⟶ Sp V) :
    (∃ r, q = r ≫ spMap (IsLocalRing.residue V)) ∨ ∃ r, q = r ≫ Out.jK V := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective q
  by_cases h : RingHom.ker φ.hom = ⊥
  · exact Or.inr (spMap_factor_jK φ.hom ((RingHom.injective_iff_ker_eq_bot _).2 h))
  · have hp : (RingHom.ker φ.hom).IsPrime := RingHom.ker_isPrime _
    have hm : RingHom.ker φ.hom = IsLocalRing.maximalIdeal V :=
      IsLocalRing.eq_maximalIdeal (hp.isMaximal h)
    refine Or.inl ⟨spMap (Ideal.Quotient.lift (IsLocalRing.maximalIdeal V) φ.hom
      fun a ha => (RingHom.mem_ker).1 (hm ▸ ha)), ?_⟩
    rw [← Spec.map_comp]
    congr 1

theorem isSemiAbelian_of_fibres_dvr (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (H : Over (Sp V)) [GrpObj H] [hc : IsCommMonObj H] (hs : Smooth H.hom) (hsep : IsSeparated H.hom)
    (hq : QuasiCompact H.hom)
    (h₁ : IsSemiAbelian ((Over.pullback (spMap (IsLocalRing.residue V))).obj H))
    (h₂ : IsSemiAbelian ((Over.pullback (Out.jK V)).obj H)) : IsSemiAbelian H := by
  have key : ∀ (Ω : Type) [Field Ω] (q : Sp Ω ⟶ Sp V), ∃ (T : Scheme.{0}) (r : Sp Ω ⟶ T) (f : T ⟶ Sp V),
      q = r ≫ f ∧ IsSemiAbelian ((Over.pullback f).obj H) := by
    intro Ω _ q
    rcases field_point_factor_dvr V Ω q with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact ⟨_, r, _, hr, h₁⟩
    · exact ⟨_, r, _, hr, h₂⟩
  refine ⟨hc, hs, hsep, hq, ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ q => ?_⟩,
    fun Ω _ _ q => ?_⟩
  · obtain ⟨T, r, f, rfl, h⟩ := key K q
    have hg : GeometricallyConnected (pullback.snd H.hom f) := h.geomConnected
    rw [← (pullbackLeftPullbackSndIso H.hom f r).hom.homeomorph.connectedSpace_iff]
    exact pullback_of_geometrically hg.1 K r
  · obtain ⟨T, r, f, rfl, h⟩ := key Ω q
    obtain ⟨E⟩ := h.fibres Ω r
    have : IsMonHom (pullCompIso r f H).symm.hom := inferInstanceAs (IsMonHom (pullCompIso r f H).inv)
    exact ⟨torusExtOfIso (pullCompIso r f H).symm E⟩

namespace Core

variable (C : Core)

theorem isPullback_a : IsPullback C.a C.A.hom C.GG.hom C.U.ι := by
  have h : IsPullback C.a (𝟙 _) C.G.ι (C.a ≫ C.G.ι) := IsPullback.of_vert_isIso_mono ⟨by simp⟩
  simpa using h.paste_vert C.cart

theorem isOpenImmersion_a : IsOpenImmersion C.a :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) C.isPullback_a.flip inferInstance

theorem range_a : Set.range C.a = C.GG.hom ⁻¹' C.U := by
  have h := C.isPullback_a
  rw [← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
    h.isoPullback.hom.surjective.range_comp, Scheme.Pullback.range_fst, Scheme.Opens.range_ι]

theorem isNoetherian_Z : IsNoetherian C.Z := by
  have := C.lft
  have := C.qc
  have : IsLocallyNoetherian C.Z := LocallyOfFiniteType.isLocallyNoetherian C.π
  have : CompactSpace C.Z := QuasiCompact.compactSpace_of_compactSpace C.π
  exact {}

theorem isNoetherian_P : IsNoetherian C.P.left := by
  have := C.isNoetherian_Z
  have := C.proper
  have : IsLocallyNoetherian C.P.left := LocallyOfFiniteType.isLocallyNoetherian C.P.hom
  have : CompactSpace C.P.left := QuasiCompact.compactSpace_of_compactSpace C.P.hom
  exact {}

theorem surjective_GG : Surjective C.GG.hom :=
  ⟨fun z => ⟨C.e z, by
    change (C.e ≫ C.G.ι ≫ C.P.hom) z = z
    rw [C.e_sec]; rfl⟩⟩

theorem nonempty_A : Nonempty C.A.left := by
  obtain ⟨z, hz⟩ := C.ne
  have := C.ab.geomConnected
  exact ⟨(C.A.hom.surjective ⟨z, hz⟩).choose⟩

theorem isIntegral_G : IsIntegral C.G.toScheme := by
  have : Nonempty C.G.toScheme := C.nonempty_A.map C.a
  exact isIntegral_of_isOpenImmersion C.G.ι

theorem flat_P : Flat (C.P.hom ≫ C.π) := by
  have := C.isNoetherian_P
  have := C.isOpenImmersion_a
  have := C.nonempty_A
  have := C.flat
  have := C.ab.smooth
  have : TopologicalSpace.NoetherianSpace C.A.left :=
    (C.a ≫ C.G.ι).isOpenEmbedding.isInducing.noetherianSpace
  have : IsDominant (C.a ≫ C.G.ι) :=
    ⟨(C.a ≫ C.G.ι).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
  have : IsSchemeTheoreticallyDominant (C.a ≫ C.G.ι) := .of_isDominant _
  have : Flat ((C.a ≫ C.G.ι) ≫ C.P.hom ≫ C.π) := by
    rw [← Category.assoc, C.cart.w]
    infer_instance
  exact flat_of_isSchemeTheoreticallyDominant
    (fun _ _ inst h => (@Module.Flat.flat_iff_torsion_eq_bot_of_isBezout ℤ _ _ _ inst.toModule _ _).mpr h)
    (C.a ≫ C.G.ι) _

variable {C} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ C.Z} (τ : C.Test y)

include τ in

theorem Test.cl : C.Cl y := by
  have hi : Function.Injective ((OO p).subtype.comp τ.j) := (OO p).subtype_injective.comp τ.j_inj
  obtain ⟨r, hr⟩ := spMap_factor_jK _ hi
  have e : gPt p ≫ spMap τ.j = r ≫ Out.jK τ.V := (Spec.map_comp _ _).symm.trans hr
  have e' : gPt p ≫ y = (r ≫ τ.yK) ≫ C.U.ι := by
    rw [Category.assoc, τ.yK_fac, ← Category.assoc, ← e, Category.assoc, τ.fac]
  unfold Cl
  rw [e']
  exact range_comp_ι_subset _ _

theorem Test.charZero : CharZero τ.V :=
  RingHom.charZero ((OO p).subtype.comp τ.j)

theorem Test.isSemiAbelian : IsSemiAbelian τ.H := by
  obtain ⟨S, hS⟩ := τ.split
  have := τ.smooth
  have : IsCommMonObj ((Over.pullback (spMap (IsLocalRing.residue τ.V))).obj τ.H) := Functor.isCommMonObj_obj
  exact isSemiAbelian_of_fibres_dvr τ.V τ.H (SmoothOfRelativeDimension.smooth C.g _) τ.sep τ.qc
    (isSemiAbelian_of_isGt _ S _ hS)
    (isSemiAbelian_of_isAbelianScheme _ (PolPull.isAbelianScheme_of_isGrpPullback C.ab τ.φ_cart))

end Core

theorem core_basic : ∀ C : Core, IsSeparated C.GG.hom ∧ LocallyOfFiniteType C.GG.hom ∧ QuasiCompact C.GG.hom ∧ IsIntegral C.G.toScheme ∧ Flat (C.GG.hom ≫ C.π) ∧ Flat (C.P.hom ≫ C.π) ∧ IsOpenImmersion C.a ∧ IsPullback C.a C.A.hom C.GG.hom C.U.ι ∧ Set.range C.a = C.GG.hom ⁻¹' C.U ∧ IsNoetherian C.Z ∧ IsNoetherian C.P.left ∧ IsDominant C.GG.hom ∧ ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z) (τ : C.Test y), C.Cl y ∧ CharZero τ.V ∧ IsSemiAbelian τ.H := by
  intro C
  have := C.proper
  have := C.isNoetherian_P
  have := C.flat_P
  have := C.surjective_GG
  have : TopologicalSpace.NoetherianSpace C.G.toScheme := C.G.ι.isOpenEmbedding.isInducing.noetherianSpace
  refine ⟨inferInstanceAs (IsSeparated (C.G.ι ≫ C.P.hom)),
    inferInstanceAs (LocallyOfFiniteType (C.G.ι ≫ C.P.hom)),
    inferInstanceAs (QuasiCompact (C.G.ι ≫ C.P.hom)), C.isIntegral_G, ?_, C.flat_P, C.isOpenImmersion_a,
    C.isPullback_a, C.range_a, C.isNoetherian_Z, C.isNoetherian_P, inferInstance,
    fun p _ y τ => ⟨τ.cl, τ.charZero, τ.isSemiAbelian⟩⟩
  change Flat ((C.G.ι ≫ C.P.hom) ≫ C.π)
  rw [Category.assoc]
  infer_instance

end GlobalTheory.ZJ
