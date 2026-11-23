import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKerTorusExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.EssFiniteTypeOfFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TorusPart

section
open TopologicalSpace GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Published

private theorem isProper_of_proj {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : IsProper f := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have := isProper_str R N
  infer_instance

private theorem isDedekind_of_normal (X : Scheme.{0}) [IsIntegral X] [GlobalTheory.IsNormalScheme X]
    [IsLocallyNoetherian X] (hd : topologicalKrullDim X ≤ 1) (U : X.Opens) (hU : IsAffineOpen U)
    (hne : Nonempty U) : IsDedekindDomain Γ(X, U) := by
  haveI := hne
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hdim : ringKrullDim Γ(X, U) ≤ 1 := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    have e := IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso hU.isoSpec).isHomeomorph
    exact e.symm.le.trans ((topologicalKrullDim_subspace_le X U).trans hd)
  have h3 : Ring.KrullDimLE 1 Γ(X, U) := Ring.krullDimLE_iff.2 (by exact_mod_cast hdim)
  haveI : Ring.DimensionLEOne Γ(X, U) :=
    ⟨fun {p} hp hp' => Ring.krullDimLE_one_iff_of_noZeroDivisors.mp h3 p hp hp'⟩
  haveI : IsIntegrallyClosed Γ(X, U) := inferInstance
  haveI : IsIntegralClosure Γ(X, U) Γ(X, U) (FractionRing Γ(X, U)) := inferInstance
  exact {}

private theorem isGen_toNorm : ∀ {Y : Scheme.{0}} [IsIntegral Y] {K : Type} [Field K] (x : Sp K ⟶ Y), IsGen x →
    ∀ (K' : Type) [Field K'] [Algebra K K'] [Algebra.IsAlgebraic K K']
    [QuasiCompact (spMap (algebraMap K K') ≫ x)] [QuasiSeparated (spMap (algebraMap K K') ≫ x)],
    IsGen (spMap (algebraMap K K') ≫ x).toNormalization := by
  intro Y _ K _ x hx K' _ _ _ _ _
  obtain ⟨hxd, hxp⟩ := hx
  refine ⟨inferInstance, ?_⟩
  set f := spMap (algebraMap K K') ≫ x with hf
  obtain ⟨y⟩ : Nonempty Y := inferInstance
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have : Nonempty V := ⟨⟨y, hyV⟩⟩
  have hxV : ⊤ ≤ x ⁻¹ᵁ V := TuplePoint.le_preimage_of_mem x hyV
  obtain ⟨hfV, hfv⟩ := GlobalTheory.ZH.CrdCalc.valR_spMap (algebraMap K K') x V hxV
  set g := f.toNormalization with hg
  have hgV : ⊤ ≤ g ⁻¹ᵁ (f.fromNormalization ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, hg, Scheme.Hom.toNormalization_fromNormalization]; exact hfV
  let φ := Scheme.stalkClosedPointTo (R := CommRingCat.of K') g
  have hφ : Function.Surjective φ.hom := by

    intro z
    haveI := hxd
    haveI := hxp
    let vx := (Points.valMap x V hxV).hom
    let v := (Points.valMap f V hfV).hom
    have hv : ∀ a, v a = algebraMap K K' (vx a) := fun a => by
      rw [← Points.valR_eq, ← Points.valR_eq]; exact hfv a
    have hvx : Function.Injective vx := TuplePoint.valMap_injective x hxV
    have hsx : Function.Surjective (Scheme.stalkClosedPointTo (R := CommRingCat.of K) x).hom :=
      (stalkClosedPointIso (.of K)).commRingCatIsoToRingEquiv.surjective.comp (x.stalkMap_surjective _)
    have hxm : x (IsLocalRing.closedPoint K) ∈ V := hxV trivial
    letI : Algebra Γ(Y, V) K := vx.toAlgebra
    letI : Algebra Γ(Y, V) K' := v.toAlgebra
    haveI : IsScalarTower Γ(Y, V) K K' := IsScalarTower.of_algebraMap_eq fun a => hv a
    haveI : FaithfulSMul Γ(Y, V) K := (faithfulSMul_iff_algebraMap_injective Γ(Y, V) K).2 hvx
    haveI : IsFractionRing Γ(Y, V) K := by
      refine IsFractionRing.of_field Γ(Y, V) K fun c => ?_
      obtain ⟨t, rfl⟩ := hsx c
      letI := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨x (IsLocalRing.closedPoint K), hxm⟩ : V)
      haveI := hV.isLocalization_stalk ⟨x (IsLocalRing.closedPoint K), hxm⟩
      obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (hV.primeIdealOf ⟨_, hxm⟩).asIdeal.primeCompl t
      have e : ∀ s, (Scheme.stalkClosedPointTo (R := CommRingCat.of K) x).hom ((Y.presheaf.germ V _ hxm).hom s) = vx s := fun s => by
        show _ = (Points.valMap x V hxV).hom s
        rw [← Points.germ_stalkClosedPointTo_eq_valMap x V hxV]; rfl
      have hab' := congrArg (Scheme.stalkClosedPointTo (R := CommRingCat.of K) x).hom hab
      rw [map_mul] at hab'
      have hb0 : (b : Γ(Y, V)) ≠ 0 := fun h0 => b.2 (h0 ▸ Ideal.zero_mem _)
      have hb : vx b ≠ 0 := (map_ne_zero_iff _ hvx).2 hb0
      refine ⟨a, b, ?_⟩
      rw [eq_div_iff (show algebraMap Γ(Y, V) K b ≠ 0 from hb)]
      change _ * vx b = vx a
      rw [← e a, ← e b]; exact hab'
    obtain ⟨c, hc0, hint⟩ := ((IsFractionRing.isAlgebraic_iff Γ(Y, V) K K').2
      (Algebra.IsAlgebraic.isAlgebraic (R := K) z)).exists_integral_multiple
    have hvc : v c ≠ 0 := by
      rw [hv]; exact (map_ne_zero_iff _ (algebraMap K K').injective).2 ((map_ne_zero_iff _ hvx).2 hc0)
    have hmem := fun a => TupleNorm.mem_range_valMap_toNormalization f hV hfV hgV a
    obtain ⟨s1, hs1⟩ := (hmem (v c * z)).2 (by rw [Algebra.smul_def] at hint; exact hint)
    obtain ⟨s2, hs2⟩ := (hmem (v c)).2 (v.isIntegralElem_map)
    let G := f.normalization.presheaf.germ (f.fromNormalization ⁻¹ᵁ V) (g (IsLocalRing.closedPoint K')) (hgV trivial)
    have eg : ∀ s, φ.hom (G.hom s) = (Points.valMap g _ hgV).hom s := fun s => by
      rw [← Points.germ_stalkClosedPointTo_eq_valMap g _ hgV]; rfl
    have hu : IsUnit (φ.hom (G.hom s2)) := by
      refine isUnit_iff_ne_zero.2 ?_
      rw [eg, hs2]; exact hvc
    obtain ⟨u, hu'⟩ := isUnit_of_map_unit φ.hom _ hu
    refine ⟨G.hom s1 * ↑u⁻¹, ?_⟩
    rw [map_mul, eg, hs1, map_units_inv, hu', eg, hs2]
    field_simp
  have := IsClosedImmersion.spec_of_surjective φ hφ
  rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of K') g]
  infer_instance

private theorem finite_intClosure_ext (k : Type) {B R L : Type} [Field k] [PerfectField k] [CommRing B]
    [Algebra k B] [Algebra.FiniteType k B] [Field R] [Algebra B R] [Field L] [Algebra R L] [Algebra B L]
    [IsScalarTower B R L] [FiniteDimensional R L]
    (h : (algebraMap B R).SurjectiveOnStalks) :
    Module.Finite B (integralClosure B L) := by
  let A := B ⧸ RingHom.ker (algebraMap B R)
  haveI : (RingHom.ker (algebraMap B R)).IsPrime := RingHom.ker_isPrime _
  letI : Algebra A R := (RingHom.kerLift (algebraMap B R)).toAlgebra
  haveI : IsScalarTower B A R := .of_algebraMap_eq fun x => (RingHom.kerLift_mk _ x).symm
  haveI : FaithfulSMul A R := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (RingHom.kerLift_injective _)
  haveI : IsFractionRing A R := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨x, y, e⟩ := NormCurve.exists_eq_div h z
    exact ⟨algebraMap B _ x, algebraMap B _ y, by
      rwa [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]⟩
  letI : Algebra A L := ((algebraMap R L).comp (algebraMap A R)).toAlgebra
  haveI : IsScalarTower A R L := .of_algebraMap_eq' rfl
  haveI : IsScalarTower B A L := .of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply A R L, ← IsScalarTower.algebraMap_apply B A R,
      ← IsScalarTower.algebraMap_apply B R L]
  haveI := NormFin.finite_integralClosure_of_perfectField k A R L
  haveI : Module.Finite B (integralClosure A L) := Module.Finite.trans A _
  have h' : Module.Finite B ((integralClosure A L).restrictScalars B) := this
  rwa [integralClosure_restrictScalars_of_isIntegral] at h'

private theorem isFinite_ext {k : Type} [Field k] [PerfectField k] {X : Scheme.{0}} (s : X ⟶ Sp k)
    [LocallyOfFiniteType s] {K : Type} [Field K] (x : Sp K ⟶ X)
    (hx : IsPreimmersion x) (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K']
    [QuasiCompact (spMap (algebraMap K K') ≫ x)] [QuasiSeparated (spMap (algebraMap K K') ≫ x)] :
    IsFinite (spMap (algebraMap K K') ≫ x).fromNormalization := by
  let g : Sp K' ⟶ Sp K := spMap (algebraMap K K')
  haveI hg : IsFinite g := (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.mpr inferInstance)
  let f : Sp K' ⟶ X := g ≫ x
  change IsFinite f.fromNormalization
  refine ⟨fun U hU => ?_⟩
  rw [f.fromNormalization_app hU]
  letI := (f.app U).hom.toAlgebra
  have h : Module.Finite Γ(X, U) (integralClosure Γ(X, U) Γ(Sp K', f ⁻¹ᵁ U)) := by
    by_cases hne : Nonempty (f ⁻¹ᵁ U)
    · haveI : Nonempty (x ⁻¹ᵁ U) := by
        obtain ⟨z, hz⟩ := hne
        exact ⟨⟨g z, hz⟩⟩
      letI := (NormCurve.isField_sections (f ⁻¹ᵁ U)).toField
      letI := (NormCurve.isField_sections (x ⁻¹ᵁ U)).toField
      letI := (NormCurve.constHom s U).toAlgebra
      haveI : Algebra.FiniteType k Γ(X, U) := NormCurve.finiteType_constHom s hU
      letI := (x.app U).hom.toAlgebra
      letI : Algebra Γ(Sp K, x ⁻¹ᵁ U) Γ(Sp K', f ⁻¹ᵁ U) := (g.app (x ⁻¹ᵁ U)).hom.toAlgebra
      haveI : IsScalarTower Γ(X, U) Γ(Sp K, x ⁻¹ᵁ U) Γ(Sp K', f ⁻¹ᵁ U) := .of_algebraMap_eq' rfl
      haveI : FiniteDimensional Γ(Sp K, x ⁻¹ᵁ U) Γ(Sp K', f ⁻¹ᵁ U) :=
        IsFinite.finite_app g _ (NormCurve.isAffineOpen_of_subsingleton (x ⁻¹ᵁ U))
      refine finite_intClosure_ext k (R := Γ(Sp K, x ⁻¹ᵁ U)) ?_
      have := NormCurve.surjectiveOnStalks_appLE x hU (x ⁻¹ᵁ U) le_rfl
      rwa [← Scheme.Hom.app_eq_appLE] at this
    · have : f ⁻¹ᵁ U = ⊥ := eq_bot_iff.mpr fun x hx => (hne ⟨⟨x, hx⟩⟩).elim
      have : Subsingleton Γ(Sp K', f ⁻¹ᵁ U) := by rw [this]; infer_instance
      infer_instance
  exact RingHom.Finite.comp (RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso (f.normalizationObjIso hU).inv).2)
    (RingHom.finite_algebraMap.mpr h)

end

theorem UpperTheory.finite_extension_curve_cover :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)], IsCurve k C → ∀ (K : Type) [Field K] (x : Sp K ⟶ C), IsGen x →
        ∀ (K' : Type) [Field K'] [Algebra K K'], FiniteDimensional K K' →
        ∃ (C' : Scheme.{0}) (_ : Algebra k Γ(C', ⊤)) (π : C' ⟶ C) (x' : Sp K' ⟶ C'), IsCurve k C' ∧ IsGen x' ∧
          π ≫ strHom k C = strHom k C' ∧ IsFinite π ∧ Surjective π ∧ x' ≫ π = spMap (algebraMap K K') ≫ x := by
  intro k _ _ C _ hC K _ x hx K' _ _ hfd
  obtain ⟨hs, hp, hg⟩ := hC
  haveI : IsIntegral C := LieSemineg.isIntegral_curve hs hg
  have hdC : topologicalKrullDim C = 1 := LieSemineg.dim_curve hs
  haveI : IsProper (strHom k C) := isProper_of_proj hp
  haveI : Smooth (strHom k C) := hs.smooth
  let f : Sp K' ⟶ C := spMap (algebraMap K K') ≫ x
  haveI : QuasiCompact f := QuasiCompact.of_comp f (strHom k C)
  haveI : QuasiSeparated f := QuasiSeparated.of_comp f (strHom k C)
  let π := f.fromNormalization
  let x' := f.toNormalization
  haveI hπ : IsFinite π := isFinite_ext (strHom k C) x hx.2 K'
  letI := algebraΓAlong k π
  have hstr : π ≫ strHom k C = strHom k f.normalization := comp_strHom (appTop_algebraMap_along k π)
  haveI : Algebra.IsAlgebraic K K' := inferInstance
  have hx' : IsGen x' := isGen_toNorm x hx K'

  have hgen : ∀ z : Sp K', f z = genericPoint C := by
    intro z
    haveI := hx.1
    have hd : DenseRange x := x.denseRange
    have hr : Set.range x = {f z} := by
      ext w
      constructor
      · rintro ⟨v, rfl⟩
        rw [Set.mem_singleton_iff, Scheme.Hom.comp_apply, Subsingleton.elim v (spMap (algebraMap K K') z)]
      · rintro rfl
        exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
    refine ((genericPoint_spec C).eq ?_).symm
    rw [isGenericPoint_def, ← hr]
    exact hd.closure_range
  have hξ : genericPoint C ∈ Set.range π := by
    obtain ⟨z⟩ : Nonempty (Sp K') := inferInstance
    refine ⟨x' z, ?_⟩
    rw [← Scheme.Hom.comp_apply, f.toNormalization_fromNormalization]
    exact hgen _
  have hsurj : Function.Surjective π := fun y =>
    (genericPoint_specializes y).mem_closed π.isClosedMap.isClosed_range hξ
  have hdim : topologicalKrullDim f.normalization = 1 :=
    ((Published.dim_le_of_isIntegralHom π).antisymm
      (PosBaseChange.dim_le_of_isClosedMap π.isClosedMap hsurj)).trans hdC
  haveI : LocallyOfFiniteType (strHom k f.normalization) := hstr ▸ inferInstance
  haveI : IsProper (strHom k f.normalization) := hstr ▸ inferInstance
  haveI : IsLocallyNoetherian f.normalization :=
    LocallyOfFiniteType.isLocallyNoetherian (strHom k f.normalization)
  haveI : IsIntegral f.normalization := inferInstance
  haveI : GlobalTheory.IsNormalScheme f.normalization := inferInstance
  have hD := isDedekind_of_normal f.normalization hdim.le
  haveI : Smooth (strHom k f.normalization) :=
    CurveThrough.smooth_of_dedekind_charts k _ _ hD
  refine ⟨f.normalization, inferInstance, π, x', ⟨?_, ?_, ?_⟩, hx', hstr, hπ, ⟨hsurj⟩,
    f.toNormalization_fromNormalization⟩
  · exact NefCurveTest.smoothOfRelativeDimension_one _ hdim
  · exact ProperCurve.isProjOver_of_isProper _ hdim
  · exact geometricallyConnected_of_isAlgClosed _
