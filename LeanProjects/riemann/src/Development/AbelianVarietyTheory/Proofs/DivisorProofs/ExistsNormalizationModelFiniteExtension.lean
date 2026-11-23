import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalFiniteModelOfExtension
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NormCover

open GlobalTheory.BplusDescent

theorem genericPoint_mem {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} (hU : (U : Set X).Nonempty) :
    genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by simpa using hU)

theorem isFinite_fromNormalization_fieldPt {X : Scheme.{0}} [IsIntegral X] [GlobalTheory.IsNormalScheme X]
    [IsLocallyNoetherian X] {L : Type} [Field L] [CharZero L]
    (ψ : X.presheaf.stalk (genericPoint X) ⟶ .of L) (hψ : ψ.hom.Finite) :
    IsFinite (fieldPt ψ).fromNormalization := by
  refine ⟨fun U hU => ?_⟩
  by_cases hne : (U : Set X).Nonempty
  · have hη := genericPoint_mem hne
    haveI : Nonempty U := hne.to_subtype
    letI : Algebra Γ(X, U) Γ((fieldPt ψ).normalization, (fieldPt ψ).fromNormalization ⁻¹ᵁ U) :=
      ((fieldPt ψ).fromNormalization.app U).hom.toAlgebra
    letI : Algebra Γ((fieldPt ψ).normalization, (fieldPt ψ).fromNormalization ⁻¹ᵁ U) L :=
      (normFun ψ hη).hom.toAlgebra
    letI : Algebra Γ(X, U) L := (X.presheaf.germ U _ hη ≫ ψ).hom.toAlgebra
    letI : Algebra X.functionField L := ψ.hom.toAlgebra
    haveI : IsScalarTower Γ(X, U) Γ((fieldPt ψ).normalization, (fieldPt ψ).fromNormalization ⁻¹ᵁ U) L :=
      .of_algebraMap_eq' (congrArg CommRingCat.Hom.hom (app_normFun ψ hη)).symm
    haveI := functionField_isFractionRing_of_isAffineOpen X U hU
    haveI : IsScalarTower Γ(X, U) X.functionField L := .of_algebraMap_eq' rfl
    haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    haveI : FiniteDimensional X.functionField L := hψ
    haveI : CharZero X.functionField := ψ.hom.charZero
    haveI : IsIntegralClosure Γ((fieldPt ψ).normalization, (fieldPt ψ).fromNormalization ⁻¹ᵁ U) Γ(X, U) L :=
      ⟨(normFun_spec ψ hη hU).1, fun {x} => ((normFun_spec ψ hη hU).2 x).symm⟩
    exact IsIntegralClosure.finite Γ(X, U) X.functionField L _
  · haveI : Subsingleton Γ((fieldPt ψ).normalization, (fieldPt ψ).fromNormalization ⁻¹ᵁ U) := by
      refine subsingleton_of_forall_eq 0 fun s => ?_
      rw [← basicOpen_eq_bot_iff]
      exact eq_bot_iff.2 fun z hz => (hne ⟨_, ((fieldPt ψ).normalization.basicOpen_le s hz :)⟩).elim
    letI := ((fieldPt ψ).fromNormalization.app U).hom.toAlgebra
    change Module.Finite _ _
    infer_instance

end GlobalTheory.NormCover

namespace GlobalTheory.NormCover

open GlobalTheory.BplusDescent

theorem exists_normalization_model : ∀ (k Ω : Type) [CommRing k] [IsNoetherianRing k] [Field Ω] [CharZero Ω] [Algebra k Ω]
    (M : RatModel k Ω) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra k Ω'] [IsScalarTower k Ω Ω']
    [FiniteDimensional Ω Ω'], Geo.Tor.IsNormalScheme M.Z → ∃ (M' : RatModel k Ω') (π : M'.Z ⟶ M.Z),
      Geo.Tor.IsNormalScheme M'.Z ∧ IsFinite π ∧ M'.pt ≫ π = spMap (algebraMap Ω Ω') ≫ M.pt := by
  intro k Ω _ _ _ _ _ M Ω' _ _ _ _ _ hN
  haveI : GlobalTheory.IsNormalScheme M.Z := GlobalTheory.IsNormalScheme.of_pred hN
  haveI := M.lft
  haveI := M.sep
  haveI := M.qc
  haveI : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  haveI : CharZero Ω' := charZero_of_injective_algebraMap (algebraMap Ω Ω').injective
  let ρ : M.Z.presheaf.stalk (genericPoint M.Z) ⟶ .of Ω :=
    M.Z.presheaf.stalkSpecializes (M.pt_specializes (IsLocalRing.closedPoint Ω) (genericPoint M.Z)) ≫
      Scheme.stalkClosedPointTo M.pt
  have hρ : fieldPt ρ = M.pt := by
    simp only [fieldPt, ρ, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk M.pt
  let ψ : M.Z.presheaf.stalk (genericPoint M.Z) ⟶ .of Ω' := ρ ≫ CommRingCat.ofHom (algebraMap Ω Ω')
  have hψ : fieldPt ψ = spMap (algebraMap Ω Ω') ≫ M.pt := by
    rw [← hρ]
    simp only [fieldPt, ψ, Spec.map_comp, Category.assoc]
  have hρs : Function.Surjective ρ.hom := by
    intro x
    obtain ⟨U, f, hU, rfl⟩ := M.onto x
    have hη := genericPoint_mem hU
    refine ⟨M.Z.presheaf.germ U _ hη f, ?_⟩
    have key : ∀ (g : Sp Ω ⟶ M.Z) (_ : fieldPt ρ = g) (e : ⊤ ≤ g ⁻¹ᵁ U),
        g.appLE U ⊤ e ≫ (Scheme.ΓSpecIso (.of Ω)).hom = M.Z.presheaf.germ U _ hη ≫ ρ := by
      rintro _ rfl e
      exact fieldPt_appLE ρ hη
    have e := M.top_le_preimage_pt hU
    rw [valF, dif_pos e]
    exact (congrArg (fun g => g.hom f) (key M.pt hρ e)).symm
  have hψfin : ψ.hom.Finite :=
    RingHom.Finite.comp (RingHom.finite_algebraMap.2 inferInstance) (RingHom.Finite.of_surjective ρ.hom hρs)
  haveI hfin : IsFinite (fieldPt ψ).fromNormalization := isFinite_fromNormalization_fieldPt ψ hψfin

  have hgen : Set.range (fieldPt ψ).toNormalization = {genericPoint (fieldPt ψ).normalization} := by
    have hc : ∀ w : Sp Ω', w = IsLocalRing.closedPoint Ω' := fun w =>
      Subsingleton.elim (α := PrimeSpectrum Ω') _ _
    have hr : Set.range (fieldPt ψ).toNormalization = {(fieldPt ψ).toNormalization (IsLocalRing.closedPoint Ω')} := by
      ext z
      constructor
      · rintro ⟨w, rfl⟩
        rw [hc w]
        rfl
      · rintro rfl
        exact ⟨_, rfl⟩
    have hd : closure (Set.range (fieldPt ψ).toNormalization) = Set.univ := (fieldPt ψ).toNormalization.denseRange.closure_range
    rw [hr] at hd ⊢
    have hg : IsGenericPoint ((fieldPt ψ).toNormalization (IsLocalRing.closedPoint Ω')) ⊤ := hd
    rw [hg.eq (genericPoint_spec (fieldPt ψ).normalization)]
  have hpts : (fieldPt ψ).toNormalization ≫ (fieldPt ψ).fromNormalization ≫ M.s = spMap (algebraMap k Ω') := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hψ, Category.assoc, M.pt_s, spMap, spMap,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have honto : ∀ x : Ω', ∃ (U : (fieldPt ψ).normalization.Opens) (f : Γ((fieldPt ψ).normalization, U)), (U : Set (fieldPt ψ).normalization).Nonempty ∧
      valF (fieldPt ψ).toNormalization U f = x := by
    intro x
    obtain ⟨U, hU, hηU, -⟩ := exists_isAffineOpen_mem_and_subset (x := genericPoint M.Z) (U := ⊤) trivial
    haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
    letI : Algebra Γ(M.Z, U) Ω' := (M.Z.presheaf.germ U _ hηU ≫ ψ).hom.toAlgebra
    letI : Algebra M.Z.functionField Ω' := ψ.hom.toAlgebra
    haveI := functionField_isFractionRing_of_isAffineOpen M.Z U hU
    haveI : IsScalarTower Γ(M.Z, U) M.Z.functionField Ω' := .of_algebraMap_eq' rfl
    haveI : FiniteDimensional M.Z.functionField Ω' := hψfin
    obtain ⟨⟨a, ha⟩, hax⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors Γ(M.Z, U)) x
      (Algebra.IsIntegral.isIntegral (R := M.Z.functionField) x)
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
    have hηV : genericPoint M.Z ∈ M.Z.basicOpen a := by
      refine genericPoint_mem ?_
      rw [Set.nonempty_iff_ne_empty]
      exact fun h => ha0 ((basicOpen_eq_bot_iff a).1 (SetLike.coe_injective h))
    have hV : IsAffineOpen (M.Z.basicOpen a) := hU.basicOpen a
    let r := M.Z.presheaf.map (homOfLE (M.Z.basicOpen_le a)).op
    letI : Algebra Γ(M.Z, U) Γ(M.Z, M.Z.basicOpen a) := r.hom.toAlgebra
    letI : Algebra Γ(M.Z, M.Z.basicOpen a) Ω' := (M.Z.presheaf.germ _ _ hηV ≫ ψ).hom.toAlgebra
    haveI : IsScalarTower Γ(M.Z, U) Γ(M.Z, M.Z.basicOpen a) Ω' := .of_algebraMap_eq' (by
      have e : r ≫ M.Z.presheaf.germ _ _ hηV = M.Z.presheaf.germ U _ hηU := TopCat.Presheaf.germ_res _ _ _ _
      change (M.Z.presheaf.germ U _ hηU ≫ ψ).hom = (r ≫ M.Z.presheaf.germ _ _ hηV ≫ ψ).hom
      simp only [← e, Category.assoc])
    have hunit : IsUnit (r.hom a) := M.Z.toRingedSpace.isUnit_res_basicOpen a
    have hxV : IsIntegral Γ(M.Z, M.Z.basicOpen a) x := by
      have h1 : IsIntegral Γ(M.Z, M.Z.basicOpen a) (algebraMap Γ(M.Z, U) Ω' a * x) := by
        have := hax.tower_top (A := Γ(M.Z, M.Z.basicOpen a))
        rwa [Submonoid.smul_def, Algebra.smul_def] at this
      have h2 : x = algebraMap Γ(M.Z, M.Z.basicOpen a) Ω' (↑hunit.unit⁻¹ : Γ(M.Z, M.Z.basicOpen a)) *
          (algebraMap Γ(M.Z, U) Ω' a * x) := by
        rw [IsScalarTower.algebraMap_apply Γ(M.Z, U) Γ(M.Z, M.Z.basicOpen a) Ω' a, ← _root_.mul_assoc, ← map_mul]
        have : (↑hunit.unit⁻¹ : Γ(M.Z, M.Z.basicOpen a)) * algebraMap Γ(M.Z, U) Γ(M.Z, M.Z.basicOpen a) a = 1 :=
          hunit.val_inv_mul
        rw [this, map_one, _root_.one_mul]
      rw [h2]
      exact isIntegral_algebraMap.mul h1
    obtain ⟨c, hc⟩ := ((normFun_spec ψ hηV hV).2 x).2 hxV
    have hW : ⊤ ≤ (fieldPt ψ).toNormalization ⁻¹ᵁ ((fieldPt ψ).fromNormalization ⁻¹ᵁ M.Z.basicOpen a) := by
      intro w _
      show (fieldPt ψ).fromNormalization ((fieldPt ψ).toNormalization w) ∈ M.Z.basicOpen a
      rw [← Scheme.Hom.comp_apply, Scheme.Hom.toNormalization_fromNormalization, fieldPt_apply]
      exact hηV
    refine ⟨(fieldPt ψ).fromNormalization ⁻¹ᵁ M.Z.basicOpen a, c,
      ⟨_, hW (x := IsLocalRing.closedPoint Ω') trivial⟩, ?_⟩
    rw [valF, dif_pos hW]
    exact hc
  let M' : RatModel k Ω' :=
    { Z := (fieldPt ψ).normalization
      s := (fieldPt ψ).fromNormalization ≫ M.s
      sep := inferInstance
      lft := inferInstance
      qc := inferInstance
      pt := (fieldPt ψ).toNormalization
      pt_s := hpts
      gen := hgen
      onto := honto }
  refine ⟨M', (fieldPt ψ).fromNormalization, (GlobalTheory.IsNormalScheme.normalization_of_isIntegral (fieldPt ψ)).pred _, hfin, ?_⟩
  exact (Scheme.Hom.toNormalization_fromNormalization (fieldPt ψ)).trans hψ

end GlobalTheory.NormCover
