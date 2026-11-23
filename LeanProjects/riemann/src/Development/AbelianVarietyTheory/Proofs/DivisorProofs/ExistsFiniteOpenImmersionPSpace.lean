import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteIntegralClosureOfIsIntegrallyClosed
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

namespace GlobalTheory.ZMain

open CategoryTheory AlgebraicGeometry TopologicalSpace

theorem finite_integralClosure_field (R L : Type*) [CommRing R] [Algebra.FiniteType ℤ R] [Field L]
    [Algebra R L] [Algebra.EssFiniteType R L] : Module.Finite R (integralClosure R L) := by
  rcases CharP.char_is_prime_or_zero L (ringChar L) with hp | h0
  · let p := ringChar L
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : CharP L p := ringChar.charP L
    let I := RingHom.ker (algebraMap R L)
    let R' := R ⧸ I
    letI : Algebra R' L := (Ideal.Quotient.lift I (algebraMap R L) fun _ h => h).toAlgebra
    haveI : IsScalarTower R R' L := .of_algebraMap_eq fun _ => rfl
    have hinj : Function.Injective (algebraMap R' L) := by
      rw [injective_iff_map_eq_zero]
      intro a ha
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
    haveI : IsDomain R' := hinj.isDomain _
    haveI : FaithfulSMul R' L := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
    haveI : CharP R' p := ⟨fun n => by
      rw [← map_eq_zero_iff _ hinj, map_natCast, CharP.cast_eq_zero_iff L]⟩
    letI : Algebra (ZMod p) R' := (ZMod.castHom dvd_rfl R').toAlgebra
    haveI : Algebra.FiniteType ℤ R' := .trans (S := R) inferInstance inferInstance
    haveI : Algebra.FiniteType (ZMod p) R' := .of_restrictScalars_finiteType ℤ (ZMod p) R'
    haveI : IsNoetherianRing R' := Algebra.FiniteType.isNoetherianRing (ZMod p) R'
    haveI : Module.Finite R R' := Module.Finite.of_surjective (Algebra.linearMap R R')
      Ideal.Quotient.mk_surjective
    let F := FractionRing R'
    letI : Algebra F L := FractionRing.liftAlgebra R' L
    haveI : Algebra.EssFiniteType R' L := .of_comp R R' L
    haveI : Algebra.EssFiniteType F L := .of_comp R' F L
    let E := algebraicClosure F L
    haveI : FiniteDimensional F E := finiteDimensional_algebraicClosure_of_essFiniteType F L
    haveI : Module.Finite R' (integralClosure R' E) :=
      NormFin.finite_integralClosure_of_perfectField (ZMod p) R' F E
    haveI : IsScalarTower R' E L := .of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply R' F L x, IsScalarTower.algebraMap_apply R' F E x,
        ← IsScalarTower.algebraMap_apply F E L]
    have hmem : ∀ z : integralClosure R' L, (z : L) ∈ E := fun z =>
      mem_algebraicClosure_iff.mpr (z.2.tower_top (A := F)).isAlgebraic
    let ψ : integralClosure R' L →ₗ[R'] integralClosure R' E :=
      { toFun := fun z => ⟨⟨z, hmem z⟩, (isIntegral_algHom_iff (IsScalarTower.toAlgHom R' E L)
            (IsScalarTower.toAlgHom R' E L).toRingHom.injective).mp z.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    haveI : Module.Finite R' (integralClosure R' L) := Module.Finite.of_injective ψ
      fun a b h => Subtype.ext (congrArg (fun w : integralClosure R' E => ((w : E) : L)) h)
    exact finite_integralClosure_of_finite_tower R R' L
  · haveI : CharZero L := (CharP.ringChar_zero_iff_CharZero L).mp h0
    exact finite_integralClosure_of_essFiniteType_field ℤ R L

universe u

theorem isFinite_fromNormalization_int {X Y : Scheme.{u}} {o : CommRingCat.{u}}
    [Algebra.FiniteType ℤ o] (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (g : Y ⟶ Spec o)
    [LocallyOfFiniteType g] [IsIntegral X]
    (hess : (f.residueFieldMap (genericPoint X)).hom.EssFiniteType) :
    IsFinite f.fromNormalization := by
  refine ⟨fun U hU => ?_⟩
  letI := (f.app U).hom.toAlgebra
  letI : Algebra o Γ(Y, U) := ((Scheme.ΓSpecIso o).inv ≫ g.appLE ⊤ U le_top).hom.toAlgebra
  haveI : Algebra.FiniteType o Γ(Y, U) :=
    (g.finiteType_appLE (isAffineOpen_top _) hU le_top).comp
      (.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso o).inv).2)
  haveI : Algebra.FiniteType ℤ Γ(Y, U) := .trans (S := o) inferInstance inferInstance
  haveI : IsNoetherianRing Γ(Y, U) := Algebra.FiniteType.isNoetherianRing ℤ _
  let D : Set X := {genericPoint X}
  have hD : Dense D := dense_iff_closure_eq.mpr (genericPoint_spec X)
  let ι := ↥(D ∩ (f ⁻¹ᵁ U : X.Opens))
  haveI : Finite ι := ((Set.finite_singleton _).inter_of_left _).to_subtype
  letI (x : ι) : Algebra Γ(Y, U) (X.residueField x.1) :=
    (f.app U ≫ X.evaluation (f ⁻¹ᵁ U) x.1 x.2.2).hom.toAlgebra
  haveI (x : ι) : Algebra.EssFiniteType Γ(Y, U) (X.residueField x.1) := by
    change (f.app U ≫ X.evaluation (f ⁻¹ᵁ U) x.1 x.2.2).hom.EssFiniteType
    rw [← Scheme.evaluation_naturality f (V := U) x.1 x.2.2]
    have hx : x.1 = genericPoint X := x.2.1
    exact .comp (.comp (essFiniteType_germ hU (f x.1) x.2.2)
      (RingHom.FiniteType.of_surjective _ (Y.residue_surjective _)).essFiniteType)
      (by rw [hx] at *; exact hess)
  haveI (x : ι) := finite_integralClosure_field Γ(Y, U) (X.residueField x.1)
  haveI : Module.Finite Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)) := by
    refine finite_integralClosure_of_family (L := fun x : ι => X.residueField x.1)
      (fun x => { (X.evaluation (f ⁻¹ᵁ U) x.1 x.2.2).hom with commutes' := fun _ => rfl })
      fun b hb => ?_
    rw [← basicOpen_eq_bot_iff, eq_bot_iff]
    intro y hy
    obtain ⟨x, hx, hxD⟩ := hD.inter_open_nonempty _ (X.basicOpen b).isOpen ⟨y, hy⟩
    exact ((X.evaluation_eq_zero_iff_notMem_basicOpen x (X.basicOpen_le b hx) b).mp
      (hb ⟨x, hxD, X.basicOpen_le b hx⟩) hx).elim
  rw [f.fromNormalization_app hU]
  exact RingHom.Finite.comp
    (.of_surjective _ (ConcreteCategory.bijective_of_isIso (f.normalizationObjIso hU).inv).2)
    (RingHom.finite_algebraMap.mpr this)

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor in

theorem exists_finite_openImmersion_pSpace : ∀ (o : Type) [CommRing o] [IsNoetherianRing o]
    [Algebra.FiniteType ℤ o] (m : ℕ) (X : Scheme.{0}) (f : X ⟶ PSpace o m), IsIntegral X →
    Geo.Tor.IsNormalScheme X → LocallyOfFiniteType f → QuasiCompact f → IsSeparated f →
    LocallyQuasiFinite f → ∃ (Z : Scheme.{0}) (z : Z ⟶ PSpace o m) (i : X ⟶ Z), IsFinite z ∧
      IsOpenImmersion i ∧ i ≫ z = f ∧ Geo.Tor.IsNormalScheme Z ∧ IsIntegral Z ∧
      Dense (Set.range i) := by
  intro o _ _ _ m X f hX hN _ _ _ _
  haveI : Algebra.FiniteType ℤ (CommRingCat.of o) := ‹Algebra.FiniteType ℤ o›
  haveI := isProper_str o m
  haveI : GlobalTheory.IsNormalScheme X := GlobalTheory.IsNormalScheme.of_pred hN
  refine ⟨f.normalization, f.fromNormalization, f.toNormalization,
    isFinite_fromNormalization_int f (PSpace.str o m)
      (LocallyOfFiniteType.stalkMap f _).residueFieldMap,
    inferInstance, f.toNormalization_fromNormalization,
    (GlobalTheory.IsNormalScheme.normalization_of_isIntegral f).pred _, inferInstance,
    (inferInstance : IsDominant f.toNormalization).denseRange⟩

end GlobalTheory.ZMain
