import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExistsAfterFiniteExtensionOfCompleteDVRStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemPadicAlgClValuationSubringIffNormLeOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.BoundedOnFramesIffIntegralOnFrames
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcGenericPointDescendsToPowerSeries
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc.TraitOfPoint

variable {p : ℕ} [Fact p.Prime]

theorem base_integralClosure (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] :
    ∃ _ : IsDiscreteValuationRing (integralClosure ℤ_[p] K), GlobalTheory.Mum.Base (integralClosure ℤ_[p] K) := by
  haveI := GlobalTheory.isDiscreteValuationRing_integralClosure_padicInt p K
  exact ⟨inferInstance, ⟨inferInstance, inferInstance, inferInstance,
    GlobalTheory.DiscEval.isAdicComplete_integralClosure K⟩, GlobalTheory.charZero_integralClosure_padicInt⟩

theorem lft_toInt {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [h : ArithBase o Ω] (M : RatModel o Ω) :
    LocallyOfFiniteType (M.s ≫ spMap (algebraMap ℤ o)) := by
  have hft := h.ft
  have := M.lft
  have : LocallyOfFiniteType (spMap (algebraMap ℤ o)) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.2 hft
  infer_instance

end GlobalTheory.Poinc.TraitOfPoint

open GlobalTheory.Poinc.TraitOfPoint Polynomial in

theorem GlobalTheory.Poinc.exists_trait_of_classical_point : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (i : F.X ⟶ Z), IsOpenImmersion i → ∀ (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ Y.Z), Set.range (gPt p ≫ y ≫ πY ≫ X₁.π) ⊆ Set.range i → ∃ (T : Trait F) (ι : FractionRing T.V →+* PadicAlgCl p) (j : T.V →+* OO p) (ξ : Sp T.V ⟶ Y.Z), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))) ∧ (∀ v, (j v : PadicAlgCl p) = ι (algebraMap T.V (FractionRing T.V) v)) ∧ IsLocalHom j ∧ spMap j ≫ ξ = y ∧ jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ i := by
  intro g n F Z i hi W8 X₁ Y πY p _ y hy
  haveI := hi
  haveI := lft_toInt Y
  obtain ⟨K, hK, H⟩ := GlobalTheory.padicAlgCl_integral_points.2 Y.Z (Y.s ≫ spMap (algebraMap ℤ X₁.o₁)) p y
  haveI := hK
  obtain ⟨j₀, y₀, hj₀, -, hy₀⟩ := H K le_rfl
  obtain ⟨hdvr, hbase⟩ := base_integralClosure K

  have hinj₀ : Function.Injective (algebraMap (integralClosure ℤ_[p] K) (PadicAlgCl p)) :=
    fun a b h => Subtype.ext (Subtype.ext h)
  let ι₀ : FractionRing (integralClosure ℤ_[p] K) →+* PadicAlgCl p := IsFractionRing.lift hinj₀
  have hgen : gPt p ≫ spMap j₀ = spMap ι₀ ≫ jK (integralClosure ℤ_[p] K) :=
    GlobalTheory.ArcPointDescent.sp_sq fun a => by
      simp only [ι₀, IsFractionRing.lift_algebraMap]
      exact hj₀ a
  have hrange : Set.range (jK (integralClosure ℤ_[p] K) ≫ y₀ ≫ πY ≫ X₁.π) ⊆ Set.range i := by
    rintro _ ⟨w, rfl⟩
    have hw : w = spMap ι₀ (IsLocalRing.closedPoint (PadicAlgCl p)) := Subsingleton.elim _ _
    refine hy ⟨IsLocalRing.closedPoint (PadicAlgCl p), ?_⟩
    have e : gPt p ≫ y ≫ πY ≫ X₁.π = spMap ι₀ ≫ jK (integralClosure ℤ_[p] K) ≫ y₀ ≫ πY ≫ X₁.π := by
      rw [← hy₀]
      simp only [← Category.assoc]
      rw [hgen]
    rw [e, hw]
    exact Scheme.Hom.comp_apply _ _ _
  let yK := IsOpenImmersion.lift i _ hrange
  obtain ⟨T, f, fK, hfinj, -, hffin, hfK, hTy⟩ :=
    GlobalTheory.T.traitExistsAfterFiniteExtension_of_completeDVR g n (cycAway n) (zetaAway n) F (integralClosure ℤ_[p] K) hbase hdvr yK

  letI : Algebra (integralClosure ℤ_[p] K) T.V := f.toAlgebra
  haveI : Module.Finite (integralClosure ℤ_[p] K) T.V := hffin
  haveI : Module.IsTorsionFree (integralClosure ℤ_[p] K) T.V :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hfinj
  haveI : Module.IsTorsionFree (integralClosure ℤ_[p] K) (FractionRing T.V) := by
    refine Module.isTorsionFree_iff_algebraMap_injective.mpr ?_
    rw [IsScalarTower.algebraMap_eq (integralClosure ℤ_[p] K) T.V (FractionRing T.V)]
    exact (IsFractionRing.injective T.V (FractionRing T.V)).comp hfinj
  haveI : Module.IsTorsionFree (integralClosure ℤ_[p] K) (PadicAlgCl p) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj₀
  haveI : Algebra.IsAlgebraic (integralClosure ℤ_[p] K) T.V := inferInstance
  haveI : Algebra.IsAlgebraic T.V (FractionRing T.V) := IsLocalization.isAlgebraic _ (nonZeroDivisors T.V)
  haveI : Algebra.IsAlgebraic (integralClosure ℤ_[p] K) (FractionRing T.V) :=
    Algebra.IsAlgebraic.trans (integralClosure ℤ_[p] K) T.V (FractionRing T.V)
  let ι' : FractionRing T.V →ₐ[integralClosure ℤ_[p] K] PadicAlgCl p := IsAlgClosed.lift
  let ι : FractionRing T.V →+* PadicAlgCl p := ι'.toRingHom
  have hιf : ∀ a : integralClosure ℤ_[p] K, ι (algebraMap T.V (FractionRing T.V) (f a)) = ((a : K) : PadicAlgCl p) := by
    intro a
    have h1 := ι'.commutes a
    rw [IsScalarTower.algebraMap_apply (integralClosure ℤ_[p] K) T.V (FractionRing T.V)] at h1
    exact h1

  let φ : ℤ_[p] →+* T.V := f.comp (algebraMap ℤ_[p] (integralClosure ℤ_[p] K))
  have hcomp : ι.comp ((algebraMap T.V (FractionRing T.V)).comp φ) = algebraMap ℤ_[p] (PadicAlgCl p) := by
    ext c
    change ι (algebraMap T.V (FractionRing T.V) (f (algebraMap ℤ_[p] (integralClosure ℤ_[p] K) c))) = _
    rw [hιf]
    rfl
  have hφint : φ.IsIntegral :=
    RingHom.IsIntegral.trans _ _ (fun x => Algebra.IsIntegral.isIntegral x) hffin.to_isIntegral

  have hint : ∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V)) := by
    intro x
    constructor
    · intro hx
      obtain ⟨P, hPm, hP⟩ := (GlobalTheory.isIntegral_padicInt_iff_norm_le_one (ι x)).2 hx
      have hTV : IsIntegral T.V x := by
        refine ⟨P.map φ, hPm.map φ, ?_⟩
        rw [Polynomial.eval₂_map]
        apply ι.injective
        rw [Polynomial.hom_eval₂, hcomp, map_zero]
        exact hP
      exact IsIntegrallyClosed.isIntegral_iff.1 hTV
    · rintro ⟨v, rfl⟩
      obtain ⟨P, hPm, hP⟩ := hφint v
      apply (GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).1
      refine ⟨P, hPm, ?_⟩
      have h2 := congrArg (ι.comp (algebraMap T.V (FractionRing T.V))) hP
      rw [Polynomial.hom_eval₂, map_zero] at h2
      rw [← hcomp, ← RingHom.comp_assoc]
      exact h2
  let j : T.V →+* OO p := (ι.comp (algebraMap T.V (FractionRing T.V))).codRestrict (OO p) fun v =>
    (mem_OO_iff _).2 ((hint _).2 ⟨v, rfl⟩)
  have hjf : j.comp f = j₀ := by
    ext a
    change ι (algebraMap T.V (FractionRing T.V) (f a)) = ((j₀ a : OO p) : PadicAlgCl p)
    rw [hιf, hj₀]
  refine ⟨T, ι, j, spMap f ≫ y₀, hint, fun v => rfl, ?_, ?_, ?_⟩
  · refine ⟨fun v hv => ?_⟩
    have h1 : ‖ι (algebraMap T.V (FractionRing T.V) v)‖ = 1 :=
      le_antisymm ((hint _).2 ⟨v, rfl⟩) (not_lt.1 fun h => ((not_isUnit_OO_iff (j v)).2 h) hv)
    have h0 : algebraMap T.V (FractionRing T.V) v ≠ 0 := fun h => by
      rw [h, map_zero, norm_zero] at h1
      exact zero_ne_one h1
    obtain ⟨w, hw⟩ := (hint (algebraMap T.V (FractionRing T.V) v)⁻¹).1 (by rw [map_inv₀, norm_inv, h1, inv_one])
    refine IsUnit.of_mul_eq_one w (IsFractionRing.injective T.V (FractionRing T.V) ?_)
    rw [map_mul, map_one, hw, mul_inv_cancel₀ h0]
  · rw [← Category.assoc, GlobalTheory.ArcPointDescent.sp_comp (h := j₀) (fun a => by rw [← hjf]; rfl), hy₀]
  · have e1 : jK T.V ≫ spMap f = spMap fK ≫ jK (integralClosure ℤ_[p] K) :=
      GlobalTheory.ArcPointDescent.sp_sq fun a => (hfK a).symm
    have hyK : yK ≫ i = jK (integralClosure ℤ_[p] K) ≫ y₀ ≫ πY ≫ X₁.π := IsOpenImmersion.lift_fac _ _ _
    rw [hTy, Category.assoc (spMap fK) yK i, hyK]
    simp only [← Category.assoc]
    rw [e1]
