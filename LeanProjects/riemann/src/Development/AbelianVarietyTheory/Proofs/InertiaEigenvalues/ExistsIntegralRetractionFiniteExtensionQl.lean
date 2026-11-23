import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InclIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrComplete

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

namespace GlobalTheory.CoefRetraction

theorem exists_retraction (A K L : Type) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] [Field K]
    [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    ∃ r : L →ₗ[K] K, r 1 = 1 ∧ ∀ x : L, IsIntegral A x → ∃ a : A, algebraMap A K a = r x := by
  classical
  have : Module.IsTorsionFree A L := .trans_faithfulSMul A K L
  have : Module.Free A (integralClosure A L) :=
    IsIntegralClosure.module_free A K L (integralClosure A L)
  have : Module.Finite A (integralClosure A L) :=
    IsIntegralClosure.finite A K L (integralClosure A L)
  have : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure A L) (nonZeroDivisors A)) L :=
    IsIntegralClosure.isLocalization A K L (integralClosure A L)

  let b := Module.Free.chooseBasis A (integralClosure A L)
  let bL := b.localizationLocalization K (nonZeroDivisors A) L
  have hrepr : ∀ (z : integralClosure A L) i,
      bL.repr (algebraMap (integralClosure A L) L z) i = algebraMap A K (b.repr z i) :=
    fun z i => b.localizationLocalization_repr_algebraMap K (nonZeroDivisors A) L z i

  have hspan : (1 : A) ∈ Ideal.span (Set.range fun i => b.repr 1 i) := by
    obtain ⟨d, hd⟩ : ∃ d : A, Ideal.span (Set.range fun i => b.repr 1 i) = Ideal.span {d} :=
      ⟨Submodule.IsPrincipal.generator (Ideal.span (Set.range fun i => b.repr 1 i)),
        (Submodule.IsPrincipal.span_singleton_generator _).symm⟩
    have hdiv : ∀ i, ∃ e : A, e * d = b.repr 1 i := fun i => by
      have hi : b.repr 1 i ∈ Ideal.span (Set.range fun i => b.repr 1 i) :=
        Ideal.subset_span ⟨i, rfl⟩
      rw [hd] at hi
      exact Ideal.mem_span_singleton'.mp hi
    choose e he using hdiv
    set β : integralClosure A L := ∑ i, e i • b i with hβ
    have hdβ : d • β = 1 := by
      rw [hβ, Finset.smul_sum]
      conv_rhs => rw [← b.sum_repr 1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, mul_comm, he i]
    have hL : algebraMap A L d * (β : L) = 1 := by
      have := congrArg (fun z : integralClosure A L => (z : L)) hdβ
      simpa [Algebra.smul_def] using this
    have hK : algebraMap K L (algebraMap A K d) * (β : L) = 1 := by
      rw [← IsScalarTower.algebraMap_apply]; exact hL
    have hd0 : algebraMap A K d ≠ 0 := by
      intro h0; rw [h0, map_zero, zero_mul] at hK; exact zero_ne_one hK
    have hint : IsIntegral A (algebraMap K L (algebraMap A K d)⁻¹) := by
      rw [map_inv₀, inv_eq_of_mul_eq_one_right hK]
      exact β.2
    have hint' : IsIntegral A (algebraMap A K d)⁻¹ :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom A K L) (algebraMap K L).injective).mp hint
    obtain ⟨u, hu⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint'
    have hud : u * d = 1 := by
      apply IsFractionRing.injective A K
      rw [map_mul, hu, map_one, inv_mul_cancel₀ hd0]
    rw [hd, ← hud]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self d)
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp hspan
  refine ⟨∑ i, algebraMap A K (a i) • bL.coord i, ?_, ?_⟩
  · have h1 : (1 : L) = algebraMap (integralClosure A L) L 1 := (map_one _).symm
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.Basis.coord_apply,
      smul_eq_mul]
    rw [h1]
    simp only [hrepr]
    rw [← map_one (algebraMap A K), ← ha, map_sum]
    simp only [map_mul]
  · intro x hx
    set z : integralClosure A L := ⟨x, show x ∈ integralClosure A L from hx⟩ with hz
    have hx' : x = algebraMap (integralClosure A L) L z := rfl
    refine ⟨∑ i, a i * b.repr z i, ?_⟩
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.Basis.coord_apply,
      smul_eq_mul]
    rw [hx']
    simp only [hrepr]
    rw [map_sum]
    simp only [map_mul]

theorem exists_retraction_closure (R F K L : Type) [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [Field K] [Algebra F K] [Algebra R K] [IsScalarTower R F K] [FiniteDimensional F K]
    [IsPrincipalIdealRing (integralClosure R K)]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    ∃ r : L →ₗ[K] K, r 1 = 1 ∧ ∀ x : L, IsIntegral R x → IsIntegral R (r x) := by
  have : IsScalarTower (integralClosure R K) K L := inferInstance
  have : IsFractionRing (integralClosure R K) K :=
    integralClosure.isFractionRing_of_finite_extension F K
  have : IsScalarTower R (integralClosure R K) L := IsScalarTower.of_algebraMap_eq fun y => by
    rw [IsScalarTower.algebraMap_apply R K L, IsScalarTower.algebraMap_apply (integralClosure R K) K L]
    rfl
  obtain ⟨r, hr1, hr⟩ := exists_retraction (integralClosure R K) K L
  refine ⟨r, hr1, fun x hx => ?_⟩
  obtain ⟨a, ha⟩ := hr x (hx.tower_top)
  rw [← ha]
  exact a.2

theorem exists_integral_retraction : ∀ (l : ℕ) [Fact l.Prime] (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1),
    ∃ r : ↥LL'.1 →ₗ[ℚ_[l]] ↥LL.1, (∀ a x, r (incl hL a * x) = a * r x) ∧ r 1 = 1 ∧
      (∀ x ∈ OL LL', r x ∈ OL LL) := by
  intro l _ LL LL' hL
  letI : Algebra ↥LL.1 ↥LL'.1 := (incl hL).toRingHom.toAlgebra
  have hmap : ∀ y : ↥LL.1, algebraMap ↥LL.1 ↥LL'.1 y = incl hL y := fun _ => rfl
  have : IsScalarTower ℚ_[l] ↥LL.1 ↥LL'.1 := IsScalarTower.of_algebraMap_eq fun q => by
    rw [hmap, AlgHom.commutes]
  have : IsScalarTower ℤ_[l] ↥LL.1 ↥LL'.1 := IsScalarTower.of_algebraMap_eq fun z => by
    rw [hmap, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1,
      IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL'.1, AlgHom.commutes]
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have : FiniteDimensional ℚ_[l] ↥LL'.1 := LL'.2
  have : FiniteDimensional ↥LL.1 ↥LL'.1 := FiniteDimensional.right ℚ_[l] ↥LL.1 ↥LL'.1
  have : IsPrincipalIdealRing (integralClosure ℤ_[l] ↥LL.1) := by
    obtain ⟨h, -⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
    exact h.toIsPrincipalIdealRing
  obtain ⟨r, hr1, hr⟩ := exists_retraction_closure ℤ_[l] ℚ_[l] ↥LL.1 ↥LL'.1
  refine ⟨r.restrictScalars ℚ_[l], fun a x => ?_, hr1, fun x hx => hr x hx⟩
  rw [LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply, ← hmap, ← Algebra.smul_def,
    LinearMap.map_smul, smul_eq_mul]

end GlobalTheory.CoefRetraction
