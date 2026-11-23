import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedLaurentIsDVRStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedIntegersAdicComplete
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAbsoluteValueCompleteSpaceOfDvr
open GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.K5

open Polynomial

theorem exists_valuation_pow_eq (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (f : AbsoluteValue K ℝ) (hna : IsNonarchimedean f)
    (hnt : f.IsNontrivial) (hc : CompleteSpace (WithAbs f)) :
    ∃ v : Valuation Ω ℝ≥0, (∀ x : K, (v (algebraMap K Ω x) : ℝ) = f x) ∧
      (∀ x : Ω, v x ≤ 1 ↔ ∀ i, f ((minpoly K x).coeff i) ≤ 1) ∧
      ∀ x : Ω, (v x : ℝ) ^ (minpoly K x).natDegree = f ((minpoly K x).coeff 0) := by
  obtain ⟨a, ha⟩ := hnt.exists_abv_gt_one
  letI : NontriviallyNormedField (WithAbs f) :=
    NontriviallyNormedField.ofNormNeOne ⟨WithAbs.toAbs f a, by
      intro h; rw [WithAbs.toAbs_eq_zero] at h; rw [h, map_zero] at ha; linarith, by
      rw [WithAbs.norm_toAbs_eq]; exact ha.ne'⟩
  haveI : IsUltrametricDist (WithAbs f) :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm fun x y => hna x.ofAbs y.ofAbs
  haveI : IsScalarTower K (WithAbs f) Ω := inferInstance
  haveI : Algebra.IsAlgebraic (WithAbs f) Ω := Algebra.IsAlgebraic.tower_top (K := K) (WithAbs f)
  have hmin : ∀ x : Ω, minpoly (WithAbs f) x = (minpoly K x).map (algebraMap K (WithAbs f)) := by
    intro x
    have hx : IsIntegral K x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    have hmap : (minpoly K x).map (algebraMap K (WithAbs f)) =
        Polynomial.mapEquiv (WithAbs.equiv f).symm (minpoly K x) := by
      rw [Polynomial.mapEquiv_apply]; rfl
    symm
    apply minpoly.eq_of_irreducible_of_monic
    · rw [hmap]; exact (MulEquiv.irreducible_iff _).mpr (minpoly.irreducible hx)
    · rw [Polynomial.aeval_map_algebraMap]; exact minpoly.aeval K x
    · exact (minpoly.monic hx).map _
  let v : Valuation Ω ℝ≥0 :=
    { toFun := fun x => ⟨spectralNorm (WithAbs f) Ω x, spectralNorm_nonneg x⟩
      map_zero' := by ext; exact spectralNorm_zero
      map_one' := by ext; exact spectralNorm_one
      map_mul' := fun x y => by
        ext; exact spectralAlgNorm_mul (K := WithAbs f) (L := Ω) x y
      map_add_le_max' := fun x y => by
        show spectralNorm (WithAbs f) Ω (x + y) ≤
          max (spectralNorm (WithAbs f) Ω x) (spectralNorm (WithAbs f) Ω y)
        exact isNonarchimedean_spectralNorm x y }
  have hv : ∀ x : Ω, (v x : ℝ) = spectralNorm (WithAbs f) Ω x := fun _ => rfl
  have hco : ∀ (x : Ω) (i : ℕ), ‖(minpoly (WithAbs f) x).coeff i‖ = f ((minpoly K x).coeff i) := by
    intro x i
    rw [hmin x, Polynomial.coeff_map, WithAbs.algebraMap_right_apply, WithAbs.norm_toAbs_eq]
    rfl
  refine ⟨v, fun x => ?_, fun x => ?_, fun x => ?_⟩
  · rw [hv]
    have : algebraMap K Ω x = algebraMap (WithAbs f) Ω (WithAbs.toAbs f x) := rfl
    rw [this, spectralNorm_extends, WithAbs.norm_toAbs_eq]
  · have hx : IsIntegral (WithAbs f) x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    rw [← NNReal.coe_le_coe, NNReal.coe_one, hv]
    show spectralValue (minpoly (WithAbs f) x) ≤ 1 ↔ _
    rw [spectralValue_le_one_iff (minpoly.monic hx)]
    exact forall_congr' fun i => by rw [hco]
  · have hx : IsIntegral K x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    have hd : (minpoly (WithAbs f) x).natDegree = (minpoly K x).natDegree := by
      rw [hmin x, (minpoly.monic hx).natDegree_map]
    rw [hv, spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow (WithAbs f) Ω x, hco, hd, one_div]
    exact Real.rpow_inv_natCast_pow (f.nonneg _) (minpoly.natDegree_pos hx).ne'

theorem exists_pow_div_zpow_isIntegral (R K Ω : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Field K]
    [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
    [Algebra.IsAlgebraic K Ω] (π : R) (hπ : Irreducible π) (x : Ω) (hx : x ≠ 0) :
    ∃ (a : ℤ) (b : ℕ), 0 < b ∧ IsIntegral R (x ^ b / (algebraMap R Ω π) ^ a) ∧
      IsIntegral R ((algebraMap R Ω π) ^ a / x ^ b) := by
  obtain ⟨f, hna, hnt, hball, hc⟩ :=
    GlobalTheory.KLC.exists_absoluteValue_completeSpace_of_isDiscreteValuationRing R K
  obtain ⟨v, hext, hle, hpow⟩ := exists_valuation_pow_eq K Ω f hna hnt hc
  have hint : ∀ z : Ω, v z ≤ 1 → IsIntegral R z := by
    intro z hz
    have hzK : IsIntegral K z := (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
    have hl : minpoly K z ∈ Polynomial.lifts (algebraMap R K) :=
      (Polynomial.lifts_iff_coeff_lifts _).2 fun i => (hball _).1 ((hle z).1 hz i)
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (minpoly.monic hzK)
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap K, hq, minpoly.aeval]
  have hR : ∀ r : R, v (algebraMap R Ω r) ≤ 1 := by
    intro r
    rw [IsScalarTower.algebraMap_apply R K Ω, ← NNReal.coe_le_coe, hext]
    exact (hball _).2 ⟨r, rfl⟩
  have hU : ∀ u : Rˣ, v (algebraMap R Ω u) = 1 := by
    intro u
    have h1 : v (algebraMap R Ω u) * v (algebraMap R Ω (u⁻¹ : Rˣ)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    refine le_antisymm (hR _) ?_
    calc 1 = _ := h1.symm
      _ ≤ v (algebraMap R Ω u) * 1 := by gcongr; exact hR _
      _ = _ := mul_one _
  have hxK : IsIntegral K x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hinj : Function.Injective (algebraMap R Ω) := by
    rw [IsScalarTower.algebraMap_eq R K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective R K)
  have hπ0 : v (algebraMap R Ω π) ≠ 0 :=
    (map_ne_zero v).2 ((map_ne_zero_iff _ hinj).2 hπ.ne_zero)
  have hc0 : (minpoly K x).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hxK hx
  obtain ⟨r, s, hs, hrs⟩ := IsFractionRing.div_surjective (A := R) ((minpoly K x).coeff 0)
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hc0 (by rw [← hrs]; simp)
  obtain ⟨i, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr0 hπ
  obtain ⟨j, w, rfl⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hs) hπ
  have key : v (x ^ (minpoly K x).natDegree) = v (algebraMap R Ω π ^ ((i : ℤ) - j)) := by
    have h1 : v x ^ (minpoly K x).natDegree = v (algebraMap K Ω ((minpoly K x).coeff 0)) := by
      apply NNReal.coe_injective
      rw [NNReal.coe_pow, hpow, hext]
    rw [map_pow, h1, ← hrs, map_div₀, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply, map_zpow₀, zpow_sub₀ hπ0]
    simp [hU]
  have hx0 : v (x ^ (minpoly K x).natDegree) ≠ 0 := (map_ne_zero v).2 (pow_ne_zero _ hx)
  refine ⟨(i : ℤ) - j, (minpoly K x).natDegree, minpoly.natDegree_pos hxK, hint _ ?_, hint _ ?_⟩
  · rw [map_div₀, ← key, div_self hx0]
  · rw [map_div₀, ← key, div_self hx0]

theorem exists_pow_div_p_zpow_isInt : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ x : Ω, x ≠ 0 → ∃ (a : ℤ) (b : ℕ), 0 < b ∧ IsInt p (x ^ b / (p : Ω) ^ a) ∧
    IsInt p ((p : Ω) ^ a / x ^ b) := by
  intro p _ Ω _ _ hΩ x hx
  obtain ⟨hdom, hdvr, hirr⟩ := completed_laurent_isDVR p
  have hmax : IsLocalRing.maximalIdeal (O0 p) = Ideal.span {(p : O0 p)} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hirr
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal (O0 p)) (O0 p) := by
    rw [hmax]; exact o0_isAdicComplete_span_p p
  haveI : FaithfulSMul (O0 p) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 hΩ.inj
  letI : Algebra (FractionRing (O0 p)) Ω := FractionRing.liftAlgebra (O0 p) Ω
  haveI : IsScalarTower (O0 p) (FractionRing (O0 p)) Ω :=
    FractionRing.isScalarTower_liftAlgebra (O0 p) Ω
  haveI : Algebra.IsAlgebraic (O0 p) Ω := hΩ.alg
  haveI : Algebra.IsAlgebraic (FractionRing (O0 p)) Ω :=
    Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective (O0 p) (FractionRing (O0 p)))
  have := exists_pow_div_zpow_isIntegral (O0 p) (FractionRing (O0 p)) Ω (p : O0 p) hirr x hx
  rwa [map_natCast] at this

end GlobalTheory.K5
