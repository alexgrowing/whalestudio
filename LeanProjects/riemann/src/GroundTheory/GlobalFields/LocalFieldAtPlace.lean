import Mathlib
import GroundTheory.GlobalFields.LocalAtPlace

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField WithZero

open scoped WithZero

namespace GroundTheory.Global

section Discrete

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

theorem isDiscreteValuationRing_adicCompletionIntegers :
    IsDiscreteValuationRing (v.adicCompletionIntegers K) :=
  inferInstance

theorem valued_adicCompletion_surjective :
    Function.Surjective (Valued.v : v.adicCompletion K → ℤᵐ⁰) :=
  valuedAdicCompletion_surjective K v

theorem valued_of_irreducible {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) :
    Valued.v (ϖ : v.adicCompletion K) = exp (-1 : ℤ) := by
  have h : Valuation.IsUniformizer (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
      (ϖ : v.adicCompletion K) :=
    Valuation.isUniformizer_of_maximalIdeal_eq_span Valued.v
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ)
  rw [h.val, Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
    (valuedAdicCompletion_surjective K v)]
  rfl

end Discrete

section AbsoluteValue

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

noncomputable def normalizedAbv : AbsoluteValue (v.adicCompletion K) ℝ where
  toFun x := ‖x‖
  map_mul' := norm_mul
  nonneg' := norm_nonneg
  eq_zero' _ := norm_eq_zero
  add_le' := norm_add_le

theorem normalizedAbv_apply (x : v.adicCompletion K) : normalizedAbv v x = ‖x‖ :=
  rfl

theorem normalizedAbv_eq_toNNReal (x : v.adicCompletion K) :
    normalizedAbv v x = WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (Valued.v x) :=
  FinitePlace.norm_def v x

theorem normalizedAbv_eq_zpow {x : v.adicCompletion K} (hx : x ≠ 0) :
    normalizedAbv v x = (Ideal.absNorm v.asIdeal : ℝ) ^ log (Valued.v x) := by
  have hx' : Valued.v x ≠ 0 := (Valued.v).ne_zero_iff.2 hx
  have key : ∀ (y : ℤᵐ⁰) (hy : y ≠ 0), Multiplicative.toAdd (unzero hy) = log y := by
    rintro (_ | a) hy
    · exact absurd rfl hy
    · rfl
  rw [normalizedAbv_eq_toNNReal, WithZeroMulInt.toNNReal_neg_apply _ hx', key]
  simp

theorem normalizedAbv_of_irreducible {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) :
    normalizedAbv v (ϖ : v.adicCompletion K) = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  have h0 : (ϖ : v.adicCompletion K) ≠ 0 := by
    intro h
    exact hϖ.ne_zero (Subtype.ext h)
  rw [normalizedAbv_eq_zpow v h0, valued_of_irreducible v hϖ, log_exp, zpow_neg_one]

end AbsoluteValue

section LocalField

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

noncomputable instance : ValuativeRel (v.adicCompletion K) :=
  .ofValuation Valued.v

instance : (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).Compatible :=
  .ofValuation _

instance : IsValuativeTopology (v.adicCompletion K) :=
  IsValuativeTopology.of_mem_nhds_iff_vle Valued.v Valued.mem_nhds

instance : ValuativeRel.IsNontrivial (v.adicCompletion K) :=
  (ValuativeRel.isNontrivial_iff_isNontrivial Valued.v).2 inferInstance

end LocalField

section Bridge

open ValuativeRel

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

theorem mem_valuationInteger_iff (x : v.adicCompletion K) :
    x ∈ 𝒪[v.adicCompletion K] ↔ x ∈ v.adicCompletionIntegers K := by
  rw [Valuation.mem_integer_iff, mem_adicCompletionIntegers,
    (ValuativeRel.isEquiv (ValuativeRel.valuation (v.adicCompletion K)) Valued.v).le_one_iff_le_one]

end Bridge

section NumberField

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

instance : IsNonarchimedeanLocalField (v.adicCompletion K) where

end NumberField

end GroundTheory.Global
