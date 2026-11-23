import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import ReciprocityTheory.ThetaQuasiPeriods.Change
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Integral
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Imports

namespace GlobalTheory.NoetherPrimitive

open Polynomial
open scoped nonZeroDivisors

theorem exists_map_eq_C_mul {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (f : K[X]) :
    ∃ s : R, s ≠ 0 ∧ ∃ g : R[X], g.map (algebraMap R K) = C (algebraMap R K s) * f := by
  obtain ⟨s, hs, h⟩ := IsLocalization.integerNormalization_spec R⁰ f
  refine ⟨s, nonZeroDivisors.ne_zero hs, IsLocalization.integerNormalization R⁰ f, ?_⟩
  rw [h, ← smul_eq_C_mul, algebraMap_smul]

theorem exists_C_mem_span {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (p : R[X]) (hp : (p.map (algebraMap R K)).Separable) :
    ∃ q : R, q ≠ 0 ∧ C q ∈ Ideal.span {p, p.derivative} := by
  obtain ⟨u, v, huv⟩ := hp
  obtain ⟨s, hs, U, hU⟩ := exists_map_eq_C_mul (R := R) u
  obtain ⟨t, ht, V, hV⟩ := exists_map_eq_C_mul (R := R) v
  refine ⟨s * t, mul_ne_zero hs ht, Ideal.mem_span_pair.2 ⟨C t * U, C s * V, ?_⟩⟩
  apply Polynomial.map_injective (algebraMap R K) (IsFractionRing.injective R K)
  rw [derivative_map] at huv
  simp only [Polynomial.map_add, Polynomial.map_mul, map_C, hU, hV, map_mul]
  linear_combination (C (algebraMap R K s) * C (algebraMap R K t)) * huv

theorem exists_common_denominator {R A : Type*} [CommRing R] [IsDomain R] [CommRing A]
    [Algebra R A] [Module.Finite R A] (a : A)
    (h : ∀ b : A, ∃ s : R, s ≠ 0 ∧ ∃ r : R[X], algebraMap R A s * b = aeval a r) :
    ∃ s : R, s ≠ 0 ∧ ∀ b : A, ∃ r : R[X], algebraMap R A s * b = aeval a r := by
  first
  | exact @_root_.GlobalTheory.CommonDenominatorForFinset.exists_common_denominator
  | exact _root_.GlobalTheory.CommonDenominatorForFinset.exists_common_denominator
  | (apply _root_.GlobalTheory.CommonDenominatorForFinset.exists_common_denominator <;> assumption)
  | (intros; apply _root_.GlobalTheory.CommonDenominatorForFinset.exists_common_denominator <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CommonDenominatorForFinset.exists_common_denominator <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CommonDenominatorForFinset.exists_common_denominator ..)

theorem exists_primitive_element_discriminant_multiple (R A K L : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing A] [IsDomain A] [Algebra R A] [FaithfulSMul R A] [Module.Finite R A]
    [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra A L]
    [IsFractionRing A L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R A L] :
    ∃ (a : A) (q : R), q ≠ 0 ∧ C q ∈ Ideal.span {minpoly R a, (minpoly R a).derivative} ∧
      ∀ b : A, ∃ r : R[X], algebraMap R A q * b = aeval a r := by
  haveI : IsLocalization (Algebra.algebraMapSubmonoid A R⁰) L := inferInstance
  haveI : Module.Finite K L := Module.Finite.of_isLocalization R A R⁰
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K L
  obtain ⟨⟨a, ⟨_, t, ht, rfl⟩⟩, hat⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid A R⁰) α
  have ht' : algebraMap R K t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 (nonZeroDivisors.ne_zero ht)
  have hat' : α = algebraMap K L (algebraMap R K t)⁻¹ * algebraMap A L a := by
    simp only at hat
    rw [← hat, ← IsScalarTower.algebraMap_apply R A L, IsScalarTower.algebraMap_apply R K L,
      mul_left_comm, ← map_mul, inv_mul_cancel₀ ht', map_one, mul_one]
  have hint : IsIntegral R a := Algebra.IsIntegral.isIntegral a
  have htop : Algebra.adjoin K {α} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic α), hα, IntermediateField.top_toSubalgebra]
  obtain ⟨q₁, hq₁, h₁⟩ := exists_common_denominator (R := R) a fun b => by
    have hb : algebraMap A L b ∈ Algebra.adjoin K {α} := htop ▸ Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hb
    obtain ⟨f, hf⟩ := hb
    obtain ⟨s, hs, g, hg⟩ := exists_map_eq_C_mul (R := R) (f.comp (C (algebraMap R K t)⁻¹ * X))
    refine ⟨s, hs, g, IsFractionRing.injective A L ?_⟩
    rw [← aeval_algebraMap_apply, ← aeval_map_algebraMap K, hg, map_mul, map_mul, aeval_C,
      aeval_comp, map_mul, aeval_C, aeval_X, ← hat', ← hf, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
    rfl
  obtain ⟨q₂, hq₂, h₂⟩ := exists_C_mem_span (K := K) (minpoly R a) (by
    rw [← minpoly.isIntegrallyClosed_eq_field_fractions K L hint]
    exact Algebra.IsSeparable.isSeparable K _)
  refine ⟨a, q₂ * q₁, mul_ne_zero hq₂ hq₁, ?_, fun b => ?_⟩
  · rw [C_mul]; exact Ideal.mul_mem_right _ _ h₂
  · obtain ⟨r, hr⟩ := h₁ b
    exact ⟨C q₂ * r, by rw [map_mul, map_mul, aeval_C, mul_assoc, hr]⟩

theorem exists_primitive (R A : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CharZero R] [CommRing A] [IsDomain A] [Algebra R A] [FaithfulSMul R A] [Module.Finite R A] :
    ∃ (a : A) (q : R), q ≠ 0 ∧ C q ∈ Ideal.span {minpoly R a, (minpoly R a).derivative} ∧
      ∀ b : A, ∃ r : R[X], algebraMap R A q * b = aeval a r := by
  letI : Algebra (FractionRing R) (FractionRing A) := FractionRing.liftAlgebra R (FractionRing A)
  exact exists_primitive_element_discriminant_multiple R A (FractionRing R) (FractionRing A)

end GlobalTheory.NoetherPrimitive

open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real

theorem GlobalTheory.noetherNormalization_primitive :
    (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A], ∃ (d : ℕ) (j : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A) (a : A) (p : Polynomial (MvPolynomial (Fin d) ℂ)) (q : MvPolynomial (Fin d) ℂ), ringKrullDim A = d ∧ Function.Injective j ∧ j.toRingHom.Finite ∧ p.Monic ∧ Irreducible p ∧ (∀ r : Polynomial (MvPolynomial (Fin d) ℂ), r.eval₂ j.toRingHom a = 0 ↔ p ∣ r) ∧ q ≠ 0 ∧ Polynomial.C q ∈ Ideal.span {p, p.derivative} ∧ ∀ b : A, ∃ r : Polynomial (MvPolynomial (Fin d) ℂ), j q * b = r.eval₂ j.toRingHom a) := by
  intro A _ _ _ _
  obtain ⟨d, j, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg ℂ A
  letI : Algebra (MvPolynomial (Fin d) ℂ) A := j.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin d) ℂ) A := hfin
  have hinj' : Function.Injective (algebraMap (MvPolynomial (Fin d) ℂ) A) := hinj
  haveI : FaithfulSMul (MvPolynomial (Fin d) ℂ) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj'
  obtain ⟨a, q, hq, hq₁, hq₂⟩ := GlobalTheory.NoetherPrimitive.exists_primitive (MvPolynomial (Fin d) ℂ) A
  have hint : IsIntegral (MvPolynomial (Fin d) ℂ) a := Algebra.IsIntegral.isIntegral a
  refine ⟨d, j, a, minpoly _ a, q, ?_, hinj, hfin, minpoly.monic hint, minpoly.irreducible hint,
    fun r => minpoly.isIntegrallyClosed_dvd_iff hint r, hq, hq₁, hq₂⟩
  rw [ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective hinj',
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp
