import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLogSpanTraceZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitPowerInOrderStatement
open NumberField

namespace GlobalTheory.UnitSpan

theorem injective_of_finite (K : Type) [CommRing K] [IsDomain K] [Module.Finite ℤ K]
    (τ : K →+* ℂ) : Function.Injective τ := by
  haveI : Algebra.IsIntegral ℤ K := Algebra.IsIntegral.of_finite ℤ K
  rw [injective_iff_map_eq_zero]
  have hk : RingHom.ker τ = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    rw [RingHom.comap_ker]
    have : τ.comp (algebraMap ℤ K) = Int.castRingHom ℂ := RingHom.ext_int _ _
    rw [this]
    exact (RingHom.injective_iff_ker_eq_bot _).mp Int.cast_injective
  intro a ha
  have : a ∈ RingHom.ker τ := ha
  rw [hk] at this
  exact this

theorem numberField_fractionRing (K : Type) [CommRing K] [IsDomain K] [CharZero K] [Module.Finite ℤ K] :
    NumberField (FractionRing K) := by
  haveI : @IsScalarTower ℤ ℚ (FractionRing K) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq (fun x => by rw [eq_intCast (algebraMap ℤ ℚ), map_intCast, eq_intCast])
  haveI : FiniteDimensional ℚ (FractionRing K) := Module.Finite.of_isLocalization ℤ K (nonZeroDivisors ℤ)
  exact {}

theorem span_log_units : ∀ (K : Type) [CommRing K] [IsDomain K] [CharZero K] [Module.Finite ℤ K] (c : (K →+* ℂ) → ℝ),
    (∀ τ, c ((starRingEnd ℂ).comp τ) = c τ) → ∑ᶠ τ, c τ = 0 →
    ∃ (m : ℕ) (a : Fin m → Kˣ) (r : Fin m → ℝ), ∀ τ, c τ = ∑ j, r j * Real.log (‖τ (a j : K)‖ ^ 2) := by
  intro K _ _ _ _ c hc hs
  haveI := numberField_fractionRing K
  let F := FractionRing K
  let ρ : (F →+* ℂ) → (K →+* ℂ) := fun σ => σ.comp (algebraMap K F)
  have hρ : Function.Bijective ρ := by
    constructor
    · intro σ₁ σ₂ h
      exact IsFractionRing.ringHom_ext (A := K) (K := F) fun x => RingHom.congr_fun h x
    · intro τ
      refine ⟨IsFractionRing.lift (A := K) (K := F) (injective_of_finite K τ), ?_⟩
      ext x
      exact IsFractionRing.lift_algebraMap (A := K) (K := F) (injective_of_finite K τ) x
  let e := Equiv.ofBijective ρ hρ
  have hs' : ∑ σ, c (ρ σ) = 0 := by
    rw [← finsum_eq_sum_of_fintype, ← hs]
    exact finsum_comp_equiv e
  obtain ⟨m, u, r, h⟩ := GlobalTheory.T.unit_log_span_trace_zero F (fun σ => c (ρ σ)) (fun σ => hc (ρ σ)) hs'
  choose k hk a ha using fun j => GlobalTheory.T.unit_power_in_order K F (u j)
  refine ⟨m, a, fun j => r j / k j, fun τ => ?_⟩
  obtain ⟨σ, rfl⟩ := hρ.2 τ
  rw [h σ]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : ρ σ (a j : K) = σ ((u j : 𝓞 F) : F) ^ k j := by
    show σ (algebraMap K F (a j : K)) = _
    rw [ha j, map_pow]
  rw [this, norm_pow, ← pow_mul, mul_comm (k j) 2, pow_mul, Real.log_pow (‖σ ((u j : 𝓞 F) : F)‖ ^ 2) (k j)]
  have : (k j : ℝ) ≠ 0 := by exact_mod_cast (hk j).ne'
  field_simp

end GlobalTheory.UnitSpan
