import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralityFromPadicNormBound
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsEmbeddingPadicAlgClPlace
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.IntAwayP

theorem norm_self_padicAlgCl (p : ℕ) [Fact p.Prime] : ‖(p : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
  have := PadicAlgCl.norm_extends p (p : ℚ_[p])
  rw [map_natCast] at this
  rw [this, Padic.norm_p]

theorem norm_prime_padicAlgCl_of_ne (ℓ p : ℕ) [hℓ : Fact ℓ.Prime] (hp : p.Prime) (h : ℓ ≠ p) :
    ‖(p : PadicAlgCl ℓ)‖ = 1 := by
  have h1 := PadicAlgCl.norm_extends ℓ (p : ℚ_[ℓ])
  rw [map_natCast] at h1
  rw [h1]
  have h2 : ‖(p : ℤ_[ℓ])‖ = 1 := (PadicInt.norm_natCast_eq_one_iff).2 ((Nat.coprime_primes hℓ.out hp).2 h)
  rw [← h2, PadicInt.norm_def]
  simp

theorem isIntegral_of_pow_mul (K : Type) [Field K] [NumberField K] (p : ℕ) [hp : Fact p.Prime]
    (z : K) (N : ℕ) (hN : IsIntegral ℤ ((p : K) ^ N * z))
    (h : ∀ φ : K →+* PadicAlgCl p, ‖φ z‖ ≤ 1) : IsIntegral ℤ z := by
  refine GlobalTheory.isIntegral_of_forall_padicAlgCl_norm_le_one K z fun q _ τ => ?_
  by_cases hq : q = p
  · subst hq; exact h τ
  · have h1 : ‖τ ((p : K) ^ N * z)‖ ≤ 1 :=
      GlobalTheory.norm_le_one_of_isIntegral_int (hN.map τ.toIntAlgHom)
    rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow,
      norm_prime_padicAlgCl_of_ne q p hp.out hq, one_pow, one_mul] at h1
    exact h1

theorem exists_pow_mul_isIntegral : ∀ (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] (B : ℝ), ∃ m₀ : ℕ, ∀ (c : K) (D : ℕ), (∃ m : ℕ, IsIntegral ℤ ((p : K) ^ m * D * c)) → (∀ φ : K →+* PadicAlgCl p, ‖φ c‖ ≤ B) → IsIntegral ℤ ((p : K) ^ m₀ * D * c) := by
  intro K _ _ p _ B
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨m₀, hm₀⟩ := pow_unbounded_of_one_lt B hp1
  refine ⟨m₀, fun c D ⟨m, hm⟩ hB => ?_⟩
  apply isIntegral_of_pow_mul K p _ m
  · have e : (p : K) ^ m * ((p : K) ^ m₀ * D * c) = (p : K) ^ m₀ * ((p : K) ^ m * D * c) := by ring
    rw [e]
    have hpi : IsIntegral ℤ ((p : K) ^ m₀) := by
      simpa using (isIntegral_algebraMap (R := ℤ) (A := K) (x := (p : ℤ))).pow m₀
    exact hpi.mul hm
  · intro φ
    rw [map_mul, map_mul, map_pow, map_natCast, map_natCast, norm_mul, norm_mul, norm_pow,
      norm_self_padicAlgCl]
    have hD := IsUltrametricDist.norm_natCast_le_one (PadicAlgCl p) D
    have h2 : ‖(D : PadicAlgCl p)‖ * ‖φ c‖ ≤ (p : ℝ) ^ m₀ :=
      (mul_le_of_le_one_left (norm_nonneg _) hD).trans ((hB φ).trans hm₀.le)
    rw [mul_assoc, inv_pow, inv_mul_le_iff₀ (by positivity), mul_one]
    exact h2

end GlobalTheory.IntAwayP
