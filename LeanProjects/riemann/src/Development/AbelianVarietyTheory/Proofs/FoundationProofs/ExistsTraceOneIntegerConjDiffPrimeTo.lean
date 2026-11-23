import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.TraceOne

theorem exists_of_sq (D : D7) (q n : ℕ) (hn : n % 4 = 3) (hc : Nat.Coprime q n) (b : D.host.E)
    (hb : b ^ 2 = -(n : D.host.E)) :
    ∃ w : 𝓞 D.host.E, w + sgO D w = 1 ∧
      ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → (q : 𝓞 D.host.E) ∈ P → w - sgO D w ∉ P := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, n + 1 = 4 * m := ⟨(n + 1) / 4, by omega⟩
  have hm' : (n : D.host.E) + 1 = 4 * (m : D.host.E) := by exact_mod_cast hm
  have hint : IsIntegral ℤ ((1 + b) / 2) := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℤ), ?_, ?_⟩
    · monicity!
    · rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C, map_natCast]
      linear_combination (1 / 4 : D.host.E) * hb - (1 / 4 : D.host.E) * hm'
  have hconj : D.host.conj b = -b := by
    apply D.host.φ₀.injective
    have h1 : D.host.φ₀ (D.host.conj b) = starRingEnd ℂ (D.host.φ₀ b) :=
      D.host.conjE_apply D.host.φ₀ b
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have h2 : (D.host.φ₀ b) ^ 2 = (Complex.I * (Real.sqrt n : ℂ)) ^ 2 := by
      rw [← map_pow, hb, map_neg, map_natCast, mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
        Real.sq_sqrt hn0]
      simp
    rw [h1, map_neg]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h <;> rw [h] <;> simp
  have hcw : D.host.conj ((1 + b) / 2) = (1 - b) / 2 := by
    rw [map_div₀, map_add, map_one, map_ofNat, hconj, sub_eq_add_neg]
  let w : 𝓞 D.host.E := ⟨(1 + b) / 2, hint⟩
  have hw : (w : D.host.E) = (1 + b) / 2 := rfl
  have hs : ((sgO D w : 𝓞 D.host.E) : D.host.E) = (1 - b) / 2 := by rw [sgO_coe, hw, hcw]
  refine ⟨w, ?_, fun P hP hq hmem => ?_⟩
  · apply RingOfIntegers.coe_injective
    rw [map_add, map_one]
    change (w : D.host.E) + ((sgO D w : 𝓞 D.host.E) : D.host.E) = 1
    rw [hw, hs]; ring
  · have hsq : (w - sgO D w) * -(w - sgO D w) = (n : 𝓞 D.host.E) := by
      apply RingOfIntegers.coe_injective
      rw [map_mul, map_neg, map_sub, map_natCast]
      change ((w : D.host.E) - ((sgO D w : 𝓞 D.host.E) : D.host.E)) *
        -((w : D.host.E) - ((sgO D w : 𝓞 D.host.E) : D.host.E)) = _
      rw [hw, hs]
      linear_combination (-1 : D.host.E) * hb
    have hnP : (n : 𝓞 D.host.E) ∈ P := hsq ▸ P.mul_mem_right _ hmem
    obtain ⟨u, v, huv⟩ : IsCoprime (q : 𝓞 D.host.E) (n : 𝓞 D.host.E) := hc.cast
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2
      (huv ▸ P.add_mem (P.mul_mem_left u hq) (P.mul_mem_left v hnP)))

theorem exists_trace_one : ∀ (D : D7) (q : ℕ), q.Prime → ∃ w : 𝓞 D.host.E, w + sgO D w = 1 ∧
    ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → (q : 𝓞 D.host.E) ∈ P → w - sgO D w ∉ P := by
  intro D q hq
  obtain ⟨hq₁, hd, hq8, hd16, -⟩ := D.host.hyp
  by_cases h : q = D.host.d
  · refine exists_of_sq D q D.host.q (by omega) ((Nat.coprime_primes hq hq₁).2 (by omega))
      (D.host.sqq) D.host.sqq_sq
  · exact exists_of_sq D q D.host.d (by omega) ((Nat.coprime_primes hq hd).2 h)
      (D.host.sqd) (D.host.sqd_sq)

end GlobalTheory.TraceOne
