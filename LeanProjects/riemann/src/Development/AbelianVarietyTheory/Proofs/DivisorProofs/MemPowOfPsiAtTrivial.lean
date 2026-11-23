import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocKCongr
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.GaussModulus

namespace GlobalTheory.GaussModulus

theorem mem_pow_of_psiAt_trivial {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) (c : Eˣ)
    (hc : w.valuation E (c : E) = WithZero.exp (-((a + diffExp w : ℕ) : ℤ))) (δ : 𝓞 E)
    (hδ : ∀ r : 𝓞 E, psiAt w (algebraMap E (w.adicCompletion E) ((δ : E) * r / c)) = 1) : δ ∈ w.asIdeal ^ a := by
  set t : w.adicCompletion E := algebraMap E (w.adicCompletion E) ((δ : E) / c) with ht
  have hc0 : w.valuation E (c : E) ≠ 0 := by rw [hc]; exact WithZero.exp_ne_zero
  have hδ1 : w.valuation E (δ : E) ≤ 1 := w.valuation_le_one δ
  have hvt : Valued.v t ≤ WithZero.exp (((a + diffExp w : ℕ) : ℤ)) := by
    rw [ht, valued_algebraMap, map_div₀, hc, div_le_iff₀ (zero_lt_iff.2 WithZero.exp_ne_zero), ← WithZero.exp_add]
    simpa using hδ1
  have key : ∀ s ∈ w.adicCompletionIntegers E, psiAt w (t * s) = 1 := by
    intro s hs
    have hs1 : Valued.v s ≤ 1 := hs
    obtain ⟨r, hr⟩ := exists_int_approx w hs1 (a + diffExp w)
    have e : t * s = algebraMap E (w.adicCompletion E) ((δ : E) * r / c) +
        t * (s - algebraMap E (w.adicCompletion E) (r : E)) := by
      have ha : algebraMap E (w.adicCompletion E) ((δ : E) * r / c) =
          algebraMap E (w.adicCompletion E) ((δ : E) / c) * algebraMap E (w.adicCompletion E) (r : E) := by
        rw [← (algebraMap E (w.adicCompletion E)).map_mul]; congr 1; ring
      rw [ha, ht]
      ring
    rw [e, psiAt_add, hδ r, one_mul]
    refine psiAt_eq_one ?_
    rw [map_mul]
    calc Valued.v t * Valued.v (s - algebraMap E (w.adicCompletion E) (r : E))
        ≤ WithZero.exp (((a + diffExp w : ℕ) : ℤ)) * WithZero.exp (-((a + diffExp w : ℕ) : ℤ)) :=
          mul_le_mul' hvt hr
      _ = 1 := by rw [← WithZero.exp_add]; simp
      _ ≤ WithZero.exp (diffExp w : ℤ) := by
          rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  have hvt' := (psiAt_conductor w t).1 key
  rw [ht, valued_algebraMap, map_div₀, hc, div_le_iff₀ (zero_lt_iff.2 WithZero.exp_ne_zero), ← WithZero.exp_add] at hvt'
  have h2 : w.valuation E (δ : E) ≤ WithZero.exp (-(a : ℤ)) := by
    refine hvt'.trans (le_of_eq ?_)
    congr 1
    push_cast
    ring
  rw [w.valuation_of_algebraMap] at h2
  exact (w.intValuation_le_pow_iff_mem δ a).1 (by simpa using h2)

end GlobalTheory.GaussModulus
