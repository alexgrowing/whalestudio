import Mathlib
import Formalism.QuotientMetricDivisors.ScalarLiftLowerBoundRows
import Formalism.LogFactorialBounds.LogFactorialProofs.PrimeSum
import Formalism.LogFactorialIndices.SignedSubspaceIndex.LogProductFormula

open Finset NumberField IsDedekindDomain

noncomputable section

namespace Formalism.DivisionValues

namespace place_log_sum

lemma mean_le {E : Type} [Fintype E] [Nonempty E] (u : E → ℝ) (B : ℝ) (h : ∀ s, u s ≤ B) :
    (∑ s, u s) / (Fintype.card E : ℝ) ≤ B := by
  have hc : (0 : ℝ) < (Fintype.card E : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hc]
  calc ∑ s, u s ≤ ∑ _s : E, B := Finset.sum_le_sum fun s _ => h s
    _ = B * (Fintype.card E : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end place_log_sum

theorem WeightedPlaceLogSum : LPrimeBound := by
  intro x L b a rd La g nV L' Cg Cn hx hL hb ha hrd hLa hg hlg hnV hlnV hCg hCn hL'
  have hx0 : 0 < x := by linarith
  have hrd0 : 0 < rd := by linarith
  have hb0 : 0 < b := by rw [hb]; exact Real.exp_pos L
  have hlb : Real.log b = L := by rw [hb, Real.log_exp]
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlrd : 0 ≤ Real.log rd := Real.log_nonneg hrd
  have e1 : La = Real.log x + L + Real.log rd := by
    rw [hLa, ha, Real.log_mul (mul_pos hx0 hb0).ne' hrd0.ne', Real.log_mul hx0.ne' hb0.ne', hlb]
  have e2 : L' = L + Real.log rd + Real.log g + Real.log nV := by
    rw [hL', Real.log_mul (mul_pos (mul_pos hb0 hrd0) hg).ne' hnV.ne',
      Real.log_mul (mul_pos hb0 hrd0).ne' hg.ne', Real.log_mul hb0.ne' hrd0.ne', hlb]
  refine ⟨?_, by linarith⟩
  rw [e1, e2]
  nlinarith [mul_nonneg hCg hlx, mul_nonneg hCg hlrd, mul_nonneg hCn hL, mul_nonneg hCn hlrd]

theorem prime_log_sum_bound : PrimeLogSum := by
  intro Y hY s hs
  have hn : 1 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast hY)
  have hnR : (0 : ℝ) < (⌊Y⌋₊ : ℝ) := by exact_mod_cast hn
  have hfl : (⌊Y⌋₊ : ℝ) ≤ Y := Nat.floor_le (by linarith)
  calc ∑ p ∈ s, Real.log (p : ℝ) / (p : ℝ)
      ≤ ∑ p ∈ Nat.primesLE ⌊Y⌋₊, Real.log (p : ℝ) / (p : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          exact Nat.mem_primesLE.2 ⟨Nat.le_floor (hs p hp).2, (hs p hp).1⟩
        · intro p _ _
          exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
    _ ≤ Real.log (⌊Y⌋₊ : ℝ) + Real.log 4 := Formalism.LogFactorialBounds.sum_primesLE_log_div_le _ hn
    _ ≤ Real.log Y + Real.log 4 := by
        have := Real.log_le_log hnR hfl
        linarith

namespace place_log_sum

lemma lw_nonneg {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) : 0 ≤ lw w :=
  div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)

lemma vw_nat_nonneg {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    0 ≤ vw w (n : K) := by
  have h : ((n : 𝓞 K) : K) = (n : K) := map_natCast _ n
  unfold vw
  rw [← h, ← FractionalIdeal.coeIdeal_span_singleton]
  exact FractionalIdeal.count_coe_nonneg K w _

end place_log_sum

namespace place_log_sum

end place_log_sum

end Formalism.DivisionValues
