import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.LogLeExp
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.TorsBoundPow

open NumberField

namespace UpperTheory.V.KH

theorem torsBound_of (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ (L : Type) [Field L] [NumberField L], IsTotallyComplex L → ∀ e : ℕ, 1 ≤ e →
      ∃ A s : ℕ, 1 ≤ s ∧
        (A : ℝ) ≤ K.tBound c (2 * e) (4 * e + 4) (Module.finrank ℚ L) (discr L).natAbs ∧
        (s : ℝ) ≤ Real.exp (c * ((Module.finrank ℚ L : ℝ) * ((4 * e + 4 : ℕ) : ℝ)) ^ 2) ∧
        TorsLe (K.HGL L (4 * e + 4) (2 * e)) (bound (2 * e) A s (2 * e + 2))) :
    K.TorsBound (2 * c + 1) := by
  intro L _ _ hL e he
  obtain ⟨A, s, hs, hA, hσ, hT⟩ := h L hL e he
  refine ⟨hT.1, (hT.log_le_exp hs hA hσ).trans ?_⟩
  unfold K.tBound
  rw [Real.exp_le_exp]
  have hn : (1 : ℝ) ≤ (Module.finrank ℚ L : ℝ) := by exact_mod_cast Module.finrank_pos
  have hD : (1 : ℝ) ≤ ((discr L).natAbs : ℝ) := by
    exact_mod_cast Int.natAbs_pos.2 (discr_ne_zero L)
  have hN : (8 : ℝ) ≤ ((4 * e + 4 : ℕ) : ℝ) := by exact_mod_cast (by omega : 8 ≤ 4 * e + 4)
  have hm : (1 : ℝ) ≤ ((2 * e : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * e)
  generalize ((2 * e : ℕ) : ℝ) = m at *
  generalize ((4 * e + 4 : ℕ) : ℝ) = N at *
  generalize (((discr L).natAbs : ℕ) : ℝ) = D at *
  generalize (Module.finrank ℚ L : ℝ) = n at *
  have hd : 8 ≤ n * N := by nlinarith
  generalize n * N = d at *
  have hlog : 1 ≤ Real.log (2 * D * d) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    nlinarith
  generalize Real.log (2 * D * d) = l at *
  have h1 : 2 ≤ d * N * l := by
    have : 64 ≤ d * N := by nlinarith
    nlinarith
  have h2 : 1 ≤ d ^ 2 := by nlinarith
  have h3 : m * d ^ 2 * 2 ≤ m * d ^ 2 * (d * N * l) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h4 : (m + 1) * d ^ 2 ≤ m * d ^ 2 * 2 := by nlinarith
  have h5 : 2 * m ≤ m * d ^ 2 * 2 := by nlinarith
  have h6 := mul_le_mul_of_nonneg_left (h4.trans h3) hc
  nlinarith

end UpperTheory.V.KH
