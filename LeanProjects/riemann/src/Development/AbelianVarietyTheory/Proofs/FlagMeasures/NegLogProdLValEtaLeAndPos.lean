import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas.LProd

private lemma eventually_abs_le_half_add_of_doubling_bounds (m : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    1 / (x + 1) ^ (3 + m) + 4 / 2 ^ (3 + m) / ((x + 1) * (x + 1 + 1)) ≤
      4 / 2 ^ (3 + m) / (x * (x + 1)) := by
  have hx0 : 0 < x := by linarith
  have hp : (2 : ℝ) ^ m ≤ (x + 1) ^ m := pow_le_pow_left₀ (by norm_num) (by linarith) m
  have hp0 : (0 : ℝ) < 2 ^ m := by positivity

  have hdiff : 4 / 2 ^ (3 + m) / (x * (x + 1)) - 4 / 2 ^ (3 + m) / ((x + 1) * (x + 1 + 1)) =
      1 / (2 ^ m * (x * (x + 1) * (x + 2))) := by
    rw [pow_add]
    field_simp
    ring

  have hcube : x * (x + 1) * (x + 2) ≤ (x + 1) ^ 3 := by nlinarith
  have hle : 2 ^ m * (x * (x + 1) * (x + 2)) ≤ (x + 1) ^ (3 + m) := by
    calc 2 ^ m * (x * (x + 1) * (x + 2)) ≤ (x + 1) ^ m * (x + 1) ^ 3 :=
          mul_le_mul hp hcube (by positivity) (by positivity)
      _ = (x + 1) ^ (3 + m) := by ring
  have hterm : 1 / (x + 1) ^ (3 + m) ≤ 1 / (2 ^ m * (x * (x + 1) * (x + 2))) :=
    one_div_le_one_div_of_le (by positivity) hle
  linarith

theorem tsum_le (M : ℕ) (hM : 3 ≤ M) :
    (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ M) ≤ 1 + 2 / 2 ^ M := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hM

  have hpart : ∀ N : ℕ, ∑ i ∈ Finset.range (N + 1), 1 / ((i : ℝ) + 1) ^ (3 + m) +
      4 / 2 ^ (3 + m) / (((N : ℝ) + 1) * ((N : ℝ) + 1 + 1)) ≤ 1 + 2 / 2 ^ (3 + m) := by
    intro N
    induction N with
    | zero =>
      apply le_of_eq
      norm_num
      ring
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have h := eventually_abs_le_half_add_of_doubling_bounds m ((N : ℝ) + 1) (by linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)])
      push_cast
      linarith
  apply Real.tsum_le_of_sum_range_le (fun n => by positivity)
  intro N
  cases N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    positivity
  | succ N =>
    have h := hpart N
    have : (0 : ℝ) ≤ 4 / 2 ^ (3 + m) / (((N : ℝ) + 1) * ((N : ℝ) + 1 + 1)) := by positivity
    linarith

theorem log_tsum_le (M : ℕ) (hM : 3 ≤ M) :
    Real.log (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ M) ≤ 2 / 2 ^ M := by
  have h1 := tsum_le M hM
  have h0 : 0 ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ M := tsum_nonneg fun n => by positivity
  rcases h0.eq_or_lt with h | h
  · rw [← h, Real.log_zero]
    positivity
  · linarith [Real.log_le_sub_one_of_pos h]

private lemma sum_Ioc_two_div_two_pow (n₀ k : ℕ) :
    ∑ M ∈ Finset.Ioc n₀ (n₀ + k), (2 : ℝ) / 2 ^ M = 2 / 2 ^ n₀ - 2 / 2 ^ (n₀ + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, Finset.sum_Ioc_succ_top (Nat.le_add_right n₀ k), ih, pow_succ]
    field_simp
    ring

theorem geom_le (n₀ n : ℕ) : ∑ M ∈ Finset.Ioc n₀ n, (2 : ℝ) / 2 ^ M ≤ (2 : ℝ) ^ ((1 : ℤ) - n₀) := by
  rw [zpow_sub₀ two_ne_zero, zpow_one, zpow_natCast]
  rcases le_or_gt n n₀ with h | h
  · rw [Finset.Ioc_eq_empty_of_le h, Finset.sum_empty]
    positivity
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h.le
    rw [sum_Ioc_two_div_two_pow]
    have : (0 : ℝ) ≤ 2 / 2 ^ (n₀ + k) := by positivity
    linarith

theorem neg_log_prod_le : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ n₀ n : ℕ, 2 ≤ n₀ → -Real.log (∏ M ∈ Finset.Ioc n₀ n, Formalism.HermitianLatticesTheory.lValEta E M) ≤ Formalism.HermitianLatticesTheory.fDeg E * (2 : ℝ) ^ ((1 : ℤ) - n₀) ∧ 0 < ∏ M ∈ Finset.Ioc n₀ n, Formalism.HermitianLatticesTheory.lValEta E M := by
  intro E _ _ _ hE n₀ n hn₀
  have hL : ∀ M : ℕ, 2 ≤ M → 0 < Formalism.HermitianLatticesTheory.lValEta E M ∧
      |Real.log (Formalism.HermitianLatticesTheory.lValEta E M)| ≤ (Formalism.HermitianLatticesTheory.fDeg E : ℝ) * Real.log (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ M) :=
    fun M hM => (Formalism.HermitianLattices.GlobalBoundRefinements.log_l_value_field_bound E hE M hM).2
  have hpos : ∀ M ∈ Finset.Ioc n₀ n, 0 < Formalism.HermitianLatticesTheory.lValEta E M := fun M hM =>
    (hL M (by have := (Finset.mem_Ioc.mp hM).1; omega)).1
  refine ⟨?_, Finset.prod_pos hpos⟩
  rw [Real.log_prod (fun M hM => (hpos M hM).ne'), ← Finset.sum_neg_distrib]
  have hf : (0 : ℝ) ≤ Formalism.HermitianLatticesTheory.fDeg E := by positivity
  calc ∑ M ∈ Finset.Ioc n₀ n, -Real.log (Formalism.HermitianLatticesTheory.lValEta E M)
      ≤ ∑ M ∈ Finset.Ioc n₀ n, (Formalism.HermitianLatticesTheory.fDeg E : ℝ) * (2 / 2 ^ M) := by
        apply Finset.sum_le_sum
        intro M hM
        have hM3 : 3 ≤ M := by have := (Finset.mem_Ioc.mp hM).1; omega
        calc -Real.log (Formalism.HermitianLatticesTheory.lValEta E M) ≤ |Real.log (Formalism.HermitianLatticesTheory.lValEta E M)| := neg_le_abs _
          _ ≤ (Formalism.HermitianLatticesTheory.fDeg E : ℝ) * Real.log (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ M) := (hL M (by omega)).2
          _ ≤ (Formalism.HermitianLatticesTheory.fDeg E : ℝ) * (2 / 2 ^ M) := mul_le_mul_of_nonneg_left (log_tsum_le M hM3) hf
    _ = (Formalism.HermitianLatticesTheory.fDeg E : ℝ) * ∑ M ∈ Finset.Ioc n₀ n, (2 : ℝ) / 2 ^ M := by rw [Finset.mul_sum]
    _ ≤ Formalism.HermitianLatticesTheory.fDeg E * (2 : ℝ) ^ ((1 : ℤ) - n₀) := mul_le_mul_of_nonneg_left (geom_le n₀ n) hf

end GlobalTheory.FlagMeas.LProd
