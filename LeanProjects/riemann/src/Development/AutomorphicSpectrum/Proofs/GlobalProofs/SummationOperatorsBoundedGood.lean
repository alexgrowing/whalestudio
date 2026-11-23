import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsFurther

set_option autoImplicit false

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.AopProps

variable {r : ℕ}

lemma update_add_single (i : Fin r) (m : Fin r → ℕ) (t k : ℕ) :
    Function.update (m + (Pi.single i t : Fin r → ℕ)) i k = Function.update m i k := by
  ext j
  by_cases h : j = i
  · subst h; simp
  · simp [Function.update_of_ne h, Pi.single_eq_of_ne h]

lemma add_single_eq_update (i : Fin r) (m : Fin r → ℕ) (t : ℕ) :
    m + (Pi.single i t : Fin r → ℕ) = Function.update m i (m i + t) := by
  ext j
  by_cases h : j = i
  · subst h; simp
  · simp [Function.update_of_ne h, Pi.single_eq_of_ne h]

lemma partialSum_update (i : Fin r) (v : (Fin r → ℕ) → ℚ) (m : Fin r → ℕ) (k : ℕ) :
    partialSum i v (Function.update m i k) =
      ∑ j ∈ Finset.range k, v (Function.update m i j) := by
  simp [partialSum]

lemma partialSum_periodic {l : ℕ} (i : Fin r) (v : (Fin r → ℕ) → ℚ) (hv : GoodAt l i v)
    (m : Fin r → ℕ) (k : ℕ) :
    partialSum i v (Function.update m i (k + l)) = partialSum i v (Function.update m i k) := by
  rw [partialSum_update, partialSum_update, Finset.sum_range_add]
  have h := hv.2 (Function.update m i k)
  have h2 : ∑ x ∈ Finset.range l, v (Function.update m i (k + x)) = 0 := by
    rw [← h]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [add_single_eq_update, Function.update_self, Function.update_idem]
  rw [h2, add_zero]

lemma sum_window {l : ℕ} (f : ℕ → ℚ) (hf : ∀ k, f (k + l) = f k) (a : ℕ) :
    ∑ k ∈ Finset.range l, f (a + k) = ∑ k ∈ Finset.range l, f k :=
  _root_.UpperTheory.Reformulated.B.DYdd7.main f hf a

lemma partialSumMean_add_single (l : ℕ) (i : Fin r) (v : (Fin r → ℕ) → ℚ) (m : Fin r → ℕ) (t : ℕ) :
    meanP l i v (m + (Pi.single i t : Fin r → ℕ)) = meanP l i v m := by
  simp only [meanP, update_add_single]

lemma partialSum_abs_le (i : Fin r) (v : (Fin r → ℕ) → ℚ) {C : ℝ}
    (hC : ∀ m, |(v m : ℝ)| ≤ C) (m : Fin r → ℕ) (k : ℕ) :
    |((partialSum i v (Function.update m i k) : ℚ) : ℝ)| ≤ k * C := by
  rw [partialSum_update]
  push_cast
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ C fun j _ => hC _).trans ?_
  simp

lemma partialSum_bound {l : ℕ} (hl : 0 < l) (i : Fin r) (v : (Fin r → ℕ) → ℚ)
    (hv : GoodAt l i v) {C : ℝ} (hC : ∀ m, |(v m : ℝ)| ≤ C) (m : Fin r → ℕ) :
    |((partialSum i v m : ℚ) : ℝ)| ≤ l * C := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC m)
  have hper : Function.Periodic (fun k => partialSum i v (Function.update m i k)) l :=
    fun k => partialSum_periodic i v hv m k
  have hmod : partialSum i v m = partialSum i v (Function.update m i (m i % l)) := by
    have h := hper.map_mod_nat (m i)
    simp only [Function.update_eq_self] at h
    exact h.symm
  rw [hmod]
  refine (partialSum_abs_le i v hC m _).trans ?_
  have : ((m i % l : ℕ) : ℝ) ≤ l := by exact_mod_cast (Nat.mod_lt _ hl).le
  exact mul_le_mul_of_nonneg_right this hC0

lemma abs_partialSumMean_le {l : ℕ} (hl : 0 < l) (i : Fin r) (v : (Fin r → ℕ) → ℚ)
    (hv : GoodAt l i v) {C : ℝ} (hC : ∀ m, |(v m : ℝ)| ≤ C) (m : Fin r → ℕ) :
    |((meanP l i v m : ℚ) : ℝ)| ≤ l * C := by
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  unfold meanP
  push_cast
  rw [abs_div, abs_of_pos hl', div_le_iff₀ hl']
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ ((l : ℝ) * C) fun j _ => ?_).trans ?_
  · exact_mod_cast partialSum_bound hl i v hv hC _
  · simp [mul_comm]

lemma mul_partialSumMean {l : ℕ} (hl : 0 < l) (i : Fin r) (v : (Fin r → ℕ) → ℚ) (m : Fin r → ℕ) :
    (l : ℚ) * meanP l i v m = ∑ k ∈ Finset.range l, partialSum i v (Function.update m i k) := by
  have hl' : (l : ℚ) ≠ 0 := by exact_mod_cast hl.ne'
  unfold meanP
  field_simp

lemma Aop_goodAt {l : ℕ} (hl : 0 < l) (i : Fin r) (v : (Fin r → ℕ) → ℚ) (hv : GoodAt l i v) :
    GoodAt l i (Aop l i v) := by
  have hps : ∀ (m : Fin r → ℕ) (t : ℕ), partialSum i v (m + (Pi.single i t : Fin r → ℕ)) =
      partialSum i v (Function.update m i (m i + t)) := fun m t => by
    rw [add_single_eq_update]
  refine ⟨fun m => ?_, fun m => ?_⟩
  · simp only [Aop, partialSumMean_add_single]
    have h1 : m + (Pi.single i l : Fin r → ℕ) + (Pi.single i 1 : Fin r → ℕ) =
        m + (Pi.single i (1 + l) : Fin r → ℕ) := by
      rw [add_assoc, ← Pi.single_add, add_comm l 1]
    rw [h1, hps, hps, ← add_assoc, partialSum_periodic i v hv]
  · have hterm : ∀ e, Aop l i v (m + (Pi.single i e : Fin r → ℕ)) =
        partialSum i v (Function.update m i (m i + 1 + e)) - meanP l i v m := fun e => by
      have h1 : m + (Pi.single i e : Fin r → ℕ) + (Pi.single i 1 : Fin r → ℕ) =
          m + (Pi.single i (1 + e) : Fin r → ℕ) := by
        rw [add_assoc, ← Pi.single_add, add_comm e 1]
      simp only [Aop, partialSumMean_add_single]
      rw [h1, hps, ← add_assoc]
    simp only [hterm]
    rw [Finset.sum_sub_distrib,
      sum_window (fun k => partialSum i v (Function.update m i k))
        (fun k => partialSum_periodic i v hv m k) (m i + 1), ← mul_partialSumMean hl]
    simp

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.AopProps

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

open AopProps in

theorem aop_props : ∀ (r l : ℕ) (i : Fin r) (v : (Fin r → ℕ) → ℚ), 0 < l → GoodAt l i v → BddW v →
    BddW (Aop l i v) ∧ BddW (Bop l i v) ∧ GoodAt l i (Aop l i v) := by
  intro r l i v hl hv ⟨C, hC⟩
  refine ⟨⟨l * C + l * C, fun m => ?_⟩, ⟨l * C, fun m => ?_⟩, Aop_goodAt hl i v hv⟩
  · unfold Aop
    push_cast
    exact (abs_sub _ _).trans
      (add_le_add (partialSum_bound hl i v hv hC _) (abs_partialSumMean_le hl i v hv hC _))
  · have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC m)
    unfold Bop
    split_ifs
    · exact abs_partialSumMean_le hl i v hv hC m
    · simpa using mul_nonneg (Nat.cast_nonneg l) hC0

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
