import Mathlib
import Formalism.HermitianLattices.StatementMass
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIdealInClassOfNormLeSqrtDiscr

open MeasureTheory NumberField Finset
open scoped ArithmeticFunction.zeta

namespace GlobalTheory.IdealZetaSum

theorem sum_Ioc_rpow_neg_le {s : ℝ} (hs : 1 < s) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-s) ≤ s / (s - 1) := by
  have hs1 : 0 < s - 1 := by linarith
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Ioc_self, sum_empty]; positivity
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-s)) (Set.Icc ((1 : ℕ) : ℝ) (N : ℝ)) := by
    intro x hx y _ hxy
    have : (1 : ℝ) ≤ x := by simpa using hx.1
    exact Real.rpow_le_rpow_of_nonpos (by linarith) hxy (by linarith)
  have h := AntitoneOn.sum_le_integral_Ico hN hanti
  rw [integral_rpow (Or.inr ⟨by linarith, by
    rw [Set.uIcc_of_le (by simpa using hN1)]; simp⟩)] at h
  have e : ∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-s)
      = 1 + ∑ i ∈ Ico 1 N, (((i + 1 : ℕ) : ℝ)) ^ (-s) := by
    rw [sum_Ico_add' (fun n : ℕ => (n : ℝ) ^ (-s)) 1 N 1]
    have : Ioc 0 N = insert 1 (Ico (1 + 1) (N + 1)) := by
      ext n; simp only [mem_Ioc, mem_insert, mem_Ico]; omega
    rw [this, sum_insert (by simp)]
    simp
  rw [e]
  have hpos : 0 ≤ (N : ℝ) ^ (-s + 1) := by positivity
  have h2 : ((N : ℝ) ^ (-s + 1) - ((1 : ℕ) : ℝ) ^ (-s + 1)) / (-s + 1) ≤ 1 / (s - 1) := by
    rw [Nat.cast_one, Real.one_rpow, show -s + 1 = -(s - 1) by ring, div_neg, ← neg_div]
    rw [show -s + 1 = -(s - 1) by ring] at hpos
    exact div_le_div_of_nonneg_right (by linarith) hs1.le
  have h3 : s / (s - 1) = 1 + 1 / (s - 1) := by field_simp; ring
  linarith

theorem sum_zeta_pow_mul_rpow_le (s : ℝ) (N k : ℕ) :
    ∑ n ∈ Ioc 0 N, (((ζ ^ k : ArithmeticFunction ℕ) n : ℕ) : ℝ) * (n : ℝ) ^ (-s)
      ≤ (∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-s)) ^ k := by
  induction k with
  | zero =>
    simp only [pow_zero, ArithmeticFunction.one_apply, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      ite_mul, one_mul, zero_mul, sum_ite_eq']
    split_ifs <;> simp
  | succ k ih =>
    rw [pow_succ (∑ n ∈ Ioc 0 N, (n : ℝ) ^ (-s))]
    refine le_trans ?_ (mul_le_mul_of_nonneg_right ih (sum_nonneg fun n _ => by positivity))
    rw [sum_mul_sum, ← sum_product', pow_succ]
    have e : ∀ n ∈ Ioc 0 N, (((ζ ^ k * ζ : ArithmeticFunction ℕ) n : ℕ) : ℝ) * (n : ℝ) ^ (-s)
        = ∑ x ∈ (Ioc 0 N ×ˢ Ioc 0 N).filter (fun x => x.1 * x.2 = n),
          (((ζ ^ k : ArithmeticFunction ℕ) x.1 : ℕ) : ℝ) * (x.1 : ℝ) ^ (-s) * (x.2 : ℝ) ^ (-s) := by
      intro n hn
      rw [mem_Ioc] at hn
      rw [ArithmeticFunction.mul_apply, Nat.cast_sum, sum_mul]
      refine sum_congr ?_ ?_
      · ext x
        simp only [Nat.mem_divisorsAntidiagonal, mem_filter, mem_product, mem_Ioc]
        constructor
        · rintro ⟨h, h0⟩
          have h1 : 0 < x.1 := Nat.pos_of_ne_zero (by rintro h1; rw [h1] at h; omega)
          have h2 : 0 < x.2 := Nat.pos_of_ne_zero (by rintro h1; rw [h1] at h; omega)
          refine ⟨⟨⟨h1, ?_⟩, h2, ?_⟩, h⟩ <;> nlinarith
        · rintro ⟨_, h⟩
          exact ⟨h, by omega⟩
      · intro x hx
        simp only [mem_filter, mem_product, mem_Ioc] at hx
        rw [← hx.2, Nat.cast_mul, Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity),
          ArithmeticFunction.zeta_apply_ne hx.1.2.1.ne']
        simp [mul_assoc]
    rw [sum_congr rfl e, sum_fiberwise_eq_sum_filter]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun x _ _ => by positivity

theorem sum_absNorm_rpow_neg_le : ∀ (K : Type) [Field K] [NumberField K] (s : ℝ), 1 < s →
    ∀ (S : Finset (Ideal (𝓞 K))), (∀ I ∈ S, I ≠ ⊥) →
      ∑ I ∈ S, (Ideal.absNorm I : ℝ) ^ (-s) ≤ (s / (s - 1)) ^ Module.finrank ℚ K := by
  intro K _ _ s hs S hS
  classical
  set N := S.sup (fun I => Ideal.absNorm I) with hN
  refine le_trans ?_ (pow_le_pow_left₀ (sum_nonneg fun n _ => by positivity)
    (sum_Ioc_rpow_neg_le hs N) _)
  refine le_trans ?_ (sum_zeta_pow_mul_rpow_le s N _)
  rw [← sum_fiberwise_of_maps_to (s := S) (t := Ioc 0 N) (g := fun I => Ideal.absNorm I)]
  · refine sum_le_sum fun n hn => ?_
    rw [sum_congr rfl (g := fun _ => (n : ℝ) ^ (-s))
      (fun I hI => by rw [(mem_filter.mp hI).2]), sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [Nat.cast_le]
    refine le_trans ?_ (ncard_ideal_absNorm_eq_le K (mem_Ioc.mp hn).1.ne')
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard (fun I hI => (mem_filter.mp (mem_coe.mp hI)).2)
      (Ideal.finite_setOfPred_absNorm_eq n)
  · intro I hI
    rw [mem_Ioc]
    exact ⟨Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hS I hI),
      le_sup (f := fun I => Ideal.absNorm I) hI⟩

end GlobalTheory.IdealZetaSum
