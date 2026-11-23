import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBallFamMonoNegAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearIndependentAdaptedToDecreasingChainAStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardSeminormBallLePowMulSmallerStatement
open Filter Topology
open GlobalTheory GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem log_ncard_unit_ball_le_of_indep_bound :
    ∀ (G : Type) [AddCommGroup G] [IsAddTorsionFree G] (Λ : AddSubgroup G) (B : ℝ → Set G), IsBallFam Λ B →
      (B 1).Finite → ∀ (q : ℕ) (T : ℝ), 3 ≤ q → 0 ≤ T →
      (∀ (r : ℕ) (e : Fin r → G) (n : Fin r → ℕ), LinearIndependent ℤ e → (∀ j, e j ∈ B ((2 / q : ℝ) ^ n j)) →
        ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ T) → Real.log ((B 1).ncard : ℝ) ≤ Real.log q * T := by
  classical
  intro G _ _ Λ B hB hfin q T hq hT hbound
  set S : ℕ → Set G := fun i => B ((2 / q : ℝ) ^ i) with hS
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hmono := (isBallFam_mono_neg_add G Λ B hB).1
  have hSdec : ∀ i, S (i + 1) ⊆ S i := by
    intro i
    apply hmono
    have h0 : (0 : ℝ) ≤ 2 / q := by positivity
    have h1 : (2 / q : ℝ) ≤ 1 := by
      rw [div_le_one hqpos]; exact_mod_cast (by omega : 2 ≤ q)
    exact pow_le_pow_of_le_one h0 h1 (Nat.le_succ i)
  set K : ℕ := ⌊T⌋₊ with hK

  have hsize : ∀ i m (e : Fin m → G), LinearIndependent ℤ e → (∀ j, e j ∈ S i) → m ≤ K := by
    intro i m e he hmem
    have h := hbound m e (fun _ => i) he hmem
    apply Nat.le_floor
    refine le_trans ?_ h
    have : m ≤ ∑ _j : Fin m, (i + 1) := by simp; exact Nat.le_mul_of_pos_right m (Nat.succ_pos i)
    exact_mod_cast this
  let P : ℕ → ℕ → Prop := fun i m => ∃ e : Fin m → G, LinearIndependent ℤ e ∧ ∀ j, e j ∈ S i
  let r : ℕ → ℕ := fun i => Nat.findGreatest (P i) K
  have hP0 : ∀ i, P i 0 := fun i => ⟨Fin.elim0, linearIndependent_empty_type, fun j => j.elim0⟩
  have hrspec : ∀ i, P i (r i) := fun i => Nat.findGreatest_spec (Nat.zero_le K) (hP0 i)
  have hrmax : ∀ i m (e : Fin m → G), LinearIndependent ℤ e → (∀ j, e j ∈ S i) → m ≤ r i := by
    intro i m e he hmem
    exact Nat.le_findGreatest (hsize i m e he hmem) ⟨e, he, hmem⟩
  have hrdec : ∀ i, r (i + 1) ≤ r i := by
    intro i
    obtain ⟨e, he, hmem⟩ := hrspec (i + 1)
    exact hrmax i _ e he (fun j => hSdec i (hmem j))

  have hstep : ∀ i, (S i).encard ≤ ((q ^ r i : ℕ) : ℕ∞) * (S (i + 1)).encard := by
    intro i
    have h := GlobalTheory.T.encard_seminormBall_le_pow_mul_smaller G Λ B hB ((2 / q : ℝ) ^ i) q (r i) (by omega)
      (fun n e he hmem => hrmax i n e he hmem)
    have heq : 2 * (2 / q : ℝ) ^ i / q = (2 / q : ℝ) ^ (i + 1) := by
      rw [pow_succ]; ring
    simpa [hS, heq] using h
  have hiter : ∀ k, (S 0).encard ≤ ((q ^ (∑ i ∈ Finset.range k, r i) : ℕ) : ℕ∞) * (S k).encard := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      refine ih.trans ?_
      rw [Finset.sum_range_succ, pow_add, Nat.cast_mul, mul_assoc]
      gcongr
      exact hstep k

  have hSK : S K ⊆ {0} := by
    intro x hx
    by_contra hx0
    have hli : LinearIndependent ℤ (fun _ : Fin 1 => x) := by
      rw [linearIndependent_unique_iff]; exact hx0
    have h := hbound 1 (fun _ => x) (fun _ => K) hli (fun _ => hx)
    have hlt : T < (K : ℝ) + 1 := Nat.lt_floor_add_one T
    simp at h
    linarith
  have hSK1 : (S K).encard ≤ 1 := by
    calc (S K).encard ≤ ({0} : Set G).encard := Set.encard_le_encard hSK
      _ = 1 := Set.encard_singleton 0

  obtain ⟨e, n, he, hmem, hsum⟩ := GlobalTheory.T.exists_linearIndependent_adapted_to_decreasing_chain' G S hSdec K r hrspec hrdec
  have hM : ((∑ i ∈ Finset.range K, r i : ℕ) : ℝ) ≤ T := by
    have h1 := hbound (r 0) e n he hmem
    have h2 : ∑ i ∈ Finset.range K, r i ≤ ∑ i ∈ Finset.range (K + 1), r i :=
      Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (Nat.le_succ K))
    have h3 : ((∑ i ∈ Finset.range K, r i : ℕ) : ℝ) ≤ ((∑ j, (n j + 1) : ℕ) : ℝ) := by
      exact_mod_cast h2.trans hsum
    linarith
  set M := ∑ i ∈ Finset.range K, r i with hMdef
  have hS0 : S 0 = B 1 := by simp [hS]
  have hcard : (B 1).encard ≤ ((q ^ M : ℕ) : ℕ∞) := by
    rw [← hS0]
    calc (S 0).encard ≤ ((q ^ M : ℕ) : ℕ∞) * (S K).encard := hiter K
      _ ≤ ((q ^ M : ℕ) : ℕ∞) * 1 := by gcongr
      _ = _ := mul_one _
  have hncard : (B 1).ncard ≤ q ^ M := by
    rw [← hfin.cast_ncard_eq] at hcard
    exact_mod_cast hcard
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  rcases Nat.eq_zero_or_pos (B 1).ncard with h0 | hpos
  · rw [h0]; simp; positivity
  · have hpos' : (0 : ℝ) < (B 1).ncard := by exact_mod_cast hpos
    calc Real.log ((B 1).ncard : ℝ) ≤ Real.log ((q ^ M : ℕ) : ℝ) :=
          Real.log_le_log hpos' (by exact_mod_cast hncard)
      _ = M * Real.log q := by rw [Nat.cast_pow, Real.log_pow]
      _ ≤ T * Real.log q := by gcongr
      _ = Real.log q * T := mul_comm _ _

end GlobalTheory.VolBr

example : ∀ (G : Type) [AddCommGroup G] [IsAddTorsionFree G] (Λ : AddSubgroup G) (B : ℝ → Set G), IsBallFam Λ B → (B 1).Finite → ∀ (q : ℕ) (T : ℝ), 3 ≤ q → 0 ≤ T → (∀ (r : ℕ) (e : Fin r → G) (n : Fin r → ℕ), LinearIndependent ℤ e → (∀ j, e j ∈ B ((2 / q : ℝ) ^ n j)) → ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ T) → Real.log ((B 1).ncard : ℝ) ≤ Real.log q * T := GlobalTheory.VolBr.log_ncard_unit_ball_le_of_indep_bound
