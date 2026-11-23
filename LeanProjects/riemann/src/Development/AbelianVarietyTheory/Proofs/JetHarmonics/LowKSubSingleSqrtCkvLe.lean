import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory.LowCasShift

theorem card_le {n : ℕ} (p : Fin n → Prop) [DecidablePred p] :
    (0 : ℝ) ≤ ((univ.filter p).card : ℝ) ∧ ((univ.filter p).card : ℝ) ≤ n := by
  refine ⟨Nat.cast_nonneg _, ?_⟩
  have h : (univ.filter p).card ≤ n := by
    simpa using card_filter_le (univ : Finset (Fin n)) p
  exact_mod_cast h

theorem rhoC_bd {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    -((n : ℝ) / 2) ≤ rhoC ε a ∧ rhoC ε a ≤ (n : ℝ) / 2 := by
  have h1 := card_le (fun b : Fin n => a < b ∧ ε b = ε a)
  have h2 := card_le (fun b : Fin n => b < a ∧ ε b = ε a)
  unfold rhoC
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem rhoN_bd {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    -((n : ℝ) / 2) ≤ rhoN ε a ∧ rhoN ε a ≤ (n : ℝ) / 2 := by
  have h1 := card_le (fun b : Fin n => a < b ∧ ε b ≠ ε a)
  have h2 := card_le (fun b : Fin n => b < a ∧ ε b ≠ ε a)
  unfold rhoN
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem nsq_sub_single {n : ℕ} (u : Fin n → ℝ) (s : Fin n) :
    nsq (u - Pi.single s 1) = nsq u - 2 * u s + 1 := by
  have h : ∀ a, (u - Pi.single s 1 : Fin n → ℝ) a * (u - Pi.single s 1 : Fin n → ℝ) a
      = u a * u a + (if a = s then 1 - 2 * u s else 0) := by
    intro a
    by_cases ha : a = s
    · subst ha; simp; ring
    · simp [ha]
  unfold nsq dot
  simp only [h, sum_add_distrib, sum_ite_eq', mem_univ, if_true]
  ring

theorem nsq_rhoC_le {n : ℕ} (ε : Fin n → Bool) : nsq (rhoC ε) ≤ (n : ℝ) ^ 3 := by
  unfold nsq dot
  have h : ∀ a ∈ (univ : Finset (Fin n)), rhoC ε a * rhoC ε a ≤ (n : ℝ) ^ 2 := by
    intro a _
    have := rhoC_bd ε a
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [this.1, this.2]
  have := sum_le_card_nsmul _ _ _ h
  simp only [card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  calc _ ≤ (n : ℝ) * (n : ℝ) ^ 2 := this
    _ = _ := by ring

theorem sq_le_nsq {n : ℕ} (u : Fin n → ℝ) (a : Fin n) : u a * u a ≤ nsq u := by
  unfold nsq dot
  exact single_le_sum (f := fun a => u a * u a) (fun i _ => mul_self_nonneg _) (mem_univ a)

theorem sqrt_step {X Y b : ℝ} (hb : 4 ≤ b) (hX : (b / 2) ^ 2 ≤ X) (hY : X - b ≤ Y) :
    Real.sqrt X ≤ Real.sqrt Y + 2 := by
  have h1 : b / 2 ≤ Real.sqrt X := Real.le_sqrt_of_sq_le hX
  have h0 : 0 ≤ X := le_trans (sq_nonneg _) hX
  have h2 : Real.sqrt X ^ 2 = X := Real.sq_sqrt h0
  have h3 : Real.sqrt X - 2 ≤ Real.sqrt Y := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  linarith

end GlobalTheory.LowCasShift

namespace GlobalTheory

open LowCasShift in

theorem lowK_sub_single_and_sqrt_ckv_le :
    ∀ (n kk : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (bv : ℝ) (s : Fin n), Shape ε kk μ bv →
      lowK ε (μ - Pi.single s 1) = lowK ε μ - Pi.single s 1 ∧
      Real.sqrt (ckv ε (lowK ε μ)) + Real.sqrt n ≤
        Real.sqrt (ckv ε (lowK ε (μ - Pi.single s 1))) + 8 * n := by
  intro n kk ε μ bv s h
  obtain ⟨hk1, hk2, -, hc, hnode, hb⟩ := h
  refine ⟨by unfold lowK; abel, ?_⟩
  have hn2 : 2 ≤ n := by omega
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have h37 : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 7 := pow_le_pow_right₀ hn1 (by norm_num)
  have h13 : (n : ℝ) ≤ (n : ℝ) ^ 3 := by
    simpa using pow_le_pow_right₀ hn1 (show 1 ≤ 3 by norm_num)
  have hX : ckv ε (lowK ε μ) = nsq (μ + rhoN ε) - nsq (rhoC ε) := by
    unfold ckv lowK; congr 2; abel
  have hY : ckv ε (lowK ε (μ - Pi.single s 1))
      = nsq (μ + rhoN ε) - 2 * (μ s + rhoN ε s) + 1 - nsq (rhoC ε) := by
    have : lowK ε (μ - Pi.single s 1) + rhoC ε = (μ + rhoN ε) - Pi.single s 1 := by
      unfold lowK; abel
    unfold ckv
    rw [this, nsq_sub_single]; rfl
  have hs : μ s ≤ bv / 8 + bv / 100 := by
    by_cases hsk : s.val + 1 < kk
    · exact (hc s hsk).2.2
    · have := (hnode s (by omega)).2
      linarith
  have hNs := (rhoN_bd ε s).2
  let l : Fin n := ⟨n - 1, by omega⟩
  have hl := (hnode l (by show kk ≤ n - 1 + 1; omega)).2
  have hNl := (rhoN_bd ε l).2
  have hsq := sq_le_nsq (μ + rhoN ε) l
  have hC := nsq_rhoC_le ε
  have hneg : (μ + rhoN ε) l ≤ -(9 / 10 * bv) := by
    show μ l + rhoN ε l ≤ _
    linarith
  have hb4 : 4 ≤ bv := by linarith
  have hbig : (9 / 10 * bv) ^ 2 ≤ (μ + rhoN ε) l * (μ + rhoN ε) l := by nlinarith
  have hXl : (bv / 2) ^ 2 ≤ ckv ε (lowK ε μ) := by
    rw [hX]; nlinarith
  have hstep := sqrt_step hb4 hXl (Y := ckv ε (lowK ε (μ - Pi.single s 1))) (by rw [hX, hY]; linarith)
  have hsn : Real.sqrt n ≤ n := by
    apply Real.sqrt_le_iff.mpr
    constructor <;> nlinarith
  linarith

end GlobalTheory
