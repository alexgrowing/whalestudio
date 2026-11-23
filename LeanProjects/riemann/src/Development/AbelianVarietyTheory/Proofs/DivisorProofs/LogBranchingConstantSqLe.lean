import Mathlib
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.FiniteDimensionalNablaSq

open Formalism.BasicNotions

namespace GlobalTheory.BranchBound

theorem branching_D1_le_weight_difference (n : ℕ) (lam : DomWeight (n + 1)) (sg : DomWeight n) :
    Formalism.MainNotions.PrimeDegreeVariant.D1 rfl lam sg ≤ lam.w 0 - lam.w (Fin.last n) := by
  let g : ℕ → ℤ := fun k => if hk : k < n + 1 then lam.w ⟨k, hk⟩ else 0
  have h1 : Formalism.MainNotions.PrimeDegreeVariant.D1 rfl lam sg ≤ ∑ i : Fin n, (g i - g (i + 1)) := by
    unfold Formalism.MainNotions.PrimeDegreeVariant.D1
    refine Finset.sum_le_sum fun i _ => ?_
    have a : g i = lam.w ⟨i.1, by omega⟩ := by simp [g, show i.1 < n + 1 by omega]
    have b : g (i + 1) = lam.w ⟨i.1 + 1, by omega⟩ := by simp [g, show i.1 + 1 < n + 1 by omega]
    rw [a, b]
    exact min_le_left _ _
  have h2 : ∑ i : Fin n, (g i - g (i + 1)) = g 0 - g n := by
    rw [Fin.sum_univ_eq_sum_range (fun k => g k - g (k + 1)) n]
    exact Finset.sum_range_sub' g n
  have a0 : g 0 = lam.w 0 := by simp [g]
  have an : g n = lam.w (Fin.last n) := by simp [g]; rfl
  rw [h2, a0, an] at h1
  exact h1

end GlobalTheory.BranchBound

namespace GlobalTheory.BranchBound

theorem finrank_delSq_le (N : ℕ) (lam : DomWeight N) (B : ℝ) (hB : 1 ≤ B)
    (hw : ∀ i, |((lam.w i : ℤ) : ℝ)| ≤ B) :
    (Module.finrank ℂ (delSq ℂ N lam) : ℝ) ≤ (6 * B) ^ (N * N) := by
  have hq := GlobalTheory.WeylDimGL.finrank_delSq ℂ N lam
  rw [GlobalTheory.WeylDimGL.weylDim_eq_prod_Ioi] at hq
  have hr : (Module.finrank ℂ (delSq ℂ N lam) : ℝ) = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
      (((lam.w i : ℝ) - (lam.w j : ℝ) + ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) / (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ))) := by
    have := congrArg (Rat.cast : ℚ → ℝ) hq
    push_cast at this
    exact this
  rw [hr]
  have h6 : (1 : ℝ) ≤ 6 * B := by linarith
  have hf : ∀ i : Fin N, ∀ j ∈ Finset.Ioi i,
      0 ≤ ((lam.w i : ℝ) - (lam.w j : ℝ) + ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) / (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) ∧
      ((lam.w i : ℝ) - (lam.w j : ℝ) + ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) / (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) ≤ 6 * B := by
    intro i j hj
    have hij : i < j := Finset.mem_Ioi.mp hj
    have hlt : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hij
    have hanti : (lam.w j : ℝ) ≤ lam.w i := by exact_mod_cast lam.anti hij.le
    have hbi := abs_le.mp (hw i)
    have hbj := abs_le.mp (hw j)
    have hk : (0 : ℝ) < ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ) := by linarith
    constructor
    · apply div_nonneg <;> linarith
    · rw [div_le_iff₀ hk]
      nlinarith
  calc ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
      (((lam.w i : ℝ) - (lam.w j : ℝ) + ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) / (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)))
        ≤ ∏ _i : Fin N, (6 * B) ^ N := by
          refine Finset.prod_le_prod (fun i _ => Finset.prod_nonneg fun j hj => (hf i j hj).1) fun i _ => ?_
          calc _ ≤ ∏ _j ∈ Finset.Ioi i, (6 * B) :=
                Finset.prod_le_prod (fun j hj => (hf i j hj).1) fun j hj => (hf i j hj).2
            _ = (6 * B) ^ (Finset.Ioi i).card := Finset.prod_const _
            _ ≤ (6 * B) ^ N := by
                apply pow_le_pow_right₀ h6
                simpa using Finset.card_le_univ (Finset.Ioi i)
      _ = (6 * B) ^ (N * N) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm]

end GlobalTheory.BranchBound

namespace GlobalTheory.BranchBound

theorem log_brBd_sq_le : ∀ {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (B : ℝ), 1 ≤ B →
    (N : ℝ) ≤ B → (∀ i, |((lam.w i : ℤ) : ℝ)| ≤ B) →
    Real.log (Formalism.MainNotions.PrimeDegreeVariant.brBd h lam sg ^ 2) ≤ 5 * N * B * Real.log (6 * B) := by
  intro n N h lam sg B hB hN hw
  subst h
  have hNB : ((n + 1 : ℕ) : ℝ) ≤ B := hN
  have hN0 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
  have hL : 0 < Real.log (6 * B) := Real.log_pos (by linarith)
  have hR : 0 ≤ 5 * ((n + 1 : ℕ) : ℝ) * B * Real.log (6 * B) := by positivity

  have hsp : lam.spread = lam.w 0 - lam.w (Fin.last n) + ((n + 1 : ℕ) : ℤ) := by
    unfold DomWeight.spread
    rw [dif_pos (Nat.succ_pos n)]
    rfl
  have h0 := abs_le.mp (hw 0)
  have hl := abs_le.mp (hw (Fin.last n))
  have hanti : (lam.w (Fin.last n) : ℝ) ≤ lam.w 0 := by exact_mod_cast lam.anti (Fin.zero_le _)
  set s : ℝ := (((2 * lam.spread : ℤ)) : ℝ) with hs
  have hsR : s = 2 * ((lam.w 0 : ℝ) - lam.w (Fin.last n) + ((n + 1 : ℕ) : ℝ)) := by
    rw [hs, hsp]; push_cast; ring
  have hs2 : 2 ≤ s := by rw [hsR]; push_cast at hNB ⊢; linarith
  have hs6 : s ≤ 6 * B := by rw [hsR]; push_cast at hNB ⊢; linarith
  have hls0 : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
  have hls : Real.log s ≤ Real.log (6 * B) := Real.log_le_log (by linarith) hs6

  have hD := branching_D1_le_weight_difference n lam sg
  have hDR : ((Formalism.MainNotions.PrimeDegreeVariant.D1 rfl lam sg : ℤ) : ℝ) ≤ 2 * B := by
    have : ((Formalism.MainNotions.PrimeDegreeVariant.D1 rfl lam sg : ℤ) : ℝ) ≤ (lam.w 0 : ℝ) - lam.w (Fin.last n) := by exact_mod_cast hD
    linarith
  set e : ℝ := ((((n + 1 : ℕ) : ℤ) * Formalism.MainNotions.PrimeDegreeVariant.D1 rfl lam sg : ℤ) : ℝ) with he
  have heR : e = ((n + 1 : ℕ) : ℝ) * ((Formalism.MainNotions.PrimeDegreeVariant.D1 rfl lam sg : ℤ) : ℝ) := by rw [he]; push_cast; ring
  have hel : e * Real.log s ≤ 2 * ((n + 1 : ℕ) : ℝ) * B * Real.log (6 * B) := by
    rcases le_or_gt e 0 with he0 | he0
    · have : e * Real.log s ≤ 0 := mul_nonpos_of_nonpos_of_nonneg he0 hls0
      have : 0 ≤ 2 * ((n + 1 : ℕ) : ℝ) * B * Real.log (6 * B) := by positivity
      linarith
    · have he2 : e ≤ 2 * ((n + 1 : ℕ) : ℝ) * B := by
        rw [heR]; nlinarith
      calc e * Real.log s ≤ (2 * ((n + 1 : ℕ) : ℝ) * B) * Real.log (6 * B) :=
            mul_le_mul he2 hls hls0 (by positivity)
        _ = _ := by ring

  have hc : Formalism.MainNotions.PrimeDegreeVariant.cBd rfl lam sg = s ^ e := rfl
  have hcpos : 0 < s ^ e := Real.rpow_pos_of_pos (by linarith) e
  set d : ℝ := (Module.finrank ℂ (delSq ℂ (n + 1) lam) : ℝ) with hd
  have hd0 : 0 ≤ d := by positivity
  have hb2 : Formalism.MainNotions.PrimeDegreeVariant.brBd rfl lam sg ^ 2 = (s ^ e) ^ 2 * d := by
    unfold Formalism.MainNotions.PrimeDegreeVariant.brBd
    rw [hc, mul_pow, Real.sq_sqrt hd0]
  rw [hb2]
  rcases eq_or_lt_of_le hd0 with hd0' | hdpos
  · rw [← hd0', mul_zero, Real.log_zero]; exact hR
  have hdle := finrank_delSq_le (n + 1) lam B hB hw
  have hlogd : Real.log d ≤ (((n + 1) * (n + 1) : ℕ) : ℝ) * Real.log (6 * B) := by
    rw [← Real.log_pow]
    exact Real.log_le_log hdpos hdle
  have hlogd' : Real.log d ≤ ((n + 1 : ℕ) : ℝ) * B * Real.log (6 * B) := by
    refine hlogd.trans ?_
    push_cast
    have : (((n : ℝ) + 1) * ((n : ℝ) + 1)) ≤ ((n : ℝ) + 1) * B := by
      push_cast at hNB hN0
      exact mul_le_mul_of_nonneg_left hNB hN0
    nlinarith
  rw [Real.log_mul (by positivity) hdpos.ne', Real.log_pow, Real.log_rpow (by linarith)]
  push_cast at hel hlogd' ⊢
  nlinarith

end GlobalTheory.BranchBound
