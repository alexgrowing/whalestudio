import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.LeviLogfk

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf

open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem Ck_eq (b : Frame X.Ψ r) (z u : V (nd X)) (τ : X.Ψ) (k : Fin (r + 1)) :
    Ck X b z u τ k = ∑ a : Fin r, ∑ j : Fin r, if (a : ℕ) < k ∧ (k : ℕ) ≤ j then
      (Dsg X a)⁻¹ * (Dsg X j * ‖Yd X b z u τ j a‖ ^ 2) else 0 := by
  calc Ck X b z u τ k
      = ∑ a : Fin r, if (a : ℕ) < k then (Dsg X a)⁻¹ *
          ∑ j : Fin r, (if (k : ℕ) ≤ (j : ℕ) then Dsg X j * ‖Yd X b z u τ j a‖ ^ 2 else 0) else 0 :=
        sum_castLE' (Nat.le_of_lt_succ k.isLt) (fun a : Fin r => (Dsg X a)⁻¹ *
          ∑ j : Fin r, if (k : ℕ) ≤ (j : ℕ) then Dsg X j * ‖Yd X b z u τ j a‖ ^ 2 else 0)
    _ = _ := by
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases ha : (a : ℕ) < k
      · rw [if_pos ha, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : (k : ℕ) ≤ (j : ℕ)
        · rw [if_pos hj, if_pos ⟨ha, hj⟩]
        · rw [if_neg hj, if_neg (fun h => hj h.2), mul_zero]
      · rw [if_neg ha, eq_comm]
        exact Finset.sum_eq_zero fun j _ => if_neg (fun h => ha h.1)

theorem tele_point (a j i : Fin r) :
    ((if (a : ℕ) < (i : ℕ) + 1 ∧ (i : ℕ) + 1 ≤ j then (1 : ℝ) else 0) -
      (if (a : ℕ) < i ∧ (i : ℕ) ≤ j then 1 else 0)) =
      if (a : ℕ) < j then ((if i = a then 1 else 0) - (if i = j then 1 else 0)) else 0 := by
  simp only [Fin.ext_iff]
  split_ifs <;> (try norm_num) <;> omega

theorem tele_sum (la : Fin r → ℝ) (a j : Fin r) :
    ∑ i : Fin r, la i * ((if (a : ℕ) < (i : ℕ) + 1 ∧ (i : ℕ) + 1 ≤ j then (1 : ℝ) else 0) -
      (if (a : ℕ) < i ∧ (i : ℕ) ≤ j then 1 else 0)) = if (a : ℕ) < j then la a - la j else 0 := by
  simp_rw [tele_point]
  split_ifs with h
  · simp [mul_sub, Finset.sum_sub_distrib]
  · simp

def coef (la : Wt X.Ψ r) (τ : X.Ψ) (a j : Fin r) : ℝ := Dsg X j / Dsg X a * ((la τ a : ℝ) - la τ j)

theorem tele (b : Frame X.Ψ r) (z u : V (nd X)) (la : Wt X.Ψ r) (τ : X.Ψ) :
    ∑ i : Fin r, (la τ i : ℝ) * (Ck X b z u τ i.succ - Ck X b z u τ i.castSucc) =
      ∑ a : Fin r, ∑ j : Fin r, if (a : ℕ) < j then coef X la τ a j * ‖Yd X b z u τ j a‖ ^ 2 else 0 := by
  have hdiff : ∀ i : Fin r, Ck X b z u τ i.succ - Ck X b z u τ i.castSucc =
      ∑ a : Fin r, ∑ j : Fin r, ((if (a : ℕ) < (i : ℕ) + 1 ∧ (i : ℕ) + 1 ≤ j then (1 : ℝ) else 0) -
        (if (a : ℕ) < i ∧ (i : ℕ) ≤ j then 1 else 0)) * ((Dsg X a)⁻¹ * (Dsg X j * ‖Yd X b z u τ j a‖ ^ 2)) := by
    intro i
    rw [Ck_eq, Ck_eq, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fin.val_succ, Fin.val_castSucc]
    split_ifs <;> ring
  calc ∑ i : Fin r, (la τ i : ℝ) * (Ck X b z u τ i.succ - Ck X b z u τ i.castSucc)
      = ∑ i : Fin r, ∑ a : Fin r, ∑ j : Fin r, (la τ i : ℝ) * (((if (a : ℕ) < (i : ℕ) + 1 ∧ (i : ℕ) + 1 ≤ j then (1 : ℝ) else 0) -
        (if (a : ℕ) < i ∧ (i : ℕ) ≤ j then 1 else 0)) * ((Dsg X a)⁻¹ * (Dsg X j * ‖Yd X b z u τ j a‖ ^ 2))) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hdiff i, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ a : Fin r, ∑ j : Fin r, ∑ i : Fin r, (la τ i : ℝ) * (((if (a : ℕ) < (i : ℕ) + 1 ∧ (i : ℕ) + 1 ≤ j then (1 : ℝ) else 0) -
        (if (a : ℕ) < i ∧ (i : ℕ) ≤ j then 1 else 0)) * ((Dsg X a)⁻¹ * (Dsg X j * ‖Yd X b z u τ j a‖ ^ 2))) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
    _ = _ := by
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
      have hts := tele_sum (fun i => (la τ i : ℝ)) a j
      beta_reduce at hts
      rw [show (∑ i : Fin r, (la τ i : ℝ) * (((if (a : ℕ) < (i : ℕ) + 1 ∧ (i : ℕ) + 1 ≤ j then (1 : ℝ) else 0) -
            (if (a : ℕ) < i ∧ (i : ℕ) ≤ j then 1 else 0)) * ((Dsg X a)⁻¹ * (Dsg X j * ‖Yd X b z u τ j a‖ ^ 2)))) =
          (∑ i : Fin r, (la τ i : ℝ) * ((if (a : ℕ) < (i : ℕ) + 1 ∧ (i : ℕ) + 1 ≤ j then (1 : ℝ) else 0) -
            (if (a : ℕ) < i ∧ (i : ℕ) ≤ j then 1 else 0))) * ((Dsg X a)⁻¹ * (Dsg X j * ‖Yd X b z u τ j a‖ ^ 2)) from by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring, hts]
      by_cases haj : (a : ℕ) < j
      · rw [if_pos haj, if_pos haj, coef, div_eq_mul_inv]
        ring
      · rw [if_neg haj, if_neg haj, zero_mul]

end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
