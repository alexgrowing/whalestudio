import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEX2

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutEXPbSupp

section hyp

variable {m : ℕ}

theorem rev_cs (a b : Fin (m + 1) → ℂ) (c : ℂ) (t : ℝ) (ht : 0 < t)
    (ha : ∑ i : Fin m, ‖a i.castSucc‖ ^ 2 ≤ ‖a (Fin.last m)‖ ^ 2)
    (hb : ∑ i : Fin m, ‖b i.castSucc‖ ^ 2 ≤ ‖b (Fin.last m)‖ ^ 2 - t)
    (hc : ‖c‖ ≤ ∑ i : Fin m, ‖a i.castSucc‖ * ‖b i.castSucc‖) :
    ‖a (Fin.last m)‖ * t ≤ 2 * ‖b (Fin.last m)‖ * ‖a (Fin.last m) * b (Fin.last m) + c‖ := by
  set A := ‖a (Fin.last m)‖ with hA
  set Bn := ‖b (Fin.last m)‖ with hBn
  set P := ∑ i : Fin m, ‖a i.castSucc‖ * ‖b i.castSucc‖ with hPdef
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hCS : P ^ 2 ≤ (∑ i : Fin m, ‖a i.castSucc‖ ^ 2) * (∑ i : Fin m, ‖b i.castSucc‖ ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hsb : 0 ≤ ∑ i : Fin m, ‖b i.castSucc‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have hA0 : 0 ≤ A := norm_nonneg _
  have hB0 : 0 ≤ Bn := norm_nonneg _
  have hBt : t ≤ Bn ^ 2 := by linarith
  have hP2 : P ^ 2 ≤ A ^ 2 * (Bn ^ 2 - t) := hCS.trans (mul_le_mul ha hb hsb (sq_nonneg _))
  have key : 2 * Bn * P ≤ A * (2 * Bn ^ 2 - t) := by
    have hR : 0 ≤ A * (2 * Bn ^ 2 - t) := mul_nonneg hA0 (by linarith)
    have hL : 0 ≤ 2 * Bn * P := by positivity
    have hsq : (2 * Bn * P) ^ 2 ≤ (A * (2 * Bn ^ 2 - t)) ^ 2 := by
      have e1 : (2 * Bn * P) ^ 2 = 4 * Bn ^ 2 * P ^ 2 := by ring
      have e2 : (A * (2 * Bn ^ 2 - t)) ^ 2 = 4 * Bn ^ 2 * (A ^ 2 * (Bn ^ 2 - t)) + A ^ 2 * t ^ 2 := by ring
      rw [e1, e2]
      have h4 : 4 * Bn ^ 2 * P ^ 2 ≤ 4 * Bn ^ 2 * (A ^ 2 * (Bn ^ 2 - t)) :=
        mul_le_mul_of_nonneg_left hP2 (by positivity)
      nlinarith [sq_nonneg (A * t)]
    nlinarith
  have h1 : A * Bn ≤ ‖a (Fin.last m) * b (Fin.last m) + c‖ + ‖c‖ := by
    rw [hA, hBn, ← norm_mul]
    calc ‖a (Fin.last m) * b (Fin.last m)‖ = ‖(a (Fin.last m) * b (Fin.last m) + c) - c‖ := by
          rw [add_sub_cancel_right]
      _ ≤ _ := norm_sub_le _ _
  have h2 : A * Bn - P ≤ ‖a (Fin.last m) * b (Fin.last m) + c‖ := by linarith
  calc A * t = 2 * A * Bn ^ 2 - A * (2 * Bn ^ 2 - t) := by ring
    _ ≤ 2 * A * Bn ^ 2 - 2 * Bn * P := by linarith
    _ = 2 * Bn * (A * Bn - P) := by ring
    _ ≤ 2 * Bn * ‖a (Fin.last m) * b (Fin.last m) + c‖ := mul_le_mul_of_nonneg_left h2 (by positivity)

def dS (m : ℕ) : Fin (m + 1) → ℂ := fun i => if i = Fin.last m then -1 else 1

theorem dS_cs (i : Fin m) : dS m i.castSucc = 1 := by simp [dS, Fin.castSucc_ne_last]

theorem dS_last : dS m (Fin.last m) = -1 := by simp [dS]

theorem dS_sq : diagonal (dS m) * diagonal (dS m) = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext i; unfold dS; split_ifs <;> norm_num

theorem sum_dS (v : Fin (m + 1) → ℂ) :
    ∑ i, star (v i) * dS m i * v i =
      ((∑ i : Fin m, ‖v i.castSucc‖ ^ 2 - ‖v (Fin.last m)‖ ^ 2 : ℝ) : ℂ) := by
  rw [Fin.sum_univ_castSucc, dS_last]
  simp only [dS_cs, mul_one, Complex.ofReal_sub, Complex.ofReal_sum, Complex.ofReal_pow]
  have e : ∀ w : ℂ, star w * w = ((‖w‖ : ℝ) : ℂ) ^ 2 := fun w => by
    rw [Complex.star_def, Complex.conj_mul']
  rw [sub_eq_add_neg]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => e _
  · rw [mul_neg_one, neg_mul, e]

theorem quad_eq (v w : Fin (m + 1) → ℂ) :
    star w ⬝ᵥ (diagonal (dS m) *ᵥ v) = ∑ i, star (w i) * dS m i * v i := by
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply, mul_assoc]

theorem quad_unitary (μ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (hμ : μᴴ * diagonal (dS m) * μ = diagonal (dS m)) (v : Fin (m + 1) → ℂ) :
    star (μ *ᵥ v) ⬝ᵥ (diagonal (dS m) *ᵥ (μ *ᵥ v)) = star v ⬝ᵥ (diagonal (dS m) *ᵥ v) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hμ]

theorem row_unitary (μ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (hμ : μᴴ * diagonal (dS m) * μ = diagonal (dS m)) :
    μ * diagonal (dS m) * μᴴ = diagonal (dS m) := by
  have h1 : (diagonal (dS m) * μᴴ * diagonal (dS m)) * μ = 1 := by
    calc (diagonal (dS m) * μᴴ * diagonal (dS m)) * μ = diagonal (dS m) * (μᴴ * diagonal (dS m) * μ) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hμ, dS_sq]
  have h2 : μ * (diagonal (dS m) * μᴴ * diagonal (dS m)) = 1 := mul_eq_one_comm.mp h1
  calc μ * diagonal (dS m) * μᴴ = μ * (diagonal (dS m) * μᴴ * diagonal (dS m)) * diagonal (dS m) := by
        simp only [Matrix.mul_assoc, dS_sq, Matrix.mul_one]
    _ = diagonal (dS m) := by rw [h2, Matrix.one_mul]

theorem col_id (μ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (hμ : μᴴ * diagonal (dS m) * μ = diagonal (dS m)) (j : Fin (m + 1)) :
    ((∑ i : Fin m, ‖μ i.castSucc j‖ ^ 2 - ‖μ (Fin.last m) j‖ ^ 2 : ℝ) : ℂ) = dS m j := by
  have e := congrFun (congrFun hμ j) j
  rw [Matrix.mul_apply] at e
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq] at e
  rw [← sum_dS (fun i => μ i j), ← e]

theorem row_id (μ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (hμ : μᴴ * diagonal (dS m) * μ = diagonal (dS m)) (i : Fin (m + 1)) :
    ((∑ j : Fin m, ‖μ i j.castSucc‖ ^ 2 - ‖μ i (Fin.last m)‖ ^ 2 : ℝ) : ℂ) = dS m i := by
  have e := congrFun (congrFun (row_unitary μ hμ) i) i
  rw [Matrix.mul_apply] at e
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq] at e
  rw [← sum_dS (fun j => μ i j), ← e]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem real_of_cs {x : ℝ} (h : (x : ℂ) = 1) : x = 1 := by exact_mod_cast h

theorem real_of_last {x : ℝ} (h : (x : ℂ) = -1) : x = -1 := by exact_mod_cast h

theorem entry_le_last (μ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (hμ : μᴴ * diagonal (dS m) * μ = diagonal (dS m)) (i j : Fin (m + 1)) :
    ‖μ i j‖ ≤ ‖μ (Fin.last m) (Fin.last m)‖ := by
  have hrow := real_of_last (by rw [row_id μ hμ (Fin.last m), dS_last])
  have hsq : ‖μ i j‖ ^ 2 ≤ ‖μ (Fin.last m) (Fin.last m)‖ ^ 2 := by
    have hrow' : ∀ j0 : Fin m, ‖μ (Fin.last m) j0.castSucc‖ ^ 2 ≤ ‖μ (Fin.last m) (Fin.last m)‖ ^ 2 - 1 := by
      intro j0
      have : ‖μ (Fin.last m) j0.castSucc‖ ^ 2 ≤ ∑ j : Fin m, ‖μ (Fin.last m) j.castSucc‖ ^ 2 :=
        Finset.single_le_sum (f := fun j : Fin m => ‖μ (Fin.last m) j.castSucc‖ ^ 2)
          (fun j _ => by positivity) (Finset.mem_univ j0)
      linarith
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j0, rfl⟩ | rfl
    · have hcol := real_of_cs (by rw [col_id μ hμ j0.castSucc, dS_cs])
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i0, rfl⟩ | rfl
      · have : ‖μ i0.castSucc j0.castSucc‖ ^ 2 ≤ ∑ i : Fin m, ‖μ i.castSucc j0.castSucc‖ ^ 2 :=
          Finset.single_le_sum (f := fun i : Fin m => ‖μ i.castSucc j0.castSucc‖ ^ 2)
            (fun i _ => by positivity) (Finset.mem_univ i0)
        linarith [hrow' j0]
      · linarith [hrow' j0]
    · have hcol := real_of_last (by rw [col_id μ hμ (Fin.last m), dS_last])
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i0, rfl⟩ | rfl
      · have : ‖μ i0.castSucc (Fin.last m)‖ ^ 2 ≤ ∑ i : Fin m, ‖μ i.castSucc (Fin.last m)‖ ^ 2 :=
          Finset.single_le_sum (f := fun i : Fin m => ‖μ i.castSucc (Fin.last m)‖ ^ 2)
            (fun i _ => by positivity) (Finset.mem_univ i0)
        linarith
      · exact le_rfl
  exact pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero |>.mp hsq

theorem entry_bound (μ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (hμ : μᴴ * diagonal (dS m) * μ = diagonal (dS m)) (z z' : Fin (m + 1) → ℂ) (T T' : ℝ) (hT : 0 < T)
    (hT' : 0 < T') (hz : ∑ i : Fin m, ‖z i.castSucc‖ ^ 2 = ‖z (Fin.last m)‖ ^ 2 - T)
    (hz' : ∑ i : Fin m, ‖z' i.castSucc‖ ^ 2 = ‖z' (Fin.last m)‖ ^ 2 - T') (i j : Fin (m + 1)) :
    ‖μ i j‖ * (T * T') ≤
      4 * ‖z (Fin.last m)‖ * ‖z' (Fin.last m)‖ * ‖star z ⬝ᵥ (diagonal (dS m) *ᵥ (μ *ᵥ z'))‖ := by
  set y := μ *ᵥ z' with hy

  have hyq : ∑ i : Fin m, ‖y i.castSucc‖ ^ 2 ≤ ‖y (Fin.last m)‖ ^ 2 := by
    have e := quad_unitary μ hμ z'
    rw [quad_eq, quad_eq, sum_dS, sum_dS] at e
    have e' : ∑ i : Fin m, ‖y i.castSucc‖ ^ 2 - ‖y (Fin.last m)‖ ^ 2 =
        ∑ i : Fin m, ‖z' i.castSucc‖ ^ 2 - ‖z' (Fin.last m)‖ ^ 2 := by exact_mod_cast e
    linarith

  have h1 : ‖y (Fin.last m)‖ * T ≤ 2 * ‖z (Fin.last m)‖ *
      ‖star z ⬝ᵥ (diagonal (dS m) *ᵥ y)‖ := by
    have hb : ∑ i : Fin m, ‖(fun i => -star (z i)) i.castSucc‖ ^ 2 ≤
        ‖(fun i => -star (z i)) (Fin.last m)‖ ^ 2 - T := by
      simp only [norm_neg, norm_star]; linarith
    have := rev_cs y (fun i => -star (z i)) (∑ i : Fin m, star (z i.castSucc) * y i.castSucc) T hT hyq hb (by
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [norm_mul, norm_neg, norm_star, mul_comm])
    simp only [norm_neg, norm_star] at this
    have hζ : star z ⬝ᵥ (diagonal (dS m) *ᵥ y) =
        y (Fin.last m) * -star (z (Fin.last m)) + ∑ i : Fin m, star (z i.castSucc) * y i.castSucc := by
      rw [quad_eq, Fin.sum_univ_castSucc, dS_last]
      simp only [dS_cs, mul_one]
      ring
    rw [hζ]; exact this

  have h2 : ‖μ (Fin.last m) (Fin.last m)‖ * T' ≤ 2 * ‖z' (Fin.last m)‖ * ‖y (Fin.last m)‖ := by
    have hrow := real_of_last (by rw [row_id μ hμ (Fin.last m), dS_last])
    have ha : ∑ j : Fin m, ‖(fun j => μ (Fin.last m) j) j.castSucc‖ ^ 2 ≤
        ‖(fun j => μ (Fin.last m) j) (Fin.last m)‖ ^ 2 := by simp only; linarith
    have hb : ∑ i : Fin m, ‖z' i.castSucc‖ ^ 2 ≤ ‖z' (Fin.last m)‖ ^ 2 - T' := le_of_eq hz'
    have := rev_cs (fun j => μ (Fin.last m) j) z' (∑ j : Fin m, μ (Fin.last m) j.castSucc * z' j.castSucc) T' hT'
      ha hb (by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [norm_mul])
    have hyL : y (Fin.last m) =
        μ (Fin.last m) (Fin.last m) * z' (Fin.last m) + ∑ j : Fin m, μ (Fin.last m) j.castSucc * z' j.castSucc := by
      rw [hy, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]; ring
    rw [hyL]; exact this
  have h3 := entry_le_last μ hμ i j
  have hzL : 0 ≤ ‖z (Fin.last m)‖ := norm_nonneg _
  have hz'L : 0 ≤ ‖z' (Fin.last m)‖ := norm_nonneg _
  calc ‖μ i j‖ * (T * T') ≤ ‖μ (Fin.last m) (Fin.last m)‖ * T' * T := by
        rw [mul_comm T T', ← mul_assoc]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 hT'.le) hT.le
    _ ≤ 2 * ‖z' (Fin.last m)‖ * ‖y (Fin.last m)‖ * T := mul_le_mul_of_nonneg_right h2 hT.le
    _ = 2 * ‖z' (Fin.last m)‖ * (‖y (Fin.last m)‖ * T) := by ring
    _ ≤ 2 * ‖z' (Fin.last m)‖ * (2 * ‖z (Fin.last m)‖ * ‖star z ⬝ᵥ (diagonal (dS m) *ᵥ y)‖) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring

end hyp

end Formalism.FourierDecayAlt.P.CutEXPbSupp
