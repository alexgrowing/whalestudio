import Mathlib

private theorem UpperTheory.Reformulated.B.IntertwinerDiagonalization.of_intertwine {K : Type} [Field K]
    (M : GL (Fin 2) K) (D P : Matrix (Fin 2) (Fin 2) K) (hP : P.det ≠ 0)
    (h : (↑M : Matrix (Fin 2) (Fin 2) K) * P = P * D) :
    ∃ (g : GL (Fin 2) K), (↑(g * M * g⁻¹) : Matrix (Fin 2) (Fin 2) K) = D := by
  let u : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero P hP
  have hu : (↑u : Matrix (Fin 2) (Fin 2) K) = P := rfl
  refine ⟨u⁻¹, ?_⟩
  rw [inv_inv, Units.val_mul, Units.val_mul, mul_assoc, hu, h, ← hu, ← mul_assoc,
    Units.inv_mul, one_mul]

theorem UpperTheory.Reformulated.B.IntertwinerDiagonalization.exists_diag :
    ∀ {K : Type} [inst : Field K]
    (M : GL (Fin (2 : ℕ)) K) {x : K},
    x ≠ (1 : K) →
      (↑M : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) K).trace = (1 : K) + x →
        (↑M : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) K).det = x →
          ∃ (g : GL (Fin (2 : ℕ)) K),
            (↑(g * M * g⁻¹) : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) K) = Matrix.diagonal ![(1 : K), x] := by
  intro K _ M x hx ht hd
  have hx' : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  rw [Matrix.trace_fin_two] at ht
  rw [Matrix.det_fin_two] at hd
  obtain ⟨a, b, c, d, hM⟩ : ∃ a b c d : K, (↑M : Matrix (Fin 2) (Fin 2) K) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hD : (Matrix.diagonal ![(1 : K), x] : Matrix (Fin 2) (Fin 2) K) = !![1, 0; 0, x] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hM] at ht hd
  have ht' : a + d = 1 + x := by simpa using ht
  have hd' : a * d - b * c = x := by simpa using hd
  by_cases hc : c = 0
  · by_cases hb : b = 0
    · have hq : (a - 1) * (a - x) = 0 := by
        rw [hb] at hd'
        linear_combination a * ht' - hd'
      rcases mul_eq_zero.mp hq with h | h
      · have ha : a = 1 := sub_eq_zero.mp h
        have hdx : d = x := by linear_combination ht' - ha
        refine UpperTheory.Reformulated.B.IntertwinerDiagonalization.of_intertwine M _ 1 (by simp) ?_
        rw [hM, hD, ha, hb, hc, hdx, mul_one, one_mul]
      · have ha : a = x := sub_eq_zero.mp h
        have hdx : d = 1 := by linear_combination ht' - ha
        refine UpperTheory.Reformulated.B.IntertwinerDiagonalization.of_intertwine M _ !![0, 1; 1, 0] (by simp) ?_
        rw [hM, hD, ha, hb, hc, hdx, Matrix.mul_fin_two, Matrix.mul_fin_two]
        simp
    · refine UpperTheory.Reformulated.B.IntertwinerDiagonalization.of_intertwine M _ !![b, b; 1 - a, x - a] ?_ ?_
      · have : (!![b, b; 1 - a, x - a] : Matrix (Fin 2) (Fin 2) K).det = b * (x - 1) := by
          rw [Matrix.det_fin_two_of]; ring
        rw [this]
        exact mul_ne_zero hb hx'
      · rw [hM, hD, Matrix.mul_fin_two, Matrix.mul_fin_two]
        have e1 : a * b + b * (1 - a) = b * 1 + b * 0 := by ring
        have e2 : a * b + b * (x - a) = b * 0 + b * x := by ring
        have e3 : c * b + d * (1 - a) = (1 - a) * 1 + (x - a) * 0 := by
          linear_combination ht' - hd'
        have e4 : c * b + d * (x - a) = (1 - a) * 0 + (x - a) * x := by
          linear_combination x * ht' - hd'
        rw [e1, e2, e3, e4]
  · refine UpperTheory.Reformulated.B.IntertwinerDiagonalization.of_intertwine M _ !![1 - d, x - d; c, c] ?_ ?_
    · have : (!![1 - d, x - d; c, c] : Matrix (Fin 2) (Fin 2) K).det = -(c * (x - 1)) := by
        rw [Matrix.det_fin_two_of]; ring
      rw [this]
      exact neg_ne_zero.mpr (mul_ne_zero hc hx')
    · rw [hM, hD, Matrix.mul_fin_two, Matrix.mul_fin_two]
      have e1 : a * (1 - d) + b * c = (1 - d) * 1 + (x - d) * 0 := by
        linear_combination ht' - hd'
      have e2 : a * (x - d) + b * c = (1 - d) * 0 + (x - d) * x := by
        linear_combination x * ht' - hd'
      have e3 : c * (1 - d) + d * c = c * 1 + c * 0 := by ring
      have e4 : c * (x - d) + d * c = c * 0 + c * x := by ring
      rw [e1, e2, e3, e4]
