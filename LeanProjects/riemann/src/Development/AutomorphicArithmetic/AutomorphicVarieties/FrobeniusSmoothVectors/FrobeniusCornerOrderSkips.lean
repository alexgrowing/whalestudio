import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CornerUnits

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem ch2 {K : Type} [CommRing K] (M : Matrix (Fin 2) (Fin 2) K) :
    M * (M.trace • (1 : Matrix (Fin 2) (Fin 2) K) - M) = M.det • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

theorem UpperTheory.V.Fr.frobenius_corner_order_skips :
    ∀ {H K : Type} [Group H] [CommRing K] (σ : H →* Matrix (Fin 2) (Fin 2) K) (a : H → K) (c : H →* K) (g₁ : H) (t : K), IsUnit (σ g₁ - t • (1 : Matrix (Fin 2) (Fin 2) K)).det → (∀ x y, (σ x - a x • (1 : Matrix (Fin 2) (Fin 2) K)) * (σ g₁ - t • (1 : Matrix (Fin 2) (Fin 2) K)) * (σ y - c y • (1 : Matrix (Fin 2) (Fin 2) K)) = 0) → ∀ x y, (σ x - a x • (1 : Matrix (Fin 2) (Fin 2) K)) * (σ y - c y • (1 : Matrix (Fin 2) (Fin 2) K)) = 0 := by
  intro H K _ _ σ a c g t hu h x y
  set P := σ x - a x • (1 : Matrix (Fin 2) (Fin 2) K) with hP
  set M := σ g - t • (1 : Matrix (Fin 2) (Fin 2) K) with hM
  have hQ : ∀ z, P * M * σ z = c z • (P * M) := fun z => by
    have := h x z
    rw [mul_sub, Matrix.mul_smul, mul_one, sub_eq_zero] at this
    exact this
  have h0 : P * M * (σ y - c y • (1 : Matrix (Fin 2) (Fin 2) K)) = 0 := h x y
  have h1 : P * M * M = (c g - t) • (P * M) := by
    conv_lhs => rw [show P * M * M = P * M * (σ g - t • (1 : Matrix (Fin 2) (Fin 2) K)) from rfl]
    rw [mul_sub, hQ, Matrix.mul_smul, mul_one, sub_smul]
  have h2 : M.det • P = (M.trace - (c g - t)) • (P * M) := by
    calc M.det • P = P * (M * (M.trace • (1 : Matrix (Fin 2) (Fin 2) K) - M)) := by
          rw [ch2, Matrix.mul_smul, mul_one]
      _ = _ := by rw [← mul_assoc, mul_sub, h1, Matrix.mul_smul, mul_one, ← sub_smul]
  have h3 : M.det • (P * (σ y - c y • (1 : Matrix (Fin 2) (Fin 2) K))) = 0 := by
    rw [← Matrix.smul_mul, h2, Matrix.smul_mul, h0, smul_zero]
  exact (hu.smul_eq_zero).1 h3
