import Mathlib

theorem UpperTheory.hermitian_projection_eq :
    ∀ {S : Type} [CommRing S] {n r : ℕ}
        (g P m : Matrix (Fin n) (Fin n) S) (X Y : Matrix (Fin n) (Fin r) S)
        (B C : Matrix (Fin r) (Fin r) S) (Xd Yd : Matrix (Fin r) (Fin n) S) (d e : Fin r → S),
        Xd * X = 0 → Yd * Y = 0 → Xd * Y = 1 → Yd * X = 1 →
        B.BlockTriangular id → g * X = X * B → Xd * g = C * Xd →
        (∀ i, d i = B i i) → (∀ i, IsUnit (d i)) →
        P = 1 - X * Yd - Y * Xd →
        m = (X * Matrix.diagonal d) * Yd + (Y * Matrix.diagonal e) * Xd + P * g * P →
        IsUnit m.det →
        (∃ B' : Matrix (Fin r) (Fin r) S, B'.BlockTriangular id ∧ (∀ i, B' i i = 1) ∧
            m⁻¹ * g * X = X * B') ∧
          ∀ z : Fin n → S, Xd.mulVec z = 0 →
            ∃ a : Fin r → S, (m⁻¹ * g - 1).mulVec z = X.mulVec a := by
  intro S _ n r g P m X Y B C Xd Yd d e hXdX hYdY hXdY hYdX hB hgX hXdg hd hu hP hm hdet
  have hmm : m⁻¹ * m = 1 := Matrix.nonsing_inv_mul m hdet
  obtain ⟨f, hf⟩ : ∃ f : Fin r → S, ∀ i, f i * d i = 1 :=
    ⟨fun i => (((hu i).unit⁻¹ : Sˣ) : S), fun i => (hu i).val_inv_mul⟩
  have hDF : Matrix.diagonal d * Matrix.diagonal f = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [mul_comm]
    exact hf i
  have hPX : P * X = 0 := by
    rw [hP, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc X, Matrix.mul_assoc Y, hYdX, hXdX,
      Matrix.mul_one, Matrix.mul_zero, sub_self, sub_zero]
  have hmX : m * X = X * Matrix.diagonal d := by
    rw [hm, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc _ Yd, Matrix.mul_assoc _ Xd, hYdX, hXdX,
      Matrix.mul_assoc _ P, hPX, Matrix.mul_one, Matrix.mul_zero, Matrix.mul_zero, add_zero,
      add_zero]
  have hinvX : m⁻¹ * X = X * Matrix.diagonal f := by
    calc m⁻¹ * X = m⁻¹ * (X * (Matrix.diagonal d * Matrix.diagonal f)) := by
          rw [hDF, Matrix.mul_one]
      _ = (m⁻¹ * m) * (X * Matrix.diagonal f) := by
          rw [← Matrix.mul_assoc X, ← hmX, Matrix.mul_assoc m, Matrix.mul_assoc m⁻¹]
      _ = X * Matrix.diagonal f := by rw [hmm, Matrix.one_mul]
  have hPgX : P * g * X = 0 := by
    rw [Matrix.mul_assoc, hgX, ← Matrix.mul_assoc, hPX, Matrix.zero_mul]
  have hPg : P * g = g - X * (Yd * g) - Y * C * Xd := by
    rw [hP, sub_mul, sub_mul, Matrix.one_mul, Matrix.mul_assoc X, Matrix.mul_assoc Y, hXdg,
      Matrix.mul_assoc Y]
  have hPgP : P * g * P = P * g - P * g * Y * Xd := by
    have h0 : P * g * P = P * g * (1 - X * Yd - Y * Xd) := by rw [← hP]
    rw [h0, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc _ X, hPgX,
      Matrix.zero_mul, sub_zero, ← Matrix.mul_assoc _ Y]
  have hid : g - m = X * (Yd * g - Matrix.diagonal d * Yd)
      + (Y * C - Y * Matrix.diagonal e + P * g * Y) * Xd := by
    rw [hm, hPgP, hPg]
    simp only [Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc]
    abel
  refine ⟨⟨Matrix.diagonal f * B, ?_, ?_, ?_⟩, ?_⟩
  · intro i j hij
    rw [Matrix.diagonal_mul, hB hij, mul_zero]
  · intro i
    rw [Matrix.diagonal_mul, ← hd i]
    exact hf i
  · rw [Matrix.mul_assoc, hgX, ← Matrix.mul_assoc, hinvX, Matrix.mul_assoc]
  · intro z hz
    refine ⟨(Matrix.diagonal f * (Yd * g - Matrix.diagonal d * Yd)).mulVec z, ?_⟩
    have h1 : m⁻¹ * g - 1 = (X * Matrix.diagonal f) * (Yd * g - Matrix.diagonal d * Yd)
        + m⁻¹ * (Y * C - Y * Matrix.diagonal e + P * g * Y) * Xd := by
      calc m⁻¹ * g - 1 = m⁻¹ * (g - m) := by rw [Matrix.mul_sub, hmm]
        _ = _ := by
          rw [hid, Matrix.mul_add, ← Matrix.mul_assoc, hinvX, ← Matrix.mul_assoc]
    rw [h1, Matrix.add_mulVec, ← Matrix.mulVec_mulVec z _ Xd, hz, Matrix.mulVec_zero, add_zero,
      Matrix.mul_assoc X, Matrix.mulVec_mulVec]
