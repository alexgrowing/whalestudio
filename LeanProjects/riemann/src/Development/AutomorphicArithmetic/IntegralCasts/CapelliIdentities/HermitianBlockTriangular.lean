import Mathlib

theorem UpperTheory.hermitian_block_triangular :
    ∀ {S : Type} [CommRing S] (τ : S →+* S), (∀ x, τ (τ x) = x) → ∀ {n r : ℕ}
        (J g : Matrix (Fin n) (Fin n) S) (X Y : Matrix (Fin n) (Fin r) S)
        (B : Matrix (Fin r) (Fin r) S) (Xd Yd : Matrix (Fin r) (Fin n) S),
        (J.map τ).transpose = J →
        Xd = (X.map τ).transpose * J → Yd = (Y.map τ).transpose * J →
        Xd * Y = 1 →
        (g.map τ).transpose * J * g = J →
        B.BlockTriangular id → g * X = X * B →
        Yd * X = 1 ∧ Yd * g * X = B ∧ Xd * g = (Xd * g * Y) * Xd ∧
          ∀ i, τ ((Xd * g * Y) i i) * B i i = 1 := by
  intro S _ τ hτ n r J g X Y B Xd Yd hJ hXd hYd hXY hg hB hgX
  classical
  have star_mul : ∀ {a b c : ℕ} (P : Matrix (Fin a) (Fin b) S) (Q : Matrix (Fin b) (Fin c) S),
      ((P * Q).map τ).transpose = (Q.map τ).transpose * (P.map τ).transpose := by
    intro a b c P Q
    rw [Matrix.map_mul, Matrix.transpose_mul]
  have star_star : ∀ {a b : ℕ} (P : Matrix (Fin a) (Fin b) S),
      (((P.map τ).transpose).map τ).transpose = P := by
    intro a b P
    ext i j
    simp [hτ]
  have star_one : (((1 : Matrix (Fin r) (Fin r) S)).map τ).transpose = 1 := by
    rw [Matrix.map_one τ (map_zero τ) (map_one τ), Matrix.transpose_one]
  have h1 : Yd * X = 1 := by
    have h := congrArg (fun M : Matrix (Fin r) (Fin r) S => (M.map τ).transpose) hXY
    simp only [star_one] at h
    rw [star_mul, hXd, star_mul, star_star, hJ, ← Matrix.mul_assoc, ← hYd] at h
    exact h
  have h2 : Yd * g * X = B := by
    rw [Matrix.mul_assoc, hgX, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hs : (X.map τ).transpose * (g.map τ).transpose
      = (B.map τ).transpose * (X.map τ).transpose := by
    rw [← star_mul, ← star_mul, hgX]
  have hD : (B.map τ).transpose * (Xd * g) = Xd := by
    calc (B.map τ).transpose * (Xd * g)
        = ((B.map τ).transpose * (X.map τ).transpose) * J * g := by
          rw [hXd]; simp only [Matrix.mul_assoc]
      _ = (X.map τ).transpose * ((g.map τ).transpose * J * g) := by
          rw [← hs]; simp only [Matrix.mul_assoc]
      _ = Xd := by rw [hg, hXd]
  have hC : (B.map τ).transpose * (Xd * g * Y) = 1 := by
    rw [← Matrix.mul_assoc, hD, hXY]
  have hC' : (Xd * g * Y) * (B.map τ).transpose = 1 := mul_eq_one_comm.mp hC
  have h3 : Xd * g = (Xd * g * Y) * Xd := by
    calc Xd * g = ((Xd * g * Y) * (B.map τ).transpose) * (Xd * g) := by
          rw [hC', Matrix.one_mul]
      _ = (Xd * g * Y) * ((B.map τ).transpose * (Xd * g)) := by rw [Matrix.mul_assoc]
      _ = (Xd * g * Y) * Xd := by rw [hD]
  have h4 : ((Xd * g * Y).map τ).transpose * B = 1 := by
    have h := congrArg (fun M : Matrix (Fin r) (Fin r) S => (M.map τ).transpose) hC
    simp only [star_one] at h
    rwa [star_mul, star_star] at h
  refine ⟨h1, h2, h3, fun i => ?_⟩
  letI : Invertible B := invertibleOfLeftInverse B _ h4
  have hinv : (B⁻¹) = ((Xd * g * Y).map τ).transpose := Matrix.inv_eq_left_inv h4
  have htri : (B⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hB
  have h5 := congrFun (congrFun h4 i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i] at h5
  · simpa only [Matrix.transpose_apply, Matrix.map_apply, Matrix.one_apply_eq] using h5
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hlt | hgt
    · have : (B⁻¹) i k = 0 := htri hlt
      rw [hinv] at this
      rw [this, zero_mul]
    · have : B k i = 0 := hB hgt
      rw [this, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h
