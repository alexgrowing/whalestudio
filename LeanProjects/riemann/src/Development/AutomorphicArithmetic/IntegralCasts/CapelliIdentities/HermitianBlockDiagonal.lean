import Mathlib

private lemma ad_mul {S : Type} [CommRing S] (τ : S →+* S) {a b c : ℕ}
    (A : Matrix (Fin a) (Fin b) S) (B : Matrix (Fin b) (Fin c) S) :
    ((A * B).map τ).transpose = (B.map τ).transpose * (A.map τ).transpose := by
  rw [Matrix.map_mul, Matrix.transpose_mul]

private lemma ad_add {S : Type} [CommRing S] (τ : S →+* S) {a b : ℕ}
    (A B : Matrix (Fin a) (Fin b) S) :
    ((A + B).map τ).transpose = (A.map τ).transpose + (B.map τ).transpose := by
  ext i j
  simp

private lemma ad_ad {S : Type} [CommRing S] (τ : S →+* S) (hτ : ∀ x, τ (τ x) = x) {a b : ℕ}
    (A : Matrix (Fin a) (Fin b) S) :
    (((A.map τ).transpose).map τ).transpose = A := by
  ext i j
  simp [hτ]

private lemma ad_one {S : Type} [CommRing S] (τ : S →+* S) {a : ℕ} :
    (((1 : Matrix (Fin a) (Fin a) S)).map τ).transpose = 1 := by
  rw [Matrix.map_one τ (map_zero τ) (map_one τ), Matrix.transpose_one]

private lemma ad_diag_mul {S : Type} [CommRing S] (τ : S →+* S) {r : ℕ} (u v : Fin r → S)
    (h : ∀ i, τ (u i) * v i = 1) :
    ((Matrix.diagonal u).map τ).transpose * Matrix.diagonal v = 1 := by
  rw [Matrix.diagonal_map (map_zero τ), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact h i

theorem UpperTheory.hermitian_block_diagonal :
    ∀ {S : Type} [CommRing S] (τ : S →+* S), (∀ x, τ (τ x) = x) → ∀ {n r : ℕ}
        (J g P m : Matrix (Fin n) (Fin n) S) (X Y : Matrix (Fin n) (Fin r) S)
        (C : Matrix (Fin r) (Fin r) S) (Xd Yd : Matrix (Fin r) (Fin n) S) (d e : Fin r → S),
        (J.map τ).transpose = J → IsUnit J.det →
        Xd = (X.map τ).transpose * J → Yd = (Y.map τ).transpose * J →
        Xd * X = 0 → Yd * Y = 0 → Xd * Y = 1 →
        (g.map τ).transpose * J * g = J →
        Xd * g = C * Xd →
        (∀ i, τ (e i) * d i = 1) →
        P = 1 - X * Yd - Y * Xd →
        m = (X * Matrix.diagonal d) * Yd + (Y * Matrix.diagonal e) * Xd + P * g * P →
        IsUnit m.det ∧ (m.map τ).transpose * J * m = J ∧
          m * X = X * Matrix.diagonal d ∧ m * Y = Y * Matrix.diagonal e := by
  intro S _ τ hτ n r J g P m X Y C Xd Yd d e hJ hdet hXd hYd hXX hYY hXY hg hC hde hP hm
  have adXd : (Xd.map τ).transpose = J * X := by rw [hXd, ad_mul, hJ, ad_ad τ hτ]
  have adYd : (Yd.map τ).transpose = J * Y := by rw [hYd, ad_mul, hJ, ad_ad τ hτ]
  have hYX : Yd * X = 1 := by
    have h := congrArg (fun A => (A.map τ).transpose) hXY
    simp only [ad_mul, adXd, ad_one] at h
    rw [hYd, Matrix.mul_assoc, h]
  have hed : ((Matrix.diagonal e).map τ).transpose * Matrix.diagonal d = 1 :=
    ad_diag_mul τ e d hde
  have hdeD : ((Matrix.diagonal d).map τ).transpose * Matrix.diagonal e = 1 :=
    ad_diag_mul τ d e (fun i => by
      have h := congrArg τ (hde i)
      rw [map_mul, hτ, map_one, mul_comm] at h
      exact h)
  have XX : ∀ {k : ℕ} (A : Matrix (Fin r) (Fin k) S), Xd * (X * A) = 0 := fun A => by
    rw [← Matrix.mul_assoc, hXX, Matrix.zero_mul]
  have YY : ∀ {k : ℕ} (A : Matrix (Fin r) (Fin k) S), Yd * (Y * A) = 0 := fun A => by
    rw [← Matrix.mul_assoc, hYY, Matrix.zero_mul]
  have XY : ∀ {k : ℕ} (A : Matrix (Fin r) (Fin k) S), Xd * (Y * A) = A := fun A => by
    rw [← Matrix.mul_assoc, hXY, Matrix.one_mul]
  have YX : ∀ {k : ℕ} (A : Matrix (Fin r) (Fin k) S), Yd * (X * A) = A := fun A => by
    rw [← Matrix.mul_assoc, hYX, Matrix.one_mul]
  have PX : P * X = 0 := by
    rw [hP]
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hYX, hXX, Matrix.mul_one,
      Matrix.mul_zero, sub_self, sub_zero]
  have PY : P * Y = 0 := by
    rw [hP]
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hYY, hXY, Matrix.mul_one,
      Matrix.mul_zero, sub_zero, sub_self]
  have XdP : Xd * P = 0 := by
    rw [hP]
    simp only [Matrix.mul_sub, Matrix.mul_one, XX, XY, sub_zero, sub_self]
  have YdP : Yd * P = 0 := by
    rw [hP]
    simp only [Matrix.mul_sub, Matrix.mul_one, YX, YY, sub_zero, sub_self]
  have PP : P * P = P := by
    calc P * P = (1 - X * Yd - Y * Xd) * P := by rw [← hP]
      _ = P := by
        simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, YdP, XdP, Matrix.mul_zero,
          sub_zero]
  have PX' : ∀ {k : ℕ} (A : Matrix (Fin r) (Fin k) S), P * (X * A) = 0 := fun A => by
    rw [← Matrix.mul_assoc, PX, Matrix.zero_mul]
  have PY' : ∀ {k : ℕ} (A : Matrix (Fin r) (Fin k) S), P * (Y * A) = 0 := fun A => by
    rw [← Matrix.mul_assoc, PY, Matrix.zero_mul]
  have XdP' : ∀ {k : ℕ} (A : Matrix (Fin n) (Fin k) S), Xd * (P * A) = 0 := fun A => by
    rw [← Matrix.mul_assoc, XdP, Matrix.zero_mul]
  have YdP' : ∀ {k : ℕ} (A : Matrix (Fin n) (Fin k) S), Yd * (P * A) = 0 := fun A => by
    rw [← Matrix.mul_assoc, YdP, Matrix.zero_mul]
  have PP' : ∀ {k : ℕ} (A : Matrix (Fin n) (Fin k) S), P * (P * A) = P * A := fun A => by
    rw [← Matrix.mul_assoc, PP]
  have hed' : ∀ {k : ℕ} (A : Matrix (Fin r) (Fin k) S),
      ((Matrix.diagonal e).map τ).transpose * (Matrix.diagonal d * A) = A := fun A => by
    rw [← Matrix.mul_assoc, hed, Matrix.one_mul]
  have hde' : ∀ {k : ℕ} (A : Matrix (Fin r) (Fin k) S),
      ((Matrix.diagonal d).map τ).transpose * (Matrix.diagonal e * A) = A := fun A => by
    rw [← Matrix.mul_assoc, hdeD, Matrix.one_mul]
  have hmX : m * X = X * Matrix.diagonal d := by
    rw [hm]
    simp only [Matrix.add_mul, Matrix.mul_assoc, hYX, hXX, PX, Matrix.mul_one, Matrix.mul_zero,
      add_zero]
  have hmY : m * Y = Y * Matrix.diagonal e := by
    rw [hm]
    simp only [Matrix.add_mul, Matrix.mul_assoc, hYY, hXY, PY, Matrix.mul_one, Matrix.mul_zero,
      add_zero, zero_add]
  have hPJ : (P.map τ).transpose * J = J * P := by
    have hPe : P + X * Yd + Y * Xd = 1 := by rw [hP]; abel
    have h := congrArg (fun A => (A.map τ).transpose) hPe
    simp only [ad_add, ad_mul, adXd, adYd, ad_one] at h
    have h2 : (P.map τ).transpose = 1 - (J * Y) * (X.map τ).transpose
        - (J * X) * (Y.map τ).transpose := by
      rw [← h]; abel
    rw [h2, hP]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc,
      ← hXd, ← hYd]
    abel
  have hPJ' : ∀ {k : ℕ} (A : Matrix (Fin n) (Fin k) S),
      (P.map τ).transpose * (J * A) = J * (P * A) := fun A => by
    rw [← Matrix.mul_assoc, hPJ, Matrix.mul_assoc]
  have hg' : ∀ {k : ℕ} (A : Matrix (Fin n) (Fin k) S),
      (g.map τ).transpose * (J * (g * A)) = J * A := fun A => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hg]
  have hgX : (g.map τ).transpose * (J * X) = J * (X * (C.map τ).transpose) := by
    have h := congrArg (fun A => (A.map τ).transpose) hC
    simp only [ad_mul, adXd] at h
    rw [h, Matrix.mul_assoc]
  have hgX' : ∀ {k : ℕ} (A : Matrix (Fin r) (Fin k) S),
      (g.map τ).transpose * (J * (X * A)) = J * (X * ((C.map τ).transpose * A)) := fun A => by
    rw [← Matrix.mul_assoc J X A, ← Matrix.mul_assoc, hgX]
    simp only [Matrix.mul_assoc]
  have hC' : ∀ {k : ℕ} (A : Matrix (Fin n) (Fin k) S), Xd * (g * A) = C * (Xd * A) := fun A => by
    rw [← Matrix.mul_assoc, hC, Matrix.mul_assoc]
  have hmid : (g.map τ).transpose * (J * (P * (g * P))) =
      J * P - J * (X * ((C.map τ).transpose * (Yd * (g * P)))) := by
    have hexp : ∀ {k : ℕ} (A : Matrix (Fin n) (Fin k) S),
        P * A = A - X * (Yd * A) - Y * (Xd * A) := fun A => by
      rw [hP]
      simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
    rw [hexp (g * P)]
    simp only [Matrix.mul_sub, hg', hgX', hC', XdP, Matrix.mul_zero, sub_zero]
  have hadm : (m.map τ).transpose =
      (J * Y) * (((Matrix.diagonal d).map τ).transpose * (X.map τ).transpose)
        + (J * X) * (((Matrix.diagonal e).map τ).transpose * (Y.map τ).transpose)
        + (P.map τ).transpose * ((g.map τ).transpose * (P.map τ).transpose) := by
    rw [hm]
    simp only [ad_add, ad_mul, adXd, adYd, Matrix.mul_assoc]
  have hiso : (m.map τ).transpose * J * m = J := by
    have hmJ : (m.map τ).transpose * J =
        J * (Y * (((Matrix.diagonal d).map τ).transpose * Xd))
          + J * (X * (((Matrix.diagonal e).map τ).transpose * Yd))
          + (P.map τ).transpose * ((g.map τ).transpose * (J * P)) := by
      rw [hadm, hXd, hYd]
      simp only [Matrix.add_mul, Matrix.mul_assoc, hPJ]
    rw [hmJ]
    conv_lhs => rw [hm]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, XX, XY, YX, YY, XdP', YdP',
      PX', PY', PP', XdP, YdP, hed', hde', Matrix.mul_zero, add_zero, zero_add, hmid,
      Matrix.mul_sub, hPJ', PP]
    conv_rhs => rw [show J = J * (1 : Matrix (Fin n) (Fin n) S) from (Matrix.mul_one J).symm]
    rw [show (1 : Matrix (Fin n) (Fin n) S) = P + X * Yd + Y * Xd by rw [hP]; abel]
    simp only [Matrix.mul_add]
    abel
  refine ⟨?_, hiso, hmX, hmY⟩
  have h := congrArg Matrix.det hiso
  rw [Matrix.det_mul] at h
  rw [← h] at hdet
  exact isUnit_of_mul_isUnit_right hdet
