import Mathlib

namespace GlobalTheory.FrobeniusDefect

open Matrix

variable {R : Type} [CommRing R] {d : ℕ}

theorem nzd_mul {a b : R} (ha : ∀ x : R, a * x = 0 → x = 0) (hb : ∀ x : R, b * x = 0 → x = 0) :
    ∀ x : R, (a * b) * x = 0 → x = 0 :=
  fun x h => hb x (ha _ (by rw [← mul_assoc]; exact h))

theorem nzd_pow {a : R} (ha : ∀ x : R, a * x = 0 → x = 0) :
    ∀ n : ℕ, ∀ x : R, a ^ n * x = 0 → x = 0
  | 0 => fun x h => by simpa using h
  | n + 1 => by rw [pow_succ]; exact nzd_mul (nzd_pow ha n) ha

theorem nzd_unit {a : R} (ha : ∀ x : R, a * x = 0 → x = 0) (v : Rˣ) :
    ∀ x : R, (a * v) * x = 0 → x = 0 :=
  nzd_mul ha (fun x h => by simpa using congrArg (fun y => (↑v⁻¹ : R) * y) h)

theorem smul_cancel {c : R} (hc : ∀ x : R, c * x = 0 → x = 0)
    {M N : Matrix (Fin d) (Fin d) R} (h : c • M = c • N) : M = N := by
  ext i j
  have := congrArg (fun P => P i j) h
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact sub_eq_zero.mp (hc _ (by rw [mul_sub, this, sub_self]))

theorem mul_left_of {c : R} {P P' : Matrix (Fin d) (Fin d) R} (h : P * P' = c • 1)
    (X : Matrix (Fin d) (Fin d) R) : P * (P' * X) = c • X := by
  rw [← Matrix.mul_assoc, h, Matrix.smul_mul, Matrix.one_mul]

theorem left_cancel {c : R} (hc : ∀ x : R, c * x = 0 → x = 0)
    {P P' : Matrix (Fin d) (Fin d) R} (h : P' * P = c • 1)
    {X Y : Matrix (Fin d) (Fin d) R} (hXY : P * X = P * Y) : X = Y :=
  smul_cancel hc (by rw [← mul_left_of h X, ← mul_left_of h Y, hXY])

theorem mul_comm_of_nzd {c : R} (hc : ∀ x : R, c * x = 0 → x = 0)
    {M M' : Matrix (Fin d) (Fin d) R} (h : M * M' = c • 1) : M' * M = c • 1 := by
  have hdet : M.det * M'.det = c ^ d := by
    rw [← Matrix.det_mul, h, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hdM : ∀ x : R, M.det * x = 0 → x = 0 := fun x hx =>
    nzd_pow hc d x (by rw [← hdet, mul_comm M.det, mul_assoc, hx, mul_zero])
  have h0 : M * (M' * M - c • 1) = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, h, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul, sub_self]
  have h1 : M.det • (M' * M - c • 1) = M.det • (0 : Matrix (Fin d) (Fin d) R) := by
    calc M.det • (M' * M - c • 1)
          = (M.det • (1 : Matrix (Fin d) (Fin d) R)) * (M' * M - c • 1) := by
            rw [Matrix.smul_mul, Matrix.one_mul]
      _ = M.adjugate * M * (M' * M - c • 1) := by rw [Matrix.adjugate_mul]
      _ = M.det • (0 : Matrix (Fin d) (Fin d) R) := by rw [Matrix.mul_assoc, h0, Matrix.mul_zero, smul_zero]
  exact sub_eq_zero.mp (smul_cancel hdM h1)

theorem map_smul_one (f : R →+* R) (c : R) :
    (c • (1 : Matrix (Fin d) (Fin d) R)).map f = f c • (1 : Matrix (Fin d) (Fin d) R) := by
  ext i j
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem map_smul' (f : R →+* R) (c : R) (M : Matrix (Fin d) (Fin d) R) :
    (c • M).map f = f c • M.map f := by
  ext i j
  simp

theorem frobenius_defect_eq (R : Type) [CommRing R] (φ σ : R →+* R) (d N k : ℕ) (lr e e₀ : R)
    (Q Q' B B' A₀ A₀' ε : Matrix (Fin d) (Fin d) R)
    (hlr : ∀ x : R, lr * x = 0 → x = 0) (hev : ∃ v : Rˣ, e = lr * v) (he₀v : ∃ v : Rˣ, e₀ = lr * v)
    (hφσ : ∀ x, φ (σ x) = σ (φ x)) (hφlr : φ lr = lr) (hσlr : σ lr = lr) (hσe₀ : σ e₀ = e₀)
    (hA₀σ : A₀.map σ = A₀)
    (hQQ' : Q * Q' = lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R))
    (hBB' : B * B' = e ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) R))
    (hAA' : A₀ * A₀' = e₀ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) R))
    (hQA : e ^ N • (Q * A₀) = e₀ ^ N • (B * Q.map φ))
    (hεB : e ^ N • (ε * B.map σ) = σ e ^ N • (B * ε.map φ)) :
    e₀ ^ (2 * N) • (Q' * ε * Q.map σ - lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R)) =
      A₀ * (Q' * ε * Q.map σ - lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R)).map φ * A₀' := by
  obtain ⟨v, hv⟩ := hev
  obtain ⟨v₀, hv₀⟩ := he₀v
  have he : ∀ x : R, e * x = 0 → x = 0 := by rw [hv]; exact nzd_unit hlr v
  have he₀ : ∀ x : R, e₀ * x = 0 → x = 0 := by rw [hv₀]; exact nzd_unit hlr v₀
  have hσe : ∀ x : R, σ e * x = 0 → x = 0 := by
    have : σ e = lr * ((Units.map (σ : R →* R) v : Rˣ) : R) := by
      rw [hv, map_mul, hσlr]; rfl
    rw [this]; exact nzd_unit hlr _
  have hL := nzd_pow hlr (2 * k)
  have hB'B : B' * B = e ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) R) :=
    mul_comm_of_nzd (nzd_pow he _) hBB'
  have hσBB' : B.map σ * B'.map σ = σ e ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) R) := by
    rw [← Matrix.map_mul, hBB', map_smul_one, map_pow]
  have hφQ'Q : Q'.map φ * Q.map φ = lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R) := by
    rw [← Matrix.map_mul, mul_comm_of_nzd hL hQQ', map_smul_one, map_pow, hφlr]

  have h1 : B' * (Q * A₀) = (e * e₀) ^ N • Q.map φ := by
    apply smul_cancel (nzd_pow he N)
    calc e ^ N • (B' * (Q * A₀)) = B' * (e ^ N • (Q * A₀)) := by rw [Matrix.mul_smul]
      _ = B' * (e₀ ^ N • (B * Q.map φ)) := by rw [hQA]
      _ = e₀ ^ N • (B' * (B * Q.map φ)) := by rw [Matrix.mul_smul]
      _ = e₀ ^ N • (e ^ (2 * N) • Q.map φ) := by rw [mul_left_of hB'B]
      _ = e ^ N • ((e * e₀) ^ N • Q.map φ) := by rw [smul_smul, smul_smul]; congr 1; ring

  have h2 : (e * e₀) ^ N • Q'.map φ = A₀' * (Q' * B) := by
    apply left_cancel hL hφQ'Q
    apply smul_cancel (nzd_pow (nzd_mul he he₀) N)
    have lhs : (e * e₀) ^ N • (Q.map φ * ((e * e₀) ^ N • Q'.map φ)) =
        ((e * e₀) ^ (2 * N) * lr ^ (2 * k)) • (1 : Matrix (Fin d) (Fin d) R) := by
      rw [Matrix.mul_smul, ← Matrix.map_mul, hQQ', map_smul_one, map_pow, hφlr, smul_smul,
        smul_smul]
      congr 1; ring
    have rhs : (e * e₀) ^ N • (Q.map φ * (A₀' * (Q' * B))) =
        ((e * e₀) ^ (2 * N) * lr ^ (2 * k)) • (1 : Matrix (Fin d) (Fin d) R) := by
      rw [← Matrix.smul_mul, ← h1, Matrix.mul_assoc, Matrix.mul_assoc, mul_left_of hAA',
        Matrix.mul_smul, Matrix.mul_smul, mul_left_of hQQ', Matrix.mul_smul, hB'B, smul_smul,
        smul_smul]
      congr 1; ring
    rw [lhs, rhs]

  have hcomm : (Q.map φ).map σ = (Q.map σ).map φ := by
    ext i j; simp [hφσ]
  have h3 : B'.map σ * (Q.map σ * A₀) = (σ e * e₀) ^ N • (Q.map σ).map φ := by
    have := congrArg (fun M => M.map σ) h1
    simp only [Matrix.map_mul, map_smul', map_pow, map_mul, hA₀σ, hσe₀, hcomm] at this
    exact this

  have h4 : B' * (ε * B.map σ) = (σ e * e) ^ N • ε.map φ := by
    apply smul_cancel (nzd_pow he N)
    calc e ^ N • (B' * (ε * B.map σ)) = B' * (e ^ N • (ε * B.map σ)) := by rw [Matrix.mul_smul]
      _ = B' * (σ e ^ N • (B * ε.map φ)) := by rw [hεB]
      _ = σ e ^ N • (B' * (B * ε.map φ)) := by rw [Matrix.mul_smul]
      _ = σ e ^ N • (e ^ (2 * N) • ε.map φ) := by rw [mul_left_of hB'B]
      _ = e ^ N • ((σ e * e) ^ N • ε.map φ) := by rw [smul_smul, smul_smul]; congr 1; ring

  have h5 : A₀ * (Q' * ε * Q.map σ).map φ * A₀' = e₀ ^ (2 * N) • (Q' * ε * Q.map σ) := by
    have hc := nzd_mul (nzd_mul (nzd_pow (nzd_mul he he₀) N) (nzd_pow (nzd_mul hσe he) N))
      (nzd_pow (nzd_mul hσe he₀) N)
    apply smul_cancel hc
    calc ((e * e₀) ^ N * (σ e * e) ^ N * (σ e * e₀) ^ N) • (A₀ * (Q' * ε * Q.map σ).map φ * A₀')
        = A₀ * (((e * e₀) ^ N • Q'.map φ) * (((σ e * e) ^ N • ε.map φ) *
            (((σ e * e₀) ^ N • (Q.map σ).map φ) * A₀'))) := by
          simp only [Matrix.map_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
          congr 1; ring
      _ = A₀ * ((A₀' * (Q' * B)) * ((B' * (ε * B.map σ)) * ((B'.map σ * (Q.map σ * A₀)) * A₀'))) := by
          rw [h2, h4, h3]
      _ = ((e * e₀) ^ N * (σ e * e) ^ N * (σ e * e₀) ^ N) • (e₀ ^ (2 * N) • (Q' * ε * Q.map σ)) := by
          simp only [Matrix.mul_assoc, mul_left_of hAA', mul_left_of hBB', mul_left_of hσBB', hAA',
            Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul]
          congr 1; ring
  have hLφ : A₀ * (lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R)).map φ * A₀' =
      e₀ ^ (2 * N) • (lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R)) := by
    rw [map_smul_one, map_pow, hφlr, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hAA',
      smul_smul, smul_smul, mul_comm]
  have hsub : (Q' * ε * Q.map σ - lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R)).map φ =
      (Q' * ε * Q.map σ).map φ - (lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R)).map φ := by
    ext i j; simp only [Matrix.map_apply, Matrix.sub_apply, map_sub]
  rw [hsub, Matrix.mul_sub, Matrix.sub_mul, h5, hLφ, smul_sub]

end GlobalTheory.FrobeniusDefect
