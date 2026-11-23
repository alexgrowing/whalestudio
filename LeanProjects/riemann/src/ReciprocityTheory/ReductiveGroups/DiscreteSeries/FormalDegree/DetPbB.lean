import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PmatIsHermitian

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def dpbH (U : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℝ) (h : ℝ → ℝ) (W : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  U * Matrix.of (fun i j => ((h (x i - x j) : ℝ) : ℂ) * (Uᴴ * W * U) i j) * Uᴴ

def dpbD (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun i => (x i : ℂ)

theorem dpbH_add (U : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℝ) (h : ℝ → ℝ) (W W' : Matrix (Fin n) (Fin n) ℂ) :
    dpbH U x h (W + W') = dpbH U x h W + dpbH U x h W' := by
  have key : Matrix.of (fun i j => ((h (x i - x j) : ℝ) : ℂ) * (Uᴴ * (W + W') * U) i j) =
      Matrix.of (fun i j => ((h (x i - x j) : ℝ) : ℂ) * (Uᴴ * W * U) i j) +
        Matrix.of (fun i j => ((h (x i - x j) : ℝ) : ℂ) * (Uᴴ * W' * U) i j) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.add_apply, mul_add, add_mul]
  simp only [dpbH]
  rw [key, mul_add, add_mul]

theorem dpbH_smul (U : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℝ) (h : ℝ → ℝ) (c : ℂ)
    (W : Matrix (Fin n) (Fin n) ℂ) : dpbH U x h (c • W) = c • dpbH U x h W := by
  have key : Matrix.of (fun i j => ((h (x i - x j) : ℝ) : ℂ) * (Uᴴ * (c • W) * U) i j) =
      c • Matrix.of (fun i j => ((h (x i - x j) : ℝ) : ℂ) * (Uᴴ * W * U) i j) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.mul_smul, Matrix.smul_mul, smul_eq_mul]
    ring
  simp only [dpbH]
  rw [key, Matrix.mul_smul, Matrix.smul_mul]

def dpbL (U : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℝ) (h : ℝ → ℝ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := dpbH U x h
  map_add' := dpbH_add U x h
  map_smul' c W := by
    have := dpbH_smul U x h (c : ℂ) W
    simpa only [Complex.coe_smul, RingHom.id_apply] using this

theorem dpbH_conjTranspose (U : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℝ) (h : ℝ → ℝ) (he : ∀ u, h (-u) = h u)
    (W : Matrix (Fin n) (Fin n) ℂ) : (dpbH U x h W)ᴴ = dpbH U x h Wᴴ := by
  have key : (Matrix.of (fun i j => ((h (x i - x j) : ℝ) : ℂ) * (Uᴴ * W * U) i j))ᴴ =
      Matrix.of (fun i j => ((h (x i - x j) : ℝ) : ℂ) * (Uᴴ * Wᴴ * U) i j) := by
    ext i j
    have h1 : (Uᴴ * Wᴴ * U) i j = star ((Uᴴ * W * U) j i) := by
      rw [← Matrix.conjTranspose_apply]
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    have h2 : h (x j - x i) = h (x i - x j) := by rw [← neg_sub, he]
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
    rw [h1, h2, star_mul']
    simp [Complex.conj_ofReal]
  rw [dpbH, dpbH, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, key]
  exact (Matrix.mul_assoc _ _ _).symm

theorem dpb_had_conj (Q M : Matrix (Fin n) (Fin n) ℂ) (F G : Fin n → Fin n → ℂ)
    (hFG : ∀ i j k l, Q i j ≠ 0 → Q l k ≠ 0 → F i l = G j k) :
    Matrix.of (fun i l => F i l * (Q * M * Qᴴ) i l) = Q * Matrix.of (fun j k => G j k * M j k) * Qᴴ := by
  ext i l
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h1 : Q i j = 0
  · simp [h1]
  by_cases h2 : Q l k = 0
  · simp [h2]
  rw [hFG i j k l h1 h2]
  ring

theorem dpbH_indep {U V : Matrix (Fin n) (Fin n) ℂ} {x x' : Fin n → ℝ} (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (hV : Vᴴ * V = 1) (hV' : V * Vᴴ = 1) (hY : U * dpbD x * Uᴴ = V * dpbD x' * Vᴴ) (h : ℝ → ℝ)
    (W : Matrix (Fin n) (Fin n) ℂ) : dpbH U x h W = dpbH V x' h W := by
  have hQ : dpbD x * (Uᴴ * V) = (Uᴴ * V) * dpbD x' := by
    calc dpbD x * (Uᴴ * V) = Uᴴ * (U * dpbD x * Uᴴ) * V := by
          simp only [Matrix.mul_assoc]
          rw [← mul_assoc Uᴴ U, hU, one_mul]
      _ = Uᴴ * (V * dpbD x' * Vᴴ) * V := by rw [hY]
      _ = (Uᴴ * V) * dpbD x' := by
          simp only [Matrix.mul_assoc]
          rw [hV, mul_one]
  have hx : ∀ i j, (Uᴴ * V) i j ≠ 0 → x i = x' j := by
    intro i j hne
    have h1 := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) hQ
    simp only [dpbD, Matrix.diagonal_mul, Matrix.mul_diagonal] at h1
    have h2 : ((x i : ℂ) - x' j) * (Uᴴ * V) i j = 0 := by
      rw [sub_mul, h1]
      ring
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact_mod_cast sub_eq_zero.mp h3
    · exact absurd h3 hne
  have hQM : (Uᴴ * V) * (Vᴴ * W * V) * (Uᴴ * V)ᴴ = Uᴴ * W * U := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc Uᴴ * V * (Vᴴ * W * V) * (Vᴴ * U) = Uᴴ * (V * Vᴴ) * W * (V * Vᴴ) * U := by
          simp only [Matrix.mul_assoc]
      _ = Uᴴ * W * U := by rw [hV', mul_one, mul_one]
  have key := dpb_had_conj (Uᴴ * V) (Vᴴ * W * V) (fun i l => ((h (x i - x l) : ℝ) : ℂ))
    (fun j k => ((h (x' j - x' k) : ℝ) : ℂ)) (by
      intro i j k l h1 h2
      show ((h (x i - x l) : ℝ) : ℂ) = ((h (x' j - x' k) : ℝ) : ℂ)
      rw [hx i j h1, hx l k h2])
  try simp only at key
  rw [hQM] at key
  simp only [dpbH]
  rw [key, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [hU', mul_one, ← mul_assoc U Uᴴ, hU', one_mul]

theorem dpbH_theta {U J : Matrix (Fin n) (Fin n) ℂ} {x : Fin n → ℝ} (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (hJ : J * J = 1) (hJ' : Jᴴ = J) (hY : J * (U * dpbD x * Uᴴ) * J = -(U * dpbD x * Uᴴ)) (h : ℝ → ℝ)
    (he : ∀ u, h (-u) = h u) (W : Matrix (Fin n) (Fin n) ℂ) :
    J * dpbH U x h W * J = dpbH U x h (J * W * J) := by
  have hV : (J * U)ᴴ * (J * U) = 1 := by
    rw [Matrix.conjTranspose_mul, hJ']
    calc Uᴴ * J * (J * U) = Uᴴ * (J * J) * U := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hJ, mul_one, hU]
  have hV' : (J * U) * (J * U)ᴴ = 1 := by
    rw [Matrix.conjTranspose_mul, hJ']
    calc J * U * (Uᴴ * J) = J * (U * Uᴴ) * J := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU', mul_one, hJ]
  have hD : dpbD (-x) = -dpbD x := by
    ext i j
    simp only [dpbD, Matrix.neg_apply, Matrix.diagonal_apply, Pi.neg_apply, Complex.ofReal_neg]
    split_ifs <;> simp
  have hY' : U * dpbD x * Uᴴ = (J * U) * dpbD (-x) * (J * U)ᴴ := by
    rw [hD, Matrix.conjTranspose_mul, hJ']
    calc U * dpbD x * Uᴴ = -(J * (U * dpbD x * Uᴴ) * J) := by rw [hY, neg_neg]
      _ = J * U * -dpbD x * (Uᴴ * J) := by
          simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  have hM : (J * U)ᴴ * (J * W * J) * (J * U) = Uᴴ * W * U := by
    rw [Matrix.conjTranspose_mul, hJ']
    calc Uᴴ * J * (J * W * J) * (J * U) = Uᴴ * (J * J) * W * (J * J) * U := by
          simp only [Matrix.mul_assoc]
      _ = Uᴴ * W * U := by rw [hJ, mul_one, mul_one]
  have hA : Matrix.of (fun i j => ((h ((-x) i - (-x) j) : ℝ) : ℂ) * (Uᴴ * W * U) i j) =
      Matrix.of (fun i j => ((h (x i - x j) : ℝ) : ℂ) * (Uᴴ * W * U) i j) := by
    ext i j
    simp only [Matrix.of_apply, Pi.neg_apply]
    rw [neg_sub_neg, ← neg_sub, he]
  rw [dpbH_indep hU hU' hV hV' hY' h (J * W * J)]
  simp only [dpbH]
  rw [hM, hA, Matrix.conjTranspose_mul, hJ']
  simp only [Matrix.mul_assoc]

theorem dpb_comm_D (x : Fin n → ℝ) (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (dpbD x * X - X * dpbD x) i j = ((x i - x j : ℝ) : ℂ) * X i j := by
  simp only [dpbD, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Complex.ofReal_sub]
  ring

theorem dpbH_sub_one {U : Matrix (Fin n) (Fin n) ℂ} (x : Fin n → ℝ) (hU' : U * Uᴴ = 1) (h : ℝ → ℝ)
    (W : Matrix (Fin n) (Fin n) ℂ) : dpbH U x (fun u => h u - 1) W = dpbH U x h W - W := by
  have key : Matrix.of (fun i j => ((h (x i - x j) - 1 : ℝ) : ℂ) * (Uᴴ * W * U) i j) =
      Matrix.of (fun i j => ((h (x i - x j) : ℝ) : ℂ) * (Uᴴ * W * U) i j) - Uᴴ * W * U := by
    ext i j
    simp only [Matrix.of_apply, Matrix.sub_apply, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  simp only [dpbH]
  rw [key, mul_sub, sub_mul]
  congr 1
  calc U * (Uᴴ * W * U) * Uᴴ = (U * Uᴴ) * W * (U * Uᴴ) := by simp only [Matrix.mul_assoc]
    _ = W := by rw [hU', one_mul, mul_one]

private theorem unitary_conj_mul_unitary_conj_of_conjTranspose_mul_self {U : Matrix (Fin n) (Fin n) ℂ} (hU : Uᴴ * U = 1)
    (A B : Matrix (Fin n) (Fin n) ℂ) : U * A * Uᴴ * (U * B * Uᴴ) = U * (A * B) * Uᴴ := by
  calc U * A * Uᴴ * (U * B * Uᴴ) = U * A * (Uᴴ * U) * B * Uᴴ := by simp only [Matrix.mul_assoc]
    _ = U * (A * B) * Uᴴ := by
        rw [hU, mul_one]
        simp only [Matrix.mul_assoc]

theorem dpbH_ad_left {U : Matrix (Fin n) (Fin n) ℂ} (x : Fin n → ℝ) (hU : Uᴴ * U = 1) (h : ℝ → ℝ)
    (W : Matrix (Fin n) (Fin n) ℂ) :
    (U * dpbD x * Uᴴ) * dpbH U x h W - dpbH U x h W * (U * dpbD x * Uᴴ) = dpbH U x (fun u => u * h u) W := by
  simp only [dpbH]
  rw [unitary_conj_mul_unitary_conj_of_conjTranspose_mul_self hU, unitary_conj_mul_unitary_conj_of_conjTranspose_mul_self hU, ← sub_mul, ← mul_sub]
  congr 2
  ext i j
  rw [dpb_comm_D]
  simp only [Matrix.of_apply, Complex.ofReal_mul]
  ring

theorem dpbH_ad_right {U : Matrix (Fin n) (Fin n) ℂ} (x : Fin n → ℝ) (hU : Uᴴ * U = 1) (h : ℝ → ℝ)
    (W : Matrix (Fin n) (Fin n) ℂ) :
    dpbH U x h ((U * dpbD x * Uᴴ) * W - W * (U * dpbD x * Uᴴ)) = dpbH U x (fun u => u * h u) W := by
  have e1 : Uᴴ * (U * dpbD x * Uᴴ * W) * U = dpbD x * (Uᴴ * W * U) := by
    calc Uᴴ * (U * dpbD x * Uᴴ * W) * U = (Uᴴ * U) * dpbD x * (Uᴴ * W * U) := by
          simp only [Matrix.mul_assoc]
      _ = dpbD x * (Uᴴ * W * U) := by rw [hU, one_mul]
  have e2 : Uᴴ * (W * (U * dpbD x * Uᴴ)) * U = (Uᴴ * W * U) * dpbD x * (Uᴴ * U) := by
    simp only [Matrix.mul_assoc]
  have key : Uᴴ * ((U * dpbD x * Uᴴ) * W - W * (U * dpbD x * Uᴴ)) * U =
      dpbD x * (Uᴴ * W * U) - (Uᴴ * W * U) * dpbD x := by
    rw [mul_sub, sub_mul, e1, e2, hU, mul_one]
  simp only [dpbH]
  rw [key]
  congr 2
  ext i j
  simp only [Matrix.of_apply]
  rw [dpb_comm_D, Complex.ofReal_mul]
  ring

end ReciprocityTheory.ChartRestriction.DS
