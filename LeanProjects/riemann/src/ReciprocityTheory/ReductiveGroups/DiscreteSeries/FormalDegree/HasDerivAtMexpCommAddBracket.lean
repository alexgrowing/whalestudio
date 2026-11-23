import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.TraceMulSelfEqSumEigenvaluesSq

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

section Banach

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

theorem hasDerivAt_exp_comm_add_bracket (A V X : R) (h : Commute A V) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (A + s • (V + (X * A - A * X))))
      (NormedSpace.exp A * V + (X * NormedSpace.exp A - NormedSpace.exp A * X)) 0 := by
  letI : NormedAlgebra ℚ R := NormedAlgebra.restrictScalars ℚ ℝ R
  have hdiff : DifferentiableAt ℝ NormedSpace.exp A :=
    (NormedSpace.exp_analytic (𝕂 := ℝ) A).differentiableAt
  have hchain : ∀ B : R, HasDerivAt (fun s : ℝ => NormedSpace.exp (A + s • B))
      (fderiv ℝ NormedSpace.exp A B) 0 := by
    intro B
    have hl : HasDerivAt (fun s : ℝ => A + s • B) B 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const B).const_add A
    exact hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have hV : fderiv ℝ NormedSpace.exp A V = NormedSpace.exp A * V := by
    have h2 : HasDerivAt (fun s : ℝ => NormedSpace.exp (A + s • V)) (NormedSpace.exp A * V) 0 := by
      have h3 : (fun s : ℝ => NormedSpace.exp (A + s • V)) =
          fun s => NormedSpace.exp A * NormedSpace.exp (s • V) := by
        funext s
        exact NormedSpace.exp_add_of_commute (h.smul_right s)
      rw [h3]
      have h4 := (hasDerivAt_exp_smul_const (𝕂 := ℝ) V (0 : ℝ)).const_mul (NormedSpace.exp A)
      simpa using h4
    exact (hchain V).unique h2
  have hinv : ∀ s : ℝ, NormedSpace.exp (s • X) * NormedSpace.exp (s • (-X)) = 1 ∧
      NormedSpace.exp (s • (-X)) * NormedSpace.exp (s • X) = 1 := by
    intro s
    constructor
    · rw [smul_neg, ← NormedSpace.exp_add_of_commute ((Commute.refl (s • X)).neg_right),
        add_neg_cancel, NormedSpace.exp_zero]
    · rw [smul_neg, ← NormedSpace.exp_add_of_commute ((Commute.refl (s • X)).neg_left),
        neg_add_cancel, NormedSpace.exp_zero]
  have hFG : (fun s : ℝ => NormedSpace.exp (NormedSpace.exp (s • X) * A * NormedSpace.exp (s • (-X)))) =
      fun s => NormedSpace.exp (s • X) * NormedSpace.exp A * NormedSpace.exp (s • (-X)) := by
    funext s
    exact NormedSpace.exp_units_conj
      ⟨NormedSpace.exp (s • X), NormedSpace.exp (s • (-X)), (hinv s).1, (hinv s).2⟩ A
  have hd1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  have hd2 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-X) (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at hd1 hd2
  have hc : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • X) * A * NormedSpace.exp (s • (-X)))
      (X * A - A * X) 0 := by
    have := (hd1.mul_const A).mul hd2
    refine this.congr_deriv ?_
    simp [sub_eq_add_neg]
  have hF : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • X) * NormedSpace.exp A * NormedSpace.exp (s • (-X)))
      (X * NormedSpace.exp A - NormedSpace.exp A * X) 0 := by
    have := (hd1.mul_const (NormedSpace.exp A)).mul hd2
    refine this.congr_deriv ?_
    simp [sub_eq_add_neg]
  have hG : HasDerivAt (fun s : ℝ => NormedSpace.exp (NormedSpace.exp (s • X) * A * NormedSpace.exp (s • (-X))))
      (fderiv ℝ NormedSpace.exp A (X * A - A * X)) 0 :=
    hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)
  rw [hFG] at hG
  have hB : fderiv ℝ NormedSpace.exp A (X * A - A * X) = X * NormedSpace.exp A - NormedSpace.exp A * X :=
    hG.unique hF
  have key := hchain (V + (X * A - A * X))
  rw [map_add, hV, hB] at key
  exact key

end Banach

section Operator

open scoped Matrix.Norms.Operator in
set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_mexp_comm_add_bracket (A V X : Matrix (Fin n) (Fin n) ℂ) (h : Commute A V) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (A + s • (V + (X * A - A * X))))
      (NormedSpace.exp A * V + (X * NormedSpace.exp A - NormedSpace.exp A * X)) 0 := by
  exact hasDerivAt_exp_comm_add_bracket A V X h

end Operator

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def shcAd {ε : Fin n → Bool} (y : PCoord ε → ℂ) (W : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ((pmat_isHermitian y).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
    Matrix.of (fun i j => ((shc (pev y i - pev y j) : ℝ) : ℂ) *
      ((((pmat_isHermitian y).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ))ᴴ * W *
        ((pmat_isHermitian y).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)) i j) *
    (((pmat_isHermitian y).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ))ᴴ

private theorem hasDerivAt_exp_conj_diag (U U' : Matrix (Fin n) (Fin n) ℂ) (h1 : U * U' = 1) (h2 : U' * U = 1)
    (x : Fin n → ℝ) (W : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp
        ((2 : ℂ) • (U * diagonal (fun i => (x i : ℂ)) * U') + (s : ℂ) • W))
      (NormedSpace.exp (U * diagonal (fun i => (x i : ℂ)) * U') *
        (U * Matrix.of (fun i j => ((shc (x i - x j) : ℝ) : ℂ) * (U' * W * U) i j) * U') *
        NormedSpace.exp (U * diagonal (fun i => (x i : ℂ)) * U')) 0 := by
  classical
  set D : Matrix (Fin n) (Fin n) ℂ := diagonal (fun i => (x i : ℂ)) with hD
  set W' := U' * W * U with hW'
  set A : Matrix (Fin n) (Fin n) ℂ := diagonal (fun i => (2 * x i : ℂ)) with hA
  set V : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun i j => if x i = x j then W' i j else 0) with hV
  set Xm : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.of (fun i j => if x i = x j then 0 else W' i j / (2 * (x j : ℂ) - 2 * x i)) with hXm
  have hcomm : Commute A V := by
    show A * V = V * A
    ext i j
    simp only [hA, hV, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply]
    by_cases h : x i = x j
    · simp only [h, if_true]
      ring
    · simp only [h, if_false, mul_zero, zero_mul]
  have hsplit : V + (Xm * A - A * Xm) = W' := by
    ext i j
    simp only [hA, hV, hXm, Matrix.add_apply, Matrix.sub_apply, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Matrix.of_apply]
    split_ifs with h
    · simp
    · have h' : (2 * (x j : ℂ) - 2 * x i) ≠ 0 := by
        intro h0
        apply h
        have : ((x i : ℝ) : ℂ) = x j := by linear_combination -h0 / 2
        exact_mod_cast this
      calc _ = W' i j / (2 * (x j : ℂ) - 2 * x i) * (2 * x j - 2 * x i) := by ring
        _ = W' i j := div_mul_cancel₀ _ h'
  have hder := hasDerivAt_mexp_comm_add_bracket A V Xm hcomm
  rw [hsplit] at hder
  have hexpA : NormedSpace.exp A = diagonal (fun i => Complex.exp (2 * x i)) := by
    rw [hA, Matrix.exp_diagonal]
    rw [Pi.exp_def]
    congr 1
    funext i
    exact (congrFun Complex.exp_eq_exp_ℂ _).symm
  have hexpD : NormedSpace.exp D = diagonal (fun i => Complex.exp (x i)) := by
    rw [hD, Matrix.exp_diagonal]
    rw [Pi.exp_def]
    congr 1
    funext i
    exact (congrFun Complex.exp_eq_exp_ℂ _).symm
  have hval : NormedSpace.exp A * V + (Xm * NormedSpace.exp A - NormedSpace.exp A * Xm) =
      NormedSpace.exp D * Matrix.of (fun i j => ((shc (x i - x j) : ℝ) : ℂ) * W' i j) *
        NormedSpace.exp D := by
    rw [hexpA, hexpD]
    ext i j
    simp only [hV, hXm, Matrix.add_apply, Matrix.sub_apply, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Matrix.of_apply]
    by_cases h : x i = x j
    · simp only [h, if_true, sub_self, shc, if_true, Complex.ofReal_one, mul_zero, zero_mul,
        sub_zero, add_zero, one_mul]
      rw [show (2 * (x j : ℂ)) = x j + x j by ring, Complex.exp_add]
      ring
    · simp only [h, if_false, mul_zero, zero_add]
      have hne : x i - x j ≠ 0 := sub_ne_zero.mpr h
      have hreal : (Real.exp (2 * x j) - Real.exp (2 * x i)) / (2 * x j - 2 * x i) =
          Real.exp (x i) * Real.exp (x j) * (Real.sinh (x i - x j) / (x i - x j)) := by
        have h3 : (2 * x j - 2 * x i) ≠ 0 := by
          intro h0
          apply hne
          linarith
        have ei := Real.exp_pos (x i)
        have ej := Real.exp_pos (x j)
        rw [Real.sinh_eq, Real.exp_neg, Real.exp_sub, two_mul, two_mul, Real.exp_add, Real.exp_add]
        field_simp
        ring
      unfold shc
      rw [if_neg hne]
      have hC := congrArg (fun r : ℝ => (r : ℂ)) hreal
      push_cast at hC
      push_cast
      calc _ = W' i j * ((Complex.exp (2 * (x j : ℂ)) - Complex.exp (2 * (x i : ℂ))) /
            (2 * (x j : ℂ) - 2 * x i)) := by ring
        _ = _ := by
          rw [hC]
          ring
  rw [hval] at hder

  have hunit : IsUnit U := ⟨⟨U, U', h1, h2⟩, rfl⟩
  have hconjExp : ∀ M : Matrix (Fin n) (Fin n) ℂ, NormedSpace.exp (U * M * U') = U * NormedSpace.exp M * U' :=
    fun M => Matrix.exp_units_conj ⟨U, U', h1, h2⟩ M
  have hfun : (fun s : ℝ => NormedSpace.exp ((2 : ℂ) • (U * D * U') + (s : ℂ) • W)) =
      fun s : ℝ => U * NormedSpace.exp (A + s • W') * U' := by
    funext s
    rw [← hconjExp]
    congr 1
    have hA2 : A = (2 : ℂ) • D := by
      rw [hA, hD]
      ext i j
      by_cases hij : i = j <;> simp [Matrix.diagonal_apply, hij]
    rw [hA2, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, ← Complex.coe_smul,
      Matrix.mul_smul, Matrix.smul_mul, hW']
    congr 1
    rw [show U * (U' * W * U) * U' = (U * U') * W * (U * U') by simp only [Matrix.mul_assoc], h1,
      Matrix.one_mul, Matrix.mul_one]
  have hD2 : U * D * U' = U * diagonal (fun i => (x i : ℂ)) * U' := rfl
  rw [← hD2, hfun]
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun M => U * M * U'
      map_add' := fun a b => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c a => by
        simp only [RingHom.id_apply]
        rw [Matrix.mul_smul, Matrix.smul_mul] }
  have hL := (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hder
  have hL' : HasDerivAt (fun s : ℝ => U * NormedSpace.exp (A + s • W') * U')
      (U * (NormedSpace.exp D * Matrix.of (fun i j => ((shc (x i - x j) : ℝ) : ℂ) * W' i j) *
        NormedSpace.exp D) * U') 0 := hL
  refine hL'.congr_deriv ?_
  rw [hconjExp D]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc U' U, h2, Matrix.one_mul, ← Matrix.mul_assoc U' U, h2, Matrix.one_mul]

private theorem pmat_spectral {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    pmat y = ((pmat_isHermitian y).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      diagonal (fun i => (pev y i : ℂ)) *
      (((pmat_isHermitian y).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ))ᴴ := by
  have h := (pmat_isHermitian y).spectral_theorem
  conv_lhs => rw [h]
  first
  | rfl
  | simp [Function.comp_def, Matrix.star_eq_conjTranspose, pev]

theorem hasDerivAt_exp_two {ε : Fin n → Bool} (y : PCoord ε → ℂ) (W : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp ((2 : ℂ) • pmat y + (s : ℂ) • W))
      (NormedSpace.exp (pmat y) * shcAd y W * NormedSpace.exp (pmat y)) 0 := by
  set U : Matrix (Fin n) (Fin n) ℂ :=
    ((pmat_isHermitian y).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hUdef
  have hU1 : U * Uᴴ = 1 := by
    have h0 := Matrix.mem_unitaryGroup_iff.mp (pmat_isHermitian y).eigenvectorUnitary.2
    rwa [Matrix.star_eq_conjTranspose] at h0
  have hU2 : Uᴴ * U = 1 := by
    have h0 := Matrix.mem_unitaryGroup_iff'.mp (pmat_isHermitian y).eigenvectorUnitary.2
    rwa [Matrix.star_eq_conjTranspose] at h0
  have key := hasDerivAt_exp_conj_diag U Uᴴ hU1 hU2 (pev y) W
  rw [← pmat_spectral y] at key
  exact key

end ReciprocityTheory.ChartRestriction.DS
