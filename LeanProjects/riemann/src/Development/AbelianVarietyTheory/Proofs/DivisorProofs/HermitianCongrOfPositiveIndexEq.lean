import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.HermCongruence

def signVec {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) : Fin n → ℂ :=
  fun i => if 0 < hA.eigenvalues i then 1 else -1

theorem eigenvalues_ne_zero {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hd : A.det ≠ 0)
    (i : Fin n) : hA.eigenvalues i ≠ 0 := by
  intro h
  apply hd
  rw [hA.det_eq_prod_eigenvalues]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h])

theorem exists_congr_signVec {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hd : A.det ≠ 0) :
    ∃ V : GL (Fin n) ℂ, (V : Matrix (Fin n) (Fin n) ℂ)ᴴ * A * V = diagonal (signVec hA) := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hUU : Uᴴ * U = 1 := by
    have := hA.eigenvectorUnitary.2.1
    simpa [hU, Matrix.star_eq_conjTranspose] using this
  have hspec : A = U * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    have := hA.spectral_theorem
    simpa [hU, Matrix.star_eq_conjTranspose, Function.comp_def] using this
  set c : Fin n → ℂ := fun i => ((Real.sqrt |hA.eigenvalues i|)⁻¹ : ℝ) with hc
  have hc0 : ∀ i, c i ≠ 0 := by
    intro i
    have h1 : 0 < |hA.eigenvalues i| := abs_pos.2 (eigenvalues_ne_zero hA hd i)
    simp [hc, Real.sqrt_eq_zero', not_le.2 h1, eigenvalues_ne_zero hA hd i]
  set V := U * diagonal c with hV
  have hVdet : V.det ≠ 0 := by
    rw [hV, det_mul, det_diagonal]
    refine mul_ne_zero ?_ (Finset.prod_ne_zero_iff.2 fun i _ => hc0 i)
    intro h
    have := congrArg det hUU
    rw [det_mul, h, mul_zero, det_one] at this
    exact zero_ne_one this
  refine ⟨GeneralLinearGroup.mkOfDetNeZero V hVdet, ?_⟩
  show Vᴴ * A * V = _
  have hcs : (diagonal c)ᴴ = diagonal c := by
    rw [diagonal_conjTranspose]
    congr 1; funext i; simp [hc]
  rw [hV, conjTranspose_mul, hcs]
  conv_lhs => rw [hspec]
  have : diagonal c * Uᴴ * (U * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * Uᴴ) * (U * diagonal c) =
      diagonal c * (Uᴴ * U) * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * (Uᴴ * U) * diagonal c := by
    simp only [Matrix.mul_assoc]
  rw [this, hUU, Matrix.mul_one, Matrix.mul_one, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  have hne := eigenvalues_ne_zero hA hd i
  have hpos : 0 < |hA.eigenvalues i| := abs_pos.2 hne
  have hsq : Real.sqrt |hA.eigenvalues i| * Real.sqrt |hA.eigenvalues i| = |hA.eigenvalues i| :=
    Real.mul_self_sqrt hpos.le
  have hs0 : Real.sqrt |hA.eigenvalues i| ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  have key : (Real.sqrt |hA.eigenvalues i|)⁻¹ * hA.eigenvalues i * (Real.sqrt |hA.eigenvalues i|)⁻¹ =
      if 0 < hA.eigenvalues i then 1 else -1 := by
    rw [mul_comm, ← mul_assoc, ← mul_inv, hsq]
    split_ifs with h
    · rw [abs_of_pos h]; field_simp
    · rw [abs_of_neg (lt_of_le_of_ne (not_lt.1 h) hne)]; field_simp
  simp only [signVec, hc]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, key]
  split_ifs <;> simp

end GlobalTheory.HermCongruence

namespace GlobalTheory.HermCongruence

theorem exists_equiv_pos {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : sigPosH hA = sigPosH hB) :
    ∃ e : Fin n ≃ Fin n, ∀ i, (0 < hA.eigenvalues (e i) ↔ 0 < hB.eigenvalues i) := by
  have h1 : Fintype.card {i // 0 < hB.eigenvalues i} = Fintype.card {i // 0 < hA.eigenvalues i} := h.symm
  have h2 : Fintype.card {i // ¬ 0 < hB.eigenvalues i} = Fintype.card {i // ¬ 0 < hA.eigenvalues i} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, h1]
  refine ⟨Equiv.subtypeCongr (Fintype.equivOfCardEq h1) (Fintype.equivOfCardEq h2), fun i => ?_⟩
  by_cases hi : 0 < hB.eigenvalues i
  · have hx : Equiv.subtypeCongr (Fintype.equivOfCardEq h1) (Fintype.equivOfCardEq h2) i =
        ((Fintype.equivOfCardEq h1) ⟨i, hi⟩ : Fin n) := by
      simp [Equiv.subtypeCongr, hi]
    rw [hx]
    exact iff_of_true ((Fintype.equivOfCardEq h1) ⟨i, hi⟩).2 hi
  · have hx : Equiv.subtypeCongr (Fintype.equivOfCardEq h1) (Fintype.equivOfCardEq h2) i =
        ((Fintype.equivOfCardEq h2) ⟨i, hi⟩ : Fin n) := by
      simp [Equiv.subtypeCongr, hi]
    rw [hx]
    exact iff_of_false ((Fintype.equivOfCardEq h2) ⟨i, hi⟩).2 hi

theorem perm_congr {n : ℕ} (d : Fin n → ℂ) (e : Fin n ≃ Fin n) :
    ((1 : Matrix (Fin n) (Fin n) ℂ).submatrix id e)ᴴ * diagonal d * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id e =
      diagonal (d ∘ e) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.one_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply]
  split_ifs with h <;> simp [h]

theorem congr_of_sigPosH_eq : ∀ {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian),
    A.det ≠ 0 → B.det ≠ 0 → sigPosH hA = sigPosH hB →
      ∃ Z : GL (Fin n) ℂ, B = (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * A * (Z : Matrix (Fin n) (Fin n) ℂ) := by
  intro n A B hA hB hdA hdB hs
  obtain ⟨VA, hVA⟩ := exists_congr_signVec hA hdA
  obtain ⟨VB, hVB⟩ := exists_congr_signVec hB hdB
  obtain ⟨e, he⟩ := exists_equiv_pos hA hB hs
  set P : Matrix (Fin n) (Fin n) ℂ := (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id e with hP
  have hPP : P * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id e.symm = 1 := by
    ext i j; simp [hP, Matrix.mul_apply, Matrix.one_apply]
  have hPdet : P.det ≠ 0 := by
    intro h
    have := congrArg det hPP
    rw [det_mul, h, zero_mul, det_one] at this
    exact zero_ne_one this
  have hsig : signVec hA ∘ e = signVec hB := by
    funext i
    simp only [Function.comp_apply, signVec]
    by_cases hi : 0 < hB.eigenvalues i
    · rw [if_pos hi, if_pos ((he i).2 hi)]
    · rw [if_neg hi, if_neg (fun h => hi ((he i).1 h))]
  refine ⟨VA * GeneralLinearGroup.mkOfDetNeZero P hPdet * VB⁻¹, ?_⟩
  set W : Matrix (Fin n) (Fin n) ℂ := ((VB⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) with hW
  have hVW : (VB : Matrix (Fin n) (Fin n) ℂ) * W = 1 := by
    rw [hW, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hWV : Wᴴ * (VB : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 := by
    rw [← conjTranspose_mul, hVW, conjTranspose_one]
  have hP' : ((GeneralLinearGroup.mkOfDetNeZero P hPdet : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = P := rfl
  rw [Units.val_mul, Units.val_mul, hP', ← hW, conjTranspose_mul, conjTranspose_mul]
  have : Wᴴ * (Pᴴ * (VA : Matrix (Fin n) (Fin n) ℂ)ᴴ) * A * (VA * P * W) =
      Wᴴ * (Pᴴ * ((VA : Matrix (Fin n) (Fin n) ℂ)ᴴ * A * VA) * P) * W := by
    simp only [Matrix.mul_assoc]
  rw [this, hVA, hP, perm_congr, hsig, ← hVB]
  have : Wᴴ * ((VB : Matrix (Fin n) (Fin n) ℂ)ᴴ * B * VB) * W =
      (Wᴴ * (VB : Matrix (Fin n) (Fin n) ℂ)ᴴ) * B * ((VB : Matrix (Fin n) (Fin n) ℂ) * W) := by
    simp only [Matrix.mul_assoc]
  rw [this, hWV, hVW, Matrix.one_mul, Matrix.mul_one]

end GlobalTheory.HermCongruence
