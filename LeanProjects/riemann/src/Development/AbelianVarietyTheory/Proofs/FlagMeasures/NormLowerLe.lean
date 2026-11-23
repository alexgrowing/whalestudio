import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.LduBound

theorem norm_det_le {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (B : ℝ)
    (h : ∀ i j, ‖A i j‖ ≤ B) : ‖A.det‖ ≤ (Fintype.card ι).factorial * B ^ Fintype.card ι := by
  have := Matrix.det_le (A := A) (abv := NormedField.toAbsoluteValue ℂ) (x := B) h
  rw [nsmul_eq_mul] at this
  exact this

theorem det_minor {n : ℕ} (L R : Matrix (Fin n) (Fin n) ℂ) (hL : IsLoUni L)
    (hR : ∀ a b, b < a → R a b = 0) (i j : Fin n) :
    ((L * R).submatrix (fun a : {k : Fin n // k ≤ j} => if a.1 = j then i else a.1)
      (fun a : {k : Fin n // k ≤ j} => a.1)).det = L i j * ∏ k ∈ Finset.Iic j, R k k := by
  have hf : (L * R).submatrix (fun a : {k : Fin n // k ≤ j} => if a.1 = j then i else a.1)
      (fun a : {k : Fin n // k ≤ j} => a.1) =
      L.submatrix (fun a : {k : Fin n // k ≤ j} => if a.1 = j then i else a.1)
      (fun a : {k : Fin n // k ≤ j} => a.1) * R.submatrix (fun a : {k : Fin n // k ≤ j} => a.1)
      (fun a : {k : Fin n // k ≤ j} => a.1) := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    rw [← Fintype.sum_subtype_add_sum_subtype (fun k : Fin n => k ≤ j)]
    have : ∑ k : {k : Fin n // ¬ k ≤ j}, L (if a.1 = j then i else a.1) k.1 * R k.1 b.1 = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [hR k.1 b.1 (lt_of_le_of_lt b.2 (not_le.1 k.2)), mul_zero]
    rw [this, add_zero]
  rw [hf, Matrix.det_mul]
  congr 1
  · rw [Matrix.det_of_lowerTriangular]
    · rw [Finset.prod_eq_single (⟨j, le_rfl⟩ : {k : Fin n // k ≤ j})]
      · simp
      · intro b _ hb
        have : b.1 ≠ j := fun h => hb (Subtype.ext h)
        simp only [Matrix.submatrix_apply, if_neg this]
        exact (hL _ _).2 rfl
      · simp
    · intro a b hab
      have hab' : a.1 < b.1 := hab
      have : a.1 ≠ j := ne_of_lt (lt_of_lt_of_le hab' b.2)
      simp only [Matrix.submatrix_apply, if_neg this]
      exact (hL _ _).1 hab'
  · rw [Matrix.det_of_upperTriangular]
    · simp only [Matrix.submatrix_apply]
      exact (Finset.prod_subtype (Finset.Iic j) (fun k => Finset.mem_Iic) (fun k => R k k)).symm
    · intro a b hab
      exact hR _ _ hab

theorem norm_lower_le {n : ℕ} (L U : Matrix (Fin n) (Fin n) ℂ) (t : Fin n → ℂ) (B δ : ℝ)
    (hL : IsLoUni L) (hU : IsUpUni U) (hB : 1 ≤ B) (hδ : 0 < δ)
    (ht : ∀ l : Fin n, δ ≤ ‖∏ i ∈ Finset.Iic l, t i‖)
    (hZ : ∀ i j, ‖(L * Matrix.diagonal t * U) i j‖ ≤ B) (i j : Fin n) :
    ‖L i j‖ ≤ n.factorial * B ^ n / δ := by
  have h1 := det_minor L (Matrix.diagonal t * U) hL
    (fun a b hab => by rw [Matrix.diagonal_mul, (hU a b).1 hab, mul_zero]) i j
  have h2 : ∏ k ∈ Finset.Iic j, (Matrix.diagonal t * U) k k = ∏ k ∈ Finset.Iic j, t k :=
    Finset.prod_congr rfl fun k _ => by rw [Matrix.diagonal_mul, (hU k k).2 rfl, mul_one]
  rw [h2, ← Matrix.mul_assoc] at h1
  have h3 := norm_det_le ((L * Matrix.diagonal t * U).submatrix
    (fun a : {k : Fin n // k ≤ j} => if a.1 = j then i else a.1)
      (fun a : {k : Fin n // k ≤ j} => a.1)) B (fun a b => hZ _ _)
  rw [h1, norm_mul] at h3
  have hc : Fintype.card {k : Fin n // k ≤ j} ≤ n := by
    simpa using Fintype.card_subtype_le (fun k : Fin n => k ≤ j)
  have h4 : ((Fintype.card {k : Fin n // k ≤ j}).factorial : ℝ) * B ^ Fintype.card {k : Fin n // k ≤ j}
      ≤ n.factorial * B ^ n :=
    mul_le_mul (by exact_mod_cast Nat.factorial_le hc) (pow_le_pow_right₀ hB hc) (by positivity)
      (by positivity)
  rw [le_div_iff₀ hδ]
  exact (mul_le_mul_of_nonneg_left (ht j) (norm_nonneg _)).trans (h3.trans h4)

theorem norm_inv_le {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (hA : A.det = 1) (x : ℝ)
    (h : ∀ i j, ‖A i j‖ ≤ x) (i j : Fin (m + 1)) : ‖A⁻¹ i j‖ ≤ m.factorial * x ^ m := by
  rw [Matrix.inv_def, hA, Ring.inverse_one, one_smul, Matrix.adjugate_fin_succ_eq_det_submatrix,
    norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  simpa using norm_det_le (A.submatrix j.succAbove i.succAbove) x (fun a b => h _ _)

theorem ldu_bound (m : ℕ) : ∃ c : ℝ, 0 < c ∧ ∀ (L U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (t : Fin (m + 1) → ℂ) (B δ : ℝ), IsLoUni L → IsUpUni U → 1 ≤ B → 0 < δ → δ ≤ 1 →
    (∀ l : Fin (m + 1), δ ≤ ‖∏ i ∈ Finset.Iic l, t i‖) →
    (∀ i j, ‖(L * Matrix.diagonal t * U) i j‖ ≤ B) →
    ∀ i j, ‖L i j‖ ≤ c * B ^ (m + 1) / δ ∧ ‖U i j‖ ≤ c * B ^ (m + 1) / δ ∧
      ‖L⁻¹ i j‖ ≤ c * (B ^ (m + 1) / δ) ^ m ∧ ‖U⁻¹ i j‖ ≤ c * (B ^ (m + 1) / δ) ^ m := by
  refine ⟨(m + 1).factorial + m.factorial * ((m + 1).factorial : ℝ) ^ m, by positivity, ?_⟩
  intro L U t B δ hL hU hB hδ _ ht hZ
  have hB0 : 0 < B := by linarith
  have h1 := norm_lower_le L U t B δ hL hU hB hδ ht hZ
  have h2 : ∀ i j, ‖U i j‖ ≤ (m + 1).factorial * B ^ (m + 1) / δ := fun i j =>
    norm_lower_le Uᵀ Lᵀ t B δ (fun a b => ⟨(hU b a).1, fun h => (hU b a).2 h.symm⟩)
      (fun a b => ⟨(hL b a).1, fun h => (hL b a).2 h.symm⟩) hB hδ ht
      (fun a b => by
        have : Uᵀ * Matrix.diagonal t * Lᵀ = (L * Matrix.diagonal t * U)ᵀ := by
          simp [Matrix.transpose_mul, Matrix.mul_assoc]
        rw [this]; exact hZ b a) j i
  have dL : L.det = 1 := by
    rw [Matrix.det_of_lowerTriangular L (fun a b hab => (hL a b).1 hab)]
    exact Finset.prod_eq_one fun k _ => (hL k k).2 rfl
  have dU : U.det = 1 := by
    rw [Matrix.det_of_upperTriangular (M := U) (fun a b hab => (hU a b).1 hab)]
    exact Finset.prod_eq_one fun k _ => (hU k k).2 rfl
  have e1 : ((m + 1).factorial : ℝ) * B ^ (m + 1) / δ ≤
      ((m + 1).factorial + m.factorial * ((m + 1).factorial : ℝ) ^ m) * B ^ (m + 1) / δ := by
    gcongr
    exact le_add_of_nonneg_right (by positivity)
  have e2 : (m.factorial : ℝ) * (((m + 1).factorial : ℝ) * B ^ (m + 1) / δ) ^ m ≤
      ((m + 1).factorial + m.factorial * ((m + 1).factorial : ℝ) ^ m) * (B ^ (m + 1) / δ) ^ m := by
    rw [mul_div_assoc, mul_pow, ← mul_assoc]
    gcongr
    exact le_add_of_nonneg_left (by positivity)
  exact fun i j => ⟨(h1 i j).trans e1, (h2 i j).trans e1, (norm_inv_le L dL _ h1 i j).trans e2,
    (norm_inv_le U dU _ h2 i j).trans e2⟩

end GlobalTheory.SgInf.LduBound
