import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PSpecB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.CauchyBinet
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.LeadingMinorConjDiagonal

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def wS {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n)
    (S : {S : Finset (Fin n) // S.card = i}) : ℝ :=
  ‖(((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).submatrix (Fin.castLE hi)
    (S.1.orderEmbOfFin S.2)).det‖ ^ 2

def yS {ε : Fin n → Bool} (z : PCoord ε → ℂ) (S : Finset (Fin n)) : ℝ := ∑ s ∈ S, pev z s

theorem minor_weight_cast {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n)
    (S : {S : Finset (Fin n) // S.card = i}) :
    ((wS z hi S : ℝ) : ℂ) =
      (((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).submatrix (Fin.castLE hi)
        (S.1.orderEmbOfFin S.2)).det *
      star (((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).submatrix (Fin.castLE hi)
        (S.1.orderEmbOfFin S.2)).det := by
  rw [wS, Complex.ofReal_pow, Complex.star_def, Complex.mul_conj']

theorem pmat_eq_eigenvectorUnitary_conj_diagonal_pev {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    pmat z = ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      diagonal (fun s => ((pev z s : ℝ) : ℂ)) *
      ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ := by
  have hu : ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 :=
    Unitary.mul_star_self_of_mem (pmat_isHermitian z).eigenvectorUnitary.2
  calc pmat z = pmat z * (((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ) := by rw [hu, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, pmat_mul_evU]

theorem pmat_eigenvectorUnitary_mul_conjTranspose_and_conj_mul {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 ∧
    ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ *
      ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  have hU := (pmat_isHermitian z).eigenvectorUnitary.2
  exact ⟨Unitary.mul_star_self_of_mem hU, Unitary.star_mul_self_of_mem hU⟩

theorem matrix_map_id (M : Matrix (Fin n) (Fin n) ℂ) : M.map (RingHom.id ℂ) = M := by
  ext a b
  rfl

theorem leading_minor_sum_weights {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n) (d : Fin n → ℂ) :
    Del (((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * diagonal d *
      ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ) i =
      ∑ S, ((wS z hi S : ℝ) : ℂ) * ∏ s ∈ S.1, d s := by
  unfold Del
  rw [dif_pos hi]
  have h := leading_minor_conj_diagonal (RingHom.id ℂ) hi ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) d
  rw [matrix_map_id, matrix_map_id] at h
  rw [h]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [minor_weight_cast z hi S]
  rfl

theorem lemma3a {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n) (t : ℝ) :
    Del (NormedSpace.exp ((t : ℂ) • pmat z)) i =
      ∑ S, ((wS z hi S : ℝ) : ℂ) * Complex.exp ((t * yS z S.1 : ℝ) : ℂ) := by
  have hu := (pmat_eigenvectorUnitary_mul_conjTranspose_and_conj_mul z).1
  have hUu : IsUnit ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := isUnit_iff_exists.mpr ⟨_, hu, (pmat_eigenvectorUnitary_mul_conjTranspose_and_conj_mul z).2⟩
  have hsm : (t : ℂ) • pmat z = ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * diagonal (fun s => ((t * pev z s : ℝ) : ℂ)) * ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)⁻¹ := by
    rw [Matrix.inv_eq_right_inv hu]
    conv_lhs => rw [pmat_eq_eigenvectorUnitary_conj_diagonal_pev z]
    have hd : diagonal (fun s => ((t * pev z s : ℝ) : ℂ)) =
        (t : ℂ) • diagonal (fun s => ((pev z s : ℝ) : ℂ)) := by
      ext a b
      by_cases h : a = b <;> simp [h]
    rw [hd, mul_smul_comm, smul_mul_assoc]
  have hexp : NormedSpace.exp ((t : ℂ) • pmat z) =
      ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * diagonal (fun s => Complex.exp ((t * pev z s : ℝ) : ℂ)) * ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ := by
    rw [hsm, Matrix.exp_conj _ _ hUu, Matrix.exp_diagonal, Matrix.inv_eq_right_inv hu]
    congr 1
    congr 1
    congr 1
    rw [Pi.exp_def]
    funext s
    simp only [Complex.exp_eq_exp_ℂ]
  rw [hexp, leading_minor_sum_weights z hi]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [← Complex.exp_sum]
  congr 2
  simp [yS, Finset.mul_sum]

theorem lemma3b {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n) : ∑ S, wS z hi S = 1 := by
  have h := leading_minor_sum_weights z hi (fun _ => (1 : ℂ))
  simp only [Matrix.diagonal_one, (pmat_eigenvectorUnitary_mul_conjTranspose_and_conj_mul z).1, Finset.prod_const_one, mul_one] at h
  have h1 : Del (1 : Matrix (Fin n) (Fin n) ℂ) i = 1 := by
    unfold Del
    rw [dif_pos hi, Matrix.submatrix_one _ (Fin.castLE_injective hi), Matrix.det_one]
  exact_mod_cast h.symm.trans h1

open Polynomial in
theorem sum_weights_coeff_eq_det {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n) (μ : Fin n → ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * diagonal μ *
      ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ = M) (k : ℕ) :
    ∑ S, ((wS z hi S : ℝ) : ℂ) * (∏ s ∈ S.1, (1 + X * C (μ s))).coeff k =
      (det (1 + (X : ℂ[X]) • (M.submatrix (Fin.castLE hi) (Fin.castLE hi)).map C)).coeff k := by
  have hL := leading_minor_conj_diagonal (Polynomial.C : ℂ →+* ℂ[X]) hi ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) (fun s => 1 + X * C (μ s))
  rw [conj_polynomial_diagonal _ (pmat_eigenvectorUnitary_mul_conjTranspose_and_conj_mul z).1 μ, hM] at hL
  have hsub : (1 + (X : ℂ[X]) • M.map C).submatrix (Fin.castLE hi) (Fin.castLE hi) =
      1 + (X : ℂ[X]) • (M.submatrix (Fin.castLE hi) (Fin.castLE hi)).map C := by
    ext a b
    simp [Matrix.one_apply, (Fin.castLE_injective hi).eq_iff]
  rw [hsub] at hL
  rw [hL, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [← minor_weight_cast z hi S, Polynomial.coeff_C_mul]

theorem trace_leading_submatrix_pmat {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n) :
    trace ((pmat z).submatrix (Fin.castLE hi) (Fin.castLE hi)) = 0 := by
  rw [trace_leading_submatrix]
  simp [pmat_diag_zero]

open Polynomial in

theorem lemma3c {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n) :
    ∑ S, wS z hi S * yS z S.1 = 0 := by
  have hP := sum_weights_coeff_eq_det z hi (fun s => ((pev z s : ℝ) : ℂ)) (pmat z) (pmat_eq_eigenvectorUnitary_conj_diagonal_pev z).symm 1
  rw [Matrix.coeff_det_one_add_X_smul_one, trace_leading_submatrix_pmat z hi] at hP
  have hc : ∀ S : {S : Finset (Fin n) // S.card = i},
      (∏ s ∈ S.1, (1 + X * C ((pev z s : ℝ) : ℂ))).coeff 1 = ((yS z S.1 : ℝ) : ℂ) := by
    intro S
    rw [(coeff_prod_one_add_low S.1 _).2.1, yS]
    push_cast
    rfl
  simp only [hc] at hP
  exact_mod_cast hP

open Polynomial in

theorem lemma3d {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n) :
    ∑ S, wS z hi S * yS z S.1 ^ 2 = Vi (pmat z) i := by
  have hP2 := sum_weights_coeff_eq_det z hi (fun s => ((pev z s : ℝ) : ℂ)) (pmat z) (pmat_eq_eigenvectorUnitary_conj_diagonal_pev z).symm 2
  have hsq : ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * diagonal (fun s => ((pev z s : ℝ) : ℂ) ^ 2) * ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ = pmat z * pmat z := by
    rw [← sq_conj_diagonal _ _ (pmat_eigenvectorUnitary_mul_conjTranspose_and_conj_mul z).2, ← pmat_eq_eigenvectorUnitary_conj_diagonal_pev z]
  have hP1 := sum_weights_coeff_eq_det z hi (fun s => ((pev z s : ℝ) : ℂ) ^ 2) (pmat z * pmat z) hsq 1
  beta_reduce at hP1 hP2
  rw [Matrix.coeff_det_one_add_X_smul_one] at hP1
  have h2 := coeff_two_det_hermitian _ ((pmat_isHermitian z).submatrix (Fin.castLE hi))
  rw [trace_leading_submatrix_pmat z hi] at h2
  have hS : ∀ S : {S : Finset (Fin n) // S.card = i}, ((yS z S.1 : ℝ) : ℂ) ^ 2 =
      2 * (∏ s ∈ S.1, (1 + X * C ((pev z s : ℝ) : ℂ))).coeff 2 +
        (∏ s ∈ S.1, (1 + X * C (((pev z s : ℝ) : ℂ) ^ 2))).coeff 1 := by
    intro S
    obtain ⟨-, -, h2'⟩ := coeff_prod_one_add_low S.1 (fun s => ((pev z s : ℝ) : ℂ))
    obtain ⟨-, h1'', -⟩ := coeff_prod_one_add_low S.1 (fun s => ((pev z s : ℝ) : ℂ) ^ 2)
    rw [h2', h1'', yS]
    push_cast
    ring
  apply Complex.ofReal_injective
  push_cast
  rw [variance_eq_trace_diff hi (pmat z) (pmat_isHermitian z)]
  simp only [hS, mul_add, Finset.sum_add_distrib, mul_left_comm _ (2 : ℂ), ← Finset.mul_sum]
  rw [hP2, hP1, h2]
  ring

end ReciprocityTheory.ChartRestriction.DS
