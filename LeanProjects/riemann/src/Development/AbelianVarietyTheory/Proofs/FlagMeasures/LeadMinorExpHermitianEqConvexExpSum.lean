import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.MulConjTransposeEqOneOfOrthonormal

open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory.LeadMinorExp

theorem sum_dite_card {n l : ℕ} {M : Type*} [AddCommMonoid M] (f : Set.powersetCard (Fin n) l → M) :
    ∑ J : Finset (Fin n), (if h : J.card = l then f ⟨J, h⟩ else 0) = ∑ S, f S := by
  symm
  refine Finset.sum_of_injOn (fun S : Set.powersetCard (Fin n) l => S.1)
    (fun _ _ _ _ h => Subtype.ext h) (fun _ _ => Finset.mem_univ _) ?_ ?_
  · intro J _ hJ
    rw [dif_neg]
    intro h
    exact hJ ⟨⟨J, h⟩, by simp, rfl⟩
  · intro S _
    have h : S.1.card = l := S.2
    rw [dif_pos h]

theorem exp_smul_eq {n : ℕ} {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y.IsHermitian) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • Y) =
      (hY.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
        diagonal (fun j => ((Real.exp (t * hY.eigenvalues j) : ℝ) : ℂ)) *
        (hY.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hY.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have h1 : U * Uᴴ = 1 := (hY.eigenvectorUnitary).2.2
  have h2 : Uᴴ * U = 1 := (hY.eigenvectorUnitary).2.1
  have hs : Y = U * diagonal (fun j => ((hY.eigenvalues j : ℝ) : ℂ)) * Uᴴ := by
    have := hY.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have h3 : (t : ℂ) • Y = U * diagonal (fun j => ((t * hY.eigenvalues j : ℝ) : ℂ)) * Uᴴ := by
    conv_lhs => rw [hs]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← diagonal_smul]
    congr 3
    funext j
    simp
  rw [h3]
  refine (Matrix.exp_units_conj (⟨U, Uᴴ, h1, h2⟩ : (Matrix (Fin n) (Fin n) ℂ)ˣ) _).trans ?_
  rw [Matrix.exp_diagonal]
  change U * _ * Uᴴ = _
  congr 3
  funext j
  rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp]

theorem leadMinor_exp_eq_sum (n : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ) (hY : Y.IsHermitian) (l : ℕ)
    (hl : l ≤ n) :
    ∃ w : Finset (Fin n) → ℝ, (∀ J, 0 ≤ w J) ∧ (∀ J, w J ≠ 0 → J.card = l) ∧ ∑ J, w J = 1 ∧
      ∀ t : ℝ, leadMinor (NormedSpace.exp ((t : ℂ) • Y)) l hl =
        ((∑ J, w J * Real.exp (t * ∑ j ∈ J, hY.eigenvalues j) : ℝ) : ℂ) := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hY.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have h1 : U * Uᴴ = 1 := (hY.eigenvectorUnitary).2.2
  set A : Matrix (Fin l) (Fin n) ℂ := U.submatrix (Fin.castLE hl) id with hA
  have hAA : A * Aᴴ = 1 := by
    rw [hA, conjTranspose_submatrix, ← submatrix_mul U Uᴴ _ id _ Function.bijective_id, h1]
    exact submatrix_one _ (Fin.castLE_injective hl)
  refine ⟨fun J => if h : J.card = l then
    ‖(A.submatrix id (GlobalTheory.subsetEnum (⟨J, h⟩ : Set.powersetCard (Fin n) l))).det‖ ^ 2 else 0,
    ?_, ?_, ?_, ?_⟩
  · intro J
    dsimp only
    split_ifs <;> positivity
  · intro J hJ
    by_contra h
    exact hJ (dif_neg h)
  · rw [sum_dite_card (fun S => ‖(A.submatrix id (GlobalTheory.subsetEnum S)).det‖ ^ 2)]
    exact GlobalTheory.sum_norm_sq_minors_eq_one A hAA
  · intro t
    have hsum : (∑ J : Finset (Fin n), (if h : J.card = l then
        ‖(A.submatrix id (GlobalTheory.subsetEnum (⟨J, h⟩ : Set.powersetCard (Fin n) l))).det‖ ^ 2 else 0) *
          Real.exp (t * ∑ j ∈ J, hY.eigenvalues j)) =
        ∑ S : Set.powersetCard (Fin n) l, ‖(A.submatrix id (GlobalTheory.subsetEnum S)).det‖ ^ 2 *
          Real.exp (t * ∑ j ∈ S.1, hY.eigenvalues j) := by
      rw [← sum_dite_card]
      refine Finset.sum_congr rfl fun J _ => ?_
      split_ifs <;> simp
    rw [hsum, exp_smul_eq hY t, leadMinor]
    rw [submatrix_mul _ _ _ id _ Function.bijective_id,
      submatrix_mul _ _ _ id _ Function.bijective_id, submatrix_id_id,
      ← conjTranspose_submatrix]
    refine (GlobalTheory.det_mul_diagonal_mul_eq_sum_minors A _ Aᴴ).trans ?_
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [← conjTranspose_submatrix, det_conjTranspose, Complex.star_def, Complex.mul_conj',
      Finset.mul_sum, Real.exp_sum]
    push_cast
    ring

end GlobalTheory.LeadMinorExp
