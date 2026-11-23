import Formalism.FilteredPoleLength.ReducedBasisBounds.GFiniteOrderUnipotent

open scoped BigOperators
open Finset

namespace Formalism.LatticeBaseChangeAlt

private lemma norm_det_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x : ℝ)
    (hx : ∀ i j, ‖A i j‖ ≤ x) : ‖A.det‖ ≤ n.factorial * x ^ n := by
  rw [Matrix.det_apply]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ σ : Equiv.Perm (Fin n), ‖Equiv.Perm.sign σ • ∏ i, A (σ i) i‖ ≤ x ^ n := by
    intro σ
    have hp : ‖∏ i, A (σ i) i‖ ≤ x ^ n := by
      rw [norm_prod]
      calc ∏ i, ‖A (σ i) i‖ ≤ ∏ _i : Fin n, x :=
            Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hx _ _)
        _ = x ^ n := by simp
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · rw [hs, one_smul]
      exact hp
    · rw [hs, Units.neg_smul, one_smul, norm_neg]
      exact hp
  calc ∑ σ : Equiv.Perm (Fin n), ‖Equiv.Perm.sign σ • ∏ i, A (σ i) i‖
      ≤ ∑ _σ : Equiv.Perm (Fin n), x ^ n := Finset.sum_le_sum fun σ _ => hterm σ
    _ = n.factorial * x ^ n := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

private theorem det_le_one_of_posSemidef_of_diag_eq_one {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosSemidef) (hd : ∀ j, G j j = 1) : G.det ≤ 1 := by
  have htr : G.trace = (n : ℝ) := by
    simp [Matrix.trace, hd]
  have hev : ∑ i, hG.1.eigenvalues i = (n : ℝ) := by
    have := hG.1.trace_eq_sum_eigenvalues
    rw [htr] at this
    exact this.symm
  calc G.det = ∏ i, hG.1.eigenvalues i := hG.1.det_eq_prod_eigenvalues
    _ ≤ ∏ i, Real.exp (hG.1.eigenvalues i - 1) :=
        Finset.prod_le_prod (fun i _ => hG.eigenvalues_nonneg i)
          (fun i _ => by linarith [Real.add_one_le_exp (hG.1.eigenvalues i - 1)])
    _ = Real.exp (∑ i, (hG.1.eigenvalues i - 1)) := (Real.exp_sum _ _).symm
    _ = 1 := by
        rw [Finset.sum_sub_distrib, hev]
        simp

theorem gHadamard : GHadamard := by
  intro n M
  have hs0 : ∀ j, 0 ≤ ∑ i, M i j ^ 2 := fun j => Finset.sum_nonneg fun i _ => sq_nonneg _
  by_cases hz : ∃ j, ∑ i, M i j ^ 2 = 0
  · obtain ⟨j, hj⟩ := hz
    have hcol : ∀ i, M i j = 0 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (M i j))).mp hj i
        (Finset.mem_univ _)
      exact pow_eq_zero_iff two_ne_zero |>.mp this
    rw [Matrix.det_eq_zero_of_column_eq_zero j hcol, abs_zero]
    exact Finset.prod_nonneg fun j _ => Real.sqrt_nonneg _
  push_neg at hz
  have hpos : ∀ j, 0 < ∑ i, M i j ^ 2 := fun j => lt_of_le_of_ne (hs0 j) (Ne.symm (hz j))
  obtain ⟨r, hr⟩ : ∃ r : Fin n → ℝ, r = fun j => Real.sqrt (∑ i, M i j ^ 2) := ⟨_, rfl⟩
  have hr0 : ∀ j, 0 < r j := fun j => by
    rw [hr]
    exact Real.sqrt_pos.mpr (hpos j)
  have hrsq : ∀ j, r j ^ 2 = ∑ i, M i j ^ 2 := fun j => by
    rw [hr]
    exact Real.sq_sqrt (hpos j).le
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin n) (Fin n) ℝ,
      N = M * Matrix.diagonal (fun j => (r j)⁻¹) := ⟨_, rfl⟩
  have hNe : ∀ i j, N i j = M i j * (r j)⁻¹ := fun i j => by
    rw [hN, Matrix.mul_diagonal]
  have hdiag : ∀ j, (N.conjTranspose * N) j j = 1 := by
    intro j
    rw [Matrix.mul_apply]
    have e : ∀ x, N.conjTranspose j x * N x j = M x j ^ 2 / r j ^ 2 := fun x => by
      rw [Matrix.conjTranspose_apply, star_trivial, hNe]
      ring
    rw [Finset.sum_congr rfl fun x _ => e x, ← Finset.sum_div, hrsq j]
    exact div_self (ne_of_gt (hpos j))
  have hdetG : (N.conjTranspose * N).det = N.det ^ 2 := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose, star_trivial, sq]
  have h1 : N.det ^ 2 ≤ 1 := by
    rw [← hdetG]
    exact det_le_one_of_posSemidef_of_diag_eq_one _ (Matrix.posSemidef_conjTranspose_mul_self N)
      hdiag
  have h1' : |N.det| ≤ 1 := abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have hP : 0 < ∏ j, r j := Finset.prod_pos fun j _ => hr0 j
  have h2 : N.det = M.det / ∏ j, r j := by
    rw [hN, Matrix.det_mul, Matrix.det_diagonal, Finset.prod_inv_distrib, div_eq_mul_inv]
  rw [h2, abs_div, abs_of_pos hP, div_le_one hP] at h1'
  have h3 : ∏ j, r j = ∏ j, Real.sqrt (∑ i, M i j ^ 2) := by
    rw [hr]
  rw [← h3]
  exact h1'

end Formalism.LatticeBaseChangeAlt
