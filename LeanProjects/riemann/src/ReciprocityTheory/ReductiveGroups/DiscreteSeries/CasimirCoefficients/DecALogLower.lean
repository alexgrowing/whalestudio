import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DecPos
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DecLog
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DecMoments
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DecSum
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ToMKMulInv

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool}

lemma decA_spec {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inP ε Y) :
    ∃ (U : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℝ), U ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ := by
  obtain ⟨h1, h2⟩ := hY
  have hJJ : Jm ε * Jm ε = 1 := by
    unfold Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> simp
  have hH : Yᴴ = Y := by
    unfold inG at h1
    have h3 : Yᴴ * Jm ε = Y * Jm ε := by
      rw [h2]
      exact eq_neg_of_add_eq_zero_left h1
    calc Yᴴ = Yᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = Y * Jm ε * Jm ε := by rw [h3]
      _ = Y := by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
  have hA : Y.IsHermitian := hH
  refine ⟨hA.eigenvectorUnitary, hA.eigenvalues, (hA.eigenvectorUnitary).2, ?_⟩
  first
    | exact hA.spectral_theorem
    | simpa [Matrix.star_eq_conjTranspose] using hA.spectral_theorem
    | (conv_lhs => rw [hA.spectral_theorem]); rfl

lemma decA_exp {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (y : Fin n → ℝ) :
    NormedSpace.exp (U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ) =
      U * Matrix.diagonal (fun j => ((Real.exp (y j) : ℝ) : ℂ)) * Uᴴ := by
  have hinv : U⁻¹ = Uᴴ := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.mp hU)
  have hu : IsUnit U := (Matrix.isUnit_iff_isUnit_det U).mpr (isUnit_iff_ne_zero.mpr
    (left_ne_zero_of_mul_eq_one (b := (star U).det)
      (by rw [← Matrix.det_mul, Matrix.mem_unitaryGroup_iff.mp hU, Matrix.det_one])))
  have hd : NormedSpace.exp (fun j => ((y j : ℝ) : ℂ)) = fun j => ((Real.exp (y j) : ℝ) : ℂ) := by
    funext j
    first
      | (rw [Pi.exp_apply]; simp [← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp])
      | (simp [Pi.exp_def, ← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp])
      | (simp [NormedSpace.exp_pi, ← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp])
  rw [← hinv, Matrix.exp_conj U _ hu, Matrix.exp_diagonal, hd]

lemma decA_lead_re {U : Matrix (Fin n) (Fin n) ℂ} (y : Fin n → ℝ) (i : ℕ) (hi : i ≤ n) :
    (lead i (U * Matrix.diagonal (fun j => ((Real.exp (y j) : ℝ) : ℂ)) * Uᴴ)).re =
      ∑ J : {J : Finset (Fin n) // J.card = i}, dmW U hi J * Real.exp (∑ j ∈ J.1, y j) := by
  rw [lead_unitary_diag _ i hi, Complex.re_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [show (∏ j ∈ J.1, ((Real.exp (y j) : ℝ) : ℂ)) = ((∏ j ∈ J.1, Real.exp (y j) : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_mul, Complex.ofReal_re, ← Real.exp_sum]
  rfl

lemma decA_log_lower {Y U : Matrix (Fin n) (Fin n) ℂ} {y : Fin n → ℝ} (hYp : inP ε Y)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ)
    (hq : 1 ≤ q0 ε) (hpos : 0 < hs Y) (m : ℕ) (hm : m ≤ n) :
    min 1 (1 / (Real.sqrt (2 * q0 ε) * Real.sqrt (hs Y))) *
        (∑ a : Fin n, ∑ b : Fin n, if (b : ℕ) < m ∧ m ≤ (a : ℕ) then ‖Y a b‖ ^ 2 else 0) / 4 ≤
      Real.log (lead m (NormedSpace.exp Y)).re := by
  obtain ⟨h1, h2, h3, h4⟩ := dec_moments hU hY hYp m hm
  have hE : NormedSpace.exp Y = U * Matrix.diagonal (fun j => ((Real.exp (y j) : ℝ) : ℂ)) * Uᴴ := by
    rw [hY]; exact decA_exp hU y
  rw [hE, decA_lead_re y m hm, ← h3]
  have hq' : (0 : ℝ) < 2 * q0 ε := by
    have : (1 : ℝ) ≤ q0 ε := by exact_mod_cast hq
    linarith
  have hR : 0 < Real.sqrt (2 * q0 ε) * Real.sqrt (hs Y) :=
    mul_pos (Real.sqrt_pos.mpr hq') (Real.sqrt_pos.mpr hpos)
  exact logSumExp_lower (fun J => dmW U hm J) (fun J => ∑ j ∈ J.1, y j) (fun J => by unfold dmW; positivity)
    h1 h2 hR h4

lemma decA_lead_last {Y U : Matrix (Fin n) (Fin n) ℂ} {y : Fin n → ℝ} (hYp : inP ε Y)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ) :
    (lead n (NormedSpace.exp Y)).re = 1 := by
  obtain ⟨_, h2⟩ := hYp
  have hJJ : Jm ε * Jm ε = 1 := by
    unfold Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> simp
  have htr : Matrix.trace Y = 0 := by
    have e1 : Matrix.trace Y = Matrix.trace (Jm ε * (Y * Jm ε)) := by
      rw [← Matrix.trace_mul_comm (Y * Jm ε) (Jm ε), Matrix.mul_assoc, hJJ, Matrix.mul_one]
    rw [h2, Matrix.mul_neg, ← Matrix.mul_assoc, hJJ, Matrix.one_mul, Matrix.trace_neg] at e1
    have e2 : (2 : ℂ) * Matrix.trace Y = 0 := by linear_combination e1
    simpa using e2
  have hUU : Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hU
  have hsum : ∑ j, y j = 0 := by
    have e3 : Matrix.trace Y = ((∑ j, y j : ℝ) : ℂ) := by
      rw [hY, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUU, Matrix.one_mul, Matrix.trace_diagonal]
      push_cast
      rfl
    rw [htr] at e3
    exact_mod_cast e3.symm
  rw [hY, decA_exp hU y, decA_lead_re y n le_rfl]
  have huniq : ∀ J : {J : Finset (Fin n) // J.card = n}, J = ⟨Finset.univ, by simp⟩ :=
    fun J => Subtype.ext (Finset.eq_univ_of_card _ (by simpa using J.2))
  rw [Fintype.sum_eq_single ⟨Finset.univ, by simp⟩ (fun J hJ => absurd (huniq J) hJ)]
  rw [hsum, Real.exp_zero, mul_one]
  unfold dmW
  have hid : ((Finset.univ : Finset (Fin n)).orderEmbOfFin (by simp) : Fin n → Fin n) = id :=
    (Finset.orderEmbOfFin_unique (by simp) (fun x => Finset.mem_univ x) strictMono_id).symm
  have hsub : U.submatrix (Fin.castLE (le_refl n))
      ((Finset.univ : Finset (Fin n)).orderEmbOfFin (by simp)) = U := by
    ext i j
    rw [Matrix.submatrix_apply, show Fin.castLE (le_refl n) i = i from Fin.ext rfl,
      show ((Finset.univ : Finset (Fin n)).orderEmbOfFin (by simp) : Fin n → Fin n) j = j from congrFun hid j]
  rw [hsub]
  have hdet : star U.det * U.det = 1 := by
    rw [← Matrix.det_conjTranspose, ← Matrix.det_mul, hUU, Matrix.det_one]
  have h5 : ((‖U.det‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← hdet, Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  exact_mod_cast h5

lemma decA_hs_trace (A : Matrix (Fin n) (Fin n) ℂ) : ((hs A : ℝ) : ℂ) = Matrix.trace (A * Aᴴ) := by
  unfold hs
  rw [Matrix.trace]
  push_cast
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

lemma decA_hs_conj {K : Matrix (Fin n) (Fin n) ℂ} (hK : K * Kᴴ = 1) (X : Matrix (Fin n) (Fin n) ℂ) :
    hs (Kᴴ * X * K) = hs X := by
  apply Complex.ofReal_injective
  rw [decA_hs_trace, decA_hs_trace, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  calc Matrix.trace (Kᴴ * X * K * (Kᴴ * (Xᴴ * K))) = Matrix.trace (Kᴴ * ((X * Xᴴ) * K)) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc K Kᴴ, hK, Matrix.one_mul]
    _ = Matrix.trace ((X * Xᴴ) * K * Kᴴ) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (X * Xᴴ) := by rw [Matrix.mul_assoc, hK, Matrix.mul_one]

end ReciprocityTheory.ChartRestriction.DS.S7
