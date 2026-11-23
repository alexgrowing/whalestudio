import Formalism.HermitianCurvature.StatementH
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Herglotz

namespace Formalism.FourierDecayAlt.P.Fejer

open Real Finset Formalism.FourierDecayAlt.P.Herglotz

variable {d : ℕ}

lemma fac_succ_of_mem (N : ℕ) (t : ℤ) (ht : t ∈ Finset.Icc (-(N : ℤ)) N) :
    fac (N + 1) t = 1 - |((t : ℤ) : ℝ)| / ((N : ℝ) + 1) := by
  rw [Finset.mem_Icc] at ht
  have habs : |t| ≤ (N : ℤ) := abs_le.2 ht
  have hz : (0 : ℤ) ≤ ((N + 1 : ℕ) : ℤ) - |t| := by push_cast; omega
  have hN0 : ((N : ℝ) + 1) ≠ 0 := by positivity
  unfold fac
  rw [show (((((N + 1 : ℕ) : ℤ) - |t|).toNat : ℕ) : ℝ)
      = ((((((N + 1 : ℕ) : ℤ) - |t|).toNat : ℕ) : ℤ) : ℝ) by norm_cast,
    Int.toNat_of_nonneg hz]
  push_cast
  field_simp

lemma fac_succ_of_not_mem (N : ℕ) (t : ℤ) (ht : t ∉ Finset.Icc (-(N : ℤ)) N) :
    fac (N + 1) t = 0 := by
  rw [Finset.mem_Icc] at ht
  have habs : (N : ℤ) < |t| := by
    by_contra h
    exact ht (abs_le.1 (not_lt.1 h))
  have hz : (((N + 1 : ℕ) : ℤ) - |t|).toNat = 0 := by
    rw [Int.toNat_eq_zero]; push_cast; omega
  unfold fac
  rw [hz]; simp

lemma wt_succ_of_mem (N : ℕ) (τ : Fin d → ℤ)
    (hτ : τ ∈ Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(N : ℤ)) N)) :
    wt (N + 1) τ = ∏ j, (1 - |((τ j : ℤ) : ℝ)| / ((N : ℝ) + 1)) := by
  rw [Fintype.mem_piFinset] at hτ
  unfold wt
  exact Finset.prod_congr rfl (fun j _ => fac_succ_of_mem N (τ j) (hτ j))

lemma wt_succ_of_not_mem (N : ℕ) (τ : Fin d → ℤ)
    (hτ : τ ∉ Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(N : ℤ)) N)) :
    wt (N + 1) τ = 0 := by
  rw [Fintype.mem_piFinset] at hτ
  simp only [not_forall] at hτ
  obtain ⟨j, hj⟩ := hτ
  unfold wt
  exact Finset.prod_eq_zero (Finset.mem_univ j) (fac_succ_of_not_mem N (τ j) hj)

end Formalism.FourierDecayAlt.P.Fejer

namespace Formalism.FourierDecayAlt.P

open Real Finset Formalism.FourierDecayAlt.P.Herglotz Formalism.FourierDecayAlt.P.Fejer

theorem herglotz_fejer_Zd : Formalism.FourierDecayAlt.H.HerglotzFejerZd := by
  intro d A hPD N x
  have h := hPD (box d (N + 1)) (ee x)
  simp_rw [mul_assoc, ee_mul_conj] at h
  have hd := dsum (fun τ => A τ * ee x τ) (box d (N + 1))
  beta_reduce at hd
  rw [hd] at h
  have hN0 : N + 1 ≠ 0 := by omega
  have heq : (∑' τ, ((wt (N + 1) τ : ℝ) : ℂ) * (A τ * ee x τ)) =
      (((((N + 1 : ℕ) : ℝ) ^ d)⁻¹ : ℝ) : ℂ) *
        ∑' τ, (((box d (N + 1) ×ˢ box d (N + 1)).filter (fun p => p.1 - p.2 = τ)).card : ℂ) *
          (A τ * ee x τ) := by
    rw [← tsum_mul_left]
    congr 1
    funext τ
    rw [← wt_eq (N + 1) hN0 τ]
    push_cast
    ring
  have hfin : (∑' τ, ((wt (N + 1) τ : ℝ) : ℂ) * (A τ * ee x τ)) =
      ∑ σ ∈ Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(N : ℤ)) N),
        (((∏ j, (1 - |((σ j : ℤ) : ℝ)| / ((N : ℝ) + 1))) : ℝ) : ℂ) * A σ *
          Complex.exp (2 * π * Complex.I * ∑ j, ((σ j : ℝ) : ℂ) * (x j : ℂ)) := by
    rw [tsum_eq_sum (s := Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(N : ℤ)) N))]
    · refine Finset.sum_congr rfl (fun σ hσ => ?_)
      rw [wt_succ_of_mem N σ hσ, mul_assoc]
      rfl
    · intro τ hτ
      rw [wt_succ_of_not_mem N τ hτ]
      simp
  rw [← hfin, heq, Complex.re_ofReal_mul]
  exact mul_nonneg (by positivity) h

end Formalism.FourierDecayAlt.P
