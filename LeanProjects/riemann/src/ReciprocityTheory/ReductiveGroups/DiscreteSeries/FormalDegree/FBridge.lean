import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PmatIsHermitian
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.TraceMulSelfEqSumEigenvaluesSq
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Minors

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace ComplexOrder

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem fbr_det_exp_pmat {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    (NormedSpace.exp (pmat z)).det = 1 := by
  set U : Matrix (Fin n) (Fin n) ℂ := ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hsp : pmat z = U * diagonal (fun i => (pev z i : ℂ)) * Uᴴ := by
    have := (pmat_isHermitian z).spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have h1 : Uᴴ * U = 1 := Unitary.coe_star_mul_self _
  have h2 : U * Uᴴ = 1 := Unitary.coe_mul_star_self _
  have hinv : U⁻¹ = Uᴴ := Matrix.inv_eq_right_inv h2
  have hu : IsUnit U := ⟨⟨U, Uᴴ, h2, h1⟩, rfl⟩
  rw [hsp, ← hinv, Matrix.exp_conj _ _ hu, Matrix.det_conj hu, Matrix.exp_diagonal, det_diagonal]
  have he : ∀ i, (NormedSpace.exp (fun i => (pev z i : ℂ))) i = Complex.exp (pev z i : ℂ) := by
    intro i
    rw [Pi.exp_def, Complex.exp_eq_exp_ℂ]
  simp only [he]
  rw [← Complex.exp_sum, ← Complex.ofReal_sum, sum_pev, Complex.ofReal_zero, Complex.exp_zero]

theorem fbr_det_conj {ε : Fin n → Bool} (k : KG ε) (A : Matrix (Fin n) (Fin n) ℂ) :
    (toMK k⁻¹ * A * toMK k).det = A.det := by
  rw [toMK_inv, Matrix.det_mul, Matrix.det_mul, mul_comm ((toMK k)ᴴ.det) A.det, mul_assoc, ← Matrix.det_mul,
    (toMK_facts k).1, Matrix.det_one, mul_one]

theorem fbr_phi {ε : Fin n → Bool} {lam : Fin n → ℝ} {μ : Fin n → ℤ} (hμ : IsMu lam μ) (k : KG ε)
    (z : PCoord ε → ℂ) :
    PhiM μ (toMK k⁻¹ * NormedSpace.exp (pmat z) * toMK k) =
      ((Real.exp (-Ph lam (toMK k⁻¹ * pmat z * toMK k)) : ℝ) : ℂ) := by
  obtain ⟨hP, hE⟩ := inP_conj k⁻¹ (pmat_inP z)
  rw [inv_inv] at hP hE
  rw [← hE]
  set Y := toMK k⁻¹ * pmat z * toMK k with hY
  set E := NormedSpace.exp Y with hEdef
  have hpd : E.PosDef := exp_noncompactPart_posDef hP
  have hdet : lead n E = 1 := by
    have h1 : E.det = 1 := by rw [hE, fbr_det_conj, fbr_det_exp_pmat]
    unfold lead
    rw [dif_pos le_rfl]
    convert h1 using 2
    ext a b
    rfl
  have hpos : ∀ i : Fin n, 0 < (lead ((i : ℕ) + 1) E).re := fun i => (lead_posDef hpd _ i.isLt).1
  have h : ∀ i : Fin n, lead ((i : ℕ) + 1) E = ((lead ((i : ℕ) + 1) E).re : ℂ) := fun i =>
    Complex.ext (by simp) (by simp [(lead_posDef hpd _ i.isLt).2])
  have hphi : PhiM μ E = ((∏ i : Fin n, (lead ((i : ℕ) + 1) E).re ^ (-(μ i - muNext μ i)) : ℝ) : ℂ) := by
    unfold PhiM
    rw [Complex.ofReal_prod]
    refine prod_congr rfl fun i _ => ?_
    rw [Complex.ofReal_zpow, ← h i]
  rw [hphi]
  congr 1
  have hz : ∀ i : Fin n, (lead ((i : ℕ) + 1) E).re ^ (-(μ i - muNext μ i)) =
      Real.exp (Real.log (lead ((i : ℕ) + 1) E).re * ((-(μ i - muNext μ i) : ℤ) : ℝ)) := by
    intro i
    rw [← Real.rpow_intCast, Real.rpow_def_of_pos (hpos i)]
  rw [prod_congr rfl fun i _ => hz i, ← Real.exp_sum]
  congr 1
  set g : ℕ → ℝ := fun i => -(sCoef lam i * Real.log (lead (i + 1) E).re) with hg
  have hterm : ∀ i : Fin n, Real.log (lead ((i : ℕ) + 1) E).re * ((-(μ i - muNext μ i) : ℤ) : ℝ) = g i := by
    intro i
    by_cases hi : (i : ℕ) + 1 < n
    · have hm : muNext μ i = μ ⟨(i : ℕ) + 1, hi⟩ := by simp [muNext, hi]
      have hs : sCoef lam i = lam i - lam ⟨(i : ℕ) + 1, hi⟩ + 1 := by simp [sCoef, hi]
      rw [hm, hg]
      simp only
      rw [hs]
      push_cast
      rw [hμ i, hμ ⟨(i : ℕ) + 1, hi⟩]
      simp only [rho]
      push_cast
      ring
    · have hs : sCoef lam i = 0 := by simp [sCoef, hi]
      have hn : (i : ℕ) + 1 = n := by omega
      rw [hg]
      simp only
      rw [hs, hn, hdet]
      simp
  rw [sum_congr rfl fun i _ => hterm i, Fin.sum_univ_eq_sum_range g n]
  have hsub : ∑ i ∈ range n, g i = ∑ i ∈ range (n - 1), g i := by
    symm
    refine sum_subset (range_subset_range.mpr (Nat.sub_le n 1)) ?_
    intro i hi hi'
    simp only [mem_range] at hi hi'
    have hs : sCoef lam i = 0 := by simp only [sCoef]; rw [dif_neg (by omega)]
    simp [hg, hs]
  rw [hsub, Ph, ← sum_neg_distrib]
  rfl

theorem psM_exp_pmat {ε : Fin n → Bool} {lam : Fin n → ℝ} {μ : Fin n → ℤ} (hμ : IsMu lam μ) {Λ : Fin n → ℝ}
    (T : KType ε Λ) (z : PCoord ε → ℂ) : psM T μ (NormedSpace.exp (pmat z)) = fF ε lam T (pmat z) := by
  simp only [psM, fF]
  congr 1
  refine congrArg (fun f : KG ε → T.V →L[ℂ] T.V => ∫ k, f k ∂(muK ε)) (funext fun k => ?_)
  rw [fbr_phi hμ k z]

end ReciprocityTheory.ChartRestriction.DS
