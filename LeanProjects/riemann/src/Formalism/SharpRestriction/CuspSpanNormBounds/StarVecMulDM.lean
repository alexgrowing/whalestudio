import Formalism.SharpRestriction.CuspSpanNormBounds.TrD

open MeasureTheory Matrix Finset

noncomputable section

set_option linter.unusedVariables false

namespace Formalism.MainNotions.FrameBoundFromBesselTorus

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

def alphaPt {r : ℕ} (κ τ : ℝ) (γ : Point ℂ (r + 1)) : ℝ :=
  κ ^ (rootPat γ).card * ∏ p ∈ rootPat γ, (tF r κ τ p.2.val / tF r κ τ p.1.val) ^ 2

section Alg3

variable {k r : ℕ} {κ τ : ℝ}

theorem Hpk_mul_dMi (hκ : 0 < κ) (hτ : 0 < τ) : Hpk k r * dMi k r κ τ = dM k r κ τ * Hpk k r := by
  ext i j
  rw [dMi, dM, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : Hpk k r i j = 0
  · rw [h]; simp
  · have e := tV_mul_of_Hpk hκ hτ i j h
    have : (tV k r κ τ j)⁻¹ = tV k r κ τ i := (eq_inv_of_mul_eq_one_left e).symm
    rw [this]; ring

theorem star_vecMul_dM (v : Fin (2 * r + k + 1) → ℂ) : star v ᵥ* dM k r κ τ = star (dM k r κ τ *ᵥ v) := by
  funext j
  rw [dM, Matrix.vecMul_diagonal, Pi.star_apply, Pi.star_apply, Matrix.mulVec_diagonal, star_mul',
    Complex.star_def, Complex.conj_ofReal, mul_comm]

theorem Zhat_cj (hκ : 0 < κ) (hτ : 0 < τ) {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    (hz' : inWb k r z') (g : Mx k r) (a b : Fin (r + 1)) :
    Zhat k r ((τ : ℂ) • z) ((τ : ℂ) • z') (cj k r κ τ g) a b =
      ((tF r κ τ a.val * tF r κ τ b.val : ℝ) : ℂ) * Zhat k r z z' g a b := by
  unfold Zhat herm
  rw [cj_mulVec, dM_mulVec_fvec hz' b, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec (M := Hpk k r) (N := dMi k r κ τ), Hpk_mul_dMi hκ hτ, ← Matrix.mulVec_mulVec,
    dotProduct_smul, Matrix.dotProduct_mulVec, star_vecMul_dM, dM_mulVec_fvec hz a, star_smul,
    smul_dotProduct]
  simp only [Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
  push_cast; ring

theorem bigCell_cj (hκ : 0 < κ) (hτ : 0 < τ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    cj k r κ τ (bigCell k r c μ) = bigCell k r (fun a => ((tF r κ τ a.val ^ 2 : ℝ) : ℂ) * c a) μ := by
  ext i j
  rw [cj_apply]
  unfold bigCell
  by_cases hj : j.val < r
  · rw [dif_pos hj, dif_pos hj]
    by_cases hi : i = esI k r ⟨j.val, hj⟩
    · rw [if_pos hi, if_pos hi, hi, tV_esI]
      have : tV k r κ τ j = tF r κ τ j.val := by unfold tV; rw [if_pos hj]
      rw [this, inv_inv]; push_cast; ring
    · rw [if_neg hi, if_neg hi, mul_zero]
  · rw [dif_neg hj, dif_neg hj]
    by_cases hj2 : j.val ≤ r + k
    · rw [dif_pos hj2, dif_pos hj2]
      by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
      · rw [dif_pos hi, tV_wb i hi.1 hi.2, tV_wb j (by omega) hj2]; simp
      · rw [dif_neg hi, mul_zero]
    · rw [dif_neg hj2, dif_neg hj2]
      by_cases hi : i.val = 2 * r + k - j.val
      · rw [if_pos hi, if_pos hi]
        have hti : tV k r κ τ i = tF r κ τ (2 * r + k - j.val) := by
          unfold tV; rw [if_pos (by omega), hi]
        have htj : tV k r κ τ j = (tF r κ τ (2 * r + k - j.val))⁻¹ := by
          unfold tV; rw [if_neg hj, if_neg hj2]
        have hp := tF_pos (r := r) hκ hτ (2 * r + k - j.val)
        rw [hti, htj]
        simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
        have hpc : ((tF r κ τ (2 * r + k - j.val) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
        push_cast
        rw [mul_inv]
        field_simp
      · rw [if_neg hi, if_neg hi, mul_zero]

theorem flagMat_cj (hκ : 0 < κ) (hτ : 0 < τ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (x : Mx k r)
    (i j : Fin (r + 1)) (hi : i.val < r) :
    flagMat k r ((τ : ℂ) • z) (cj k r κ τ x) i j =
      ((tF r κ τ j.val / tF r κ τ i.val : ℝ) : ℂ) * flagMat k r z x i j := by
  unfold flagMat
  rw [dif_pos hi, dif_pos hi, cj_mulVec, dM_mulVec_fvec hz j, Matrix.mulVec_smul, dMi_mulVec_apply, tV_eI,
    Pi.smul_apply, smul_eq_mul]
  push_cast; ring

theorem rootCoords_cjT (hκ : 0 < κ) (hτ : 0 < τ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    (γ : Point ℂ (r + 1)) (x : Mt k r) (p : rootPat γ) :
    rootCoords k r ((τ : ℂ) • z) γ (cjT k r κ τ x) p =
      ((tF r κ τ p.1.2.val / tF r κ τ p.1.1.val : ℝ) : ℂ) * rootCoords k r z γ x p := by
  have hp := (Finset.mem_filter.mp p.2).2.1
  have hi : p.1.1.val < r := by
    have h1 : p.1.1.val < p.1.2.val := hp
    have h2 := p.1.2.isLt
    omega
  unfold rootCoords
  rw [of_cjT]
  exact flagMat_cj hκ hτ hz (Matrix.of x) p.1.1 p.1.2 hi

theorem Tz_smul (z : Fin (2 * r + k + 1) → ℂ) (t : ℝ) : Tz k r ((t : ℂ) • z) = t ^ 2 * Tz k r z := by
  unfold Tz herm
  rw [Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct]
  simp only [Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
  rw [← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  ring

theorem inWb_bvec_wI (j : Fin (k + 1)) : inWb k r (bvec (wI k r j)) := by
  intro i hi
  have : i ≠ wI k r j := by
    intro e; rw [e] at hi; unfold wI at hi; simp only at hi; omega
  simp [bvec, this]

theorem cj_blockW (hκ : 0 < κ) (hτ : 0 < τ) (h : Matrix (Fin k) (Fin k) ℂ) :
    cj k r κ τ (blockW k r h) = blockW k r h := by
  ext i j
  rw [cj_apply]
  unfold blockW
  by_cases hi : r ≤ i.val ∧ i.val < r + k
  · rw [dif_pos hi]
    by_cases hj : r ≤ j.val ∧ j.val < r + k
    · rw [dif_pos hj, tV_wb i hi.1 (by omega), tV_wb j hj.1 (by omega)]; simp
    · rw [dif_neg hj, mul_zero]
  · rw [dif_neg hi]
    by_cases e : i = j
    · rw [if_pos e, cj_fac_diag hκ hτ i j e, one_mul]
    · rw [if_neg e, mul_zero]

theorem isHCTypeW_cjI (hκ : 0 < κ) (hτ : 0 < τ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    {u : Fin k → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {π : Mx k r → (H →L[ℂ] H)} (h : IsHCTypeW k r z u π) :
    IsHCTypeW k r ((τ : ℂ) • z) u (fun x => π (cjI k r κ τ x)) := by
  obtain ⟨g, ⟨hg1, hg2, hg3⟩, hU⟩ := h
  refine ⟨cj k r κ τ g, ⟨(cj_mem_UH_iff hκ hτ g).mpr hg1, fun a =>
    ⟨(cj_fix_bvec_iff hκ hτ g _).mpr (hg2 a).1, (cj_fix_bvec_iff hκ hτ g _).mpr (hg2 a).2⟩, ?_⟩, ?_⟩
  · rw [Tz_smul, Real.sqrt_mul (sq_nonneg τ), Real.sqrt_sq hτ.le, cj_mulVec, Matrix.mulVec_smul,
      dM_mulVec_wb (inWb_bvec_wI _), Complex.ofReal_mul, ← smul_smul, Matrix.mulVec_smul, hg3,
      Matrix.mulVec_smul, dMi_mulVec_wb hz]
  · have e : (fun h => π (cjI k r κ τ (cj k r κ τ g * blockW k r h * (cj k r κ τ g)⁻¹))) =
        fun h => π (g * blockW k r h * g⁻¹) := by
      funext h
      rw [← cj_inv hκ hτ, ← cj_blockW hκ hτ h, ← cj_mul hκ hτ, ← cj_mul hκ hτ, cjI_cj hκ hτ, cj_blockW hκ hτ]
    simp only at e ⊢
    rw [e]; exact hU

theorem isRelStab_iff (hκ : 0 < κ) (hτ : 0 < τ) (L L₁ : LocBessel k r) (hz : inWb k r L.z) (hz' : inWb k r L.z')
    (e1 : L₁.z = (τ : ℂ) • L.z) (e2 : L₁.z' = (τ : ℂ) • L.z') (e3 : L₁.c = (κ : ℂ) * L.c) (g : Mx k r) :
    IsRelStab L₁ (cj k r κ τ g) ↔ IsRelStab L g := by
  unfold IsRelStab
  rw [e1, e2, e3]
  constructor
  · intro h a ha
    have := h (cj k r κ τ a) ((cj_mem_RStab_iff hκ hτ g a).mpr ha)
    rwa [← cj_inv hκ hτ, ← cj_mul hκ hτ, ← cj_mul hκ hτ, psi_cj hκ hτ hz, psi_cj hκ hτ hz'] at this
  · intro h a₁ ha₁
    have ha : cjI k r κ τ a₁ ∈ RStab k r g := by
      rw [← cj_mem_RStab_iff hκ hτ g, cj_cjI hκ hτ]; exact ha₁
    have := h _ ha
    rw [← cj_cjI hκ hτ a₁, ← cj_inv hκ hτ, ← cj_mul hκ hτ, ← cj_mul hκ hτ, psi_cj hκ hτ hz, psi_cj hκ hτ hz']
    exact this

end Alg3

end Formalism.MainNotions.FrameBoundFromBesselTorus
