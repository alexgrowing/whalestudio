import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset

noncomputable section

open Finset Matrix
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem contDiff_entry (a b : Fin n) {m : ℕ∞ω} :
    ContDiff ℂ m (fun z : Matrix (Fin n) (Fin n) ℂ => z a b) := by
  exact (contDiff_apply ℂ ℂ b).comp (contDiff_apply ℂ (Fin n → ℂ) a)

theorem contDiff_lead (i : ℕ) {m : ℕ∞ω} : ContDiff ℂ m (lead (n := n) i) := by
  unfold lead
  by_cases h : i ≤ n
  · simp only [h, dif_pos]
    simp only [Matrix.det_apply, Units.smul_def]
    refine ContDiff.sum fun σ _ => ?_
    refine ContDiff.const_smul _ ?_
    refine contDiff_prod fun k _ => ?_
    simp only [Matrix.submatrix_apply]
    exact contDiff_entry _ _
  · simp only [h, dif_neg, not_false_eq_true]
    exact contDiff_const

theorem contDiffAt_zpow_lead (i : ℕ) (k : ℤ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : lead i z ≠ 0)
    {m : ℕ∞ω} : ContDiffAt ℂ m (fun w => lead i w ^ k) z := by
  have hl : ContDiffAt ℂ m (lead (n := n) i) z := (contDiff_lead i).contDiffAt
  rcases k with k | k
  · simp only [Int.ofNat_eq_coe, zpow_natCast]
    exact hl.pow k
  · simp only [zpow_negSucc]
    exact (hl.pow (k + 1)).inv (pow_ne_zero _ hz)

theorem contDiffAt_phiM (μ : Fin n → ℤ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n)
    {m : ℕ∞ω} : ContDiffAt ℂ m (PhiM μ) z := by
  unfold PhiM
  exact contDiffAt_prod fun i _ => contDiffAt_zpow_lead _ _ (hz i)

theorem differentiableAt_phiM (μ : Fin n → ℤ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    DifferentiableAt ℂ (PhiM μ) z := by
  exact (contDiffAt_phiM μ hz (m := 1)).differentiableAt (by norm_num)

theorem hasDerivAt_line {F : Matrix (Fin n) (Fin n) ℂ → ℂ} {z : Matrix (Fin n) (Fin n) ℂ}
    (hF : DifferentiableAt ℂ F z) (v : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℂ => F (z + t • v)) (fderiv ℂ F z v) 0 := by
  have hl : HasDerivAt (fun t : ℂ => z + t • v) v 0 := by
    have h := ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add z
    rw [one_smul] at h
    exact h
  have hF' : HasFDerivAt F (fderiv ℂ F z) (z + (0 : ℂ) • v) := by
    simpa using hF.hasFDerivAt
  exact hF'.comp_hasDerivAt (0 : ℂ) hl

def mulLeftCLM (Y : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℂ Y)

theorem lhol_lhol_eq {F : Matrix (Fin n) (Fin n) ℂ → ℂ} {z : Matrix (Fin n) (Fin n) ℂ}
    (hF : ContDiffAt ℂ 2 F z) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    Lhol X (Lhol Y F) z = fderiv ℂ F z (Y * (X * z)) + fderiv ℂ (fderiv ℂ F) z (X * z) (Y * z) := by
  unfold Lhol
  have hc : DifferentiableAt ℂ (fderiv ℂ F) z :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hu : HasFDerivAt (fun y : Matrix (Fin n) (Fin n) ℂ => Y * y) (mulLeftCLM Y) z :=
    (mulLeftCLM Y).hasFDerivAt
  have h := hc.hasFDerivAt.clm_apply hu
  erw [h.fderiv]
  rfl

theorem lhol_comm {F : Matrix (Fin n) (Fin n) ℂ → ℂ} {z : Matrix (Fin n) (Fin n) ℂ}
    (hF : ContDiffAt ℂ 2 F z) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    Lhol X (Lhol Y F) z = Lhol Y (Lhol X F) z + fderiv ℂ F z ((Y * X - X * Y) * z) := by
  rw [lhol_lhol_eq hF, lhol_lhol_eq hF]
  have hs := hF.isSymmSndFDerivAt (by simp)
  have h1 : fderiv ℂ (fderiv ℂ F) z (Y * z) (X * z) = fderiv ℂ (fderiv ℂ F) z (X * z) (Y * z) :=
    hs _ _
  have h2 : fderiv ℂ F z ((Y * X - X * Y) * z) =
      fderiv ℂ F z (Y * (X * z)) - fderiv ℂ F z (X * (Y * z)) := by
    rw [Matrix.sub_mul, map_sub, Matrix.mul_assoc, Matrix.mul_assoc]
  linear_combination -h1 - h2

end ReciprocityTheory.ChartRestriction.DS.S7
