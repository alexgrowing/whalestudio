import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.LeviFinsetSum

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf

open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates ReciprocityTheory.AnForm Filter Topology

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
  {x0 b : Frame X.Ψ r} {z u : V (nd X)}

def Ck (X : Data E r) (b : Frame X.Ψ r) (z u : V (nd X)) (τ : X.Ψ) (k : Fin (r + 1)) : ℝ :=
  ∑ a : Fin k, (Dsg X (Fin.castLE (Nat.le_of_lt_succ k.isLt) a))⁻¹ *
    Sa (Nat.le_of_lt_succ k.isLt) (Dsg X) (Yd X b z u τ) a

theorem fk_zero (τ : X.Ψ) (k : Fin (r + 1)) : fk X b z u τ k 0 ≠ 0 := by
  unfold fk
  rw [fY_zero]
  refine Finset.prod_ne_zero_iff.mpr fun a _ => ?_
  simp only [Dsg, sgn]
  split_ifs <;> norm_num

theorem cd_logfk (τ : X.Ψ) (k : Fin (r + 1)) :
    ContDiffAt ℝ 2 (fun v => Real.log |fk X b z u τ k v|) 0 := by
  have h0 : fk X b z u τ k 0 ≠ 0 := fk_zero τ k
  have hc : ContDiff ℝ 2 (fk X b z u τ k) := by
    unfold fk fY Gz
    simp only [Matrix.det_apply', Matrix.submatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]
    simp only [← starRingEnd_apply, ← Complex.conjCLE_apply, ← Complex.reCLM_apply]
    fun_prop
  have hl : ContDiffAt ℝ 2 Real.log (fk X b z u τ k 0) := Real.contDiffAt_log.mpr h0
  simp only [Real.log_abs]
  exact hl.comp 0 hc.contDiffAt

theorem levi_logfk (τ : X.Ψ) (k : Fin (r + 1)) :
    levi (fun v => Real.log |fk X b z u τ k v|) 0 (fun _ => 1) = Ck X b z u τ k :=
  core_levi (Nat.le_of_lt_succ k.isLt) (Dsg X) (Yd X b z u τ) (Dsg_ne X)

theorem line_levi (hb : b ∈ Bor X.Ψ r) (hgram : ∀ τ, gram τ.1 X.Gm (mat (rmul (cpt X x0 z) b) τ) =
      diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) (la : Wt X.Ψ r) :
    levi (fun v : Fin 1 → ℂ => -2 * Real.log (X.nfac la (cpt X x0 (z + lineL u v)))) 0 (fun _ => 1) =
      ∑ τ, ∑ i : Fin r, (la τ i : ℝ) * (Ck X b z u τ i.succ - Ck X b z u τ i.castSucc) := by
  have hcont : ∀ τ k, ContinuousAt (fk X b z u τ k) 0 := fun τ k =>
    (contDiff_fY _ _ _).continuous.continuousAt
  have hev : ∀ᶠ v in 𝓝 (0 : Fin 1 → ℂ), ∀ τ k, fk X b z u τ k v ≠ 0 := by
    rw [Filter.eventually_all]
    intro τ
    rw [Filter.eventually_all]
    intro k
    exact (hcont τ k).eventually_ne (fk_zero τ k)
  have hBne : ∀ τ (k : Fin (r + 1)), ‖((mat b τ)⁻¹.submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt))
      (Fin.castLE (Nat.le_of_lt_succ k.isLt))).det‖ ^ 2 ≠ 0 := fun τ k =>
    pow_ne_zero 2 (norm_ne_zero_iff.2 (det_lead_ne _ (upper_inv _ (hb τ).1 (fun a c h => (hb τ).2 a c h))
      (by rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']; exact inv_ne_zero (hb τ).1) _))
  have hterm : ∀ τ (i : Fin r), (fun v => (la τ i : ℝ) * ((cB X b τ i.succ + Real.log |fk X b z u τ i.succ v|) -
      (cB X b τ i.castSucc + Real.log |fk X b z u τ i.castSucc v|))) =
      fun v => ((la τ i : ℝ) * (cB X b τ i.succ - cB X b τ i.castSucc) +
        (la τ i : ℝ) * Real.log |fk X b z u τ i.succ v|) + (-(la τ i : ℝ)) * Real.log |fk X b z u τ i.castSucc v| := by
    intro τ i; funext v; ring
  have hcdt : ∀ τ (i : Fin r), ContDiffAt ℝ 2 (fun v => (la τ i : ℝ) * ((cB X b τ i.succ +
      Real.log |fk X b z u τ i.succ v|) - (cB X b τ i.castSucc + Real.log |fk X b z u τ i.castSucc v|))) 0 := by
    intro τ i
    rw [hterm]
    exact (contDiffAt_const.add (contDiffAt_const.mul (cd_logfk τ _))).add
      (contDiffAt_const.mul (cd_logfk τ _))
  have hEq : (fun v : Fin 1 → ℂ => -2 * Real.log (X.nfac la (cpt X x0 (z + lineL u v)))) =ᶠ[𝓝 0]
      fun v => ∑ τ, ∑ i : Fin r, (la τ i : ℝ) * ((cB X b τ i.succ + Real.log |fk X b z u τ i.succ v|) -
        (cB X b τ i.castSucc + Real.log |fk X b z u τ i.castSucc v|)) := by
    filter_upwards [hev] with v hv
    have hd : ∀ τ k, dmin X.Gm (cpt X x0 (z + lineL u v)) τ k ≠ 0 := fun τ k => by
      rw [lineL_apply]
      intro h0
      have h1 := dmin_line_norm (u := u) hb hgram v τ k
      rw [h0, norm_zero] at h1
      exact mul_ne_zero (hBne τ k) (abs_ne_zero.2 (hv τ k)) h1.symm
    rw [neg2log_nfac X la _ hd]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => ?_
    rw [lineL_apply, dmin_line_norm (u := u) hb hgram v τ _, dmin_line_norm (u := u) hb hgram v τ _,
      Real.log_mul (hBne _ _) (abs_ne_zero.2 (hv _ _)), Real.log_mul (hBne _ _) (abs_ne_zero.2 (hv _ _))]
    rfl
  rw [levi_congr hEq, levi_finset_sum _ _ _ _ (fun τ _ => ContDiffAt.sum fun i _ => hcdt τ i)]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [levi_finset_sum _ _ _ _ (fun i _ => hcdt τ i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hterm, levi_add_smul _ (contDiffAt_const.add (contDiffAt_const.mul (cd_logfk τ _))) (cd_logfk τ _),
    levi_affine _ _ _ _ _ (cd_logfk τ _), levi_logfk, levi_logfk]
  ring

end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
