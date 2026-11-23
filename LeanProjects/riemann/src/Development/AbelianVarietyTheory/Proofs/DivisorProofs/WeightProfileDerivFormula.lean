import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogisticFactorMem
open GlobalTheory Matrix Filter Topology Set GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation GlobalTheory.InterpCurv
open scoped ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.InterpCurv

theorem hasDerivAt_logisticFactor (κ L v : ℝ) :
    HasDerivAt (logisticFactor κ L)
      (-κ * logisticFactor κ L v * (1 - logisticFactor κ L v)) v := by
  have he : HasDerivAt (fun w => Real.exp (κ * (w - L))) (Real.exp (κ * (v - L)) * κ) v := by
    have h1 : HasDerivAt (fun w => κ * (w - L)) κ v := by
      simpa using ((hasDerivAt_id v).sub_const L).const_mul κ
    exact h1.exp
  have hpos : 0 < 1 + Real.exp (κ * (v - L)) := by positivity
  have h2 := (he.const_add 1).inv hpos.ne'
  have h3 : HasDerivAt (logisticFactor κ L)
      (-(Real.exp (κ * (v - L)) * κ) / (1 + Real.exp (κ * (v - L))) ^ 2) v := by
    have : logisticFactor κ L = fun w => (1 + Real.exp (κ * (w - L)))⁻¹ := by
      funext w; simp [logisticFactor]
    rw [this]; exact h2
  convert h3 using 1
  simp only [logisticFactor]
  field_simp
  ring

theorem hasDerivAt_logisticFactor_deriv (κ L v : ℝ) :
    HasDerivAt (fun w => -κ * logisticFactor κ L w * (1 - logisticFactor κ L w))
      (κ ^ 2 * logisticFactor κ L v * (1 - logisticFactor κ L v) *
        (1 - 2 * logisticFactor κ L v)) v := by
  have h := hasDerivAt_logisticFactor κ L v
  have h' : HasDerivAt (fun w => -κ * logisticFactor κ L w * (1 - logisticFactor κ L w))
      (-κ * (-κ * logisticFactor κ L v * (1 - logisticFactor κ L v)) * (1 - logisticFactor κ L v) +
        -κ * logisticFactor κ L v * (0 - -κ * logisticFactor κ L v * (1 - logisticFactor κ L v))) v :=
    (h.const_mul (-κ)).mul ((hasDerivAt_const v (1:ℝ)).sub h)
  exact h'.congr_deriv (by ring)

theorem weightProfile_second_deriv : ∀ (χ : ℝ → ℝ), IsCutoff χ → ∀ (κ L t u : ℝ), 0 < L → 0 < u → ContDiffAt ℝ 2 (weightProfile χ κ L t) u ∧ deriv (weightProfile χ κ L t) u = t * (deriv χ (u / L) / L * logisticFactor κ L u + χ (u / L) * (-κ * logisticFactor κ L u * (1 - logisticFactor κ L u))) ∧ deriv (deriv (weightProfile χ κ L t)) u = t * (deriv (deriv χ) (u / L) / L ^ 2 * logisticFactor κ L u + 2 * (deriv χ (u / L) / L) * (-κ * logisticFactor κ L u * (1 - logisticFactor κ L u)) + χ (u / L) * (κ ^ 2 * logisticFactor κ L u * (1 - logisticFactor κ L u) * (1 - 2 * logisticFactor κ L u))) := by
  intro χ hχ κ L t u hL hu
  set s := logisticFactor κ L with hs
  set s1 : ℝ → ℝ := fun w => -κ * s w * (1 - s w) with hs1
  have hf : weightProfile χ κ L t = fun v => t * (χ (v / L) * s v) := by
    funext v; rw [weightProfile_eq]
  have hopen : ContDiffOn ℝ ∞ χ (Ioi 0) := hχ.smooth.mono Ioi_subset_Ici_self
  have hd1 : ContDiffOn ℝ ∞ (deriv χ) (Ioi 0) :=
    hopen.deriv_of_isOpen isOpen_Ioi (by simp)
  have hχd : ∀ y, 0 < y → HasDerivAt χ (deriv χ y) y := fun y hy =>
    ((hopen.contDiffAt (Ioi_mem_nhds hy)).differentiableAt (by simp)).hasDerivAt
  have hχdd : ∀ y, 0 < y → HasDerivAt (deriv χ) (deriv (deriv χ) y) y := fun y hy =>
    ((hd1.contDiffAt (Ioi_mem_nhds hy)).differentiableAt (by simp)).hasDerivAt
  have hdiv : ∀ v : ℝ, HasDerivAt (fun w : ℝ => w / L) (1 / L) v := fun v =>
    (hasDerivAt_id v).div_const L
  have hg : ∀ v, 0 < v → HasDerivAt (fun w => χ (w / L)) (deriv χ (v / L) / L) v := by
    intro v hv
    have : HasDerivAt (fun w => χ (w / L)) (deriv χ (v / L) * (1 / L)) v :=
      (hχd (v / L) (div_pos hv hL)).comp v (hdiv v)
    exact this.congr_deriv (by ring)
  have hg1 : ∀ v, 0 < v → HasDerivAt (fun w => deriv χ (w / L) / L)
      (deriv (deriv χ) (v / L) / L ^ 2) v := by
    intro v hv
    have hc := hχdd (v / L) (div_pos hv hL)
    have h0 : HasDerivAt (fun w => deriv χ (w / L)) (deriv (deriv χ) (v / L) * (1 / L)) v :=
      HasDerivAt.comp (h₂ := deriv χ) v hc (hdiv v)
    exact (h0.div_const L).congr_deriv (by field_simp)
  have hsd : ∀ v, HasDerivAt s (s1 v) v := fun v => hasDerivAt_logisticFactor κ L v
  have hs1d : ∀ v, HasDerivAt s1
      (κ ^ 2 * s v * (1 - s v) * (1 - 2 * s v)) v := fun v =>
    hasDerivAt_logisticFactor_deriv κ L v
  set F1 : ℝ → ℝ := fun v => t * (deriv χ (v / L) / L * s v + χ (v / L) * s1 v) with hF1
  have hfd : ∀ v, 0 < v → HasDerivAt (weightProfile χ κ L t) (F1 v) v := by
    intro v hv
    rw [hf]
    have : HasDerivAt (fun w => t * (χ (w / L) * s w))
        (t * (deriv χ (v / L) / L * s v + χ (v / L) * s1 v)) v :=
      ((hg v hv).mul (hsd v)).const_mul t
    exact this
  have hderiv_ev : deriv (weightProfile χ κ L t) =ᶠ[𝓝 u] F1 := by
    filter_upwards [Ioi_mem_nhds hu] with v hv
    exact (hfd v hv).deriv
  refine ⟨?_, (hfd u hu).deriv, ?_⟩
  · rw [hf]
    have hχc : ContDiffAt ℝ 2 χ (u / L) :=
      (hopen.contDiffAt (Ioi_mem_nhds (div_pos hu hL))).of_le (WithTop.coe_le_coe.mpr le_top)
    have hgc : ContDiffAt ℝ 2 (fun w => χ (w / L)) u :=
      hχc.comp u (contDiffAt_id.div_const L)
    have hsc : ContDiff ℝ 2 s := by
      rw [hs]
      unfold logisticFactor
      refine contDiff_const.div ?_ (fun x => by positivity)
      exact contDiff_const.add ((contDiff_const.mul (contDiff_id.sub contDiff_const)).exp)
    exact contDiffAt_const.mul (hgc.mul hsc.contDiffAt)
  · rw [hderiv_ev.deriv_eq]
    have : HasDerivAt F1 (t * ((deriv (deriv χ) (u / L) / L ^ 2 * s u + deriv χ (u / L) / L * s1 u) +
        (deriv χ (u / L) / L * s1 u + χ (u / L) * (κ ^ 2 * s u * (1 - s u) * (1 - 2 * s u))))) u :=
      (((hg1 u hu).mul (hsd u)).add ((hg u hu).mul (hs1d u))).const_mul t
    rw [this.deriv]
    simp only [hs1]
    ring

end GlobalTheory.InterpCurv
