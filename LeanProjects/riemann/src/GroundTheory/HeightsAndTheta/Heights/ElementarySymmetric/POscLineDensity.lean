import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StatementsOscLineDensity
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StatementsLaplacianHoloComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFS
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open InnerProductSpace Laplacian ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

namespace OscLineDensity

theorem maDensity_comp_eval (u : ℂ → ℝ) (y : Fin 1 → ℂ) :
    maDensity (fun _ y' => u (y' 0)) y = Δ u (y 0) / (2 * Real.pi) := by
  set E : (Fin 1 → ℂ) ≃L[ℝ] ℂ := ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℂ with hE
  have hf : (fun y' : Fin 1 → ℂ => u (y' 0)) = u ∘ E := rfl
  have key : ∀ v : Fin 1 → ℂ, fderiv ℝ (fderiv ℝ (fun y' : Fin 1 → ℂ => u (y' 0))) y v v =
      iteratedFDeriv ℝ 2 u (y 0) ![v 0, v 0] := by
    intro v
    have h2 := iteratedFDeriv_two_apply (𝕜 := ℝ) (u ∘ E) y ![v, v]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h2
    have h3 := E.iteratedFDerivWithin_comp_right u uniqueDiffOn_univ (Set.mem_univ (E y)) 2
    simp only [Set.preimage_univ, iteratedFDerivWithin_univ] at h3
    rw [hf, ← h2, h3]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [maDensity_one (fun y' => u (y' 0)) y, key, key, laplacian_eq_iteratedFDeriv_complexPlane]
  simp

theorem oscChartPot_eq (x : ℂ) : OscLine.oscChartPot x =
    Real.log (Real.sqrt (Real.exp (2 * Taut.oscW x)) /
      Real.sqrt (1 + Real.exp (2 * Taut.oscW x) * ‖x‖ ^ 2)) := by
  simp [OscLine.oscChartPot, OscLine.oscMuNorm, OscLine.oscRho]

theorem contDiffAt_oscChartPot {x : ℂ} (hx : x ≠ 0) : ContDiffAt ℝ 2 OscLine.oscChartPot x := by
  have hfun : OscLine.oscChartPot = fun x : ℂ => Real.log (Real.sqrt (Real.exp (2 * Taut.oscW x)) /
      Real.sqrt (1 + Real.exp (2 * Taut.oscW x) * ‖x‖ ^ 2)) := funext oscChartPot_eq
  rw [hfun]
  have hW : ContDiffAt ℝ 2 Taut.oscW x :=
    (Taut.contDiffAt_oscW hx).of_le (WithTop.coe_le_coe.2 le_top)
  have hρ : ContDiffAt ℝ 2 (fun x : ℂ => Real.exp (2 * Taut.oscW x)) x :=
    (contDiffAt_const.mul hW).exp
  have hn : ContDiffAt ℝ 2 (fun x : ℂ => ‖x‖ ^ 2) x := (contDiff_norm_sq ℝ).contDiffAt
  have hb : ContDiffAt ℝ 2 (fun x : ℂ => 1 + Real.exp (2 * Taut.oscW x) * ‖x‖ ^ 2) x :=
    contDiffAt_const.add (hρ.mul hn)
  have hbpos : 0 < 1 + Real.exp (2 * Taut.oscW x) * ‖x‖ ^ 2 := by positivity
  have hs1 := hρ.sqrt (Real.exp_pos _).ne'
  have hs2 := hb.sqrt hbpos.ne'
  refine (hs1.div hs2 (Real.sqrt_pos.2 hbpos).ne').log ?_
  exact (div_pos (Real.sqrt_pos.2 (Real.exp_pos _)) (Real.sqrt_pos.2 hbpos)).ne'

theorem log_oscMuNorm_line (A B : Fin 2 → ℂ) {t : ℂ} (h0 : A 0 + B 0 * t ≠ 0) :
    Real.log (OscLine.oscMuNorm (fun p => A p.2 + B p.2 * t)) =
      OscLine.oscChartPot ((A 1 + B 1 * t) / (A 0 + B 0 * t)) - Real.log ‖A 0 + B 0 * t‖ := by
  have hz : (fun p : (Σ _ : Unit, Fin 2) => A p.2 + B p.2 * t) =
      torusSmul (fun _ : Unit => A 0 + B 0 * t)
        (fun p : (Σ _ : Unit, Fin 2) => ![1, (A 1 + B 1 * t) / (A 0 + B 0 * t)] p.2) := by
    funext p
    obtain ⟨k, i⟩ := p
    simp only [torusSmul]
    fin_cases i
    · simp
    · simp [mul_div_cancel₀ _ h0]
  have hpos : 0 < OscLine.oscMuNorm
      (fun p : (Σ _ : Unit, Fin 2) => ![1, (A 1 + B 1 * t) / (A 0 + B 0 * t)] p.2) :=
    OscLine.oscMuNorm_pos ⟨0, by simp⟩
  rw [hz, OscLine.oscMuNorm_homog _ _ (fun _ => h0)]
  simp only [Finset.univ_unique, Finset.prod_singleton]
  rw [Real.log_mul (zpow_ne_zero _ (norm_ne_zero_iff.mpr h0)) hpos.ne', Real.log_zpow]
  unfold OscLine.oscChartPot
  push_cast
  ring

theorem proof (h : LaplacianHoloComp.Statement) : OscLineDensity.Statement := by
  intro A B y hd h0 h1
  set t0 := y 0 with ht0
  set z0 : ℂ → ℂ := fun t => A 0 + B 0 * t with hz0
  set xf : ℂ → ℂ := fun t => (A 1 + B 1 * t) / (A 0 + B 0 * t) with hxf
  set g : ℂ → ℝ := fun t => Real.log (OscLine.oscMuNorm (fun p => A p.2 + B p.2 * t)) with hg
  have hden : maDensity (fun _ y' => Real.log (OscLine.oscMuNorm (fun p => A p.2 + B p.2 * y' 0))) y =
      Δ g t0 / (2 * Real.pi) := maDensity_comp_eval g y
  rw [hden]

  have hz0an : AnalyticAt ℂ z0 t0 := analyticAt_const.add (analyticAt_const.mul analyticAt_id)
  have hz1an : AnalyticAt ℂ (fun t : ℂ => A 1 + B 1 * t) t0 :=
    analyticAt_const.add (analyticAt_const.mul analyticAt_id)
  have hxan : AnalyticAt ℂ xf t0 := hz1an.div hz0an h0
  have hx0 : xf t0 ≠ 0 := div_ne_zero h1 h0

  have hev : ∀ᶠ t in 𝓝 t0, z0 t ≠ 0 := hz0an.continuousAt.eventually_ne h0
  have hgeq : g =ᶠ[𝓝 t0] (OscLine.oscChartPot ∘ xf) - (fun t => Real.log ‖z0 t‖) := by
    filter_upwards [hev] with t ht
    exact log_oscMuNorm_line A B ht
  have hφ : ContDiffAt ℝ 2 OscLine.oscChartPot (xf t0) := contDiffAt_oscChartPot hx0
  have hcomp : ContDiffAt ℝ 2 (OscLine.oscChartPot ∘ xf) t0 :=
    hφ.comp t0 (hxan.contDiffAt.restrict_scalars ℝ)
  have hharm : HarmonicAt (fun t => Real.log ‖z0 t‖) t0 := hz0an.harmonicAt_log_norm h0
  have hΔg : Δ g t0 = ‖deriv xf t0‖ ^ 2 * Δ OscLine.oscChartPot (xf t0) := by
    rw [(laplacian_congr_nhds hgeq).eq_of_nhds, hcomp.laplacian_sub hharm.1, hharm.2.eq_of_nhds,
      Pi.zero_apply, sub_zero]
    exact h _ _ _ hφ hxan

  have hdx : HasDerivAt xf ((B 1 * 1 * (A 0 + B 0 * t0) - (A 1 + B 1 * t0) * (B 0 * 1)) /
      (A 0 + B 0 * t0) ^ 2) t0 :=
    (((hasDerivAt_id t0).const_mul (B 1)).const_add (A 1)).div
      (((hasDerivAt_id t0).const_mul (B 0)).const_add (A 0)) h0
  have hderiv : deriv xf t0 = (A 0 * B 1 - A 1 * B 0) / (A 0 + B 0 * t0) ^ 2 := by
    rw [hdx.deriv]
    congr 1
    ring
  rw [hΔg, hderiv, norm_div, norm_pow]
  have hn0 : 0 < ‖A 0 + B 0 * t0‖ := norm_pos_iff.mpr h0
  have := Real.pi_pos
  field_simp
  ring

end OscLineDensity

end GroundTheory.Heights₂.Heights.LowerBoundFree
