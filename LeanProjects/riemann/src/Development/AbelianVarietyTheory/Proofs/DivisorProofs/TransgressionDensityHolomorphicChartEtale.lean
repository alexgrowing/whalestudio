import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernDensityFrameIndepChartJacobianFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTopCoeffComplexGermCongrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTopCoeffHolomorphicFrameChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTopCoeffCompHolomorphicJacobianSqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChangeOfFrameHolomorphicInvertibleHolomorphicChaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOnHolomorphicChartTransEtaleChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtHolomorphicComplexChartOfSmoothAtStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem corrTop_holoChart_trans : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → IsMetricOn E ⊤ H₀ → ∀ {ρ : CxPts X.str σ → ℝ}, (∀ y, CInfAt ρ y) → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)}, IsHoloChart e → ∀ (c : AlgChart X.str σ X.dim) {y : CxPts X.str σ}, y ∈ ptsIn X.str σ O → y ∈ e.source → y ∈ c.e.source → ∀ {A : Mat (fun _ : Unit => m) X.Fn}, A ∈ E.S (under y) → corrTop (fun v => ρ (e.symm v)) (fun v => H₀ A (e.symm v) ()) (fun v => H A (e.symm v) ()) (e y) = ‖transDet e c.e y‖ ^ 2 * corrDens E H₀ H ρ c y := by
  intro F _ σ X m E O H H₀ hM hM₀ ρ hρ e he c y hy hey hcy A hA
  set A' := (E.nonempty (under y)).choose with hA'def
  have hA' : A' ∈ E.S (under y) := (E.nonempty (under y)).choose_spec
  have hy₀ : y ∈ ptsIn X.str σ (⊤ : X.X.Opens) := GlobalTheory.CxPts.mem_ptsIn_top

  set φ : V X.dim → V X.dim := c.e ∘ e.symm with hφ
  have ho := isOpen_over e c.e.open_source
  have hm := mem_over e hey hcy
  have e₂ : φ (e y) = c.e y := congrArg c.e (e.left_inv hey)
  have hφa : AnalyticAt ℂ φ (e y) :=
    GlobalTheory.SCV.analyticAt_of_differentiableOn (GlobalTheory.T.differentiableOn_holomorphicChart_trans_etaleChart he c) (ho.mem_nhds hm)

  set ρc : V X.dim → ℝ := fun v => ρ (c.e.symm v)
  set G₀ : Mat (fun _ : Unit => m) X.Fn → V X.dim → Matrix (Fin m) (Fin m) ℂ := fun B v => H₀ B (c.e.symm v) ()
  set G₁ : Mat (fun _ : Unit => m) X.Fn → V X.dim → Matrix (Fin m) (Fin m) ℂ := fun B v => H B (c.e.symm v) ()
  have hback : ∀ w ∈ e.target ∩ e.symm ⁻¹' c.e.source, c.e.symm (φ w) = e.symm w := fun w hw =>
    c.e.left_inv hw.2

  have step1 : corrC (fun v => ρ (e.symm v)) (fun v => H₀ A (e.symm v) ()) (fun v => H A (e.symm v) ()) (e y) =
      corrC (fun v => ρc (φ v)) (fun v => G₀ A (φ v)) (fun v => G₁ A (φ v)) (e y) := by
    apply GlobalTheory.T.transgressionTopCoeffComplex_germ_congr
    · filter_upwards [ho.mem_nhds hm] with w hw
      simp only [ρc, hback w hw]
    · filter_upwards [ho.mem_nhds hm] with w hw
      simp only [G₀, hback w hw]
    · filter_upwards [ho.mem_nhds hm] with w hw
      simp only [G₁, hback w hw]

  have hρc : ContDiffAt ℝ ∞ ρc (c.e y) := GlobalTheory.T.contDiffAt_holomorphicComplexChart_of_smoothAt c.holo hcy (hρ y)
  have hG₀ := hM₀.mContDiffAt_chart hy₀ c hcy hA ()
  have hG₀u := hM₀.isUnit_det_chart hy₀ c hcy hA ()
  have hG₁ := hM.mContDiffAt_chart hy c hcy hA ()
  have hG₁u := hM.isUnit_det_chart hy c hcy hA ()
  have step2 : corrC (fun v => ρc (φ v)) (fun v => G₀ A (φ v)) (fun v => G₁ A (φ v)) (e y) =
      ((‖(fderiv ℂ φ (e y)).det‖ ^ 2 : ℝ) : ℂ) * corrC ρc (G₀ A) (G₁ A) (φ (e y)) := by
    apply GlobalTheory.T.transgressionTopCoeff_comp_holomorphic_jacobian_sq (hφa.contDiffAt)
    · rw [e₂]; exact hρc.differentiableAt (by simp)
    · rw [e₂]; exact hG₀
    · rw [e₂]; exact hG₀u
    · rw [e₂]; exact hG₁
    · rw [e₂]; exact hG₁u

  obtain ⟨hQ, hQu, hQh⟩ := GlobalTheory.T.changeOfFrame_holomorphic_invertible_holomorphicChart E (e := c.e) c.holo hcy hA hA'
  have step3 : corrC ρc (G₀ A) (G₁ A) (c.e y) = corrC ρc (G₀ A') (G₁ A') (c.e y) := by
    rw [← GlobalTheory.T.transgressionTopCoeff_holomorphic_frame_change ρc hG₀ hG₀u hG₁ hG₁u hQ hQu hQh]
    have hO : ∀ᶠ z in 𝓝 y, z ∈ ptsIn X.str σ O := (isOpen_ptsIn O).mem_nhds hy
    have hev := (c.e.tendsto_symm hcy).eventually
      (hO.and ((GlobalTheory.FrameLift.eventually_mem hA).and (GlobalTheory.FrameLift.eventually_mem hA')))
    apply GlobalTheory.T.transgressionTopCoeffComplex_germ_congr
    · exact Filter.EventuallyEq.rfl
    · filter_upwards [hev] with w hw
      simp only [G₀, Matrix.transpose_transpose]
      rw [hM₀.trans _ GlobalTheory.CxPts.mem_ptsIn_top A hw.2.1 A' hw.2.2 ()]
      congr 1
    · filter_upwards [hev] with w hw
      simp only [G₁, Matrix.transpose_transpose]
      rw [hM.trans _ hw.1 A hw.2.1 A' hw.2.2 ()]
      congr 1
  simp only [corrTop, corrDens]
  rw [← hA'def]
  rw [step1, step2, e₂, step3, Complex.re_ofReal_mul]
  have hT : transDet e c.e y = (fderiv ℂ φ (e y)).det := rfl
  rw [hT]
  ring

end GlobalTheory.GoodTop
