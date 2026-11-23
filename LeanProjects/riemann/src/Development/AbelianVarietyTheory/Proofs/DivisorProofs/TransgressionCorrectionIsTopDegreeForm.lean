import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernDensityFrameIndepChartJacobianFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtTransgressionTopCoeffComplexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionDensityHolomorphicChartEtaleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AemeasurableChartOfLocallyContinuousDensityStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem isTopForm_corrDens : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → IsMetricOn E ⊤ H₀ → ∀ {ρ : CxPts X.str σ → ℝ}, (∀ y, CInfAt ρ y) → IsTopForm (fun c : AlgChart X.str σ X.dim => c.e) (corrDens E H₀ H ρ) (ptsIn X.str σ O) := by
  intro F _ σ X m E O H H₀ hM hM₀ ρ hρ
  refine ⟨fun i j y hy hi hj => ?_, fun i => ?_⟩
  · exact GlobalTheory.T.transgressionDensity_holomorphicChart_etale E O H H₀ hM hM₀ hρ i.holo j hy hi hj (E.nonempty (under y)).choose_spec
  · refine GlobalTheory.T.aemeasurable_chart_of_locally_continuous_density i.e (isOpen_ptsIn O) fun y hy hc => ?_
    set A := (E.nonempty (under y)).choose with hAdef
    have hA : A ∈ E.S (under y) := (E.nonempty (under y)).choose_spec
    refine ⟨corrTop (fun v => ρ (i.e.symm v)) (fun v => H₀ A (i.e.symm v) ()) (fun v => H A (i.e.symm v) ()), ?_, ?_⟩
    · have hs : i.e.target ∩ i.e.symm ⁻¹' Set.univ ∈ 𝓝 (i.e y) := by
        simpa using i.e.open_target.mem_nhds (i.e.map_source hc)
      have hρ1 : ContDiffAt ℝ 1 (fun v => ρ (i.e.symm v)) (i.e y) :=
        ((contDiffOn_chart (S := Set.univ) (fun z _ => hρ z) i).contDiffAt hs).of_le (by norm_cast)
      have hc0 := GlobalTheory.T.continuousAt_transgressionTopCoeffComplex hρ1 (hM₀.mContDiffAt_chart mem_ptsIn_top i hc hA ())
        (hM₀.isUnit_det_chart mem_ptsIn_top i hc hA ()) (hM.mContDiffAt_chart hy i hc hA ())
        (hM.isUnit_det_chart hy i hc hA ())
      exact continuousAt_const.mul (Complex.continuous_re.continuousAt.comp hc0)
    · filter_upwards [(isOpen_ptsIn O).mem_nhds hy, i.e.open_source.mem_nhds hc, GlobalTheory.FrameLift.eventually_mem hA]
        with z hzO hzc hAz
      have h := GlobalTheory.T.transgressionDensity_holomorphicChart_etale E O H H₀ hM hM₀ hρ i.holo i hzO hzc hzc hAz
      rw [AlgChart.transDet_self i hzc, norm_one, one_pow, one_mul] at h
      exact h.symm

end GlobalTheory.GoodTop
