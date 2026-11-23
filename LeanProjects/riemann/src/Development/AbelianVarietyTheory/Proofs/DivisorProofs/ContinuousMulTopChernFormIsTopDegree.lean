import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernDensityFrameIndepChartJacobianFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AemeasurableChartOfLocallyContinuousDensityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPolarisedTopChernCoeffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTopDensityEqPolarisedTopChernStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem isTopForm_mul_topDens : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → ∀ {ρ : CxPts X.str σ → ℝ}, Continuous ρ → IsTopForm (fun c : AlgChart X.str σ X.dim => c.e) (fun c y => ρ y * topDens E H c y) (ptsIn X.str σ O) := by
  intro F _ σ X m E O H hM ρ hρ
  refine ⟨?_, ?_⟩
  · intro c c' y hy hc hc'
    have hA := (E.nonempty (under y)).choose_spec
    simp only [topDens]
    rw [chernTop_frame_chart_trans E O H hM _ hy c c' hc hc' hA hA]
    ring
  · intro c
    refine GlobalTheory.T.aemeasurable_chart_of_locally_continuous_density c.e (d := fun z => ρ z * topDens E H c z) (isOpen_ptsIn O) ?_
    intro y hy hc
    have hA := (E.nonempty (under y)).choose_spec
    refine ⟨fun v => ρ (c.e.symm v) * chernTop (MvPolynomial.X ((), X.dim))
      (fun w => H (E.nonempty (under y)).choose (c.e.symm w)) v, ?_, ?_⟩
    · have h1 : ContinuousAt (fun v => ρ (c.e.symm v)) (c.e y) :=
        hρ.continuousAt.comp (c.e.continuousAt_symm (c.e.map_source hc))
      have hsm := hM.mContDiffAt_chart hy c hc hA ()
      have hu := hM.isUnit_det_chart hy c hc hA ()
      have h2 : ContinuousAt (fun v => chernTop (MvPolynomial.X ((), X.dim))
          (fun w => H (E.nonempty (under y)).choose (c.e.symm w)) v) (c.e y) := by
        simp only [GlobalTheory.T.chernTopDensity_eq_polarisedTopChern]
        refine continuousAt_const.mul (Complex.continuous_re.continuousAt.comp ?_)
        refine GlobalTheory.T.continuousAt_polarisedTopChernCoeff (fun i a b p q => ?_)
        exact ((MContDiffAt.curv (j := 0) hsm hu (by norm_num) (coordVec a) (coordVec b)) p q).continuousAt
      exact h1.mul h2
    · filter_upwards [(isOpen_ptsIn O).mem_nhds hy, c.e.open_source.mem_nhds hc,
        GlobalTheory.FrameLift.eventually_mem hA] with z hz hzc hzA
      simp only [topDens, c.e.left_inv hzc]
      rw [hM.chernTop_frame _ hz c hzc (E.nonempty (under z)).choose_spec hzA]

end GlobalTheory.GoodTop
