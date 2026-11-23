import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.DLDer
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.IntegrableMulChar
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ThDer
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ContinuousAb
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.WtBound
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ExValCont
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ActCont
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.thDerL :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (O : Fo.Ops F) (W : Weil D), ThDerL O W := by
  intro F E _ _ _ _ _ _ _ D O W φ Y hY g h t
  obtain ⟨hOne, hDer⟩ := dLDer F E D O W Y hY
  obtain ⟨-, hcont, -⟩ := exPar E Y
  obtain ⟨-, -, -, -, hinf, -⟩ := actCont F E D

  have hnu : ∀ s, nu F (h * infGL E 2 (ex Y s)) = nu F h := by
    intro s
    have h1 : nu F (infGL E 2 (ex Y s)) = 1 := hOne s
    have h2 : nu F (h * infGL E 2 (ex Y s)) = nu F h * nu F (infGL E 2 (ex Y s)) := by
      simp only [nu, map_mul]
    rw [h2, h1, mul_one]

  have hD : Der (fun s => W.L (h * infGL E 2 (ex Y s)) φ)
      (fun s => W.L (h * infGL E 2 (ex Y s)) (O.dL D Y φ)) := by
    intro s v
    have key := (hDer φ s (D.act h⁻¹ v)).const_mul (((ab (nu F h))⁻¹ : ℝ) : ℂ)
    have e : ∀ (χ : S4 F) (r : ℝ), (W.L (h * infGL E 2 (ex Y r)) χ).1 v =
        (((ab (nu F h))⁻¹ : ℝ) : ℂ) * (W.L (infGL E 2 (ex Y r)) χ).1 (D.act h⁻¹ v) := by
      intro χ r
      rw [W.L.map_mul, Module.End.mul_apply, W.L_apply]
    simp only [e]
    exact key

  have hDom : ∀ (g : G1 F) (t : ℝ), Dom (Metric.ball t 1)
      fun s => (W.Om g (W.L (h * infGL E 2 (ex Y s)) (O.dL D Y φ))).1 := by
    intro g t
    have hc : cD (nu F h) (cD (nu F h)⁻¹ g) = g := by
      rw [← cD_mul_left, mul_inv_cancel, cD_one_left]
    have hsw : ∀ s, W.Om g (W.L (h * infGL E 2 (ex Y s)) (O.dL D Y φ)) =
        W.L (h * infGL E 2 (ex Y s)) (W.Om (cD (nu F h)⁻¹ g) (O.dL D Y φ)) := by
      intro s
      have hcomm := W.comm (h * infGL E 2 (ex Y s)) (cD (nu F h)⁻¹ g)
      rw [hnu s, hc] at hcomm
      exact (LinearMap.congr_fun hcomm (O.dL D Y φ)).symm
    have hC : IsCompact ((fun s => h * infGL E 2 (ex Y s)) '' Metric.closedBall t 1) :=
      (isCompact_closedBall t 1).image (continuous_const.mul (hinf.comp hcont))
    obtain ⟨K, hK, hB⟩ := lDom F E D W Unit Set.univ
      (fun _ => W.Om (cD (nu F h)⁻¹ g) (O.dL D Y φ)) (wtBound F _).2 _ hC
    refine ⟨K, hK, fun N => ?_⟩
    obtain ⟨B, hB⟩ := hB N
    refine ⟨B, fun s hs v => ?_⟩
    simp only [hsw s]
    exact hB (h * infGL E 2 (ex Y s), ())
      ⟨⟨s, Metric.ball_subset_closedBall hs, rfl⟩, Set.mem_univ _⟩ v
  exact thDer F _ _ (omDer F E D W _ _ hD hDom g) t (hDom g t)
