import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ThDerL
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ThBoundH
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Vol
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ThMeas
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.DLFock
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.DLDer
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ExValCont
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.One
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.UnitsCpt

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.derL :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (O : Fo.Ops F) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), DerL O W M π := by
  intro F E _ _ _ _ _ _ _ D O W M π f hf φ hφ Y hY h
  haveI : IsFiniteMeasure (M.μ.restrict M.D) := ⟨by simpa using vol F M⟩
  have hφ' := dLFock F E D O Y φ hφ
  have hOne := (dLDer F E D O W Y hY).1
  obtain ⟨hadd, hcont, -⟩ := exPar E Y
  have h0 : ex Y 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hnu : ∀ t, nu F (h * infGL E 2 (ex Y t)) = nu F h := fun t => by
    have e : nu F (infGL E 2 (ex Y t)) = 1 := hOne t
    rw [show nu F (h * infGL E 2 (ex Y t)) = nu F h * nu F (infGL E 2 (ex Y t)) by simp [nu], e, mul_one]
  have hc : Continuous fun g : G1 F => f.1 (gl g * dM (nu F h)) :=
    (decay F π f hf).1.comp (Matrix.SpecialLinearGroup.continuous_toGL.mul continuous_const)
  have hC' : IsCompact (ex Y '' Metric.closedBall (0 : ℝ) 1) := (isCompact_closedBall 0 1).image hcont
  have hC1 : ∀ y ∈ ex Y '' Metric.closedBall (0 : ℝ) 1, One F y := by
    rintro _ ⟨t, -, rfl⟩
    exact hOne t
  obtain ⟨B, hB⟩ := thBoundH F E D W π f hf _ hφ' h {dM (nu F h)} isCompact_singleton _ hC' hC1
  have key : (fun t => lift W M f.1 φ (h * infGL E 2 (ex Y t))) = fun t =>
      ∫ g in M.D, f.1 (gl g * dM (nu F h)) * Th (W.Om g (W.L (h * infGL E 2 (ex Y t)) φ)).1 ∂M.μ := by
    funext t
    simp only [lift, hnu t]
  have key' : lift W M f.1 (O.dL D Y φ) h =
      ∫ g in M.D, f.1 (gl g * dM (nu F h)) * Th (W.Om g (W.L (h * infGL E 2 (ex Y 0)) (O.dL D Y φ))).1 ∂M.μ := by
    simp only [lift, h0, map_one, mul_one]
  rw [key, key']
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (μ := M.μ.restrict M.D)
    (F := fun t g => f.1 (gl g * dM (nu F h)) * Th (W.Om g (W.L (h * infGL E 2 (ex Y t)) φ)).1)
    (F' := fun t g => f.1 (gl g * dM (nu F h)) * Th (W.Om g (W.L (h * infGL E 2 (ex Y t)) (O.dL D Y φ))).1)
    (x₀ := 0) (s := Metric.ball (0 : ℝ) 1) (bound := fun _ => B)
    (Metric.ball_mem_nhds _ one_pos) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Filter.Eventually.of_forall fun t =>
      (hc.measurable.mul (thMeas F E D W _).1).aestronglyMeasurable
  · have := (conv F E D W M π f hf φ hφ h).1
    rw [IntegrableOn] at this
    simpa only [h0, map_one, mul_one] using this
  · exact (hc.measurable.mul (thMeas F E D W _).1).aestronglyMeasurable
  · exact ae_of_all _ fun g t ht =>
      hB g _ (Set.mem_singleton _) (ex Y t) ⟨t, Metric.ball_subset_closedBall ht, rfl⟩
  · exact integrable_const _
  · exact ae_of_all _ fun g t _ => (thDerL F E D O W φ Y hY g h t).const_mul _
