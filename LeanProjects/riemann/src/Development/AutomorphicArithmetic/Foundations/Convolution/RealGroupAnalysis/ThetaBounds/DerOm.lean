import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ThDerOm
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ThBoundH
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Vol
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ThMeas
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.UnitsCpt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.derOm :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), DerOm W M π := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ φ' hφ' G hG hG0 hD h
  have hc : Continuous fun g : G1 F => f.1 (gl g * dM (nu F h)) :=
    (decay F π f hf).1.comp (Matrix.SpecialLinearGroup.continuous_toGL.mul continuous_const)
  haveI : IsFiniteMeasure (M.μ.restrict M.D) := ⟨by simpa using vol F M⟩
  have hm : ∀ ψ₀ : S4 F, AEStronglyMeasurable
      (fun g => f.1 (gl g * dM (nu F h)) * Th (W.Om g ψ₀).1) (M.μ.restrict M.D) := fun ψ₀ =>
    (hc.measurable.mul (thMeas F E D W ψ₀).1).aestronglyMeasurable
  have hP : Continuous fun s : ℝ => (gl (cD (nu F h) (G s)))⁻¹ * dM (nu F h) :=
    (continuous_gl.comp (continuous_cD.comp (continuous_const.prodMk hG))).inv.mul continuous_const
  have key : ∀ φ₀ ∈ Fock D.δ, ∃ B : ℝ, ∀ s ∈ Metric.closedBall (0 : ℝ) 1, ∀ g,
      ‖f.1 (gl g * dM (nu F h)) * Th (W.Om g (W.L h (W.Om (G s) φ₀))).1‖ ≤ B := by
    intro φ₀ hφ₀
    obtain ⟨B, hB⟩ := thBoundH F E D W π f hf φ₀ hφ₀ h _
      ((isCompact_closedBall (0 : ℝ) 1).image hP) {1} isCompact_singleton
      (by rintro _ rfl; simp [Ff.One, nu])
    refine ⟨B, fun s hs g => ?_⟩
    have e1 : W.L h (W.Om (G s) φ₀) = W.Om (cD (nu F h) (G s)) (W.L h φ₀) :=
      LinearMap.congr_fun (W.comm h (G s)) φ₀
    have e2 : W.Om g (W.Om (cD (nu F h) (G s)) (W.L h φ₀)) = W.Om (g * cD (nu F h) (G s)) (W.L h φ₀) := by
      rw [map_mul]; rfl
    have e3 : gl g * dM (nu F h) =
        gl (g * cD (nu F h) (G s)) * ((gl (cD (nu F h) (G s)))⁻¹ * dM (nu F h)) := by
      rw [gl_mul, mul_assoc, mul_inv_cancel_left]
    have h1 := hB (g * cD (nu F h) (G s)) _ ⟨s, hs, rfl⟩ 1 rfl
    rw [← e3] at h1
    rw [e1, e2]
    simpa using h1
  obtain ⟨B, hB⟩ := key φ' hφ'
  obtain ⟨B₀, hB₀⟩ := key φ hφ
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := M.μ.restrict M.D)
    (F := fun s g => f.1 (gl g * dM (nu F h)) * Th (W.Om g (W.L h (W.Om (G s) φ))).1)
    (F' := fun s g => f.1 (gl g * dM (nu F h)) * Th (W.Om g (W.L h (W.Om (G s) φ'))).1)
    (x₀ := (0 : ℝ)) (s := Metric.closedBall 0 1) (bound := fun _ => B)
    (Metric.closedBall_mem_nhds 0 one_pos)
    (Eventually.of_forall fun s => hm _)
    (Integrable.of_bound (hm _) B₀ (ae_of_all _ fun g => hB₀ 0 (by simp) g))
    (hm _)
    (ae_of_all _ fun g s hs => hB s hs g)
    (integrable_const B)
    (ae_of_all _ fun g s _ => (thDerOm F E D W φ φ' hφ' G hG hD g h s).const_mul _)
  have e : (∫ g in M.D, f.1 (gl g * dM (nu F h)) * Th (W.Om g (W.L h (W.Om (G 0) φ'))).1 ∂M.μ) =
      lift W M f.1 φ' h := by
    simp [lift, hG0]
  have := hmain.2
  rw [e] at this
  exact this
