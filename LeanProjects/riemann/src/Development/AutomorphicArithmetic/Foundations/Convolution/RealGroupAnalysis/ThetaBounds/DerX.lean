import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.DerL
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.CurveAt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.CenExp
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ExValCont
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ImportsAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ParCont
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.LiftCentre
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.derX :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (O : Fo.Ops F) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), DerX O W M π := by
  intro F E _ _ _ _ _ _ _ D O W M π f hf φ hφ Y s hY h
  obtain ⟨ω, -, hω⟩ := UpperTheory.ConvolutionTheory.R2.cen F π
  obtain ⟨z, c, hc, hz⟩ := UpperTheory.ConvolutionTheory.R2.Ff.cenExp F E D s
  have hc0 : c 0 = 1 := ((UpperTheory.ConvolutionTheory.R2.Ff.parCont F).2 c _ hc).1
  let χ : ℝ → ℂ := fun t => ((ω (ideleNorm F E (z t)) : ℂˣ) : ℂ)
  have hfx : ∀ t x, f.1 (x * TR.infGL F 2 (c t)) = χ t * f.1 x := by
    intro t x
    rw [← (hz t).2, ← UpperTheory.ConvolutionTheory.R2.scalar_comm, hω f hf]
  have hfun : ∀ t, lift W M f.1 φ (h * infGL E 2 (ex (Y + zE s) t)) =
      χ t * lift W M f.1 φ (h * infGL E 2 (ex Y t)) := by
    intro t
    rw [(UpperTheory.ConvolutionTheory.R2.Ff.exPar E Y).2.2.2.2 s t, map_mul, (hz t).1, ← mul_assoc,
      ← UpperTheory.ConvolutionTheory.R2.scalar_comm, mul_assoc]
    exact (UpperTheory.ConvolutionTheory.R2.equiv F E D W M π f hf φ).2 ω (hω f hf) (z t) _
  have hlin := (UpperTheory.ConvolutionTheory.R2.Ff.lin F E D W M π).2.2.2
  have hG := UpperTheory.ConvolutionTheory.R2.Ff.derL F E D O W M π f hf φ hφ Y hY h
  have hD : HasDerivAt (fun t => χ t * lift W M f.1 φ h)
      (lift W M (TR.lie F 2 (zF (trI F s)) f).1 φ h) 0 := by
    have h0 := UpperTheory.ConvolutionTheory.R2.Ff.derF F E D W M π f hf φ hφ c _ hc h
    refine h0.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    have e : (fun x => f.1 (x * TR.infGL F 2 (c t))) = χ t • f.1 := by
      funext x
      exact hfx t x
    simp only [e]
    rw [hlin]
    rfl
  by_cases h0 : f.1 = 0
  · have hz0 : ∀ (φ₁ : S4 F) h₁, lift W M f.1 φ₁ h₁ = 0 := by
      intro φ₁ h₁
      have := congrFun (hlin f.1 0 φ₁) h₁
      rw [zero_smul] at this
      rw [h0] at this ⊢
      simpa using this
    have hl : lift W M (TR.lie F 2 (zF (trI F s)) f).1 φ h = 0 := by
      have hc' : HasDerivAt (fun t => χ t * lift W M f.1 φ h) 0 0 := by
        simp only [hz0, mul_zero]
        exact hasDerivAt_const _ _
      exact hD.unique hc'
    rw [hl, hz0, add_zero]
    simp only [hz0]
    exact hasDerivAt_const _ _
  · obtain ⟨g, hg⟩ : ∃ g, f.1 g ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact h0 (funext hn)
    have hcv := TR.hasDerivAt_curve f g c _ hc0 hc.2
    have hχ : HasDerivAt χ (TR.lieD (zF (trI F s)) f.1 g / f.1 g) 0 := by
      refine (hcv.div_const (f.1 g)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      show χ t = f.1 (g * TR.infGL F 2 (c t)) / f.1 g
      rw [hfx, mul_div_assoc, div_self hg, mul_one]
    have hχ0 : χ 0 = 1 := by
      have := hfx 0 g
      rw [hc0, map_one, mul_one] at this
      exact (mul_right_cancel₀ hg (by rw [one_mul]; exact this.symm))
    have hex0 : ex Y 0 = 1 := by
      have := (UpperTheory.ConvolutionTheory.R2.Ff.exPar E Y).1 0 0
      rw [add_zero] at this
      exact left_eq_mul.1 this
    have hl := hD.unique (hχ.mul_const (lift W M f.1 φ h))
    have hp := hχ.mul hG
    rw [hex0, map_one, mul_one, hχ0, one_mul, ← hl, add_comm] at hp
    exact hp.congr_of_eventuallyEq (Filter.Eventually.of_forall hfun)
