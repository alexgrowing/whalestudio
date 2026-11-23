import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.MovG
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.CurveAt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.DerOm
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ParCont
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ImportsAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.mov :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), Mov W M π := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ φ' hφ' G c Y hP hG hD
  obtain ⟨hinf, hPc⟩ := UpperTheory.ConvolutionTheory.R2.Ff.parCont F
  obtain ⟨hc0, hcc, hPn⟩ := hPc c Y hP
  have hGc : Continuous G := continuous_adelicSL2_of_continuous_entries fun i j => by
    have e : (fun t => G t i j) = fun t => (TR.infGL F 2 (c t)).val i j := by
      funext t
      rw [← hG t]
      rfl
    rw [e]
    have hv : Continuous fun t => (TR.infGL F 2 (c t)).val :=
      Units.continuous_val.comp (hinf.comp hcc)
    exact hv.matrix_elem i j
  have hG0 : G 0 = 1 := gl_injective (by rw [hG, hc0, map_one, gl_one])
  have hL : LRat f.1 := (π.cusp f hf).1.left
  have hinv : ∀ t, (gl (G t))⁻¹ = TR.infGL F 2 (c (-t)) := fun t => by
    have h1 : c (-t) = (c t)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← hP.1, neg_add_cancel, hc0])
    rw [hG, h1, map_inv]
  funext h
  have d1 := UpperTheory.ConvolutionTheory.R2.Ff.derOm F E D W M π f hf φ hφ φ' hφ' G hGc hG0 hD h
  have d2 := UpperTheory.ConvolutionTheory.R2.Ff.derF F E D W M π f hf φ hφ (fun t => c (-t)) (-Y) hPn h
  have e : (fun t => lift W M (fun x => f.1 (x * TR.infGL F 2 (c (-t)))) φ h) =
      fun t => lift W M f.1 (W.Om (G t) φ) h := by
    funext t
    rw [UpperTheory.ConvolutionTheory.R2.Ff.movG F E D W M f.1 hL φ (G t) h, hinv]
  rw [e] at d2
  have hu := d1.unique d2
  have hl : (TR.lie F 2 (-Y) f).1 = (-1 : ℂ) • (TR.lie F 2 Y f).1 := by
    rw [map_neg]
    funext x
    simp
  have h4 := (UpperTheory.ConvolutionTheory.R2.Ff.lin F E D W M π).2.2.2 (TR.lie F 2 Y f).1 (-1) φ
  rw [hu, hl, h4]
  simp
