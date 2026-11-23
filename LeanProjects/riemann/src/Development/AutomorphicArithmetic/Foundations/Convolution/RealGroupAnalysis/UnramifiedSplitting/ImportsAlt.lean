import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.CorePt

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.H.core :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (v : P F) (ϖ : (Kv v)ˣ), IsU ϖ → Gd D.δ v → W.η.UnrAt v → W.η.val v = -1 →
      ∀ (Wt : GL (Fin 2) (A F) → ℂ) (α β : ℂˣ), EigAt v {α, β} Wt → (∀ b g, Wt (gl (nU b) * g) = ψ (-b) * Wt g) → ∀ φ : S4 F, Std v φ.1 →
      Integrable (iw fun g => Wt (gl g) * hat (W.Om g φ).1 ![0, 1, 1, 0]) M.ν →
      ((ab (idl v ϖ ^ 2) : ℝ) : ℂ) * (M.I0 fun g => Wt (dM (idl v ϖ ^ 2) * gl g) *
          hat (W.Om g φ).1 ![0, ((idl v ϖ ^ 2 : (A F)ˣ) : A F), (((idl v ϖ)⁻¹ : (A F)ˣ) : A F), 0]) =
        (q v)⁻¹ * ((α : ℂ) ^ 2 + (β : ℂ) ^ 2) * M.I0 fun g => Wt (gl g) * hat (W.Om g φ).1 ![0, 1, 1, 0] := by
  intro F E _ _ _ _ _ _ _ D W M v ϖ hϖ hg hu hv Wt α β hB hN φ hφ hi
  have := M.prob
  have mp : ∀ p : IdeleGroup F, MeasurePreserving (MeasurableEquiv.prodCongr (MeasurableEquiv.mulRight p) (MeasurableEquiv.refl (G1 F))) M.ν M.ν :=
    fun p => (measurePreserving_mul_right (ideleMeasure F) p).prod (MeasurePreserving.id M.κ)
  have hk : ∀ᵐ x ∂M.ν, x.2 ∈ KK F :=
    Measure.quasiMeasurePreserving_snd.ae (show ∀ᵐ k ∂M.κ, k ∈ KK F from M.supp)
  unfold Meas.I0
  have e1 := (mp (idl v ϖ)⁻¹).integral_comp' (iw fun g => Wt (gl g) * hat (W.Om g φ).1 ![0, 1, 1, 0])
  have i1 := ((mp (idl v ϖ)⁻¹).integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hi
  rw [← (mp (idl v ϖ)).integral_comp', ← integral_const_mul]
  refine (integral_congr_ae (hk.mono fun x hx => corePt F E D W v ϖ hϖ hg hu hv Wt α β hB hN φ hφ x.1 x.2 hx)).trans ?_
  refine (integral_add (hi.const_mul _) (i1.const_mul _)).trans ?_
  rw [integral_const_mul, integral_const_mul]
  erw [e1]
  ring
