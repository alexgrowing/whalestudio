import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

set_option synthInstance.maxSize 1000

private theorem wt_eq_comp {F : Type} [Field F] [NumberField F]
    (K : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F)) (N : ℕ) :
    wt (F := F) K N =
      (fun p : (Fin 4 → mixedEmbedding.mixedSpace F) × (Fin 4 → FiniteAdeleRing (𝓞 F) F) =>
        ((1 + ‖p.1‖) ^ N)⁻¹ * K.indicator (fun _ => (1 : ℝ)) p.2) ∘ splitEquivPi F (Fin 4) := by
  funext v
  by_cases h : finPartPi v ∈ K
  · simp [wt, splitEquivPi_apply, h]
  · simp [wt, splitEquivPi_apply, h]

theorem UpperTheory.ConvolutionTheory.R2.Ff.wtInt :
    ∀ (F : Type) [Field F] [NumberField F], WtInt F := by
  intro F _ _
  refine ⟨Module.finrank ℝ (Fin 4 → mixedEmbedding.mixedSpace F) + 1, fun K hK => ?_⟩
  rw [wt_eq_comp, measurePreserving_splitEquivPi.integrable_comp_emb
    (splitEquivPi F (Fin 4)).measurableEmbedding]
  refine Integrable.mul_prod (f := fun x : Fin 4 → mixedEmbedding.mixedSpace F => ((1 + ‖x‖) ^ (Module.finrank ℝ (Fin 4 → mixedEmbedding.mixedSpace F) + 1))⁻¹)
    (g := fun y => K.indicator (fun _ => (1 : ℝ)) y) ?_ ?_
  · have h := integrable_one_add_norm (E := Fin 4 → mixedEmbedding.mixedSpace F)
      (μ := mixedMeasurePi F) (r := ((Module.finrank ℝ (Fin 4 → mixedEmbedding.mixedSpace F) + 1 : ℕ) : ℝ))
      (by push_cast; linarith)
    refine h.congr (Eventually.of_forall fun x => ?_)
    have hx : (0 : ℝ) ≤ 1 + ‖x‖ := by positivity
    simp only [Real.rpow_neg hx, Real.rpow_natCast]
  · exact (integrable_indicator_iff hK.measurableSet).2
      (integrableOn_const hK.measure_lt_top.ne)
