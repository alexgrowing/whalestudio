import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OfinProd

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM UpperTheory.ConvolutionTheory.C

theorem UpperTheory.localHeckeOperator_mem_of_closed_invariant :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (w : Pl K) [MeasurableSpace (Gw n w)] (m : Measure (Gw n w))
        (φ : Gw n w → ℂ) (T : LL μ →L[ℂ] LL μ) (Z : Submodule ℂ (LL μ)), IsClosed (Z : Set (LL μ)) →
        (∀ (g : Gw n w), ∀ v ∈ Z, rhoL μ w g v ∈ Z) → IsOloc μ w m φ T → ∀ v ∈ Z, T v ∈ Z := by
  intro K _ _ n μ _ w _ m φ T Z hZ hst hT v hv
  haveI : CompleteSpace Z := hZ.completeSpace_coe
  rw [← Submodule.orthogonal_orthogonal Z, Submodule.mem_orthogonal]
  intro u hu
  rw [hT u v]
  have h0 : ∀ g : Gw n w, φ g * inner ℂ u (rhoL μ w g v) = 0 := fun g => by
    rw [(Submodule.mem_orthogonal' _ _).1 hu _ (hst g v hv), mul_zero]
  simp only [h0, integral_zero]
