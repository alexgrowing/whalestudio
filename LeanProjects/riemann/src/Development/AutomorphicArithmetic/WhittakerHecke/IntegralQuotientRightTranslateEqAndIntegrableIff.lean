import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HkSum
open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin GlobalTheory.LFun Formalism.UG Formalism.UG.P
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace UpperTheory.ConvolutionTheory.BW

theorem UpperTheory.integral_quotient_rightTranslate_eq_and_integrable_iff :
    ∀ (E : Type) [Field E] [NumberField E] (r : ℕ) (h : GA E r → ℂ), AutomorphicForm.IsLeftInvariant h → ∀ g ∈ normOneGL E r,
      (∫ y : RightCosetSpace (rationalGLOne E r), h (((Quotient.out y : normOneGL E r) : GA E r) * g) ∂(quotientMeasure (rationalGLOne E r) (mu1 E r)) = ∫ y : RightCosetSpace (rationalGLOne E r), h ((Quotient.out y : normOneGL E r) : GA E r) ∂(quotientMeasure (rationalGLOne E r) (mu1 E r))) ∧
      (Integrable (fun y : RightCosetSpace (rationalGLOne E r) => h (((Quotient.out y : normOneGL E r) : GA E r) * g)) (quotientMeasure (rationalGLOne E r) (mu1 E r)) ↔ Integrable (fun y : RightCosetSpace (rationalGLOne E r) => h ((Quotient.out y : normOneGL E r) : GA E r)) (quotientMeasure (rationalGLOne E r) (mu1 E r))) := by
  intro E _ _ r h hh g hg
  have e1 : (fun y : RightCosetSpace (rationalGLOne E r) => h ((Quotient.out y : normOneGL E r) : GA E r)) =
      CuspidalSpectrum.cuspQuot hh := by
    funext y
    conv_rhs => rw [← Quotient.out_eq y]
    rfl
  have e2 : (fun y : RightCosetSpace (rationalGLOne E r) => h (((Quotient.out y : normOneGL E r) : GA E r) * g)) =
      CuspidalSpectrum.cuspQuot hh ∘ rightMul (rationalGLOne E r) ⟨g, hg⟩ := by
    funext y
    conv_rhs => rw [← Quotient.out_eq y]
    rfl
  have hm := measurePreserving_rightMul (Γ := rationalGLOne E r) (mu1 E r) ⟨g, hg⟩
  have he : MeasurableEmbedding (rightMul (rationalGLOne E r) ⟨g, hg⟩) :=
    (rightMulHomeomorph (rationalGLOne E r) ⟨g, hg⟩).measurableEmbedding
  rw [e1, e2]
  exact ⟨hm.integral_comp he _, hm.integrable_comp_emb he⟩
