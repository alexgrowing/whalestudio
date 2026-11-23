import Mathlib
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Height
import GroundTheory.AutomorphicForms.TraceFormulaConvolution
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsAreCuspForms
import GroundTheory.AutomorphicForms.MultiplicityOne.OpenSubgroupRep
import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteLevelGroups
import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteAdelicHaar
import GroundTheory.AutomorphicForms.L2LocalComponents.CenterCommute

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.ConvolutionTheory.Tf.tensCont :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (β : CompactlySupportedContinuousMap (archGroup K n) ℂ) (e : CompactlySupportedContinuousMap (AdelicGLn.FiniteAdelicGL K n) ℂ),
    (Continuous fun x : normOneGL K n => kbar β (infPart K n (x : AdelicGLn.AdelicGL K n)) * e (finPart K n (x : AdelicGLn.AdelicGL K n))) ∧
    (HasCompactSupport fun x : normOneGL K n => kbar β (infPart K n (x : AdelicGLn.AdelicGL K n)) * e (finPart K n (x : AdelicGLn.AdelicGL K n))) ∧
    ∀ x : normOneGL K n, kbar β (infPart K n (x : AdelicGLn.AdelicGL K n)) * e (finPart K n (x : AdelicGLn.AdelicGL K n)) ≠ 0 →
      ∃ a ∈ tsupport β, ∃ h ∈ tsupport e, x = archP K n a * MultiplicityOne.finProj K n h := by
  intro K _ _ n hn β e
  have key : ∀ x : normOneGL K n, kbar β (infPart K n (x : AdelicGLn.AdelicGL K n)) *
      e (finPart K n (x : AdelicGLn.AdelicGL K n)) ≠ 0 →
      ∃ a ∈ tsupport β, ∃ h ∈ tsupport e, x = archP K n a * MultiplicityOne.finProj K n h := by
    intro x hx
    have hk := left_ne_zero_of_mul hx
    have he := right_ne_zero_of_mul hx
    obtain ⟨s, hs⟩ : ∃ s, β (infPart K n (x : AdelicGLn.AdelicGL K n) * zInf K n s) ≠ 0 := by
      by_contra h0
      simp only [not_exists, ne_eq, not_not] at h0
      exact hk (by simp [kbar, h0])
    refine ⟨_, subset_tsupport _ hs, _, subset_tsupport _ he, ?_⟩
    have hf : ∀ h, MultiplicityOne.finProj K n h = retractOne (finEmb K n h) := fun h => rfl
    rw [archimedeanProjection_mul_positiveScalar hn, hf, ← retract_infEmb, ← retractOne_mul,
      infEmb_infPart_mul_finEmb_finPart, retractOne_coe]
  refine ⟨?_, ?_, key⟩
  · exact ((continuous_kbar hn β.continuous β.hasCompactSupport).comp
      (continuous_infPart.comp continuous_subtype_val)).mul
      (e.continuous.comp (continuous_finPart.comp continuous_subtype_val))
  · have hC : IsCompact ((fun p : archGroup K n × AdelicGLn.FiniteAdelicGL K n =>
        archP K n p.1 * MultiplicityOne.finProj K n p.2) '' (tsupport β ×ˢ tsupport e)) :=
      (β.hasCompactSupport.isCompact.prod e.hasCompactSupport.isCompact).image
        ((continuous_archP.comp continuous_fst).mul
          (MultiplicityOne.continuous_finProj.comp continuous_snd))
    refine HasCompactSupport.intro hC fun x hx => ?_
    by_contra hne
    obtain ⟨a, ha, h, hh, rfl⟩ := key x hne
    exact hx ⟨(a, h), ⟨ha, hh⟩, rfl⟩
