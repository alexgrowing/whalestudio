import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C

theorem UpperTheory.cfc_apply_of_eigenvector :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →L[ℂ] H), IsSelfAdjoint A → ∀ (φ : ℝ → ℝ), Continuous φ → ∀ (x : ℝ) (v : H), A v = (x : ℂ) • v → (cfc φ A : H →L[ℂ] H) v = (φ x : ℂ) • v := by
  intro H _ _ _ A hA φ hφ x v hv
  by_cases hv0 : v = 0
  · simp [hv0]
  have halg : ∀ r : ℝ, (algebraMap ℝ (H →L[ℂ] H) r) v = (r : ℂ) • v := by
    intro r
    rw [Algebra.algebraMap_eq_smul_one]
    simp
  have hx : x ∈ spectrum ℝ A := by
    rw [spectrum.mem_iff]
    rintro ⟨u, hu⟩
    apply hv0
    have h0 : (u : H →L[ℂ] H) v = 0 := by
      rw [hu, ContinuousLinearMap.sub_apply, halg, hv, sub_self]
    have h1 : ((↑u⁻¹ * ↑u : H →L[ℂ] H)) v = v := by
      rw [Units.inv_mul]; rfl
    rw [← h1, ContinuousLinearMap.mul_apply, h0, map_zero]
  have key : ∀ f : C(spectrum ℝ A, ℝ), (cfcHom hA f : H →L[ℂ] H) v = ((f ⟨x, hx⟩ : ℝ) : ℂ) • v := by
    intro f
    induction f using ContinuousMap.induction_on_of_compact with
    | const r =>
      have : (ContinuousMap.const (spectrum ℝ A) r) = algebraMap ℝ C(spectrum ℝ A, ℝ) r := rfl
      rw [this, AlgHomClass.commutes, halg]
      simp
    | id =>
      rw [cfcHom_id hA, hv]; rfl
    | star_id =>
      rw [star_trivial, cfcHom_id hA, hv]; rfl
    | add f g hf hg =>
      rw [map_add, ContinuousLinearMap.add_apply, hf, hg]
      simp [add_smul]
    | mul f g hf hg =>
      rw [map_mul, ContinuousLinearMap.mul_apply, hg, map_smul, hf, smul_smul]
      simp [mul_comm]
    | frequently f hf =>
      have hc : IsClosed {g : C(spectrum ℝ A, ℝ) | (cfcHom hA g : H →L[ℂ] H) v = ((g ⟨x, hx⟩ : ℝ) : ℂ) • v} := by
        apply isClosed_eq
        · exact (cfcHom_continuous hA).clm_apply continuous_const
        · exact (Complex.continuous_ofReal.comp (continuous_eval_const _)).smul continuous_const
      exact hc.closure_subset (mem_closure_iff_frequently.mpr hf)
  rw [cfc_apply φ A hA hφ.continuousOn, key]
  rfl
