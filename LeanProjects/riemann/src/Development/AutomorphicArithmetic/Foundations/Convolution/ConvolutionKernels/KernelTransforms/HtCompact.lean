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

theorem UpperTheory.ConvolutionTheory.Tf.htCompact :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (S : Set (AdelicGLn.AdelicGL K n)), IsCompact S → ∃ Y : ℝ, 1 ≤ Y ∧ (∀ g ∈ S, AutomorphicForm.height g ≤ Y) ∧
      ∀ (k : ℕ), ∀ g ∈ S ^ k, AutomorphicForm.height g ≤ Y ^ k := by
  intro K _ _ n S hS
  obtain ⟨M, hM⟩ := CuspidalSpectrum.exists_height_le_of_isCompact hS
  have hC : 1 ≤ AutomorphicForm.heightConst K n := AutomorphicForm.one_le_heightConst
  have hM1 : (1 : ℝ) ≤ max 1 M := le_max_left _ _
  have hM' : ∀ g ∈ S, AutomorphicForm.height g ≤ max 1 M := fun g hg =>
    (hM g hg).trans (le_max_right _ _)
  have hY : 1 ≤ AutomorphicForm.heightConst K n * max 1 M :=
    one_le_mul_of_one_le_of_one_le hC hM1
  refine ⟨AutomorphicForm.heightConst K n * max 1 M, hY, fun g hg => ?_, fun k => ?_⟩
  · exact (hM' g hg).trans (le_mul_of_one_le_left (zero_le_one.trans hM1) hC)
  · induction k with
    | zero =>
      intro g hg
      rw [pow_zero, Set.mem_one] at hg
      rw [hg, AutomorphicForm.height_one, pow_zero]
    | succ k ih =>
      intro g hg
      rw [pow_succ] at hg
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hg
      have h1 := ih a ha
      have h2 := hM' b hb
      have hb0 := (AutomorphicForm.height_pos b).le
      have hC0 : 0 ≤ AutomorphicForm.heightConst K n := zero_le_one.trans hC
      have hP0 : 0 ≤ (AutomorphicForm.heightConst K n * max 1 M) ^ k :=
        pow_nonneg (zero_le_one.trans hY) k
      calc AutomorphicForm.height (a * b)
          ≤ AutomorphicForm.heightConst K n * AutomorphicForm.height a * AutomorphicForm.height b :=
            AutomorphicForm.height_mul_le a b
        _ ≤ AutomorphicForm.heightConst K n * (AutomorphicForm.heightConst K n * max 1 M) ^ k
              * max 1 M :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1 hC0) h2 hb0 (mul_nonneg hC0 hP0)
        _ = (AutomorphicForm.heightConst K n * max 1 M) ^ (k + 1) := by ring
