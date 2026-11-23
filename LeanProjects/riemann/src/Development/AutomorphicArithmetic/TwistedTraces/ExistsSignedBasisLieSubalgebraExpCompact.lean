import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
import Development.AutomorphicArithmetic.TwistedTraces.ExistsSignedOrthonormalBasisOfIsCompl
import Development.AutomorphicArithmetic.TwistedTraces.TrFormDefiniteOnArchSkewArchHerm
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableCartan

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.exists_signed_basis_lieSubalgebra_exp_compact :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), ∃ B : LinearMap.BilinForm ℝ (isExpLieAlgebra K n).lieSubalgebra, (∀ X Y, B X Y = trForm K n X Y) ∧ (∀ X Y, B X Y = B Y X) ∧ ∃ (d : ℕ) (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra K n).lieSubalgebra) (ε : Fin d → ℝ), (∀ i, ε i = 1 ∨ ε i = -1) ∧ (∀ i j, B (b i) (b j) = if i = j then ε i else 0) ∧ ∀ i, ε i = -1 → ∀ t : ℝ, (isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie (b i)) ∈ archCompact K n := by
  intro K _ _ n
  have hmk : ∀ X Y : (isExpLieAlgebra K n).lieSubalgebra, trForm K n X Y =
      Algebra.trace ℝ (NumberField.mixedEmbedding.mixedSpace K)
        (Matrix.trace (mat (X : ArchMatrix K n) * mat (Y : ArchMatrix K n))) := fun _ _ => rfl
  let B : LinearMap.BilinForm ℝ (isExpLieAlgebra K n).lieSubalgebra :=
    LinearMap.mk₂ ℝ (fun X Y => trForm K n X Y)
      (fun X₁ X₂ Y => by
        simp only [hmk, mat_coe_add, Matrix.add_mul, Matrix.trace_add, map_add])
      (fun r X Y => by
        simp only [hmk, mat_coe_smul, Matrix.smul_mul, Matrix.trace_smul, map_smul])
      (fun X Y₁ Y₂ => by
        simp only [hmk, mat_coe_add, Matrix.mul_add, Matrix.trace_add, map_add])
      (fun r X Y => by
        simp only [hmk, mat_coe_smul, Matrix.mul_smul, Matrix.trace_smul, map_smul])
  have hB : ∀ X Y, B X Y = trForm K n X Y := fun _ _ => rfl
  have hsymm : ∀ X Y, B X Y = B Y X := by
    intro X Y
    rw [hB, hB, hmk, hmk, Matrix.trace_mul_comm]
  obtain ⟨h1, h2, h3⟩ := UpperTheory.trForm_definite_on_archSkew_archHerm K n
  haveI : FiniteDimensional ℝ (isExpLieAlgebra K n).lieSubalgebra :=
    FiniteDimensional.finiteDimensional_submodule (isExpLieAlgebra K n).lieSubalgebra.toSubmodule
  obtain ⟨d, b, ε, hε, horth, hk⟩ := UpperTheory.exists_signed_orthonormal_basis_of_isCompl _ B (archSkew K n) (archHerm K n)
    isCompl_archSkew_archHerm hsymm h1 h2 h3
  refine ⟨B, hB, hsymm, d, b, ε, hε, horth, fun i hi t => expG_mem_archCompact_of_skew _ ?_⟩
  have h := hk i hi
  rw [mem_archSkew] at h
  show Matrix.conjTranspose (t • mat (b i : ArchMatrix K n)) = -(t • mat (b i : ArchMatrix K n))
  rw [Matrix.conjTranspose_smul, star_trivial, h, smul_neg]
