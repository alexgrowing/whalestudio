import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeIntCut
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndFrFix
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrTanDirAlg

open NumberField TensorProduct

namespace GlobalTheory.IntSepElement

variable (E : Type) [Field E] [NumberField E]

open scoped Classical in

noncomputable def dualB : Module.Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) ℚ E :=
  (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) (integralBasis E)

theorem sum_dualB (z : E) :
    ∑ i, Algebra.trace ℚ E (z * integralBasis E i) • dualB E i = z := by
  classical
  conv_rhs => rw [← (dualB E).sum_repr z]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dualB, LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]

theorem repr_eq_trace (z : E) (i : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    (integralBasis E).repr z i = Algebra.trace ℚ E (dualB E i * z) := by
  classical
  have h : ∀ j, Algebra.trace ℚ E (dualB E i * integralBasis E j) = if j = i then 1 else 0 := by
    intro j
    have h := LinearMap.BilinForm.apply_dualBasis_left (traceForm_nondegenerate ℚ E)
      (integralBasis E) i j
    rw [Algebra.traceForm_apply] at h
    convert h
    rfl
  conv_rhs => rw [← (integralBasis E).sum_repr z]
  rw [Finset.mul_sum, map_sum]
  simp_rw [mul_smul_comm, LinearMap.map_smul, h, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp

theorem trace_dualB_int (c : 𝓞 E) (i : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    Algebra.trace ℚ E (dualB E i * (c : E)) = ((RingOfIntegers.basis E).repr c i : ℚ) := by
  rw [← repr_eq_trace]
  exact integralBasis_repr_apply E c i

theorem sum_mul_dualB : ∑ i, integralBasis E i * dualB E i = 1 := by
  classical
  have key : ∀ z : E, Algebra.trace ℚ E ((∑ i, integralBasis E i * dualB E i) * z) = Algebra.trace ℚ E z := by
    intro z
    rw [Finset.sum_mul, map_sum, Algebra.trace_eq_matrix_trace (integralBasis E) z, Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, repr_eq_trace]
    congr 1
    ring
  rw [← sub_eq_zero]
  refine (traceForm_nondegenerate ℚ E).1 _ fun z => ?_
  rw [Algebra.traceForm_apply, sub_mul, map_sub, key, one_mul, sub_self]

theorem discr_mul_dualB (i : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    ∃ y : 𝓞 E, (y : E) = ((discr E : ℤ) : E) * dualB E i := by
  classical
  have hmem : dualB E i ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    rw [Submodule.mem_traceDual]
    intro a ha
    rw [Submodule.mem_one] at ha
    obtain ⟨a, rfl⟩ := ha
    refine ⟨(RingOfIntegers.basis E).repr a i, ?_⟩
    rw [Algebra.traceForm_apply]
    exact (trace_dualB_int E a i).symm
  have := isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ)
    (1 : Submodule (𝓞 E) E) (b := integralBasis E) (fun i => by
      rw [integralBasis_apply]; exact (RingOfIntegers.isIntegral_coe _)) (Submodule.one_le.mp le_rfl) hmem
  rw [← coe_discr, Algebra.smul_def, mul_one, map_intCast] at this
  exact ⟨⟨_, this⟩, rfl⟩

theorem exists_sep_discr :
    ∃ x y : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → 𝓞 E, ∑ i, x i * y i = ((discr E : ℤ) : 𝓞 E) ∧
      ∀ a : 𝓞 E, (∑ i, (a * x i) ⊗ₜ[ℤ] y i : 𝓞 E ⊗[ℤ] 𝓞 E) = ∑ i, x i ⊗ₜ[ℤ] (a * y i) := by
  choose y hy using discr_mul_dualB E
  have hy' : ∀ i, algebraMap (𝓞 E) E (y i) = ((discr E : ℤ) : E) * dualB E i := hy
  refine ⟨RingOfIntegers.basis E, y, ?_, fun a => ?_⟩
  · apply RingOfIntegers.coe_injective
    rw [map_sum, map_intCast]
    simp only [map_mul, hy', ← integralBasis_apply]
    calc ∑ i, integralBasis E i * (((discr E : ℤ) : E) * dualB E i)
        = ((discr E : ℤ) : E) * ∑ i, integralBasis E i * dualB E i := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      _ = _ := by rw [sum_mul_dualB, mul_one]
  · have h1 : ∀ k, ∑ i, (RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E i) k • y i = a * y k := by
      intro k
      apply RingOfIntegers.coe_injective
      rw [map_sum, map_mul, hy']
      have h2 := sum_dualB E (dualB E k * algebraMap (𝓞 E) E a)
      calc ∑ i, algebraMap (𝓞 E) E ((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E i) k • y i)
          = ((discr E : ℤ) : E) * ∑ i, Algebra.trace ℚ E
              (dualB E k * algebraMap (𝓞 E) E a * integralBasis E i) • dualB E i := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            have h3 := trace_dualB_int E (a * RingOfIntegers.basis E i) k
            have h4 : ((a * RingOfIntegers.basis E i : 𝓞 E) : E) = algebraMap (𝓞 E) E a * integralBasis E i := by
              rw [integralBasis_apply, ← map_mul]
            rw [h4, ← mul_assoc] at h3
            rw [h3, map_zsmul, hy', Int.cast_smul_eq_zsmul, mul_smul_comm]
        _ = _ := by rw [h2]; ring
    calc (∑ i, (a * RingOfIntegers.basis E i) ⊗ₜ[ℤ] y i : 𝓞 E ⊗[ℤ] 𝓞 E)
        = ∑ i, ∑ k, RingOfIntegers.basis E k ⊗ₜ[ℤ]
            ((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E i) k • y i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr (a * RingOfIntegers.basis E i)]
          rw [TensorProduct.sum_tmul]
          exact Finset.sum_congr rfl fun k _ => TensorProduct.smul_tmul _ _ _
      _ = _ := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => by rw [← TensorProduct.tmul_sum, h1]

end GlobalTheory.IntSepElement
