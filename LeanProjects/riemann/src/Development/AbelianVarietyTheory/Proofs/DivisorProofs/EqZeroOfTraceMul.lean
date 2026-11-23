import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulFix
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledDarbouxCoordsCompat
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

noncomputable section

namespace GlobalTheory.AdelicTraceNondeg

theorem trace_one_tmul {F E R : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [CommRing R]
    [Algebra F R] (e : E) : Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e) = algebraMap F R (Algebra.trace F E e) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

theorem eq_zero_of_trace_mul {F E R : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [CommRing R]
    [Algebra F R] (m : R ⊗[F] E) (h : ∀ z : R ⊗[F] E, Algebra.trace R (R ⊗[F] E) (m * z) = 0) : m = 0 := by
  let b := Module.finBasis F E
  let d := (Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) b
  let bA := Algebra.TensorProduct.basis R b
  have key : ∀ j, bA.repr m j = 0 := by
    intro j
    have hj := h ((1 : R) ⊗ₜ[F] d j)
    rw [← bA.sum_repr m, Finset.sum_mul, map_sum] at hj
    rw [← hj, Finset.sum_eq_single j]
    · rw [Algebra.TensorProduct.basis_apply, smul_mul_assoc, map_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        trace_one_tmul, smul_eq_mul]
      have := (Algebra.traceForm F E).apply_dualBasis_left (traceForm_nondegenerate F E) b j j
      rw [Algebra.traceForm_apply, mul_comm] at this
      rw [this]; simp
    · intro i _ hij
      rw [Algebra.TensorProduct.basis_apply, smul_mul_assoc, map_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        trace_one_tmul, smul_eq_mul]
      have := (Algebra.traceForm F E).apply_dualBasis_left (traceForm_nondegenerate F E) b j i
      rw [Algebra.traceForm_apply, mul_comm] at this
      rw [this, if_neg hij, map_zero, mul_zero]
    · intro hj'; exact absurd (Finset.mem_univ j) hj'
  exact bA.repr.injective (by ext j; simp [key j])

theorem trace_pairing_nondeg : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ψ : AddChar (AF F) ℂ),
    IsStd ψ → ∀ m : AEF F E, m ≠ 0 → ∃ z : AEF F E, ψ (Algebra.trace (AF F) (AEF F E) (m * z)) ≠ 1 := by
  intro F E _ _ _ _ _ ψ hψ m hm
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : Algebra.IsSeparable F E := Algebra.IsAlgebraic.isSeparable_of_perfectField
  by_contra hne
  push_neg at hne
  apply hm
  refine eq_zero_of_trace_mul m fun z => ?_
  refine GlobalTheory.DiagNonvan.eq_zero_of_psi_mul hψ _ fun y => ?_
  have e1 : Algebra.trace (AF F) (AEF F E) (m * z) * y = Algebra.trace (AF F) (AEF F E) (m * (y • z)) := by
    rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
  rw [e1]
  exact hne _

example : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ψ : AddChar (AF F) ℂ),
    IsStd ψ → ∀ m : AEF F E, m ≠ 0 → ∃ z : AEF F E, ψ (Algebra.trace (AF F) (AEF F E) (m * z)) ≠ 1 :=
  trace_pairing_nondeg

end GlobalTheory.AdelicTraceNondeg
