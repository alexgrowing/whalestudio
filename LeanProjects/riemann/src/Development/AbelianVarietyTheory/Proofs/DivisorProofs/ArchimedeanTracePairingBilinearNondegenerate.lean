import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPairApply
open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.VacLn

noncomputable section

namespace GlobalTheory.VacLn.TrNondeg

theorem trace_pi' {R : Type} [Field R] {ι : Type} [Fintype ι]
    {E : ι → Type} [∀ c, CommRing (E c)] [∀ c, Algebra R (E c)] [∀ c, Module.Finite R (E c)]
    (x : ∀ c, E c) : Algebra.trace R (∀ c, E c) x = ∑ c, Algebra.trace R (E c) (x c) := by
  classical
  let b : ∀ c, Module.Basis (Fin (Module.finrank R (E c))) R (E c) := fun c => Module.finBasis R (E c)
  rw [Algebra.trace_eq_matrix_trace (Pi.basis b), Matrix.trace, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Algebra.trace_eq_matrix_trace (b c), Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_repr, Pi.basis_apply]

def conjM {F : Type} [Field F] [NumberField F] (z : mixedEmbedding.mixedSpace F) :
    mixedEmbedding.mixedSpace F :=
  (z.1, fun w => starRingEnd ℂ (z.2 w))

theorem trace_conjM_mul {F : Type} [Field F] [NumberField F] (z : mixedEmbedding.mixedSpace F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (conjM z * z) =
      ∑ w, z.1 w ^ 2 + ∑ w, 2 * Complex.normSq (z.2 w) := by
  rw [Algebra.trace_prod_apply, trace_pi', trace_pi']
  congr 1
  · refine Finset.sum_congr rfl fun w _ => ?_
    simp [conjM, Algebra.trace_self_apply, sq]
  · refine Finset.sum_congr rfl fun w _ => ?_
    simp [conjM, Algebra.trace_complex_apply, Complex.normSq_apply, Complex.mul_re]

theorem eq_zero_of_trace_conjM_mul {F : Type} [Field F] [NumberField F]
    (z : mixedEmbedding.mixedSpace F)
    (h : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (conjM z * z) = 0) : z = 0 := by
  rw [trace_conjM_mul] at h
  have h1 : 0 ≤ ∑ w, z.1 w ^ 2 := Finset.sum_nonneg fun w _ => sq_nonneg _
  have h2 : 0 ≤ ∑ w, 2 * Complex.normSq (z.2 w) :=
    Finset.sum_nonneg fun w _ => mul_nonneg (by norm_num) (Complex.normSq_nonneg _)
  have e1 := (Finset.sum_eq_zero_iff_of_nonneg fun w _ => sq_nonneg (z.1 w)).1 (by linarith)
  have e2 := (Finset.sum_eq_zero_iff_of_nonneg fun w _ =>
    mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (Complex.normSq_nonneg (z.2 w))).1 (by linarith)
  ext w
  · simpa using e1 w (Finset.mem_univ _)
  · have := e2 w (Finset.mem_univ _)
    have : Complex.normSq (z.2 w) = 0 := by linarith
    simpa using Complex.normSq_eq_zero.1 this

end GlobalTheory.VacLn.TrNondeg

namespace GlobalTheory.VacLn

theorem trPair_nondeg : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (y : κ → mixedEmbedding.mixedSpace F),
    (∀ x, trPair F κ x y = 0) → y = 0 := by
  intro F _ _ κ _ y h
  have h0 := h (fun i => TrNondeg.conjM (y i))
  rw [trPair_apply, map_sum] at h0
  have hnn : ∀ i, 0 ≤ Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (TrNondeg.conjM (y i) * y i) := by
    intro i
    rw [TrNondeg.trace_conjM_mul]
    exact add_nonneg (Finset.sum_nonneg fun w _ => sq_nonneg _)
      (Finset.sum_nonneg fun w _ => mul_nonneg (by norm_num) (Complex.normSq_nonneg _))
  have e := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hnn i).1 h0
  funext i
  exact TrNondeg.eq_zero_of_trace_conjM_mul _ (e i (Finset.mem_univ _))

end GlobalTheory.VacLn
