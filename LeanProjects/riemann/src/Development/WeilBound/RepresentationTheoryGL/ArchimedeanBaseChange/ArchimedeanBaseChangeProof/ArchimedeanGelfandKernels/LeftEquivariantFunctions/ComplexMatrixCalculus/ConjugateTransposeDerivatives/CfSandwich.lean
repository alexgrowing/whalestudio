import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ConjugateTransposeDerivatives.TraceSingleMulSingle

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace PositivityTheory.RgBcC

open PositivityTheory.RgTw (Mat hb)
open Cxa

theorem cf_apply {n : ℕ} (H : Mat n) (m : Md n) : cf n H m = (((H * hbM m).trace.re : ℝ) : ℂ) := rfl

private theorem cf_eq_trace_mul_hbM_of_isHermitian {n : ℕ} (H : Mat n) (hH : H.IsHermitian) (m : Md n) :
    cf n H m = (H * hbM m).trace := by
  rw [cf_apply]
  exact trace_re_of_herm hH (by rw [hbM_eq]; exact hb_herm _)

theorem hbExp : HbExp := by
  intro n H hH
  have key : ∀ p : Fin n × Fin n, trace ((H - ∑ m : Md n, cf n H m • hbM m) * hb p) = 0 := by
    intro p
    rw [sub_mul, trace_sub, Finset.sum_mul, trace_sum]
    simp_rw [smul_mul_assoc, trace_smul]
    rw [← finProdFinEquiv.sum_comp]
    simp only [hbM_eq, Equiv.symm_apply_apply, hb_ortho, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ p, if_pos (Finset.mem_univ _), cf_eq_trace_mul_hbM_of_isHermitian H hH, hbM_eq,
      Equiv.symm_apply_apply, sub_self]
  exact (sub_eq_zero.mp (eq_zero_of_trace _ key))

theorem cfPair : CfPair := by
  intro n H H' hH hH'
  conv_rhs => rw [hbExp n H' hH']
  rw [Matrix.mul_sum, trace_sum]
  simp_rw [mul_smul_comm, trace_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [cf_eq_trace_mul_hbM_of_isHermitian H hH m, mul_comm]

theorem cf_sandwich {n : ℕ} (x K : Mat n) (hK : K.IsHermitian) (p : Md n) :
    cf n (x * K * xᴴ) p = ∑ r, cf n K r * cf n (x * hbM r * xᴴ) p := by
  have hM : ∀ r : Md n, (hbM r).IsHermitian := fun r => by rw [hbM_eq]; exact hb_herm _
  rw [cf_eq_trace_mul_hbM_of_isHermitian _ (herm_sandwich x K hK) p]
  conv_lhs => rw [hbExp n K hK]
  rw [Matrix.mul_sum, Finset.sum_mul, Finset.sum_mul, trace_sum]
  simp_rw [mul_smul_comm, smul_mul_assoc, trace_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [cf_eq_trace_mul_hbM_of_isHermitian _ (herm_sandwich x _ (hM r)) p]

theorem mtLaws : MtLaws := by
  intro n
  have hM : ∀ r : Md n, (hbM r).IsHermitian := fun r => by rw [hbM_eq]; exact hb_herm _
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext p q
    show (cf n) (1 * hbM q * (1 : Mat n)ᴴ) p = (1 : Matrix (Md n) (Md n) ℂ) p q
    rw [conjTranspose_one, Matrix.mul_one, Matrix.one_mul, cf_eq_trace_mul_hbM_of_isHermitian _ (hM q), hbM_eq, hbM_eq,
      hb_ortho, Matrix.one_apply]
    by_cases h : p = q
    · subst h
      simp
    · have h' : finProdFinEquiv.symm q ≠ finProdFinEquiv.symm p := fun e => h (finProdFinEquiv.symm.injective e).symm
      rw [if_neg h', if_neg h]
  · intro x y
    ext p q
    rw [Matrix.mul_apply]
    show (cf n) (x * y * hbM q * (x * y)ᴴ) p = ∑ r, (cf n) (x * hbM r * xᴴ) p * (cf n) (y * hbM q * yᴴ) r
    have e : x * y * hbM q * (x * y)ᴴ = x * (y * hbM q * yᴴ) * xᴴ := by
      rw [conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [e, cf_sandwich x _ (herm_sandwich y _ (hM q)) p]
    exact Finset.sum_congr rfl fun r _ => mul_comm _ _
  · intro x H hH
    ext p
    simp only [Matrix.mulVec, dotProduct]
    rw [cf_sandwich x H hH p]
    exact Finset.sum_congr rfl fun r _ => mul_comm _ _
  · intro x H hH
    ext p
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    have hs : (xᴴ * H * x).IsHermitian := by
      have := herm_sandwich xᴴ H hH
      rwa [conjTranspose_conjTranspose] at this
    refine Eq.trans (cfPair n (x * hbM p * xᴴ) H (herm_sandwich _ _ (hM p)) hH) ?_
    rw [cf_eq_trace_mul_hbM_of_isHermitian _ hs p, Matrix.mul_assoc (x * hbM p), trace_mul_comm (x * hbM p)]
    simp only [Matrix.mul_assoc]

end PositivityTheory.RgBcC
