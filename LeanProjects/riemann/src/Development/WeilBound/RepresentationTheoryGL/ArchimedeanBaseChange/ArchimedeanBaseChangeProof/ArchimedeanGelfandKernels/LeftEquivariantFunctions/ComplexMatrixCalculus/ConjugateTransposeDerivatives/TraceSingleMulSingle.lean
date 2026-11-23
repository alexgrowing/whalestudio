import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.SwapLaws

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace PositivityTheory.RgBcC.Cxa

open PositivityTheory.RgTw (Mat hb)

variable {n : ℕ}

theorem trace_single_mul_single (a b c d : Fin n) (x y : ℂ) :
    (single a b x * single c d y).trace = if b = c ∧ a = d then x * y else 0 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply, ite_and]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', ite_and]
  by_cases h1 : a = d <;> by_cases h2 : b = c <;> simp [h1, h2]

theorem sq_inv_sqrt_two : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 1 / 2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

theorem hb_herm (p : Fin n × Fin n) : (hb p).IsHermitian := by
  unfold PositivityTheory.RgTw.hb
  split_ifs with h1 h2
  · rw [h1]
    simp [IsHermitian, conjTranspose_single]
  · simp [IsHermitian, conjTranspose_smul, conjTranspose_add, conjTranspose_single, add_comm]
  · simp [IsHermitian, conjTranspose_smul, conjTranspose_sub, conjTranspose_single]
    rw [← smul_neg, neg_sub]

theorem hb_ortho (p q : Fin n × Fin n) : (hb p * hb q).trace = if p = q then 1 else 0 := by
  obtain ⟨i, j⟩ := p
  obtain ⟨k, l⟩ := q
  have s2 := sq_inv_sqrt_two
  simp only [PositivityTheory.RgTw.hb, Prod.mk.injEq]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 <;>
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
    trace_add, trace_sub, trace_smul, trace_single_mul_single, smul_eq_mul] <;>
  simp only [Fin.ext_iff, Fin.lt_iff_val_lt_val] at * <;>
  split_ifs <;>
  (try (exfalso; omega)) <;>
  (try simp) <;>
  (try ring_nf) <;>
  first
  | linear_combination 2 * s2
  | linear_combination 2 * s2 - 2 * ((Real.sqrt 2 : ℂ))⁻¹ ^ 2 * Complex.I_sq

theorem trace_mul_single (D : Mat n) (a b : Fin n) (c : ℂ) : (D * single a b c).trace = D b a * c := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply, ite_and]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem hbM_eq (m : Md n) : hbM m = hb (finProdFinEquiv.symm m) := rfl

theorem eq_zero_of_trace (D : Mat n) (h : ∀ p, (D * hb p).trace = 0) : D = 0 := by
  have hs : ((Real.sqrt 2 : ℂ))⁻¹ ≠ 0 := by
    refine inv_ne_zero ?_
    rw [Ne, Complex.ofReal_eq_zero, Real.sqrt_eq_zero']
    norm_num
  have hdiag : ∀ i, D i i = 0 := by
    intro i
    have e := h (i, i)
    simp only [PositivityTheory.RgTw.hb, if_true, trace_mul_single, mul_one] at e
    exact e
  have key : ∀ i j : Fin n, i < j → D i j = 0 ∧ D j i = 0 := by
    intro i j hij
    have e1 := h (i, j)
    have e2 := h (j, i)
    simp only [PositivityTheory.RgTw.hb, ne_of_lt hij, (ne_of_lt hij).symm, not_lt_of_gt hij, hij, if_false, if_true,
      Matrix.mul_smul, trace_smul, Matrix.mul_add, Matrix.mul_sub, trace_add, trace_sub, trace_mul_single,
      smul_eq_mul, mul_one] at e1 e2
    have f1 : D j i + D i j = 0 := (mul_eq_zero.mp e1).resolve_left hs
    have f2 : D i j - D j i = 0 := (mul_eq_zero.mp e2).resolve_left (mul_ne_zero hs Complex.I_ne_zero)
    constructor
    · linear_combination (f1 + f2) / 2
    · linear_combination (f1 - f2) / 2
  ext i j
  rcases lt_trichotomy i j with hij | hij | hij
  · exact (key i j hij).1
  · subst hij
    exact hdiag i
  · exact (key j i hij).2

theorem trace_re_of_herm {A B : Mat n} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (((A * B).trace.re : ℝ) : ℂ) = (A * B).trace := by
  rw [← Complex.conj_eq_iff_re]
  have h := Matrix.trace_conjTranspose (A * B)
  rw [conjTranspose_mul, hA.eq, hB.eq, trace_mul_comm] at h
  exact h.symm

theorem herm_sandwich (x M : Mat n) (hM : M.IsHermitian) : (x * M * xᴴ).IsHermitian := by
  simp only [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose, hM.eq, Matrix.mul_assoc]

end PositivityTheory.RgBcC.Cxa

namespace PositivityTheory.RgBcC

open PositivityTheory.RgTw (Mat hb)
open Cxa

theorem hbOrtho : HbOrtho := by
  intro n
  refine ⟨fun p q => ?_, fun p => ?_⟩
  · rw [hbM_eq, hbM_eq, hb_ortho]
    simp only [EmbeddingLike.apply_eq_iff_eq]
  · rw [hbM_eq]
    exact hb_herm _

end PositivityTheory.RgBcC
