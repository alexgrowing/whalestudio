import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CyclicVectorOfSeparableCharpolyField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CyclicVectorGeneratedAlgebraStructure

open Matrix

namespace GlobalTheory.UnitDiscAlg

section Basic
variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}

theorem integ_mul {x y : Matrix (Fin n) (Fin n) E} (hx : ∀ i j, ‖x i j‖ ≤ 1) (hy : ∀ i j, ‖y i j‖ ≤ 1) :
    ∀ i j, ‖(x * y) i j‖ ≤ 1 := by
  intro i j
  rw [Matrix.mul_apply]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    (fun k _ => by rw [norm_mul]; exact mul_le_one₀ (hx i k) (norm_nonneg _) (hy k j))

theorem integ_add {x y : Matrix (Fin n) (Fin n) E} (hx : ∀ i j, ‖x i j‖ ≤ 1) (hy : ∀ i j, ‖y i j‖ ≤ 1) :
    ∀ i j, ‖(x + y) i j‖ ≤ 1 := by
  intro i j
  rw [Matrix.add_apply]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx i j) (hy i j))

theorem integ_sub {x y : Matrix (Fin n) (Fin n) E} (hx : ∀ i j, ‖x i j‖ ≤ 1) (hy : ∀ i j, ‖y i j‖ ≤ 1) :
    ∀ i j, ‖(x - y) i j‖ ≤ 1 := by
  intro i j
  rw [Matrix.sub_apply, sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx i j) (by rw [norm_neg]; exact hy i j))

theorem integ_one : ∀ i j, ‖(1 : Matrix (Fin n) (Fin n) E) i j‖ ≤ 1 := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem integ_zero : ∀ i j, ‖(0 : Matrix (Fin n) (Fin n) E) i j‖ ≤ 1 := by
  intro i j
  simp

theorem integ_pow {x : Matrix (Fin n) (Fin n) E} (hx : ∀ i j, ‖x i j‖ ≤ 1) (k : ℕ) :
    ∀ i j, ‖(x ^ k) i j‖ ≤ 1 := by
  induction k with
  | zero => simpa using integ_one
  | succ k ih => rw [pow_succ]; exact integ_mul ih hx

theorem integ_smul {x : Matrix (Fin n) (Fin n) E} {a : E} (ha : ‖a‖ ≤ 1) (hx : ∀ i j, ‖x i j‖ ≤ 1) :
    ∀ i j, ‖(a • x) i j‖ ≤ 1 := by
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_one₀ ha (norm_nonneg _) (hx i j)

end Basic

theorem comm_of_bezout {E : Type} [Field E] {n : ℕ} {N a b : Matrix (Fin n) (Fin n) E}
    (h : ∃ u v : Polynomial E, u * N.charpoly + v * Polynomial.derivative N.charpoly = 1)
    (ha : a * N = N * a) (hb : b * N = N * b) : a * b = b * a := by
  obtain ⟨u, v, huv⟩ := h
  have hs : N.charpoly.Separable := ⟨u, v, huv⟩
  obtain ⟨w, hw⟩ := GlobalTheory.RegSS.cyclicField E (Fin n) N hs
  have hbij := (GlobalTheory.RegSS.CycAlg.cyclicAlgebra E (Fin n) N w hw).2.2
  have ha' := GlobalTheory.RegSS.mem_genAlg_of_commute hbij ha
  have hb' := GlobalTheory.RegSS.mem_genAlg_of_commute hbij hb
  exact congrArg Subtype.val
    (mul_comm (⟨a, ha'⟩ : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg N) ⟨b, hb'⟩)

end GlobalTheory.UnitDiscAlg
