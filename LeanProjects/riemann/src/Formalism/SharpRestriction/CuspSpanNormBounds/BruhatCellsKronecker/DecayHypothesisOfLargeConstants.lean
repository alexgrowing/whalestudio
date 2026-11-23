import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.TraceConjMulEqHilbertSchmidt
import Formalism.SharpRestriction.CuspSpanNormBounds.ThresholdCubicInequalitySignPattern

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexOrder
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

theorem one_le_hilbert_schmidt_of_mem {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) (hg : Formalism.REAL.inUJ ε g) (a : Fin n) :
    1 ≤ Formalism.REAL.hs g := by
  have h := congrFun (congrFun hg a) a
  unfold Formalism.REAL.Jm at h
  rw [Matrix.mul_apply] at h
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq] at h
  let s : Fin n → ℝ := fun j => if ε j then 1 else -1
  have h' : ((∑ j, s j * ‖g j a‖ ^ 2 : ℝ) : ℂ) = ((s a : ℝ) : ℂ) := by
    have e2 : ((s a : ℝ) : ℂ) = if ε a = true then 1 else -1 := by
      show (((if ε a then 1 else -1 : ℝ)) : ℂ) = _
      split_ifs <;> simp
    rw [e2, ← h]
    push_cast
    apply Finset.sum_congr rfl
    intro j _
    rw [← Complex.conj_mul' (g j a)]
    show (((if ε j then 1 else -1 : ℝ)) : ℂ) * _ = _
    split_ifs <;> simp
  have h'' : ∑ j, s j * ‖g j a‖ ^ 2 = s a := by exact_mod_cast h'
  have hs1 : s a * s a = 1 := by
    show (if ε a then (1 : ℝ) else -1) * (if ε a then (1 : ℝ) else -1) = 1
    split_ifs <;> norm_num
  have hle : ∀ j, s a * s j ≤ 1 := by
    intro j
    show (if ε a then (1 : ℝ) else -1) * (if ε j then (1 : ℝ) else -1) ≤ 1
    split_ifs <;> norm_num
  calc (1 : ℝ) = s a * ∑ j, s j * ‖g j a‖ ^ 2 := by rw [h'', hs1]
    _ = ∑ j, (s a * s j) * ‖g j a‖ ^ 2 := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
    _ ≤ ∑ j, ‖g j a‖ ^ 2 := Finset.sum_le_sum (fun j _ => by nlinarith [hle j, sq_nonneg ‖g j a‖])
    _ ≤ Formalism.REAL.hs g := by
        unfold Formalism.REAL.hs
        exact Finset.sum_le_sum (fun i _ =>
          Finset.single_le_sum (f := fun j => ‖g i j‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ a))

theorem compact_to_unitary_hermitian (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool)
    (P g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hP : IsCayleyU k r ε P)
    (hg : g ∈ Formalism.REAL.Kset ε) :
    P⁻¹ * g * P ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∩
      (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _) := by
  have a1 : P.conjTranspose * P = 1 := Matrix.mem_unitaryGroup_iff'.1 hP.2
  have a2 : P * P.conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.1 hP.2
  have iP : P⁻¹ = P.conjTranspose := Matrix.inv_eq_left_inv a1
  have gJ : g.conjTranspose * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := (Formalism.REAL.maximal_compact_facts _ ε).1 g hg
  rw [iP]
  constructor
  · show (P.conjTranspose * g * P).conjTranspose * Formalism.QuantumDeterminants.Hpk k r * (P.conjTranspose * g * P) = Formalism.QuantumDeterminants.Hpk k r
    rw [← hP.1.2]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc P.conjTranspose * (g.conjTranspose * P) * (P.conjTranspose * Formalism.REAL.Jm ε * P) * (P.conjTranspose * g * P)
        = P.conjTranspose * (g.conjTranspose * ((P * P.conjTranspose) * Formalism.REAL.Jm ε * (P * P.conjTranspose)) * g) * P := by
          simp only [Matrix.mul_assoc]
      _ = P.conjTranspose * Formalism.REAL.Jm ε * P := by
          rw [a2, Matrix.one_mul, Matrix.mul_one, gJ, Matrix.mul_assoc]
  · have hs : P.conjTranspose ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := by
      rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mem hP.2
    exact mul_mem (mul_mem hs hg.1) hP.2

end Formalism.MainNotions.BridgeLemma

end
