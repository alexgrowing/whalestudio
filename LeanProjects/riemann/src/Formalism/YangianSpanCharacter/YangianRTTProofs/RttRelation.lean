import Formalism.YangianSpanCharacter.StatementT

namespace Formalism.YangianSpanCharacter.P

open Matrix Formalism.YangianSpanCharacter.T

set_option linter.unusedSimpArgs false in
theorem rttRelation : Formalism.YangianSpanCharacter.T.RTT := by
  intro R A _ _ _ p c ci Y Y' hW
  obtain ⟨hcc, hcc', hpc⟩ := hW
  have hpc2 : ∀ x : A, p * (c * x) = c * (p * x) + c * x := fun x => by
    rw [← mul_assoc, hpc, add_mul, mul_assoc]
  have hpci : p * ci = ci * p - ci := by
    have h := congrArg (fun x => ci * x * ci) hpc
    simp only [mul_add, add_mul, ← mul_assoc, hcc', one_mul] at h
    simp only [mul_assoc, hcc, mul_one] at h
    rw [h]; abel
  have hpci2 : ∀ x : A, p * (ci * x) = ci * (p * x) - ci * x := fun x => by
    rw [← mul_assoc, hpci, sub_mul, mul_assoc]
  have hcc2 : ∀ x : A, c * (ci * x) = x := fun x => by rw [← mul_assoc, hcc, one_mul]
  have hcc2' : ∀ x : A, ci * (c * x) = x := fun x => by rw [← mul_assoc, hcc', one_mul]
  ext ⟨i, k⟩ ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, T1, T2, Pf, Tm,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
  all_goals
    simp only [Algebra.algebraMap_eq_smul_one, mul_add, add_mul, mul_sub, sub_mul, neg_mul,
      mul_neg, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, mul_assoc, smul_add, smul_sub,
      smul_neg, smul_smul, hpc, hpc2, hpci, hpci2, hcc, hcc', hcc2, hcc2', neg_neg, sub_smul]
  all_goals module

end Formalism.YangianSpanCharacter.P
