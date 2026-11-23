import Mathlib
import Formalism.PeriodIntegrals.ContractionsCovariantIff
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorCommutatorQuantumDet
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantHatDecomposition.InjDecomp

open Finset Matrix Formalism.REAL Formalism.FourierDecayAlt.Q

namespace PI.QnCovHatW

theorem skip_one_eq_succAbove {m : ℕ} (i : Fin (m + 1)) (j : Fin m) : skip1 (t := m + 1) i j = i.succAbove j := by
  apply Fin.ext
  unfold skip1
  by_cases h : (j : ℕ) < (i : ℕ)
  · rw [if_pos h, Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simpa using h)]
    rfl
  · rw [if_neg h, Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simp only [Fin.coe_castSucc]; omega)]
    rfl

theorem qminor_skip {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin (m + 1) → Fin (m + 1) → A)
    (i j : Fin (m + 1)) (u : ℂ) :
    qminor E (skip1 i) (skip1 j) u = qminor (t := m) E i.succAbove j.succAbove u := by
  have h1 : (fun k : Fin m => skip1 (t := m + 1) i k) = i.succAbove := funext (skip_one_eq_succAbove i)
  have h2 : (fun k : Fin m => skip1 (t := m + 1) j k) = j.succAbove := funext (skip_one_eq_succAbove j)
  rw [← h1, ← h2]

theorem int_smul_eq {A : Type} [Ring A] [Algebra ℂ A] (k : ℤ) (x : A) :
    ((k : ℂ)) • x = (k : A) * x := by
  rw [Algebra.smul_def, map_intCast]

theorem swap4 {M : Type*} [AddCommMonoid M] {ι : Type*} [Fintype ι] (f : ι → ι → ι → ι → M) :
    ∑ i, ∑ j, ∑ i', ∑ j', f i j i' j' = ∑ i', ∑ j', ∑ i, ∑ j, f i j i' j' := by
  calc ∑ i, ∑ j, ∑ i', ∑ j', f i j i' j' = ∑ i, ∑ i', ∑ j', ∑ j, f i j i' j' := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i' _ => Finset.sum_comm
    _ = ∑ i', ∑ i, ∑ j', ∑ j, f i j i' j' := Finset.sum_comm
    _ = ∑ i', ∑ j', ∑ i, ∑ j, f i j i' j' :=
        Finset.sum_congr rfl fun i' _ => Finset.sum_comm

theorem det_sub_eq {m : ℕ} (P : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (i' i : Fin (m + 1)) :
    ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ k, P ((i'.succAbove ∘ σ) k) (i.succAbove k) =
      (P.submatrix i'.succAbove i.succAbove).det := by
  rw [Matrix.det_apply']
  rfl

theorem det_sub_eq' {m : ℕ} (Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (j j' : Fin (m + 1)) :
    ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ k, Q (j.succAbove k) ((j'.succAbove ∘ σ) k) =
      (Q.submatrix j.succAbove j'.succAbove).det := by
  rw [← Matrix.det_transpose, Matrix.det_apply']
  rfl

theorem scal {m : ℕ} (P Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (hPQ : P * Q = 1)
    (a β : Fin (m + 1) → ℂ) (i' j' : Fin (m + 1)) :
    ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
        ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * (β ᵥ* P) i * (Q *ᵥ a) j) *
          ((P.submatrix i'.succAbove i.succAbove).det * (Q.submatrix j.succAbove j'.succAbove).det) =
      (-1 : ℂ) ^ ((i' : ℕ) + (j' : ℕ)) * β i' * a j' := by
  have hsign : ∀ i j : Fin (m + 1), ((-1 : ℂ)) ^ ((i : ℕ) + (j : ℕ)) =
      (-1 : ℂ) ^ ((i' : ℕ) + (j' : ℕ)) * ((-1 : ℂ) ^ ((i' : ℕ) + (i : ℕ)) * (-1 : ℂ) ^ ((j : ℕ) + (j' : ℕ))) := by
    intro i j
    rw [← pow_add, ← pow_add]
    have h : (i' : ℕ) + j' + ((i' : ℕ) + i + ((j : ℕ) + j')) = ((i : ℕ) + j) + 2 * ((i' : ℕ) + j') := by ring
    rw [h, pow_add (-1 : ℂ) ((i : ℕ) + (j : ℕ)), pow_mul]
    norm_num
  have hX : ∑ i : Fin (m + 1), (β ᵥ* P) i * ((-1 : ℂ) ^ ((i' : ℕ) + (i : ℕ)) *
      (P.submatrix i'.succAbove i.succAbove).det) = P.det * β i' := by
    have h1 : ∀ i : Fin (m + 1), (-1 : ℂ) ^ ((i' : ℕ) + (i : ℕ)) *
        (P.submatrix i'.succAbove i.succAbove).det = P.adjugate i i' :=
      fun i => (Matrix.adjugate_fin_succ_eq_det_submatrix P i i').symm
    simp_rw [h1]
    have h2 : ∑ i, (β ᵥ* P) i * P.adjugate i i' = (β ᵥ* P ᵥ* P.adjugate) i' := rfl
    rw [h2, Matrix.vecMul_vecMul, Matrix.mul_adjugate]
    first
    | (rw [Matrix.vecMul_smul, Matrix.vecMul_one]; rfl)
    | simp [Matrix.vecMul, dotProduct, Matrix.one_apply, mul_comm]
  have hY : ∑ j : Fin (m + 1), ((-1 : ℂ) ^ ((j : ℕ) + (j' : ℕ)) *
      (Q.submatrix j.succAbove j'.succAbove).det) * (Q *ᵥ a) j = Q.det * a j' := by
    have h1 : ∀ j : Fin (m + 1), (-1 : ℂ) ^ ((j : ℕ) + (j' : ℕ)) *
        (Q.submatrix j.succAbove j'.succAbove).det = Q.adjugate j' j :=
      fun j => (Matrix.adjugate_fin_succ_eq_det_submatrix Q j' j).symm
    simp_rw [h1]
    have h2 : ∑ j, Q.adjugate j' j * (Q *ᵥ a) j = (Q.adjugate *ᵥ (Q *ᵥ a)) j' := rfl
    rw [h2, Matrix.mulVec_mulVec, Matrix.adjugate_mul]
    first
    | (rw [Matrix.smul_mulVec_assoc, Matrix.one_mulVec]; rfl)
    | simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
  have hdet : P.det * Q.det = 1 := by
    rw [← Matrix.det_mul, hPQ, Matrix.det_one]
  calc _ = (-1 : ℂ) ^ ((i' : ℕ) + (j' : ℕ)) *
        ((∑ i : Fin (m + 1), (β ᵥ* P) i * ((-1 : ℂ) ^ ((i' : ℕ) + (i : ℕ)) *
          (P.submatrix i'.succAbove i.succAbove).det)) *
        (∑ j : Fin (m + 1), ((-1 : ℂ) ^ ((j : ℕ) + (j' : ℕ)) *
          (Q.submatrix j.succAbove j'.succAbove).det) * (Q *ᵥ a) j)) := by
        rw [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hsign i j]
        ring
    _ = (-1 : ℂ) ^ ((i' : ℕ) + (j' : ℕ)) * β i' * a j' := by
        rw [hX, hY]
        linear_combination (-1 : ℂ) ^ ((i' : ℕ) + (j' : ℕ)) * β i' * a j' * hdet

theorem qnCovHat_of_lin (hL : PI.QnCovLin) : PI.QnCovHat := by
  intro A _ _ n E P Q hE hQP hPQ u a β
  cases n with
  | zero => simp [chatA]
  | succ m =>
  have rskew : ∀ (d c : Fin m → Fin (m + 1)) (σ : Equiv.Perm (Fin m)),
      qminor E (c ∘ σ) d u = ((Equiv.Perm.sign σ : ℤ) : ℂ) • qminor E c d u := by
    intro d c σ
    rw [int_smul_eq]
    exact quantumMinorRowSkew_holds A (m + 1) m E c d σ u
  have rzero : ∀ (d c : Fin m → Fin (m + 1)), ¬ Function.Injective c → qminor E c d u = 0 := by
    intro d c hc
    obtain ⟨p, q, hpq, hne⟩ := Function.not_injective_iff.mp hc
    exact quantumMinor_eq_zero_of_row_eq quantumMinorRowSkew_holds E c d u p q hne hpq
  have cskew : ∀ (c d : Fin m → Fin (m + 1)) (σ : Equiv.Perm (Fin m)),
      qminor E c (d ∘ σ) u = ((Equiv.Perm.sign σ : ℤ) : ℂ) • qminor E c d u := by
    intro c d σ
    rw [int_smul_eq]
    exact quantumMinorColSkew_holds A (m + 1) m E hE c d σ u
  have czero : ∀ (c d : Fin m → Fin (m + 1)), ¬ Function.Injective d → qminor E c d u = 0 := by
    intro c d hd
    obtain ⟨p, q, hpq, hne⟩ := Function.not_injective_iff.mp hd
    exact quantumMinor_eq_zero_of_col_eq quantumMinorColSkew_holds E hE c d u p q hne hpq
  have key : ∀ i j : Fin (m + 1), qminor (Econj E P Q) i.succAbove j.succAbove u =
      ∑ i' : Fin (m + 1), ∑ j' : Fin (m + 1),
        ((P.submatrix i'.succAbove i.succAbove).det * (Q.submatrix j.succAbove j'.succAbove).det) •
          qminor E i'.succAbove j'.succAbove u := by
    intro i j
    rw [hL A (m + 1) m E P Q hQP i.succAbove j.succAbove u]
    simp_rw [mul_smul]
    simp_rw [← Finset.smul_sum]
    have inner : ∀ c : Fin m → Fin (m + 1),
        ∑ d : Fin m → Fin (m + 1), (∏ k, Q (j.succAbove k) (d k)) • qminor E c d u =
          ∑ j' : Fin (m + 1), (Q.submatrix j.succAbove j'.succAbove).det • qminor E c j'.succAbove u := by
      intro c
      rw [alt_sum (fun d => qminor E c d u) (cskew c) (czero c)]
      refine Finset.sum_congr rfl fun j' _ => ?_
      rw [det_sub_eq']
    simp_rw [inner]
    rw [alt_sum (fun c => ∑ j' : Fin (m + 1),
        (Q.submatrix j.succAbove j'.succAbove).det • qminor E c j'.succAbove u) ?_ ?_]
    · refine Finset.sum_congr rfl fun i' _ => ?_
      rw [det_sub_eq, Finset.smul_sum]
    · intro c σ
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j' _ => ?_
      rw [rskew, smul_comm]
    · intro c hc
      refine Finset.sum_eq_zero fun j' _ => ?_
      rw [rzero _ c hc, smul_zero]
  simp only [chatA, qminor_skip]
  simp_rw [key, Finset.smul_sum, smul_smul]
  rw [swap4]
  refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j' _ => ?_
  simp_rw [← Finset.sum_smul]
  rw [scal P Q hPQ a β i' j']

end PI.QnCovHatW
