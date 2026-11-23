import Formalism.PeriodIntegrals.QmRowExp
import Formalism.PeriodIntegrals.QmRowForm
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorCommutatorQuantumDet

open Finset

noncomputable section

namespace PI.QmRowExpWork

open Formalism.REAL

def cyc0 (m : ℕ) (j : Fin (m + 1)) : Equiv.Perm (Fin (m + 1)) := (Fin.cycleRange j).symm

theorem cycle_perm_zero (m : ℕ) (j : Fin (m + 1)) : cyc0 m j 0 = j := by
  apply (Fin.cycleRange j).injective
  simp [cyc0, Fin.cycleRange_self]

theorem cycle_perm_succ (m : ℕ) (j : Fin (m + 1)) (k : Fin m) : cyc0 m j k.succ = j.succAbove k := by
  apply (Fin.cycleRange j).injective
  simp [cyc0, Fin.cycleRange_succAbove]

theorem sign_cycle_perm (m : ℕ) (j : Fin (m + 1)) :
    Equiv.Perm.sign (cyc0 m j) = (-1) ^ (j : ℕ) := by
  rw [cyc0, Equiv.Perm.sign_symm, Fin.sign_cycleRange]

def ext0 {m : ℕ} (τ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 1)) :=
  ((finSuccEquiv m).trans (Equiv.optionCongr τ)).trans (finSuccEquiv m).symm

theorem matrixExtendByZero_zero {m : ℕ} (τ : Equiv.Perm (Fin m)) : ext0 τ 0 = 0 := by
  simp [ext0]

theorem extByZero_succ {m : ℕ} (τ : Equiv.Perm (Fin m)) (k : Fin m) : ext0 τ k.succ = (τ k).succ := by
  simp [ext0]

theorem sign_extend_perm {m : ℕ} (τ : Equiv.Perm (Fin m)) :
    Equiv.Perm.sign (ext0 τ) = Equiv.Perm.sign τ := by
  rw [ext0, Equiv.Perm.sign_trans_trans_symm, Equiv.optionCongr_sign]

def phi0 (m : ℕ) (p : Fin (m + 1) × Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 1)) :=
  cyc0 m p.1 * ext0 p.2

theorem firstColumnSplit_bijective (m : ℕ) : Function.Bijective (phi0 m) := by
  have hinj : Function.Injective (phi0 m) := by
    rintro ⟨j, τ⟩ ⟨j', τ'⟩ h
    simp only [phi0] at h
    have hj : j = j' := by
      have := congrArg (fun σ : Equiv.Perm (Fin (m + 1)) => σ 0) h
      simpa [Equiv.Perm.mul_apply, matrixExtendByZero_zero, cycle_perm_zero] using this
    subst hj
    have h2 : ext0 τ = ext0 τ' := mul_left_cancel h
    have hτ : τ = τ' := by
      ext k
      have := congrArg (fun σ : Equiv.Perm (Fin (m + 1)) => σ k.succ) h2
      simp only [extByZero_succ, Fin.succ_inj] at this
      rw [this]
    rw [hτ]
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, ?_⟩
  simp [Fintype.card_perm, Nat.factorial_succ]

theorem qminorRow_succ {A : Type*} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin (m + 1) → Fin n) (u : ℂ) :
    qminorRow E a b u = ∑ σ : Equiv.Perm (Fin (m + 1)), ((Equiv.Perm.sign σ : ℤ) : A) *
      (List.ofFn fun k : Fin (m + 1) => Tm E (u - (m : ℂ) + ((k : ℕ) : ℂ)) (a k) (b (σ k))).prod := by
  have e : ∀ k : ℕ, u - ((m + 1 : ℕ) : ℂ) + 1 + (k : ℂ) = u - (m : ℂ) + (k : ℂ) := by
    intro k
    push_cast
    ring
  simp only [qminorRow, e]

theorem rowFirst {A : Type*} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin (m + 1) → Fin n) (u : ℂ) :
    qminorRow E a b u = ∑ j : Fin (m + 1), (((-1 : ℤ) ^ (j : ℕ) : ℤ) : A) *
      (Tm E (u - (m : ℂ)) (a 0) (b j) * qminorRow E (a ∘ Fin.succ) (b ∘ j.succAbove) u) := by
  rw [qminorRow_succ, ← (firstColumnSplit_bijective m).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [qminorRow, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have e : ∀ k : ℕ, u - (m : ℂ) + ((k + 1 : ℕ) : ℂ) = u - (m : ℂ) + 1 + (k : ℂ) := by
    intro k
    push_cast
    ring
  simp only [phi0, Equiv.Perm.sign_mul, sign_cycle_perm, sign_extend_perm, Units.val_mul, Int.cast_mul,
    List.ofFn_succ, List.prod_cons, Equiv.Perm.mul_apply, matrixExtendByZero_zero, cycle_perm_zero, extByZero_succ, cycle_perm_succ,
    Fin.val_zero, Nat.cast_zero, add_zero, Fin.val_succ, e, Function.comp_apply]
  rw [mul_assoc]
  congr 1
  rw [← mul_assoc, ← mul_assoc, Int.cast_comm]

theorem rowLast {A : Type*} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin (m + 1) → Fin n) (u : ℂ) :
    qminorRow E a b u = ∑ j : Fin (m + 1), (((-1 : ℤ) ^ (m + (j : ℕ)) : ℤ) : A) *
      (qminorRow E (a ∘ Fin.castSucc) (b ∘ j.succAbove) (u - 1) * Tm E u (a (Fin.last m)) (b j)) := by
  rw [qminorRow_succ, ← (lastColumnSplit_bijective m).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [qminorRow, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have e : ∀ k : ℕ, u - 1 - (m : ℂ) + 1 + (k : ℂ) = u - (m : ℂ) + (k : ℂ) := by
    intro k
    ring
  have hs : ((-1 : ℤ) ^ (m + (j : ℕ))) = (-1) ^ (m - (j : ℕ)) := by
    have hj : (j : ℕ) ≤ m := Nat.lt_succ_iff.mp j.isLt
    have : m + (j : ℕ) = (m - (j : ℕ)) + 2 * (j : ℕ) := by omega
    rw [this, pow_add, pow_mul]
    simp
  simp only [lastColumnSplit, Equiv.Perm.sign_mul, sign_cycleToLast, sign_extendLast, Units.val_mul, Int.cast_mul,
    List.ofFn_succ', List.prod_concat, Equiv.Perm.mul_apply, extendLast_last, cycleToLast_last,
    extendLast_castSucc, cycleToLast_castSucc, Fin.val_last, Fin.val_castSucc, e, Function.comp_apply,
    sub_add_cancel, hs, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  rw [mul_assoc, mul_assoc]

theorem expFirstRow_of (h : PI.RowForm) : PI.ExpFirstRow := by
  intro A _ _ n t E hE a b u
  rw [h A n (t + 1) E hE a b u, rowFirst]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [h A n t E hE]

theorem expLastRow_of (h : PI.RowForm) : PI.ExpLastRow := by
  intro A _ _ n t E hE a b u
  rw [h A n (t + 1) E hE a b u, rowLast]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [h A n t E hE]

end PI.QmRowExpWork

namespace PI

theorem qmRowExp_of_rowForm (h : PI.QmRowForm) : PI.QmRowExp :=
  ⟨QmRowExpWork.expFirstRow_of h, QmRowExpWork.expLastRow_of h⟩

end PI
