import Formalism.PeriodIntegrals.QmColExp
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorCommutatorQuantumDet

open Finset

noncomputable section

namespace PI.QmColExpWork

open Formalism.REAL

def cyc0 (m : ℕ) (j : Fin (m + 1)) : Equiv.Perm (Fin (m + 1)) := (Fin.cycleRange j).symm

theorem cycle_perm_zero (m : ℕ) (j : Fin (m + 1)) : cyc0 m j 0 = j := by
  unfold cyc0
  first
  | exact Fin.cycleRange_symm_zero j
  | rw [Equiv.symm_apply_eq, Fin.cycleRange_self]

theorem cycle_perm_succ (m : ℕ) (j : Fin (m + 1)) (k : Fin m) : cyc0 m j k.succ = j.succAbove k := by
  unfold cyc0
  first
  | exact Fin.cycleRange_symm_succ j k
  | rw [Equiv.symm_apply_eq, Fin.cycleRange_succAbove]

theorem sign_cycle_perm (m : ℕ) (j : Fin (m + 1)) :
    Equiv.Perm.sign (cyc0 m j) = (-1) ^ (j : ℕ) := by
  unfold cyc0
  rw [Equiv.Perm.sign_symm, Fin.sign_cycleRange]

def ext0 {m : ℕ} (τ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 1)) :=
  ((finSuccEquiv m).trans (Equiv.optionCongr τ)).trans (finSuccEquiv m).symm

theorem matrixExtendByZero_zero {m : ℕ} (τ : Equiv.Perm (Fin m)) : ext0 τ 0 = 0 := by
  simp [ext0]

theorem extByZero_succ {m : ℕ} (τ : Equiv.Perm (Fin m)) (k : Fin m) : ext0 τ k.succ = (τ k).succ := by
  simp [ext0]

theorem sign_extend_perm {m : ℕ} (τ : Equiv.Perm (Fin m)) :
    Equiv.Perm.sign (ext0 τ) = Equiv.Perm.sign τ := by
  unfold ext0
  first
  | exact (Equiv.Perm.sign_symm_trans_trans _ _).trans (Equiv.optionCongr_sign τ)
  | exact (Equiv.Perm.sign_permCongr _ _).trans (Equiv.optionCongr_sign τ)

def phi0 (m : ℕ) (p : Fin (m + 1) × Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 1)) :=
  cyc0 m p.1 * ext0 p.2

theorem firstColumnSplit_bijective (m : ℕ) : Function.Bijective (phi0 m) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩
  · rintro ⟨j, τ⟩ ⟨j', τ'⟩ h
    have h0 : j = j' := by
      have := congrArg (fun σ : Equiv.Perm (Fin (m + 1)) => σ 0) h
      simpa [phi0, Equiv.Perm.mul_apply, matrixExtendByZero_zero, cycle_perm_zero] using this
    subst h0
    have h1 : ext0 τ = ext0 τ' :=
      mul_left_cancel (show cyc0 m j * ext0 τ = cyc0 m j * ext0 τ' from h)
    have h2 : τ = τ' := by
      refine Equiv.ext fun k => ?_
      have := congrArg (fun σ : Equiv.Perm (Fin (m + 1)) => σ k.succ) h1
      simpa [extByZero_succ] using this
    subst h2
    rfl
  · simp [Fintype.card_perm, Fintype.card_prod, Fintype.card_fin, Nat.factorial_succ]

theorem expFirst {A : Type*} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin (m + 1) → Fin n) (u : ℂ) :
    qminor E a b u = ∑ j : Fin (m + 1), (((-1 : ℤ) ^ (j : ℕ) : ℤ) : A) *
      (Tm E u (a j) (b 0) * qminor E (a ∘ j.succAbove) (b ∘ Fin.succ) (u - 1)) := by
  unfold qminor
  conv_lhs => rw [← (firstColumnSplit_bijective m).sum_comp]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hs : Equiv.Perm.sign (phi0 m (j, τ)) = (-1) ^ (j : ℕ) * Equiv.Perm.sign τ := by
    simp only [phi0, Equiv.Perm.sign_mul, sign_cycle_perm, sign_extend_perm]
  have h0 : phi0 m (j, τ) 0 = j := by
    simp only [phi0, Equiv.Perm.mul_apply, matrixExtendByZero_zero, cycle_perm_zero]
  have hk : ∀ k : Fin m, phi0 m (j, τ) k.succ = j.succAbove (τ k) := by
    intro k
    simp only [phi0, Equiv.Perm.mul_apply, extByZero_succ, cycle_perm_succ]
  have hu : ∀ k : Fin m, u - (((k.succ : Fin (m + 1)) : ℕ) : ℂ) = u - 1 - ((k : ℕ) : ℂ) := by
    intro k
    rw [Fin.val_succ, Nat.cast_succ]
    ring
  simp only [hs, List.ofFn_succ, List.prod_cons, h0, hk, hu, Function.comp_apply,
    Fin.val_zero, Nat.cast_zero, sub_zero]
  simp only [← zsmul_eq_mul, smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  first
  | (push_cast; ring)
  | push_cast
  | simp

theorem expLast {A : Type*} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin (m + 1) → Fin n) (u : ℂ) :
    qminor E a b u = ∑ j : Fin (m + 1), (((-1 : ℤ) ^ (m + (j : ℕ)) : ℤ) : A) *
      (qminor E (a ∘ j.succAbove) (b ∘ Fin.castSucc) u * Tm E (u - (m : ℂ)) (a j) (b (Fin.last m))) := by
  unfold qminor
  have hr : ∀ k : Fin m, finRotate (m + 1) k.castSucc = k.succ := by
    intro k
    first
    | exact finRotate_castSucc k
    | exact Fin.ext (by rw [coe_finRotate_of_ne_last (Fin.castSucc_lt_last k).ne, Fin.coe_castSucc, Fin.val_succ])
  have hbij : Function.Bijective
      (fun p : Fin (m + 1) × Equiv.Perm (Fin m) => phi0 m p * finRotate (m + 1)) :=
    (Equiv.mulRight (finRotate (m + 1))).bijective.comp (firstColumnSplit_bijective m)
  conv_lhs => rw [← hbij.sum_comp]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hs : Equiv.Perm.sign (phi0 m (j, τ) * finRotate (m + 1)) =
      (-1) ^ (j : ℕ) * Equiv.Perm.sign τ * (-1) ^ m := by
    clear hr hbij
    have h1 : Equiv.Perm.sign (phi0 m (j, τ)) = (-1) ^ (j : ℕ) * Equiv.Perm.sign τ := by
      simp only [phi0, Equiv.Perm.sign_mul, sign_cycle_perm, sign_extend_perm]
    rw [Equiv.Perm.sign_mul, h1, sign_finRotate]
    all_goals first | rfl | exact rfl | simp [mul_comm, mul_left_comm, mul_assoc]
  have hl : (phi0 m (j, τ) * finRotate (m + 1)) (Fin.last m) = j := by
    simp only [Equiv.Perm.mul_apply, finRotate_last, phi0, matrixExtendByZero_zero, cycle_perm_zero]
  have hk : ∀ k : Fin m, (phi0 m (j, τ) * finRotate (m + 1)) k.castSucc = j.succAbove (τ k) := by
    intro k
    simp only [Equiv.Perm.mul_apply, hr, phi0, extByZero_succ, cycle_perm_succ]
  simp only [hs, List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_cons,
    List.prod_nil, mul_one, hl, hk, Function.comp_apply, Fin.val_last, Fin.coe_castSucc]
  simp only [← zsmul_eq_mul, smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  first
  | (push_cast; ring)
  | push_cast
  | simp

theorem expFirstCol : PI.ExpFirstCol := fun _ _ _ _ _ E a b u => expFirst E a b u

theorem expLastCol : PI.ExpLastCol := fun _ _ _ _ _ E a b u => expLast E a b u

end PI.QmColExpWork
