import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowFormPermutationSplit.Development
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd

open Finset Formalism.REAL

noncomputable section

namespace PI.UnitaryGroupMassFormula.QmRowForm

def opE {A : Type*} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) : Fin n → Fin n → Aᵐᵒᵖ :=
  fun a b => MulOpposite.op (E b a)

theorem glRel_opE {A : Type*} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E) : GlRel (opE E) := by
  intro a b c d
  have h := hE d c b a
  show MulOpposite.op (E b a) * MulOpposite.op (E d c) - MulOpposite.op (E d c) * MulOpposite.op (E b a) =
    (if b = c then MulOpposite.op (E d a) else 0) - (if d = a then MulOpposite.op (E b c) else 0)
  rw [← MulOpposite.op_mul, ← MulOpposite.op_mul, ← MulOpposite.op_sub, h]
  clear h hE
  split_ifs <;> simp_all

theorem Tm_opE {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (x : ℂ) (a b : Fin n) :
    Tm (opE E) x a b = MulOpposite.op (Tm E x b a) := by
  unfold Tm opE
  by_cases h : a = b
  · subst h
    simp
  · simp [h, Ne.symm h]

theorem reverse_ofFn' {α : Type*} {t : ℕ} (f : Fin t → α) :
    (List.ofFn f).reverse = List.ofFn (fun k => f (Fin.rev k)) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  rw [List.getElem_reverse, List.getElem_ofFn, List.getElem_ofFn]
  congr 1
  apply Fin.ext
  simp only [Fin.val_rev, List.length_ofFn]
  omega

def revConj (t : ℕ) : Equiv.Perm (Fin t) ≃ Equiv.Perm (Fin t) where
  toFun τ := Fin.revPerm * τ * Fin.revPerm
  invFun τ := Fin.revPerm * τ * Fin.revPerm
  left_inv τ := by ext k; simp
  right_inv τ := by ext k; simp

theorem sign_revConj {t : ℕ} (τ : Equiv.Perm (Fin t)) :
    Equiv.Perm.sign (revConj t τ) = Equiv.Perm.sign τ := by
  show Equiv.Perm.sign (Fin.revPerm * τ * Fin.revPerm) = _
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, mul_right_comm, Int.units_mul_self, one_mul]

theorem qminorRow_eq_unop {A : Type*} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin t → Fin n) (u : ℂ) :
    PI.qminorRow E a b u = MulOpposite.unop (qminor (opE E) (b ∘ Fin.rev) (a ∘ Fin.rev) u) := by
  unfold PI.qminorRow Formalism.REAL.qminor
  rw [show ∀ f : Equiv.Perm (Fin t) → Aᵐᵒᵖ, MulOpposite.unop (∑ σ, f σ) = ∑ σ, MulOpposite.unop (f σ) from
    fun f => map_sum (MulOpposite.opAddEquiv : A ≃+ Aᵐᵒᵖ).symm f Finset.univ]
  refine Fintype.sum_equiv (revConj t) _ _ (fun σ => ?_)
  rw [MulOpposite.unop_mul, MulOpposite.unop_intCast, sign_revConj, ← Int.cast_comm]
  congr 1
  rw [MulOpposite.unop_list_prod, List.map_ofFn, reverse_ofFn']
  congr 2
  funext k
  have hk : (((Fin.rev k : Fin t) : ℕ) : ℂ) = (t : ℂ) - 1 - ((k : ℕ) : ℂ) := by
    rw [Fin.val_rev, Nat.cast_sub (by have := k.isLt; omega)]
    push_cast
    ring
  have hσ : (revConj t σ) (Fin.rev k) = Fin.rev (σ k) := by
    show Fin.revPerm (σ (Fin.revPerm (Fin.rev k))) = Fin.rev (σ k)
    simp
  simp only [Function.comp_apply, Tm_opE, MulOpposite.unop_op, hσ, Fin.rev_rev, hk]
  congr 1
  ring

theorem qminorRow_skew {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E)
    (a b : Fin t → Fin n) (τ : Equiv.Perm (Fin t)) (u : ℂ) :
    PI.qminorRow E (a ∘ τ) b u = ((Equiv.Perm.sign τ : ℤ) : A) * PI.qminorRow E a b u := by
  have ha : a ∘ τ ∘ Fin.rev = (a ∘ Fin.rev) ∘ (revConj t τ) := by
    funext k; simp [revConj]
  rw [qminorRow_eq_unop, qminorRow_eq_unop, Function.comp_assoc, ha,
    quantumMinorColSkew_holds Aᵐᵒᵖ n t (opE E) (glRel_opE E hE), MulOpposite.unop_mul, MulOpposite.unop_intCast,
    sign_revConj, ((Int.cast_commute _ _).eq)]

theorem double_row_increasing : DblInc := by
  intro A _ _ n t E hE a b u
  have inner : ∀ σ : Equiv.Perm (Fin t),
      (∑ τ : Equiv.Perm (Fin t), (((Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign τ : ℤ) : ℤ) : A) *
        (List.ofFn fun k : Fin t => Tm E (u - (t : ℂ) + 1 + ((k : ℕ) : ℂ)) (a (σ k)) (b (τ k))).prod) =
        PI.qminorRow E a b u := by
    intro σ
    have e : PI.qminorRow E (a ∘ σ) b u = ∑ τ : Equiv.Perm (Fin t), ((Equiv.Perm.sign τ : ℤ) : A) *
        (List.ofFn fun k : Fin t => Tm E (u - (t : ℂ) + 1 + ((k : ℕ) : ℂ)) (a (σ k)) (b (τ k))).prod := rfl
    calc _ = ((Equiv.Perm.sign σ : ℤ) : A) * ∑ τ : Equiv.Perm (Fin t), ((Equiv.Perm.sign τ : ℤ) : A) *
          (List.ofFn fun k : Fin t => Tm E (u - (t : ℂ) + 1 + ((k : ℕ) : ℂ)) (a (σ k)) (b (τ k))).prod := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun τ _ => ?_
          rw [Int.cast_mul, mul_assoc]
      _ = PI.qminorRow E a b u := by
          rw [← e, qminorRow_skew E hE, ← mul_assoc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self,
            Units.val_one, Int.cast_one, one_mul]
  unfold doubleRowFormSum
  rw [Finset.sum_congr rfl (fun σ _ => inner σ), Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, Nat.cast_smul_eq_nsmul]

end PI.UnitaryGroupMassFormula.QmRowForm
