import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

open Formalism.REAL

noncomputable section

namespace GlobalTheory.CompanionTheory.CapelliAntipode

theorem unop_ofFn_prod {A : Type*} [Ring A] : ∀ {t : ℕ} (f : Fin t → Aᵐᵒᵖ),
    MulOpposite.unop (List.ofFn f).prod = (List.ofFn fun i => MulOpposite.unop (f i.rev)).prod
  | 0, f => by simp
  | t + 1, f => by
    rw [List.ofFn_succ, List.prod_cons, MulOpposite.unop_mul, unop_ofFn_prod (fun i => f i.succ),
      List.ofFn_succ' (fun i : Fin (t + 1) => MulOpposite.unop (f i.rev)), List.prod_concat]
    simp only [Fin.rev_last, Fin.rev_castSucc]

theorem ofFn_prod_neg {A : Type*} [Ring A] [Algebra ℂ A] : ∀ {t : ℕ} (g : Fin t → A),
    (List.ofFn fun k => -g k).prod = ((-1 : ℂ) ^ t) • (List.ofFn g).prod
  | 0, g => by simp
  | t + 1, g => by
    rw [List.ofFn_succ, List.prod_cons, ofFn_prod_neg (fun k => g k.succ), List.ofFn_succ (f := g),
      List.prod_cons, pow_succ, mul_comm, mul_smul, neg_mul, mul_smul_comm, neg_one_smul]

theorem Tm_op_neg {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (X : Fin n → Fin n → A) (w : ℂ)
    (i j : Fin n) :
    Tm (fun i j => MulOpposite.op (-X i j)) w i j = MulOpposite.op (-(Tm X (-w) i j)) := by
  unfold Tm
  by_cases h : i = j
  · simp [h, MulOpposite.algebraMap_apply, add_comm]
  · simp [h]

theorem arg_rev {t : ℕ} (v : ℂ) (j : Fin t) :
    -(v - (((Fin.rev j : Fin t) : ℕ) : ℂ)) = ((t : ℂ) - 1 - v) - ((j : ℕ) : ℂ) := by
  have hj := j.isLt
  rw [Fin.val_rev, Nat.cast_sub (by omega : (j : ℕ) + 1 ≤ t)]
  push_cast
  ring

theorem unop_term {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (X : Fin n → Fin n → A) (v : ℂ)
    (σ : Equiv.Perm (Fin n)) :
    MulOpposite.unop ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : Aᵐᵒᵖ) *
        (List.ofFn fun k : Fin n =>
          Tm (fun i j => MulOpposite.op (-X i j)) (v - ((k : ℕ) : ℂ)) (id (σ k)) (id k)).prod) =
      ((-1 : ℂ) ^ n) • ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : A) *
        (List.ofFn fun j : Fin n =>
          Tm X (((n : ℂ) - 1 - v) - ((j : ℕ) : ℂ)) (σ j.rev) j.rev).prod) := by
  rw [MulOpposite.unop_mul, MulOpposite.unop_intCast, unop_ofFn_prod]
  simp only [Tm_op_neg, MulOpposite.unop_op, id, arg_rev]
  rw [ofFn_prod_neg, smul_mul_assoc, ← Int.cast_comm]

theorem qminor_id_rev {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (X : Fin n → Fin n → A) (w : ℂ) :
    qminor X id (id ∘ (Fin.revPerm : Equiv.Perm (Fin n))) w =
      (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤˣ) : ℤ) : A) *
        ∑ σ : Equiv.Perm (Fin n), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : A) *
          (List.ofFn fun j : Fin n => Tm X (w - ((j : ℕ) : ℂ)) (σ j.rev) j.rev).prod := by
  unfold qminor
  rw [Finset.mul_sum]
  refine (Fintype.sum_equiv (Equiv.mulRight (Fin.revPerm : Equiv.Perm (Fin n))) _ _ (fun σ => ?_)).symm
  simp only [Equiv.coe_mulRight, Equiv.Perm.sign_mul, Equiv.Perm.mul_apply, Fin.revPerm_apply,
    Function.comp_apply, id, Units.val_mul, Int.cast_mul]
  rw [← mul_assoc, Int.cast_comm]

theorem unop_qdet_op_neg (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A)
    (hX : GlRel X) (v : ℂ) :
    MulOpposite.unop (qdet (fun i j => MulOpposite.op (-X i j)) v) =
      ((-1 : ℂ) ^ n) • qdet X ((n : ℂ) - 1 - v) := by
  have hs := quantumMinorColSkew_holds A n n X hX id id (Fin.revPerm : Equiv.Perm (Fin n)) ((n : ℂ) - 1 - v)
  rw [qminor_id_rev] at hs
  have hu : (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤˣ) : ℤ) : A) *
      (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤˣ) : ℤ) : A) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have h2 := congrArg (fun x => (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤˣ) : ℤ) : A) * x) hs
  simp only [← mul_assoc, hu, one_mul] at h2
  have h3 : qdet X ((n : ℂ) - 1 - v) = _ := h2.symm
  rw [h3]
  unfold qdet qminor
  rw [Finset.unop_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun σ _ => unop_term X v σ

end GlobalTheory.CompanionTheory.CapelliAntipode
