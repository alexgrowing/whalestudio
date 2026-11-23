import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BorderMinorRotation.Development

open Finset Formalism.REAL

noncomputable section

namespace PI.UnitaryGroupMassFormula.QmBorderFull

open PI

theorem val_succAbove {t : ℕ} (p : Fin (t + 1)) (i : Fin t) :
    ((p.succAbove i : Fin (t + 1)) : ℕ) = if (i : ℕ) < (p : ℕ) then (i : ℕ) else (i : ℕ) + 1 := by
  by_cases h : (i : ℕ) < (p : ℕ)
  · rw [if_pos h]
    first
    | exact congrArg Fin.val (Fin.succAbove_of_castSucc_lt p i h)
    | (rw [Fin.succAbove_of_castSucc_lt p i (by simpa [Fin.lt_iff_val_lt_val] using h)]; simp)
  · rw [if_neg h]
    first
    | exact congrArg Fin.val (Fin.succAbove_of_le_castSucc p i (Nat.not_lt.mp h))
    | (rw [Fin.succAbove_of_le_castSucc p i (by simp [Fin.le_iff_val_le_val]; omega)]; simp)

theorem skip_one_eq_succAbove {t : ℕ} (p : Fin (t + 1)) (i : Fin t) : skip1 p i = p.succAbove i := by
  apply Fin.ext
  rw [val_succAbove]
  unfold skip1
  split_ifs with h1 h2 <;> first | rfl | (exact absurd h1 h2) | (exact absurd h2 h1) | omega

theorem comp_skip1 {α : Type*} {t : ℕ} (f : Fin (t + 1) → α) (p : Fin (t + 1)) :
    f ∘ skip1 p = f ∘ p.succAbove := by
  funext i
  exact congrArg f (skip_one_eq_succAbove p i)

theorem bS_castSucc {n m : ℕ} (v : Fin m → Fin n) (es : Fin n) : bS v es ∘ Fin.castSucc = v := by
  funext i
  first | simp [bS] | (simp only [Function.comp_apply, bS, Fin.snoc_castSucc])

theorem bS_last {n m : ℕ} (v : Fin m → Fin n) (es : Fin n) : bS v es (Fin.last m) = es := by
  first | simp [bS] | (simp only [bS, Fin.snoc_last])

theorem rot_cons {n k : ℕ} (e : Fin n) (W : Fin k → Fin n) :
    bE e W = Fin.snoc (α := fun _ => Fin n) W e ∘ (finRotate (k + 1)).symm := by
  first
  | (rw [Fin.snoc_eq_cons_rotate]; funext i; simp [bE])
  | (funext i; obtain ⟨j, rfl⟩ := (finRotate (k + 1)).surjective i; simp only [Function.comp_apply, Equiv.symm_apply_apply, bE]; induction j using Fin.lastCases <;> simp [finRotate_last, finRotate_succ_apply])

theorem rowE (hLR : ExpLastRow) {A : Type} [Ring A] [Algebra ℂ A] {n k : ℕ} (E : Fin n → Fin n → A)
    (hE : GlRel E) (e : Fin n) (W : Fin k → Fin n) (v : Fin (k + 1) → Fin n) (he : ∀ x, v x ≠ e) (u : ℂ) :
    qminor E (bE e W) v u =
      ∑ x : Fin (k + 1), (((-1 : ℤ) ^ (x : ℕ) : ℤ) : A) * (qminor E W (v ∘ x.succAbove) (u - 1) * E e (v x)) := by
  have hperm : ∀ (a : Fin (k + 1) → Fin n) (τ : Equiv.Perm (Fin (k + 1))),
      qminor E (a ∘ τ) v u = ((Equiv.Perm.sign τ : ℤ) : A) * qminor E a v u := by
    intro a τ
    unfold qminor
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun σ => ?_)
    have hτ : ((Equiv.Perm.sign τ : ℤ) : A) * ((Equiv.Perm.sign τ : ℤ) : A) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
    simp only [Equiv.coe_mulLeft, Equiv.Perm.mul_apply, Function.comp_apply, Equiv.Perm.sign_mul,
      Units.val_mul, Int.cast_mul]
    rw [← mul_assoc, ← mul_assoc, hτ, one_mul]
  have hs : ∀ x : Fin (k + 1), ((Equiv.Perm.sign (finRotate (k + 1)).symm : ℤ) : A) *
      (((-1 : ℤ) ^ (k + (x : ℕ)) : ℤ) : A) = (((-1 : ℤ) ^ (x : ℕ) : ℤ) : A) := by
    intro x
    rw [Equiv.Perm.sign_symm, sign_finRotate, ← Int.cast_mul, Units.val_pow_eq_pow_val, Units.val_neg,
      Units.val_one, ← pow_add]
    congr 1
    have hx : ∀ a : ℕ, a = 2 * k + (x : ℕ) → (-1 : ℤ) ^ a = (-1) ^ (x : ℕ) := by
      rintro a rfl
      rw [pow_add, pow_mul, neg_one_sq, one_pow, one_mul]
    exact hx _ (by omega)
  rw [rot_cons e W, hperm, hLR A n k E hE (Fin.snoc (α := fun _ => Fin n) W e) v u, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have h1 : (Fin.snoc (α := fun _ => Fin n) W e ∘ Fin.castSucc) = W := by
    funext i
    simp
  have h2 : Tm E u e (v x) = E e (v x) := by
    unfold Tm
    rw [if_neg (fun h => he x h.symm), zero_add]
  rw [← mul_assoc, hs x, h1, Fin.snoc_last, h2]

theorem rw_zero {n k : ℕ} (e es : Fin n) (v : Fin (k + 1) → Fin n) (w : Fin (k + 1)) :
    (bE e (bS v es) ∘ (w.castSucc.succ).succAbove) 0 = e := by
  first
  | simp [bE]
  | (show bE e (bS v es) ((w.castSucc.succ).succAbove 0) = e; rw [Fin.succ_succAbove_zero]; simp only [bE, Fin.cons_zero])

theorem rw_last {n k : ℕ} (e es : Fin n) (v : Fin (k + 1) → Fin n) (w : Fin (k + 1)) :
    (bE e (bS v es) ∘ (w.castSucc.succ).succAbove) (Fin.last (k + 1)) = es := by
  show bE e (bS v es) ((w.castSucc.succ).succAbove (Fin.last (k + 1))) = es
  have hw := w.isLt
  have h1 : (w.castSucc.succ).succAbove (Fin.last (k + 1)) = (Fin.last (k + 1)).succ :=
    Fin.ext (by simp only [val_succAbove, Fin.val_succ, Fin.coe_castSucc, Fin.val_last]; split_ifs <;> omega)
  rw [h1]
  simp only [bE, bS, Fin.cons_succ, Fin.snoc_last]

theorem rows_succ {n k : ℕ} (e es : Fin n) (v : Fin (k + 1) → Fin n) (w : Fin (k + 1))
    (h : k + 1 = k + 1 - 1 + 1) :
    (bE e (bS v es) ∘ (w.castSucc.succ).succAbove) ∘ Fin.succ =
      Fin.snoc (α := fun _ => Fin n) (v ∘ skip1 w) es ∘ Fin.cast h := by
  funext j
  simp only [Function.comp_apply]
  have hw := w.isLt
  refine Fin.lastCases ?_ (fun j => ?_) j
  · have h1 : (w.castSucc.succ).succAbove (Fin.last k).succ = (Fin.last (k + 1)).succ :=
      Fin.ext (by simp only [val_succAbove, Fin.val_succ, Fin.coe_castSucc, Fin.val_last]; split_ifs <;> omega)
    rw [h1]
    simp only [bE, bS, Fin.cons_succ, Fin.snoc_last, Fin.cast_last]
  · have hj := j.isLt
    have h2 : (w.castSucc.succ).succAbove (Fin.castSucc j).succ = (Fin.castSucc (w.succAbove j)).succ :=
      Fin.ext (by simp only [val_succAbove, Fin.val_succ, Fin.coe_castSucc]; split_ifs <;> omega)
    have h3 : Fin.cast h (Fin.castSucc j) = Fin.castSucc (Fin.cast (by omega) j : Fin (k + 1 - 1)) :=
      Fin.ext (by simp only [Fin.coe_cast, Fin.coe_castSucc])
    rw [h2, h3]
    simp only [bE, bS, Fin.cons_succ, Fin.snoc_castSucc, Function.comp_apply]
    rw [skip_one_eq_succAbove]
    rfl

theorem rows_last {n k : ℕ} (e es : Fin n) (v : Fin (k + 1) → Fin n) (w : Fin (k + 1)) :
    (bE e (bS v es) ∘ (w.castSucc.succ).succAbove) ∘ (Fin.last (k + 1)).succAbove = bE e (v ∘ w.succAbove) := by
  funext j
  have hw := w.isLt
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [Function.comp_apply]
    have h0 : (Fin.last (k + 1)).succAbove 0 = 0 := Fin.ext (by rw [val_succAbove]; simp)
    rw [h0, Fin.succ_succAbove_zero]
    simp only [bE, Fin.cons_zero]
  · simp only [Function.comp_apply]
    have hj := j.isLt
    have h1 : (w.castSucc.succ).succAbove ((Fin.last (k + 1)).succAbove j.succ) = (Fin.castSucc (w.succAbove j)).succ :=
      Fin.ext (by simp only [val_succAbove, Fin.val_succ, Fin.coe_castSucc, Fin.val_last]; split_ifs <;> omega)
    rw [h1]
    simp only [bE, bS, Fin.cons_succ, Fin.snoc_castSucc, Function.comp_apply]

theorem cmul {A : Type*} [Ring A] (s : ℤ) (x y : A) : x * ((s : A) * y) = (s : A) * (x * y) := by
  rw [← mul_assoc, ← mul_assoc, Int.cast_comm]

theorem bfMid_of (hLC : ExpLastCol) (hLR : ExpLastRow) (hX : BFCross) : BFMid := by
  intro A _ _ n m E e es v hE hB u w
  cases m with
  | zero => exact w.elim0
  | succ k =>
  have hv : ∀ x, v x ≠ e := hB.2.2.1
  have hves : ∀ x, v x ≠ es := hB.2.2.2
  have hL : bE e (bS v es) w.castSucc.succ = v w := by simp [bE, bS]
  have hT : Tm E u (v w) e = E (v w) e := by simp [Tm, hv w]
  rw [hL, show bE e (bS v es) 0 = e from rfl, hT, show bE e (bS v es) ∘ Fin.succ = bS v es from rfl]
  rw [hLC A n (k + 1) E _ (bS v es) (u - 1), Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp only [bS_castSucc, bS_last]
  rw [hX A n k E e es v hE hB u w]
  simp only [Fin.succAbove_zero, Fin.succ_last, rw_zero, rw_last, rows_last]
  rw [rows_succ e es v w (by omega), rowE hLR E hE e (v ∘ w.succAbove) v hv (u - 1)]
  simp only [comp_skip1]
  have hTe : Tm E (u - 1 - ((k + 1 : ℕ) : ℂ)) e es = E e es := by simp [Tm, hB.2.1]
  have hu2 : u - 1 - 1 = u - 2 := by ring
  have hu3 : u - 1 - ((k + 1 : ℕ) : ℂ) = u - ((k + 1 : ℕ) : ℂ) - 1 := by ring
  rw [hTe, hu2, hu3]
  have hcomm : ∀ x, E e (v x) * Tm E (u - ((k + 1 : ℕ) : ℂ) - 1) es es =
      Tm E (u - ((k + 1 : ℕ) : ℂ) - 1) es es * E e (v x) := fun x =>
    (tm_comm_E E hE _ es e (v x) hB.2.1.symm (hves x)).symm
  have he2 : ((-1 : ℤ) ^ (k + 1 + (k + 1))) = 1 := Even.neg_one_pow ⟨k + 1, rfl⟩
  have p0 : ∀ Q : A, (((-1 : ℤ) ^ ((w : ℕ) + 1) : ℤ) : A) * (E (v w) e * ((((-1 : ℤ) ^ (k + 1) : ℤ) : A) * (Q * E e es)))
      = (((-1 : ℤ) ^ ((w : ℕ) + 1 + (k + 1)) : ℤ) : A) * (E (v w) e * (Q * E e es)) := by
    intro Q; rw [cmul, ← mul_assoc, ← Int.cast_mul, ← pow_add]
  have pm : ∀ S : A, (((-1 : ℤ) ^ ((w : ℕ) + 1) : ℤ) : A) * (E (v w) e * ((((-1 : ℤ) ^ (w : ℕ) : ℤ) : A) * S))
      = -(E (v w) e * S) := by
    intro S
    rw [cmul, ← mul_assoc, ← Int.cast_mul, ← pow_add, Odd.neg_one_pow ⟨w, by ring⟩, Int.cast_neg, Int.cast_one,
      neg_one_mul]
  have pl : ∀ f : Fin (k + 1) → A,
      (((-1 : ℤ) ^ ((w : ℕ) + 1) : ℤ) : A) * (E (v w) e * ∑ x : Fin (k + 1), (((-1 : ℤ) ^ (x : ℕ) : ℤ) : A) * f x)
      = -∑ x : Fin (k + 1), (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) * (E (v w) e * f x) := by
    intro f
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [cmul, ← mul_assoc, ← Int.cast_mul, ← pow_add,
      show ((-1 : ℤ) ^ ((w : ℕ) + 1 + (x : ℕ))) = -(-1) ^ ((w : ℕ) + (x : ℕ)) by ring, Int.cast_neg, neg_mul]
  simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_zero, Fin.val_last, add_zero, Nat.succ_eq_add_one, he2,
    Int.cast_one, one_mul, Finset.sum_mul, mul_assoc, hcomm, mul_add]
  simp only [p0, pm, pl]
  simp only [Finset.mul_sum, mul_ite, mul_zero, cmul]
  abel

end PI.UnitaryGroupMassFormula.QmBorderFull
