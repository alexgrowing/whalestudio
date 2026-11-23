import Formalism.PeriodIntegrals.QmBorderFull
import Formalism.PeriodIntegrals.QmBorderES
import Formalism.PeriodIntegrals.QmColExp
import Formalism.PeriodIntegrals.QmRowExp
import Formalism.PeriodIntegrals.QmSkip
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds

open Finset Formalism.REAL

noncomputable section

namespace PI.UnitaryGroupMassFormula.QmBorderFull

open PI

def BFMid : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n m : ℕ) (E : Fin n → Fin n → A) (e es : Fin n) (v : Fin m → Fin n),
    GlRel E → IsBorder e es v → ∀ (u : ℂ) (w : Fin m),
      (((-1 : ℤ) ^ ((w.castSucc.succ : Fin (m + 1 + 1)) : ℕ) : ℤ) : A) *
        (Tm E u (bE e (bS v es) w.castSucc.succ) (bE e (bS v es) 0) *
          qminor E (bE e (bS v es) ∘ (w.castSucc.succ).succAbove) (bE e (bS v es) ∘ Fin.succ) (u - 1))
      = - (∑ x : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) *
            (E (v w) e * qminor E (v ∘ skip1 w) (v ∘ skip1 x) (u - 2) * Tm E (u - (m : ℂ) - 1) es es * E e (v x)))
        - (∑ w' : Fin m, ∑ x : Fin m, ∑ x' : Fin m,
            if w ≠ w' ∧ x ≠ x' then ((sg2 w w' * sg2 x x' : ℤ) : A) *
              (E (v w) e * E es (v x) *
                qminor E (v ∘ skip2 (min w w') (max w w')) (v ∘ skip2 (min x x') (max x x')) (u - 2) *
                E e (v x') * E (v w') es)
            else 0)
        + (((-1 : ℤ) ^ ((w : ℕ) + 1 + m) : ℤ) : A) *
            (E (v w) e * qminor E (Fin.snoc (α := fun _ => Fin n) (v ∘ skip1 w) es ∘ Fin.cast (by
                have := w.isLt; omega)) v (u - 1) * E e es)

def BFCross : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n k : ℕ) (E : Fin n → Fin n → A) (e es : Fin n) (v : Fin (k + 1) → Fin n),
    GlRel E → IsBorder e es v → ∀ (u : ℂ) (w : Fin (k + 1)),
      ∑ j : Fin k, (((-1 : ℤ) ^ ((k + 1) + ((j.castSucc.succ : Fin (k + 1 + 1)) : ℕ)) : ℤ) : A) *
        (qminor E ((bE e (bS v es) ∘ (w.castSucc.succ).succAbove) ∘ (j.castSucc.succ).succAbove) v (u - 1) *
          Tm E (u - 1 - ((k + 1 : ℕ) : ℂ)) ((bE e (bS v es) ∘ (w.castSucc.succ).succAbove) j.castSucc.succ) es)
      = (((-1 : ℤ) ^ (w : ℕ) : ℤ) : A) *
        ∑ w' : Fin (k + 1), ∑ x : Fin (k + 1), ∑ x' : Fin (k + 1),
            if w ≠ w' ∧ x ≠ x' then ((sg2 w w' * sg2 x x' : ℤ) : A) *
              (E es (v x) *
                qminor E (v ∘ skip2 (min w w') (max w w')) (v ∘ skip2 (min x x') (max x x')) (u - 2) *
                E e (v x') * E (v w') es)
            else 0

theorem tm_comm_E {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E)
    (u : ℂ) (e c d : Fin n) (h1 : e ≠ c) (h2 : d ≠ e) : Tm E u e e * E c d = E c d * Tm E u e e := by
  have h := hE e e c d
  rw [if_neg h1, if_neg h2, sub_zero, sub_eq_zero] at h
  rw [Formalism.REAL.Tm, if_pos rfl, add_mul, mul_add, Algebra.commutes, h]

theorem bL_last {n m : ℕ} (e es : Fin n) (v : Fin m → Fin n) :
    bE e (bS v es) ∘ (Fin.last (m + 1)).succAbove = bE e v := by
  funext i
  simp only [Function.comp_apply, Fin.succAbove_last]
  cases i using Fin.cases with
  | zero => simp [PI.bE]
  | succ j =>
    first
    | simp [PI.bE, PI.bS, ← Fin.succ_castSucc]
    | simp [PI.bE, PI.bS, Fin.cons_snoc_eq_snoc_cons]

private theorem mul_intCast_mul_eq_intCast_mul_mul {A : Type*} [Ring A] (s x : A) (z : ℤ) :
    s * ((z : A) * x) = (z : A) * (s * x) := by
  rw [← mul_assoc, ← mul_assoc, (Int.cast_commute z s).symm.eq]

theorem borderFull_of (hFC : ExpFirstCol) (hS : BorderS) (hM : BFMid) : BorderFull := by
  unfold PI.ExpFirstCol at hFC
  unfold PI.BorderS at hS
  unfold BFMid at hM
  unfold PI.BorderFull
  intro A _ _ n m E e es v hE hv u
  have hv2 : Function.Injective v ∧ e ≠ es ∧ (∀ j, v j ≠ e) ∧ ∀ j, v j ≠ es := hv
  obtain ⟨_, hne, hve, _⟩ := hv2
  have hmid := hM A n m E e es v hE hv u
  have hs : PI.bE e (PI.bS v es) ∘ Fin.succ = PI.bS v es := by
    funext i
    simp [PI.bE]
  have h0v : PI.bE e (PI.bS v es) 0 = e := by simp [PI.bE]
  have hLv : PI.bE e (PI.bS v es) (Fin.last m).succ = es := by simp [PI.bE, PI.bS]
  have hL : PI.bE e (PI.bS v es) ∘ ((Fin.last m).succ).succAbove = PI.bE e v := by
    rw [Fin.succ_last]
    exact bL_last e es v
  have hgen : Formalism.REAL.Tm E u es e = E es e := by
    simp [Formalism.REAL.Tm, hne.symm]
  have hu : u - 1 - (m : ℂ) = u - (m : ℂ) - 1 := by ring
  have hT2 : Formalism.REAL.Tm E u e e * ∑ w : Fin m, ∑ x : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) *
        (E es (v x) * Formalism.REAL.qminor E (v ∘ PI.skip1 w) (v ∘ PI.skip1 x) (u - 1) * E (v w) es)
      = ∑ w : Fin m, ∑ x : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) *
        (E es (v x) * Formalism.REAL.Tm E u e e * Formalism.REAL.qminor E (v ∘ PI.skip1 w) (v ∘ PI.skip1 x) (u - 1) * E (v w) es) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_intCast_mul_eq_intCast_mul_mul]
    congr 1
    rw [← mul_assoc, ← mul_assoc, tm_comm_E E hE u e es (v x) hne (hve x)]
  rw [hFC A n (m + 1) E (PI.bE e (PI.bS v es)) (PI.bE e (PI.bS v es)) u,
    Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  first
  | simp only [hmid]
  | rw [Finset.sum_congr rfl (fun w _ => hmid w)]
  rw [Fin.succAbove_zero, hs, h0v, hL, hLv, hgen]
  simp only [Fin.val_zero, pow_zero, Int.cast_one, one_mul, Fin.val_succ, Fin.val_last]
  rw [hS A n m E e es v hE hv (u - 1), hu, mul_sub (Formalism.REAL.Tm E u e e), hT2,
    ← mul_assoc (Formalism.REAL.Tm E u e e) (Formalism.REAL.qminor E v v (u - 1))]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  abel

end PI.UnitaryGroupMassFormula.QmBorderFull
