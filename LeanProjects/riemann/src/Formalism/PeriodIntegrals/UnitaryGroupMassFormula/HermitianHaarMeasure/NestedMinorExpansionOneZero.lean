import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.Development

open Matrix Finset

noncomputable section

namespace PI.QnHermHaar

open Formalism.REAL Formalism.FourierDecayAlt.Q

theorem valSuccAbove {n : ℕ} (p : Fin (n + 1)) (x : Fin n) :
    (p.succAbove x).val = if x.val < p.val then x.val else x.val + 1 := by
  unfold Fin.succAbove
  split_ifs with h1 h2 h2 <;> simp_all [Fin.lt_def]

theorem skip1Eq {t : ℕ} (i : Fin (t + 1)) (j : Fin t) : skip1 i j = i.succAbove j := by
  apply Fin.ext
  rw [valSuccAbove]
  unfold skip1
  split_ifs <;> simp

theorem skip1Fun {t : ℕ} (i : Fin (t + 1)) : (skip1 i : Fin t → Fin (t + 1)) = i.succAbove :=
  funext (skip1Eq i)

theorem valSkip2 {t : ℕ} (i i' : Fin t) (j : Fin (t - 2)) :
    (skip2 i i' j).val =
      if j.val < i.val then j.val else if j.val + 1 < i'.val then j.val + 1 else j.val + 2 := by
  unfold skip2
  split_ifs <;> rfl

theorem skip2Lt {t : ℕ} (i' : Fin (t + 2)) (k : Fin (t + 1)) (h : (k : ℕ) < (i' : ℕ)) :
    (skip2 (i'.succAbove k) i' : Fin t → Fin (t + 2)) = i'.succAbove ∘ k.succAbove := by
  funext x
  apply Fin.ext
  have hx := x.isLt
  simp only [Function.comp, valSuccAbove, valSkip2]
  split_ifs <;> omega

theorem skip2Gt {t : ℕ} (i' : Fin (t + 2)) (k : Fin (t + 1)) (h : ¬ (k : ℕ) < (i' : ℕ)) :
    (skip2 i' (i'.succAbove k) : Fin t → Fin (t + 2)) = i'.succAbove ∘ k.succAbove := by
  funext x
  apply Fin.ext
  have hx := x.isLt
  simp only [Function.comp, valSuccAbove, valSkip2]
  split_ifs <;> omega

theorem pairSum {A : Type*} [Ring A] [Algebra ℂ A] {t : ℕ} (c d : Fin (t + 2) → A)
    (G : (Fin t → Fin (t + 2)) → A) :
    ∑ i : Fin (t + 2), ∑ i' : Fin (t + 2),
        (if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ))) • ((c i * d i' - c i' * d i) * G (skip2 i i')) else 0) =
      ∑ i' : Fin (t + 2), ∑ k : Fin (t + 1),
        ((-1 : ℂ) ^ ((i' : ℕ) + (k : ℕ))) • (c (i'.succAbove k) * d i' * G (i'.succAbove ∘ k.succAbove)) := by
  have hR : ∀ i' : Fin (t + 2), ∑ k : Fin (t + 1),
      ((-1 : ℂ) ^ ((i' : ℕ) + (k : ℕ))) • (c (i'.succAbove k) * d i' * G (i'.succAbove ∘ k.succAbove)) =
        ∑ j : Fin (t + 2),
          ((if j < i' then ((-1 : ℂ) ^ ((j : ℕ) + (i' : ℕ))) • (c j * d i' * G (skip2 j i')) else 0) -
            (if i' < j then ((-1 : ℂ) ^ ((i' : ℕ) + (j : ℕ))) • (c j * d i' * G (skip2 i' j)) else 0)) := by
    intro i'
    conv_rhs => rw [Fin.sum_univ_succAbove _ i']
    simp only [lt_irrefl, if_false, sub_zero, zero_add]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases hk : (k : ℕ) < (i' : ℕ)
    · have hv : ((i'.succAbove k : Fin (t + 2)) : ℕ) = k := by rw [valSuccAbove, if_pos hk]
      have h1 : i'.succAbove k < i' := by rw [Fin.lt_def, hv]; exact hk
      have h2 : ¬ i' < i'.succAbove k := by rw [Fin.lt_def, hv]; omega
      rw [if_pos h1, if_neg h2, sub_zero, skip2Lt i' k hk, hv, add_comm (k : ℕ)]
    · have hv : ((i'.succAbove k : Fin (t + 2)) : ℕ) = k + 1 := by rw [valSuccAbove, if_neg hk]
      have h1 : ¬ i'.succAbove k < i' := by rw [Fin.lt_def, hv]; omega
      have h2 : i' < i'.succAbove k := by rw [Fin.lt_def, hv]; omega
      rw [if_pos h2, if_neg h1, zero_sub, skip2Gt i' k hk, hv, ← neg_smul]
      congr 1
      rw [← add_assoc, pow_succ]
      ring
  have hL : ∀ i i' : Fin (t + 2),
      (if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ))) • ((c i * d i' - c i' * d i) * G (skip2 i i')) else 0) =
        (if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ))) • (c i * d i' * G (skip2 i i')) else 0) -
          (if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ))) • (c i' * d i * G (skip2 i i')) else 0) := by
    intro i i'
    split_ifs <;> simp [sub_mul, smul_sub]
  simp only [hL, Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl (fun i' _ => hR i')]
  simp only [Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_comm

theorem intCastMul {A : Type*} [Ring A] [Algebra ℂ A] (z : ℤ) (X : A) : (z : A) * X = (z : ℂ) • X := by
  rw [Algebra.smul_def, map_intCast]

theorem eSq (e : ℤˣ) : ((e : ℤ) : ℂ) * ((e : ℤ) : ℂ) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp

theorem starE (e : ℤˣ) : star (((e : ℤ) : ℂ)) = ((e : ℤ) : ℂ) := star_intCast _

theorem prodSA {t : ℕ} (ε : Fin (t + 1) → ℤˣ) (i : Fin (t + 1)) :
    ∏ k, ε (i.succAbove k) = ε i * ∏ k, ε k := by
  rw [Fin.prod_univ_succAbove ε i, ← mul_assoc, Int.units_mul_self, one_mul]

theorem prodSA2 {t : ℕ} (ε : Fin (t + 2) → ℤˣ) (i : Fin (t + 2)) (k : Fin (t + 1)) :
    ∏ x, ε (i.succAbove (k.succAbove x)) = ε i * ε (i.succAbove k) * ∏ k, ε k := by
  have h := prodSA (fun y => ε (i.succAbove y)) k
  rw [h, prodSA ε i, ← mul_assoc, mul_comm (ε (i.succAbove k)) (ε i)]

theorem star1 (hSM : StarMinor) {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {t : ℕ}
    (E : Fin (t + 1) → Fin (t + 1) → A) (ε : Fin (t + 1) → ℤˣ) (hGl : GlRel E)
    (hE : ∀ a b, star (E a b) = (((ε a * ε b : ℤˣ) : ℤ) : A) * E b a) (i j : Fin (t + 1)) (w : ℂ) :
    star (qminor E i.succAbove j.succAbove w) =
      (((ε i : ℤ) : ℂ) * ((ε j : ℤ) : ℂ)) • qminor E j.succAbove i.succAbove (star w) := by
  rw [hSM A (t + 1) t E ε hGl hE i.succAbove j.succAbove w, intCastMul, prodSA, prodSA,
    mul_mul_mul_comm, Int.units_mul_self, mul_one]
  push_cast
  rfl

theorem star2 (hSM : StarMinor) {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {t : ℕ}
    (E : Fin (t + 2) → Fin (t + 2) → A) (ε : Fin (t + 2) → ℤˣ) (hGl : GlRel E)
    (hE : ∀ a b, star (E a b) = (((ε a * ε b : ℤˣ) : ℤ) : A) * E b a) (i : Fin (t + 2)) (k : Fin (t + 1))
    (j : Fin (t + 2)) (l : Fin (t + 1)) (w : ℂ) :
    star (qminor E (i.succAbove ∘ k.succAbove) (j.succAbove ∘ l.succAbove) w) =
      (((ε i : ℤ) : ℂ) * ((ε (i.succAbove k) : ℤ) : ℂ) * (((ε j : ℤ) : ℂ) * ((ε (j.succAbove l) : ℤ) : ℂ))) •
        qminor E (j.succAbove ∘ l.succAbove) (i.succAbove ∘ k.succAbove) (star w) := by
  rw [hSM A (t + 2) t E ε hGl hE _ _ w, intCastMul]
  simp only [Function.comp_apply]
  rw [prodSA2, prodSA2, mul_mul_mul_comm, Int.units_mul_self, mul_one]
  push_cast
  rfl

theorem mvC (hMV : MoveVec) {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A) (y : Fin n → A)
    (hGl : GlRel E) (hL : ∀ a b c, E a b * y c - y c * E a b = if a = c then -y b else 0)
    (hC : ∀ a b, y a * y b = y b * y a) (a : Fin t → Fin n) (b : Fin (t + 1) → Fin n) (w : ℂ) :
    ∑ j : Fin (t + 1), ((-1 : ℂ) ^ (j : ℕ)) • (y (b j) * qminor E a (b ∘ j.succAbove) w) =
      ∑ j : Fin (t + 1), ((-1 : ℂ) ^ (j : ℕ)) • (qminor E a (b ∘ j.succAbove) (w - 1) * y (b j)) := by
  have h := hMV A n t E y hGl hL hC a b w
  simp only [intCastMul] at h
  push_cast at h
  exact h

theorem nested_minor_expansion_zero_one {A : Type*} [Ring A] [Algebra ℂ A] {t : ℕ} (E : Fin (t + 1) → Fin (t + 1) → A)
    (Y Yb : Fin (t + 1) → A) (x xb : Fin (t + 1) → ℂ) (u : ℂ) :
    tA E Y Yb x xb u 0 1 = -∑ i : Fin (t + 1), ∑ j : Fin (t + 1),
      ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * x j) • (Yb i * qminor E i.succAbove j.succAbove (u - 1)) := by
  simp only [tA, skip1Fun]

theorem nested_minor_expansion_one_zero {A : Type*} [Ring A] [Algebra ℂ A] {t : ℕ} (E : Fin (t + 1) → Fin (t + 1) → A)
    (Y Yb : Fin (t + 1) → A) (x xb : Fin (t + 1) → ℂ) (u : ℂ) :
    tA E Y Yb x xb u 1 0 = -∑ i : Fin (t + 1), ∑ j : Fin (t + 1),
      ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * xb i) • (Y j * qminor E i.succAbove j.succAbove u) := by
  simp only [tA, skip1Fun]

theorem star_transfer_diagonal_zero (hSM : StarMinor) {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {m : ℕ}
    (E : Fin m → Fin m → A) (Y Yb : Fin m → A) (x xb : Fin m → ℂ) (ε : Fin m → ℤˣ) (hGl : GlRel E)
    (hE : ∀ a b, star (E a b) = (((ε a * ε b : ℤˣ) : ℤ) : A) * E b a) (u : ℂ) :
    star (tA E Y Yb x xb u 0 0) = tA E Y Yb x xb (star u) 0 0 := by
  show star (qminor E id id u) = qminor E id id (star u)
  rw [hSM A m m E ε hGl hE id id u, Int.units_mul_self]
  simp

theorem star_transfer_zero_one (hSM : StarMinor) (hMV : MoveVec) {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]
    [StarModule ℂ A] {m : ℕ}
    (E : Fin m → Fin m → A) (Y Yb : Fin m → A) (x xb : Fin m → ℂ) (ε : Fin m → ℤˣ) (hGl : GlRel E)
    (hE : ∀ a b, star (E a b) = (((ε a * ε b : ℤˣ) : ℤ) : A) * E b a)
    (hYY : ∀ a b, Y a * Y b = Y b * Y a)
    (hLY : ∀ a b c, E a b * Y c - Y c * E a b = if a = c then -Y b else 0)
    (hYb : ∀ c, Yb c = ((ε c : ℤ) : ℂ) • star (Y c)) (hxb : ∀ c, xb c = ((ε c : ℤ) : ℂ) * star (x c))
    (u : ℂ) :
    star (tA E Y Yb x xb u 0 1) = tA E Y Yb x xb (star u) 1 0 := by
  cases m with
  | zero => simp [tA]
  | succ t =>
    rw [nested_minor_expansion_zero_one, nested_minor_expansion_one_zero]
    have hterm : ∀ i j : Fin (t + 1),
        star (((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * x j) • (Yb i * qminor E i.succAbove j.succAbove (u - 1))) =
          ((-1 : ℂ) ^ ((j : ℕ) + (i : ℕ)) * xb j) •
            (qminor E j.succAbove i.succAbove (star u - 1) * Y i) := by
      intro i j
      rw [star_smul, star_mul (Yb i), star1 hSM E ε hGl hE, hYb i, star_smul, star_star, starE, hxb j, star_mul,
        star_pow, star_neg, star_one, star_sub, star_one]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
      congr 1
      have h1 := eSq (ε i)
      linear_combination ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * star (x j) * ((ε j : ℤ) : ℂ)) * h1
    simp only [star_neg, star_sum, hterm]
    rw [Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl (fun a _ => ?_)
    have hmv := mvC hMV E Y hGl hLY hYY a.succAbove id (star u)
    simp only [Function.id_comp, id] at hmv
    have e1 : ∀ i : Fin (t + 1), ((-1 : ℂ) ^ ((a : ℕ) + (i : ℕ)) * xb a) • (qminor E a.succAbove i.succAbove (star u - 1) * Y i)
        = ((-1 : ℂ) ^ (a : ℕ) * xb a) • (((-1 : ℂ) ^ (i : ℕ)) • (qminor E a.succAbove i.succAbove (star u - 1) * Y i)) := by
      intro i; rw [smul_smul, pow_add]; ring_nf
    have e2 : ∀ j : Fin (t + 1), ((-1 : ℂ) ^ ((a : ℕ) + (j : ℕ)) * xb a) • (Y j * qminor E a.succAbove j.succAbove (star u))
        = ((-1 : ℂ) ^ (a : ℕ) * xb a) • (((-1 : ℂ) ^ (j : ℕ)) • (Y j * qminor E a.succAbove j.succAbove (star u))) := by
      intro j; rw [smul_smul, pow_add]; ring_nf
    simp only [e1, e2, ← Finset.smul_sum, hmv]

end PI.QnHermHaar
