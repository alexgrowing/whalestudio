import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.NestedMinorExpansionOneZero

open Matrix Finset

noncomputable section

namespace PI.QnHermHaar

open Formalism.REAL Formalism.FourierDecayAlt.Q

theorem mulAM {A : Type*} [Ring A] [Algebra ℂ A] (X : A) (c : ℂ) : X * algebraMap ℂ A c = c • X := by
  rw [Algebra.smul_def, Algebra.commutes]

theorem swap4a {A : Type*} [AddCommMonoid A] {p q : ℕ} (F : Fin p → Fin q → Fin p → Fin q → A) :
    ∑ i, ∑ k, ∑ j, ∑ l, F i k j l = ∑ j, ∑ i, ∑ l, ∑ k, F i k j l := by
  calc ∑ i, ∑ k, ∑ j, ∑ l, F i k j l = ∑ i, ∑ j, ∑ k, ∑ l, F i k j l :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ l, ∑ k, F i k j l :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ j, ∑ i, ∑ l, ∑ k, F i k j l := Finset.sum_comm

theorem swap4b {A : Type*} [AddCommMonoid A] {p q : ℕ} (F : Fin p → Fin q → Fin p → Fin q → A) :
    ∑ i, ∑ k, ∑ j, ∑ l, F i k j l = ∑ i, ∑ j, ∑ k, ∑ l, F i k j l :=
  Finset.sum_congr rfl fun i _ => Finset.sum_comm

theorem nested_minor_expansion_one_one {A : Type*} [Ring A] [Algebra ℂ A] {t : ℕ} (E : Fin (t + 2) → Fin (t + 2) → A)
    (Y Yb : Fin (t + 2) → A) (x xb : Fin (t + 2) → ℂ) (u : ℂ) :
    tA E Y Yb x xb u 1 1 = -∑ i : Fin (t + 2), ∑ k : Fin (t + 1), ∑ j : Fin (t + 2), ∑ l : Fin (t + 1),
      ((-1 : ℂ) ^ ((i : ℕ) + (k : ℕ)) * (-1 : ℂ) ^ ((j : ℕ) + (l : ℕ)) * xb i * x j) •
        (Yb (i.succAbove k) * Y (j.succAbove l) *
          qminor E (i.succAbove ∘ k.succAbove) (j.succAbove ∘ l.succAbove) (u - 1)) := by
  simp only [tA]
  congr 1

  set G : (Fin t → Fin (t + 2)) → A := fun s => ∑ j : Fin (t + 2), ∑ j' : Fin (t + 2),
    (if j < j' then ((-1 : ℂ) ^ ((j : ℕ) + (j' : ℕ))) •
      ((Y j * algebraMap ℂ A (x j') - Y j' * algebraMap ℂ A (x j)) * qminor E s (skip2 j j') (u - 1)) else 0)
    with hG
  have h1 : ∀ i i' : Fin (t + 2), (∑ j : Fin (t + 2), ∑ j' : Fin (t + 2),
      if i < i' ∧ j < j' then
        ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ) + (j : ℕ) + (j' : ℕ))) •
          ((Yb i * algebraMap ℂ A (xb i') - Yb i' * algebraMap ℂ A (xb i)) *
            (Y j * algebraMap ℂ A (x j') - Y j' * algebraMap ℂ A (x j)) *
            qminor E (skip2 i i') (skip2 j j') (u - 1))
      else 0) =
      if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ))) •
        ((Yb i * algebraMap ℂ A (xb i') - Yb i' * algebraMap ℂ A (xb i)) * G (skip2 i i')) else 0 := by
    intro i i'
    by_cases hi : i < i'
    · simp only [hi, true_and, if_true, hG, Finset.mul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun j' _ => ?_))
      split_ifs
      · rw [mul_smul_comm, smul_smul, ← pow_add, mul_assoc]
        congr 2
        ring
      · simp
    · simp [hi]
  simp only [h1]
  have hp := pairSum Yb (fun i => algebraMap ℂ A (xb i)) G
  try simp only at hp
  rw [hp]
  have hq : ∀ s : Fin t → Fin (t + 2), G s = ∑ j : Fin (t + 2), ∑ l : Fin (t + 1),
      ((-1 : ℂ) ^ ((j : ℕ) + (l : ℕ))) • (Y (j.succAbove l) * algebraMap ℂ A (x j) *
        qminor E s (j.succAbove ∘ l.succAbove) (u - 1)) := by
    intro s
    have h := pairSum Y (fun j => algebraMap ℂ A (x j)) (fun s' => qminor E s s' (u - 1))
    rw [hG]
    exact h
  simp only [hq, Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ =>
    Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => ?_))))
  simp only [mulAM, smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
  congr 1
  ring

theorem transfer_commutator_one_one (hMV : MoveVec) (hMC : MoveCov) {A : Type} [Ring A] [Algebra ℂ A] {t : ℕ}
    (E : Fin (t + 2) → Fin (t + 2) → A) (Y Yb : Fin (t + 2) → A) (hGl : GlRel E)
    (hYY : ∀ a b, Y a * Y b = Y b * Y a) (hYbYb : ∀ a b, Yb a * Yb b = Yb b * Yb a)
    (hLY : ∀ a b c, E a b * Y c - Y c * E a b = if a = c then -Y b else 0)
    (hLYb : ∀ a b c, E a b * Yb c - Yb c * E a b = if b = c then Yb a else 0)
    (a b : Fin (t + 2)) (w : ℂ) :
    ∑ k : Fin (t + 1), ∑ l : Fin (t + 1), ((-1 : ℂ) ^ (k : ℕ) * (-1 : ℂ) ^ (l : ℕ)) •
        (qminor E (a.succAbove ∘ k.succAbove) (b.succAbove ∘ l.succAbove) w * Yb (a.succAbove k) *
          Y (b.succAbove l)) =
      ∑ k : Fin (t + 1), ∑ l : Fin (t + 1), ((-1 : ℂ) ^ (k : ℕ) * (-1 : ℂ) ^ (l : ℕ)) •
        (Yb (a.succAbove k) * Y (b.succAbove l) *
          qminor E (a.succAbove ∘ k.succAbove) (b.succAbove ∘ l.succAbove) w) := by
  have hz : ∀ (p : ℕ) (X : A), (((-1 : ℤ) ^ p : ℤ) : A) * X = ((-1 : ℂ) ^ p) • X := by
    intro p X
    rw [← zsmul_eq_mul, ← Int.cast_smul_eq_zsmul ℂ]
    push_cast
    try rfl
  have MC := fun l : Fin (t + 1) =>
    hMC A (t + 2) t E Yb hGl hLYb hYbYb a.succAbove (b.succAbove ∘ l.succAbove) w
  have MV := fun k : Fin (t + 1) =>
    hMV A (t + 2) t E Y hGl hLY hYY (a.succAbove ∘ k.succAbove) b.succAbove w
  simp only [hz] at MC MV
  have h1 : ∀ l : Fin (t + 1), ∑ k : Fin (t + 1), ((-1 : ℂ) ^ (k : ℕ) * (-1 : ℂ) ^ (l : ℕ)) •
      (qminor E (a.succAbove ∘ k.succAbove) (b.succAbove ∘ l.succAbove) w *
        (Yb (a.succAbove k) * Y (b.succAbove l))) =
      ∑ k : Fin (t + 1), ((-1 : ℂ) ^ (k : ℕ) * (-1 : ℂ) ^ (l : ℕ)) •
      (Yb (a.succAbove k) *
        (qminor E (a.succAbove ∘ k.succAbove) (b.succAbove ∘ l.succAbove) (w - 1) * Y (b.succAbove l))) := by
    intro l
    have e := congrArg (fun S => ((-1 : ℂ) ^ (l : ℕ)) • (S * Y (b.succAbove l))) (MC l)
    simp only [Finset.sum_mul, Finset.smul_sum, smul_mul_assoc, smul_smul, mul_assoc,
      mul_comm ((-1 : ℂ) ^ (l : ℕ))] at e
    exact e.symm
  have h2 : ∀ k : Fin (t + 1), ∑ l : Fin (t + 1), ((-1 : ℂ) ^ (k : ℕ) * (-1 : ℂ) ^ (l : ℕ)) •
      (Yb (a.succAbove k) *
        (qminor E (a.succAbove ∘ k.succAbove) (b.succAbove ∘ l.succAbove) (w - 1) * Y (b.succAbove l))) =
      ∑ l : Fin (t + 1), ((-1 : ℂ) ^ (k : ℕ) * (-1 : ℂ) ^ (l : ℕ)) •
      (Yb (a.succAbove k) * (Y (b.succAbove l) *
        qminor E (a.succAbove ∘ k.succAbove) (b.succAbove ∘ l.succAbove) w)) := by
    intro k
    have e := congrArg (fun S => ((-1 : ℂ) ^ (k : ℕ)) • (Yb (a.succAbove k) * S)) (MV k)
    simp only [Finset.mul_sum, Finset.smul_sum, mul_smul_comm, smul_smul] at e
    exact e.symm
  simp only [mul_assoc]
  rw [Finset.sum_comm, Finset.sum_congr rfl fun l _ => h1 l, Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => h2 k

theorem starY {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {m : ℕ} (Y Yb : Fin m → A)
    (ε : Fin m → ℤˣ) (hYb : ∀ c, Yb c = ((ε c : ℤ) : ℂ) • star (Y c)) (c : Fin m) :
    star (Y c) = ((ε c : ℤ) : ℂ) • Yb c := by
  have he : ((ε c : ℤ) : ℂ) * ((ε c : ℤ) : ℂ) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  rw [hYb c, smul_smul, he, one_smul]

theorem starYb {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {m : ℕ} (Y Yb : Fin m → A)
    (ε : Fin m → ℤˣ) (hYb : ∀ c, Yb c = ((ε c : ℤ) : ℂ) • star (Y c)) (c : Fin m) :
    star (Yb c) = ((ε c : ℤ) : ℂ) • Y c := by
  rw [hYb c, star_smul, star_star, star_intCast]

theorem lower_right_ne_zero_of_upper_right_zero (hSM : StarMinor) (hMV : MoveVec) (hMC : MoveCov) {A : Type} [Ring A] [StarRing A]
    [Algebra ℂ A] [StarModule ℂ A] {m : ℕ}
    (E : Fin m → Fin m → A) (Y Yb : Fin m → A) (x xb : Fin m → ℂ) (ε : Fin m → ℤˣ) (hGl : GlRel E)
    (hE : ∀ a b, star (E a b) = (((ε a * ε b : ℤˣ) : ℤ) : A) * E b a)
    (hYY : ∀ a b, Y a * Y b = Y b * Y a) (hYbYb : ∀ a b, Yb a * Yb b = Yb b * Yb a)
    (hLY : ∀ a b c, E a b * Y c - Y c * E a b = if a = c then -Y b else 0)
    (hLYb : ∀ a b c, E a b * Yb c - Yb c * E a b = if b = c then Yb a else 0)
    (hYb : ∀ c, Yb c = ((ε c : ℤ) : ℂ) • star (Y c)) (hxb : ∀ c, xb c = ((ε c : ℤ) : ℂ) * star (x c))
    (u : ℂ) :
    star (tA E Y Yb x xb u 1 1) = tA E Y Yb x xb (star u) 1 1 := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m <;> simp [tA]
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 2 := ⟨m - 2, by omega⟩
  have hterm : ∀ (i : Fin (t + 2)) (k : Fin (t + 1)) (j : Fin (t + 2)) (l : Fin (t + 1)),
      star (((-1 : ℂ) ^ ((i : ℕ) + (k : ℕ)) * (-1 : ℂ) ^ ((j : ℕ) + (l : ℕ)) * xb i * x j) •
        (Yb (i.succAbove k) * Y (j.succAbove l) *
          qminor E (i.succAbove ∘ k.succAbove) (j.succAbove ∘ l.succAbove) (u - 1))) =
      ((-1 : ℂ) ^ ((i : ℕ) + (k : ℕ)) * (-1 : ℂ) ^ ((j : ℕ) + (l : ℕ)) * xb j * x i) •
        (qminor E (j.succAbove ∘ l.succAbove) (i.succAbove ∘ k.succAbove) (star u - 1) *
          Yb (j.succAbove l) * Y (i.succAbove k)) := by
    intro i k j l
    rw [star_smul, star_mul (Yb _ * Y _), star_mul (Yb _), star2 hSM E ε hGl hE, starY Y Yb ε hYb, starYb Y Yb ε hYb,
      star_sub, star_one]
    simp only [star_mul', star_pow, star_neg, star_one, hxb, starE, star_star]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
    congr 1
    have h1 := eSq (ε i)
    have h2 := eSq (ε (i.succAbove k))
    have h4 := eSq (ε (j.succAbove l))
    set p2 := ((ε (i.succAbove k) : ℤ) : ℂ)
    set p4 := ((ε (j.succAbove l) : ℤ) : ℂ)
    linear_combination ((-1 : ℂ) ^ ((i : ℕ) + (k : ℕ)) * (-1 : ℂ) ^ ((j : ℕ) + (l : ℕ)) * x i * star (x j) *
      ((ε j : ℤ) : ℂ)) * (p2 * p2 * p4 * p4 * h1 + p4 * p4 * h2 + h4)
  rw [nested_minor_expansion_one_one, nested_minor_expansion_one_one]
  simp only [star_neg, star_sum, hterm]
  congr 1
  conv_lhs => rw [swap4a]
  conv_rhs => rw [swap4b]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  have eL : ∑ l : Fin (t + 1), ∑ k : Fin (t + 1),
      ((-1 : ℂ) ^ ((b : ℕ) + (k : ℕ)) * (-1 : ℂ) ^ ((a : ℕ) + (l : ℕ)) * xb a * x b) •
        (qminor E (a.succAbove ∘ l.succAbove) (b.succAbove ∘ k.succAbove) (star u - 1) *
          Yb (a.succAbove l) * Y (b.succAbove k)) =
      ((-1 : ℂ) ^ (a : ℕ) * (-1 : ℂ) ^ (b : ℕ) * xb a * x b) • ∑ l : Fin (t + 1), ∑ k : Fin (t + 1),
        ((-1 : ℂ) ^ (l : ℕ) * (-1 : ℂ) ^ (k : ℕ)) •
          (qminor E (a.succAbove ∘ l.succAbove) (b.succAbove ∘ k.succAbove) (star u - 1) *
            Yb (a.succAbove l) * Y (b.succAbove k)) := by
    simp only [Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ => ?_))
    congr 1
    ring
  have eR : ∑ k : Fin (t + 1), ∑ l : Fin (t + 1),
      ((-1 : ℂ) ^ ((a : ℕ) + (k : ℕ)) * (-1 : ℂ) ^ ((b : ℕ) + (l : ℕ)) * xb a * x b) •
        (Yb (a.succAbove k) * Y (b.succAbove l) *
          qminor E (a.succAbove ∘ k.succAbove) (b.succAbove ∘ l.succAbove) (star u - 1)) =
      ((-1 : ℂ) ^ (a : ℕ) * (-1 : ℂ) ^ (b : ℕ) * xb a * x b) • ∑ k : Fin (t + 1), ∑ l : Fin (t + 1),
        ((-1 : ℂ) ^ (k : ℕ) * (-1 : ℂ) ^ (l : ℕ)) •
          (Yb (a.succAbove k) * Y (b.succAbove l) *
            qminor E (a.succAbove ∘ k.succAbove) (b.succAbove ∘ l.succAbove) (star u - 1)) := by
    simp only [Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
    congr 1
    ring
  rw [eL, eR, transfer_commutator_one_one hMV hMC E Y Yb hGl hYY hYbYb hLY hLYb a b (star u - 1)]

end PI.QnHermHaar
