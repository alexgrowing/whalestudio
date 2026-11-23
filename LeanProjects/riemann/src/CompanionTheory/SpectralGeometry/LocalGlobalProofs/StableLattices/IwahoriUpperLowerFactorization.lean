import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsCongIdealTwoTorsion

open CompanionTheory.Rg.FlB

namespace GlobalTheory.CompanionTheory.Iwahori.Gauss

open GlobalTheory.CompanionTheory.Iwahori

variable {E ι : Type} [Ring E] [Fintype ι] {wt : ι → ℕ} {P : ι → E}

theorem eq_zero_of_mul_pieces (hP : IsPieces P) {y : E} (h : ∀ j, y * P j = 0) : y = 0 := by
  have : y * ∑ j, P j = 0 := by
    rw [Finset.mul_sum]; exact Finset.sum_eq_zero (fun j _ => h j)
  rwa [hP.sum, mul_one] at this

theorem eq_zero_of_pieces_mul (hP : IsPieces P) {y : E} (h : ∀ j, P j * y = 0) : y = 0 := by
  have : (∑ j, P j) * y = 0 := by
    rw [Finset.sum_mul]; exact Finset.sum_eq_zero (fun j _ => h j)
  rwa [hP.sum, one_mul] at this

theorem block_mul (hP : IsPieces P) (u x y v : E) :
    u * (x * y) * v = ∑ l, (u * x * P l) * (P l * y * v) := by
  have h : ∀ l, (u * x * P l) * (P l * y * v) = u * x * (P l) * y * v := by
    intro l
    calc (u * x * P l) * (P l * y * v) = u * x * (P l * P l) * y * v := by
          simp only [mul_assoc]
      _ = _ := by rw [hP.idem]
  simp_rw [h]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum, hP.sum]
  simp only [mul_one, mul_assoc]

theorem isUpper_mul (hP : IsPieces P) {a b : E} (ha : IsUpper wt P a) (hb : IsUpper wt P b) :
    IsUpper wt P (a * b) := by
  intro i j hij
  rw [block_mul hP]
  refine Finset.sum_eq_zero fun l _ => ?_
  rcases lt_or_ge (wt l) (wt i) with h | h
  · rw [ha i l h, zero_mul]
  · rw [hb l j (lt_of_lt_of_le hij h), mul_zero]

theorem isLowerUni_mul (hwt : Function.Injective wt) (hP : IsPieces P) {a b : E}
    (ha : IsLowerUni wt P a) (hb : IsLowerUni wt P b) : IsLowerUni wt P (a * b) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [block_mul hP]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge (wt i) (wt l) with h | h
    · rw [ha.1 i l h, zero_mul]
    · rw [hb.1 l j (lt_of_le_of_lt h hij), mul_zero]
  · rw [block_mul hP, Finset.sum_eq_single i]
    · rw [ha.2, hb.2, hP.idem]
    · intro l _ hl
      rcases lt_trichotomy (wt i) (wt l) with h | h | h
      · rw [ha.1 i l h, zero_mul]
      · exact absurd (hwt h).symm hl
      · rw [hb.1 l i h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h

theorem isUpper_one (hP : IsPieces P) : IsUpper wt P 1 := fun i j h => by
  rw [mul_one]
  exact hP.orth i j (fun e => by subst e; exact lt_irrefl _ h)

theorem isLowerUni_one (hP : IsPieces P) : IsLowerUni wt P 1 := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · rw [mul_one]
    exact hP.orth i j (fun e => by subst e; exact lt_irrefl _ h)
  · rw [mul_one, hP.idem]

theorem sub_one_mul_mem {J : AddSubgroup E} (hJ : IsCongIdeal J P) {a b : E}
    (ha : a - 1 ∈ J) (hb : b - 1 ∈ J) : a * b - 1 ∈ J := by
  have : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by noncomm_ring
  rw [this]
  exact J.add_mem (J.add_mem (hJ.mul_mem _ ha _ hb) ha) hb

theorem step (hwt : Function.Injective wt) (hP : IsPieces P) {J : AddSubgroup E}
    (hJ : IsCongIdeal J P) (m : ℕ)
    (ih : ∀ k : E, k - 1 ∈ J →
      (∀ i j, (m ≤ wt i ∨ m ≤ wt j) → P i * (k - 1) * P j = 0) →
      ∃ a b : E, a - 1 ∈ J ∧ b - 1 ∈ J ∧ IsUpper wt P a ∧ IsLowerUni wt P b ∧ k = a * b)
    (q : ι) (hq : wt q = m) (x : E) (hx : x ∈ J)
    (hH : ∀ i j, (m + 1 ≤ wt i ∨ m + 1 ≤ wt j) → P i * x * P j = 0) :
    ∃ a b : E, a - 1 ∈ J ∧ b - 1 ∈ J ∧ IsUpper wt P a ∧ IsLowerUni wt P b ∧ 1 + x = a * b := by
  have hl : ∀ i, m + 1 ≤ wt i → P i * x = 0 := fun i hi =>
    eq_zero_of_mul_pieces hP fun j => hH i j (Or.inl hi)
  have hr : ∀ j, m + 1 ≤ wt j → x * P j = 0 := fun j hj =>
    eq_zero_of_pieces_mul hP fun i => by rw [← mul_assoc]; exact hH i j (Or.inr hj)
  have hne : ∀ j, m + 1 ≤ wt j → P q * P j = 0 := fun j hj =>
    hP.orth q j (fun e => by subst e; omega)
  have hne' : ∀ j, m + 1 ≤ wt j → P j * P q = 0 := fun j hj =>
    hP.orth j q (fun e => by subst e; omega)
  have hQQ := hP.idem q
  obtain ⟨y, hy, h1, h2⟩ := hJ.inv (x * P q) (hJ.right_mem q x hx)
  obtain ⟨z, hz, hzdef⟩ : ∃ z ∈ J, 1 + z = (1 + y) * (1 + x) :=
    ⟨(1 + y) * (1 + x) - 1,
      sub_one_mul_mem hJ (by rwa [add_sub_cancel_left]) (by rwa [add_sub_cancel_left]),
      by abel⟩
  have hAB : 1 + x = (1 + x * P q) * (1 + z) := by
    rw [hzdef, ← mul_assoc, h1, one_mul]
  have hzQ : z * P q = 0 := by
    have e : (1 + x) * P q = (1 + x * P q) * P q := by
      simp only [add_mul, one_mul, mul_assoc, hQQ]
    have : (1 + z) * P q = P q := by
      calc (1 + z) * P q = (1 + y) * ((1 + x) * P q) := by rw [hzdef, mul_assoc]
        _ = (1 + y) * ((1 + x * P q) * P q) := by rw [e]
        _ = ((1 + y) * (1 + x * P q)) * P q := by rw [mul_assoc]
        _ = P q := by rw [h2, one_mul]
    rw [add_mul, one_mul] at this
    simpa using this
  have hzr : ∀ j, m + 1 ≤ wt j → z * P j = 0 := by
    intro j hj
    have e1 : (1 + x) * P j = P j := by rw [add_mul, one_mul, hr j hj, add_zero]
    have e2 : (1 + x * P q) * P j = P j := by
      rw [add_mul, one_mul, mul_assoc, hne j hj, mul_zero, add_zero]
    have e3 : (1 + y) * P j = P j := by
      calc (1 + y) * P j = (1 + y) * ((1 + x * P q) * P j) := by rw [e2]
        _ = ((1 + y) * (1 + x * P q)) * P j := by rw [mul_assoc]
        _ = P j := by rw [h2, one_mul]
    have : (1 + z) * P j = P j := by
      rw [hzdef, mul_assoc, e1, e3]
    rw [add_mul, one_mul] at this
    simpa using this
  have hzl : ∀ i, m + 1 ≤ wt i → P i * z = 0 := by
    intro i hi
    have e1 : P i * (1 + x) = P i := by rw [mul_add, mul_one, hl i hi, add_zero]
    have e2 : P i * (1 + x * P q) = P i := by
      rw [mul_add, mul_one, ← mul_assoc, hl i hi, zero_mul, add_zero]
    have e3 : P i * (1 + y) = P i := by
      calc P i * (1 + y) = (P i * (1 + x * P q)) * (1 + y) := by rw [e2]
        _ = P i * ((1 + x * P q) * (1 + y)) := by rw [mul_assoc]
        _ = P i := by rw [h1, mul_one]
    have : P i * (1 + z) = P i := by
      rw [hzdef, ← mul_assoc, e3, e1]
    rw [mul_add, mul_one] at this
    simpa using this
  have hsJ : z - P q * z ∈ J := J.sub_mem hz (hJ.left_mem q z hz)
  have hsr : ∀ j, m ≤ wt j → (z - P q * z) * P j = 0 := by
    intro j hj
    rcases hj.eq_or_lt with h | h
    · have : j = q := hwt (h.symm.trans hq.symm)
      subst this
      rw [sub_mul, hzQ, mul_assoc, hzQ, mul_zero, sub_zero]
    · rw [sub_mul, hzr j h, mul_assoc, hzr j h, mul_zero, sub_zero]
  have hsl : ∀ i, m ≤ wt i → P i * (z - P q * z) = 0 := by
    intro i hi
    rcases hi.eq_or_lt with h | h
    · have : i = q := hwt (h.symm.trans hq.symm)
      subst this
      rw [mul_sub, ← mul_assoc, hQQ, sub_self]
    · rw [mul_sub, hzl i h, ← mul_assoc, hne' i h, zero_mul, sub_zero]
  have hS : ∀ i j, (m ≤ wt i ∨ m ≤ wt j) →
      P i * ((1 + (z - P q * z)) - 1) * P j = 0 := by
    intro i j hij
    rw [add_sub_cancel_left]
    rcases hij with h | h
    · rw [hsl i h, zero_mul]
    · rw [mul_assoc, hsr j h, mul_zero]
  obtain ⟨a', b', ha, hb, hau, hbl, hk⟩ :=
    ih (1 + (z - P q * z)) (by rwa [add_sub_cancel_left]) hS
  have hSC : (1 + (z - P q * z)) * (1 + P q * z) = 1 + z := by
    have : (1 + (z - P q * z)) * (1 + P q * z)
        = 1 + z + (z * P q) * z - P q * (z * P q) * z := by noncomm_ring
    rw [this, hzQ]
    simp
  have hA : IsUpper wt P (1 + x * P q) := by
    intro i j hij
    have hm : P i * (1 + x * P q) * P j = P i * P j + P i * x * (P q * P j) := by
      simp only [mul_add, add_mul, mul_one, mul_assoc]
    rw [hm, hP.orth i j (fun e => by subst e; exact lt_irrefl _ hij), zero_add]
    by_cases hjq : j = q
    · subst hjq
      rw [hl i (by omega), zero_mul]
    · rw [hP.orth q j (Ne.symm hjq), mul_zero]
  have hC : IsLowerUni wt P (1 + P q * z) := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have hm : P i * (1 + P q * z) * P j = P i * P j + (P i * P q) * (z * P j) := by
        simp only [mul_add, add_mul, mul_one, mul_assoc]
      rw [hm, hP.orth i j (fun e => by subst e; exact lt_irrefl _ hij), zero_add]
      by_cases hiq : i = q
      · subst hiq
        rw [hzr j (by omega), mul_zero]
      · rw [hP.orth i q hiq, zero_mul]
    · have hm : P i * (1 + P q * z) * P i = P i * P i + (P i * P q) * (z * P i) := by
        simp only [mul_add, add_mul, mul_one, mul_assoc]
      rw [hm, hP.idem]
      by_cases hiq : i = q
      · subst hiq
        rw [hzQ, mul_zero, add_zero]
      · rw [hP.orth i q hiq, zero_mul, add_zero]
  refine ⟨(1 + x * P q) * a', b' * (1 + P q * z), ?_, ?_, isUpper_mul hP hA hau,
    isLowerUni_mul hwt hP hbl hC, ?_⟩
  · exact sub_one_mul_mem hJ (by rw [add_sub_cancel_left]; exact hJ.right_mem q x hx) ha
  · exact sub_one_mul_mem hJ hb (by rw [add_sub_cancel_left]; exact hJ.left_mem q z hz)
  · rw [hAB, ← hSC, hk]
    simp only [mul_assoc]

theorem exists_of_support (hwt : Function.Injective wt) (hP : IsPieces P) {J : AddSubgroup E}
    (hJ : IsCongIdeal J P) (m : ℕ) :
    ∀ k : E, k - 1 ∈ J →
      (∀ i j, (m ≤ wt i ∨ m ≤ wt j) → P i * (k - 1) * P j = 0) →
      ∃ a b : E, a - 1 ∈ J ∧ b - 1 ∈ J ∧ IsUpper wt P a ∧ IsLowerUni wt P b ∧ k = a * b := by
  induction m with
  | zero =>
    intro k _ h
    have h0 : k - 1 = 0 := eq_zero_of_mul_pieces hP fun j => eq_zero_of_pieces_mul hP fun i => by
      rw [← mul_assoc]; exact h i j (Or.inl (Nat.zero_le _))
    have hk : k = 1 := sub_eq_zero.mp h0
    exact ⟨1, 1, by simp, by simp, isUpper_one hP, isLowerUni_one hP, by simp [hk]⟩
  | succ m ih =>
    intro k hk h
    by_cases hq : ∃ q, wt q = m
    · obtain ⟨q, hq⟩ := hq
      have := step hwt hP hJ m ih q hq (k - 1) hk h
      simpa using this
    · have hq' : ∀ i, m ≤ wt i → m + 1 ≤ wt i := fun i hi => by
        rcases hi.eq_or_lt with e | e
        · exact absurd ⟨i, e.symm⟩ hq
        · exact e
      refine ih k hk fun i j hij => h i j ?_
      rcases hij with e | e
      · exact Or.inl (hq' i e)
      · exact Or.inr (hq' j e)

theorem block_gauss : ∀ {E ι : Type} [Ring E] [Fintype ι] (wt : ι → ℕ), Function.Injective wt →
    ∀ (P : ι → E), GlobalTheory.CompanionTheory.Iwahori.IsPieces P → ∀ J : AddSubgroup E,
    GlobalTheory.CompanionTheory.Iwahori.IsCongIdeal J P → ∀ k : E, k - 1 ∈ J →
    ∃ a b : E, a - 1 ∈ J ∧ b - 1 ∈ J ∧ GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a ∧
      GlobalTheory.CompanionTheory.Iwahori.IsLowerUni wt P b ∧ k = a * b := by
  intro E ι _ _ wt hwt P hP J hJ k hk
  refine exists_of_support hwt hP hJ (Finset.univ.sup wt + 1) k hk ?_
  intro i j h
  have h1 := Finset.le_sup (f := wt) (Finset.mem_univ i)
  have h2 := Finset.le_sup (f := wt) (Finset.mem_univ j)
  omega

end GlobalTheory.CompanionTheory.Iwahori.Gauss
