import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinOfPI
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertSchurOfAdjointClosed

open CompanionTheory.D.gk.admitted (stdPoly word word_nil word_cons)

namespace GlobalTheory.CompanionTheory.PrimeRing.StdChain

variable {R : Type} [Ring R]

theorem word_left (E : R) (m : ℕ) (q x : ℕ → R) (hE : ∀ i ≤ m, E * q i = q i) (hid : q m * q m = q m)
    (hx : ∀ i < m, q i * x i = x i) (n k : ℕ) (hk : k + n = m) :
    q k * (word E ((List.range' k n).map x) * q m) = word E ((List.range' k n).map x) * q m := by
  cases n with
  | zero =>
    obtain rfl : k = m := by omega
    simp [hE k le_rfl, hid]
  | succ n =>
    have hkm : k < m := by omega
    have hEx : E * x k = x k := by
      rw [← hx k hkm, ← mul_assoc, hE k hkm.le]
    rw [List.range'_succ, List.map_cons, word_cons, hEx]
    simp only [← mul_assoc, hx k hkm]

theorem word_cases (E : R) (m : ℕ) (q x : ℕ → R) (hE : ∀ i ≤ m, E * q i = q i) (hid : q m * q m = q m)
    (hx1 : ∀ i < m, q i * x i = x i) (hx2 : ∀ i < m, x i * q (i + 1) = x i)
    (horth : ∀ i ≤ m, ∀ k ≤ m, i ≠ k → q i * q k = 0) (l : List ℕ) (hl : ∀ a ∈ l, a < m) :
    word E (l.map x) * q m = 0 ∨ ∃ k, k + l.length = m ∧ l = List.range' k l.length := by
  induction l with
  | nil => exact Or.inr ⟨m, rfl, rfl⟩
  | cons a l ih =>
    have ha : a < m := hl a (by simp)
    have hEx : E * x a = x a := by
      rw [← hx1 a ha, ← mul_assoc, hE a ha.le]
    rw [List.map_cons, word_cons, hEx]
    rcases ih (fun b hb => hl b (by simp [hb])) with h | ⟨k, hk, h⟩
    · left
      rw [mul_assoc, h, mul_zero]
    · by_cases hak : a + 1 = k
      · right
        refine ⟨a, by simp; omega, ?_⟩
        rw [List.length_cons, List.range'_succ, hak, ← h]
      · left
        have hw := word_left E m q x hE hid hx1 l.length k hk
        rw [← h] at hw
        calc x a * word E (l.map x) * q m
            = x a * q (a + 1) * (q k * (word E (l.map x) * q m)) := by
              rw [hx2 a ha, hw, mul_assoc]
          _ = x a * (q (a + 1) * q k) * (word E (l.map x) * q m) := by
              simp only [mul_assoc]
          _ = 0 := by
              rw [horth (a + 1) (by omega) k (by omega) hak]
              simp

theorem exists_chain (A S : Set R) (E : R) (m : ℕ) (q : ℕ → R)
    (hmul : ∀ a ∈ A, ∀ b ∈ A, a * b ∈ A) (hS : S ⊆ A)
    (hprime : ∀ x ∈ A, ∀ y ∈ A, y ≠ 0 → (∀ s ∈ S, x * s * y = 0) → x = 0)
    (hA : ∀ i ≤ m, q i ∈ A) (hne : ∀ i ≤ m, q i ≠ 0) (hid : ∀ i ≤ m, q i * q i = q i)
    (hE : ∀ i ≤ m, E * q i = q i) (n k : ℕ) (hk : k + n = m) :
    ∃ (x : ℕ → R) (y : R), y ≠ 0 ∧ y ∈ A ∧ q k * y = y ∧
      (∀ i, k ≤ i → i < m → x i ∈ A ∧ q i * x i = x i ∧ x i * q (i + 1) = x i) ∧
      word E ((List.range' k n).map x) * q m = y := by
  induction n generalizing k with
  | zero =>
    obtain rfl : k = m := by omega
    exact ⟨0, q k, hne k le_rfl, hA k le_rfl, hid k le_rfl, fun i h1 h2 => absurd h2 (by omega),
      by simp [hE k le_rfl]⟩
  | succ n ih =>
    obtain ⟨x, y, hy0, hyA, hqy, hx, hw⟩ := ih (k + 1) (by omega)
    have hkm : k < m := by omega
    obtain ⟨s, hs, hsy⟩ : ∃ s ∈ S, q k * s * y ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hne k hkm.le (hprime _ (hA k hkm.le) y hyA hy0 hcon)
    have hqs : q k * s ∈ A := hmul _ (hA k hkm.le) _ (hS hs)
    have hxk : q k * s * q (k + 1) ∈ A := hmul _ hqs _ (hA (k + 1) hkm)
    refine ⟨Function.update x k (q k * s * q (k + 1)), q k * s * y, hsy, hmul _ hqs _ hyA, ?_, ?_, ?_⟩
    · simp only [← mul_assoc, hid k hkm.le]
    · intro i h1 h2
      rcases eq_or_lt_of_le h1 with rfl | h3
      · rw [Function.update_self]
        refine ⟨hxk, ?_, ?_⟩
        · simp only [← mul_assoc, hid k hkm.le]
        · rw [mul_assoc _ (q (k + 1)), hid (k + 1) hkm]
      · rw [Function.update_of_ne (by omega)]
        exact hx i (by omega) h2
    · have hmap : (List.range' (k + 1) n).map (Function.update x k (q k * s * q (k + 1))) =
          (List.range' (k + 1) n).map x := by
        apply List.map_congr_left
        intro a ha
        have := List.mem_range'_1.mp ha
        rw [Function.update_of_ne (by omega)]
      have hEq : E * (q k * s * q (k + 1)) = q k * s * q (k + 1) := by
        simp only [← mul_assoc, hE k hkm.le]
      rw [List.range'_succ, List.map_cons, word_cons, hmap, Function.update_self, mul_assoc, hw, hEq,
        mul_assoc _ (q (k + 1)), hqy]

theorem no_chain_nat (A S : Set R) (E : R) (m : ℕ) (q : ℕ → R)
    (hmul : ∀ a ∈ A, ∀ b ∈ A, a * b ∈ A) (hS : S ⊆ A)
    (hprime : ∀ x ∈ A, ∀ y ∈ A, y ≠ 0 → (∀ s ∈ S, x * s * y = 0) → x = 0)
    (hstd : ∀ a : Fin m → R, (∀ i, a i ∈ A) → stdPoly E a = 0)
    (hA : ∀ i ≤ m, q i ∈ A) (hne : ∀ i ≤ m, q i ≠ 0) (hid : ∀ i ≤ m, q i * q i = q i)
    (horth : ∀ i ≤ m, ∀ k ≤ m, i ≠ k → q i * q k = 0) (hE : ∀ i ≤ m, E * q i = q i) : False := by
  obtain ⟨x, y, hy0, -, -, hx, hw⟩ :=
    exists_chain A S E m q hmul hS hprime hA hne hid hE m 0 (by omega)
  have hx' : ∀ i, i < m → x i ∈ A ∧ q i * x i = x i ∧ x i * q (i + 1) = x i :=
    fun i hi => hx i (Nat.zero_le _) hi
  have h0 := hstd (fun i => x i) (fun i => (hx' i i.2).1)
  have hm : ∀ π : Equiv.Perm (Fin m), (List.ofFn fun i => x (π i)) =
      (List.ofFn fun i => (π i : ℕ)).map x := by
    intro π
    rw [List.map_ofFn]
    rfl
  have key : stdPoly E (fun i : Fin m => x i) * q m = y := by
    rw [stdPoly, Finset.sum_mul, Finset.sum_eq_single 1]
    · rw [hm]
      simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul, Equiv.Perm.coe_one, id]
      rw [CompanionTheory.D.gk.admitted.FinOfPIAux.ofFn_val, hw]
    · intro π _ hπ
      rw [hm, mul_assoc]
      rcases word_cases E m q x hE (hid m le_rfl) (fun i hi => (hx' i hi).2.1)
        (fun i hi => (hx' i hi).2.2) horth (List.ofFn fun i => (π i : ℕ))
        (by simp [List.mem_ofFn]) with h | ⟨k, hk, h⟩
      · rw [h, mul_zero]
      · exfalso
        apply hπ
        rw [List.length_ofFn] at hk h
        obtain rfl : k = 0 := by omega
        rw [← CompanionTheory.D.gk.admitted.FinOfPIAux.ofFn_val] at h
        ext i
        exact congrFun (List.ofFn_injective h) i
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [h0, zero_mul] at key
  exact hy0 key.symm

theorem no_orthogonal_idempotents : ∀ (R : Type) [Ring R] (A S : Set R) (E : R) (m : ℕ) (q : Fin (m + 1) → R),
    (∀ a ∈ A, ∀ b ∈ A, a * b ∈ A) → S ⊆ A →
    (∀ x ∈ A, ∀ y ∈ A, y ≠ 0 → (∀ s ∈ S, x * s * y = 0) → x = 0) →
    (∀ a : Fin m → R, (∀ i, a i ∈ A) → stdPoly E a = 0) →
    (∀ i, q i ∈ A) → (∀ i, q i ≠ 0) → (∀ i, q i * q i = q i) → (∀ i k, i ≠ k → q i * q k = 0) →
    (∀ i, E * q i = q i) → False := by
  intro R _ A S E m q hmul hS hprime hstd hA hne hid horth hE
  let qq : ℕ → R := fun i => if h : i < m + 1 then q ⟨i, h⟩ else 0
  have hqq : ∀ i (h : i ≤ m), qq i = q ⟨i, Nat.lt_succ_of_le h⟩ := fun i h =>
    dif_pos (Nat.lt_succ_of_le h)
  refine no_chain_nat A S E m qq hmul hS hprime hstd ?_ ?_ ?_ ?_ ?_
  · intro i h
    rw [hqq i h]
    exact hA _
  · intro i h
    rw [hqq i h]
    exact hne _
  · intro i h
    rw [hqq i h]
    exact hid _
  · intro i h k h' hik
    rw [hqq i h, hqq k h']
    exact horth _ _ fun e => hik (congrArg Fin.val e)
  · intro i h
    rw [hqq i h]
    exact hE _

end GlobalTheory.CompanionTheory.PrimeRing.StdChain
