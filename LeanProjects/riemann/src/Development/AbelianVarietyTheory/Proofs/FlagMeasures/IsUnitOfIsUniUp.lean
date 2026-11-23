import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass

noncomputable section

namespace GlobalTheory.GLm.TraceTail

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

theorem isUnit_of_isUniUp {n : ℕ} {M : Mt g n} (h : IsUniUp M) : IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_upperTriangular (fun a b hab => (h a b).1 hab)]
  rw [Finset.prod_eq_one (fun a _ => (h a a).2 rfl)]
  exact isUnit_one

theorem val_toG {n : ℕ} {M : Mt g n} (h : IsUnit M) : ((toG M : Gn g n) : Mt g n) = M := by
  simp [toG, h]

theorem tr_eDat (N : ℕ) (P : Mt g N → Prop) (φ : Mt g N → ZMod g) (ψ : AddChar (ZMod g) ℂ)
    (χ : Gn g N → ℂ) :
    tr (eDat g N P φ ψ) χ = ((Finset.univ.filter fun u : Gn g N => P (u : Mt g N)).card : ℂ)⁻¹ *
      ∑ u : Gn g N, if P (u : Mt g N) then (ψ (φ (u : Mt g N)))⁻¹ * χ u else 0 := by
  unfold tr eDat
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : P (x : Mt g N) <;>
    simp [MonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply, Finsupp.single_apply, hx, mul_assoc]

theorem card_uniUp (N : ℕ) (S : ℕ → Prop) :
    (Finset.univ.filter fun u : Gn g N => IsUniUp (u : Mt g N) ∧
      ∀ b, S b → ∀ a, a < b → entN (u : Mt g N) a b = 0).card =
      g ^ (∑ b ∈ Finset.range N, if S b then 0 else b) := by
  let T : Fin N → Fin N → Finset (ZMod g) := fun a b =>
    if a < b ∧ ¬ S b then Finset.univ else {(1 : Mt g N) a b}
  have key : ∀ M : Mt g N, (IsUniUp M ∧ ∀ b, S b → ∀ a, a < b → entN M a b = 0) ↔
      ∀ a b, M a b ∈ T a b := by
    intro M
    simp only [T]
    constructor
    · rintro ⟨h1, h2⟩ a b
      split_ifs with h
      · simp
      · rw [Finset.mem_singleton]
        rcases lt_trichotomy a b with hab | hab | hab
        · have hS : S b := by tauto
          have := h2 b hS a hab
          simp only [entN, a.2, b.2, and_self, dif_pos] at this
          rw [Matrix.one_apply_ne hab.ne]; exact this
        · subst hab; rw [(h1 a a).2 rfl, Matrix.one_apply_eq]
        · rw [(h1 a b).1 hab, Matrix.one_apply_ne hab.ne']
    · intro h
      refine ⟨fun a b => ⟨fun hab => ?_, fun hab => ?_⟩, fun b hb a hab => ?_⟩
      · have := h a b
        rw [if_neg (fun h' => lt_asymm hab h'.1), Finset.mem_singleton] at this
        rw [this, Matrix.one_apply_ne hab.ne']
      · subst hab
        have := h a a
        rw [if_neg (fun h' => lt_irrefl _ h'.1), Finset.mem_singleton] at this
        rw [this, Matrix.one_apply_eq]
      · unfold entN
        split_ifs with hN
        · have := h ⟨a, hN.1⟩ ⟨b, hN.2⟩
          rw [if_neg (fun h' => h'.2 hb), Finset.mem_singleton] at this
          rw [this, Matrix.one_apply_ne (by intro h'; simp at h'; omega)]
        · rfl
  have h1 : (Finset.univ.filter fun u : Gn g N => IsUniUp (u : Mt g N) ∧
      ∀ b, S b → ∀ a, a < b → entN (u : Mt g N) a b = 0).card =
      (Fintype.piFinset fun a => Fintype.piFinset fun b => T a b).card := by
    refine Finset.card_bij (fun u _ => (u : Mt g N)) (fun u hu => ?_) (fun u _ v _ h => Units.ext h)
      (fun M hM => ?_)
    · exact Fintype.mem_piFinset.2 fun a => Fintype.mem_piFinset.2 fun b =>
        (key _).1 (Finset.mem_filter.1 hu).2 a b
    · have := (key M).2 fun a b => Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 hM a) b
      have hu := isUnit_of_isUniUp this.1
      refine ⟨toG M, ?_, val_toG hu⟩
      rw [Finset.mem_filter, val_toG hu]
      exact ⟨Finset.mem_univ _, this⟩
  rw [h1, Fintype.card_piFinset]
  simp only [Fintype.card_piFinset]
  rw [Finset.prod_comm, ← Finset.prod_pow_eq_pow_sum, Finset.prod_range]
  refine Finset.prod_congr rfl fun b _ => ?_
  by_cases hb : S b
  · simp [T, hb]
  · have : ∀ a, (T a b).card = if a < b then g else 1 := by
      intro a
      by_cases hab : a < b <;> simp [T, hb, hab]
    simp only [this, hb, if_false]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    congr 1
    rw [show Finset.univ.filter (fun a => a < b) = Finset.Iio b by ext; simp]
    simp

theorem val_diag1 {k : ℕ} (n : ℕ) (u : Gn g k) (hu : IsUniUp (u : Mt g k)) :
    ((diag1 u n : Gn g n) : Mt g n) = fun i j : Fin n =>
      if (i : ℕ) < k ∧ (j : ℕ) < k then entN (u : Mt g k) i j else (1 : Mt g n) i j := by
  unfold diag1
  refine val_toG (isUnit_of_isUniUp fun a b => ⟨fun hab => ?_, fun hab => ?_⟩)
  · show (if (a : ℕ) < k ∧ (b : ℕ) < k then entN (u : Mt g k) a b else (1 : Mt g n) a b) = 0
    split_ifs with h
    · simp only [entN, h, and_self, dif_pos]
      exact (hu _ _).1 hab
    · exact Matrix.one_apply_ne hab.ne'
  · subst hab
    show (if (a : ℕ) < k ∧ (a : ℕ) < k then entN (u : Mt g k) a a else (1 : Mt g n) a a) = 1
    split_ifs with h
    · simp only [entN, h, and_self, dif_pos]
      exact (hu _ _).2 rfl
    · exact Matrix.one_apply_eq _

theorem isUniUp_iff {n : ℕ} (M : Mt g n) : IsUniUp M ↔
    ∀ a b, a < n → b < n → (b < a → entN M a b = 0) ∧ (a = b → entN M a b = 1) := by
  constructor
  · intro h a b ha hb
    simp only [entN, ha, hb, and_self, dif_pos]
    exact ⟨fun hab => (h _ _).1 hab, fun hab => (h _ _).2 (Fin.ext hab)⟩
  · intro h a b
    have := h a b a.2 b.2
    simp only [entN, a.2, b.2, and_self, dif_pos] at this
    exact ⟨fun hab => this.1 hab, fun hab => this.2 (congrArg _ hab)⟩

theorem entN_tl {n : ℕ} (k : ℕ) (M : Mt g n) {a b : ℕ} (ha : a < k) (hb : b < k) :
    entN (tl k M) a b = entN M a b := by
  conv_lhs => simp only [entN, ha, hb, and_self, dif_pos]
  rfl

theorem entN_br {n : ℕ} (k r : ℕ) (M : Mt g n) {a b : ℕ} (ha : a < r) (hb : b < r) :
    entN (br k r M) a b = entN M (k + a) (k + b) := by
  conv_lhs => simp only [entN, ha, hb, and_self, dif_pos]
  rfl

theorem entN_fin {n : ℕ} (M : Mt g n) (a b : Fin n) : entN M a b = M a b := by
  simp [entN]

theorem fibre_iff {N k : ℕ} (hk : k < N) (x : Mt g N) (u : Gn g k) :
    (IsUniUp (u : Mt g k) ∧ InR (k + 1) x ∧ tl (k + 1) x = ((diag1 u (k + 1) : Gn g (k + 1)) : Mt g (k + 1))) ↔
      ((IsUniUp x ∧ ∀ a, a < k → entN x a k = 0) ∧ (u : Mt g k) = tl k x) := by
  constructor
  · rintro ⟨hu, ⟨hP, hB⟩, ht⟩
    rw [val_diag1 _ u hu] at ht
    have ht' : ∀ a b (ha : a < k + 1) (hb : b < k + 1), entN x a b =
        if a < k ∧ b < k then entN (u : Mt g k) a b else if a = b then 1 else 0 := by
      intro a b ha hb
      have := congrFun (congrFun ht ⟨a, ha⟩) ⟨b, hb⟩
      simpa [tl, Matrix.one_apply] using this
    rw [isUniUp_iff] at hu hB
    refine ⟨⟨(isUniUp_iff x).2 fun a b ha hb => ?_, fun a ha => ?_⟩, ?_⟩
    · by_cases h1 : a < k + 1
      · by_cases h2 : b < k + 1
        · rw [ht' a b h1 h2]
          split_ifs with h3 h4
          · exact hu a b h3.1 h3.2
          · exact ⟨fun h => by omega, fun _ => rfl⟩
          · exact ⟨fun _ => rfl, fun h => absurd h h4⟩
        · exact ⟨fun h => by omega, fun h => by omega⟩
      · by_cases h2 : b < k + 1
        · refine ⟨fun _ => ?_, fun h => by omega⟩
          exact (entN_fin x ⟨a, ha⟩ ⟨b, hb⟩).trans (hP ⟨a, ha⟩ ⟨b, hb⟩ h2 (by simpa using h1))
        · have := hB (a - (k + 1)) (b - (k + 1)) (by omega) (by omega)
          rw [entN_br _ _ _ (by omega) (by omega), show k + 1 + (a - (k + 1)) = a by omega,
            show k + 1 + (b - (k + 1)) = b by omega] at this
          exact ⟨fun h => this.1 (by omega), fun h => this.2 (by omega)⟩
    · rw [ht' a k (by omega) (by omega), if_neg (by omega), if_neg (by omega)]
    · ext a b
      rw [tl, ht' a b (by omega) (by omega), if_pos ⟨a.2, b.2⟩, entN_fin]
  · rintro ⟨⟨hx, h0⟩, hu⟩
    have hx' := (isUniUp_iff x).1 hx
    have hu1 : IsUniUp (u : Mt g k) := by
      rw [hu, isUniUp_iff]
      intro a b ha hb
      rw [entN_tl _ _ ha hb]
      exact hx' a b (by omega) (by omega)
    refine ⟨hu1, ⟨fun a b h1 h2 => (hx a b).1 (by show (b : ℕ) < a; omega), ?_⟩, ?_⟩
    · rw [isUniUp_iff]
      intro a b ha hb
      rw [entN_br _ _ _ ha hb]
      have := hx' (k + 1 + a) (k + 1 + b) (by omega) (by omega)
      exact ⟨fun h => this.1 (by omega), fun h => this.2 (by omega)⟩
    · rw [val_diag1 _ u hu1]
      ext a b
      have ha := a.2
      have hb := b.2
      have := hx' a b (by omega) (by omega)
      simp only [tl]
      split_ifs with h
      · rw [hu, entN_tl _ _ h.1 h.2]
      · rcases lt_trichotomy (a : ℕ) b with hab | hab | hab
        · rw [Matrix.one_apply_ne (fun h' => by rw [h'] at hab; omega), show (b : ℕ) = k by omega]
          exact h0 a (by omega)
        · rw [this.2 hab, Fin.ext hab, Matrix.one_apply_eq]
        · rw [this.1 hab, Matrix.one_apply_ne (fun h' => by rw [h'] at hab; omega)]

theorem sup_split {N k : ℕ} (hk : k < N) (x : Mt g N) (h0 : ∀ a, a < k → entN x a k = 0) :
    ∑ i ∈ Finset.range (N - 1), entN x i (i + 1) =
      ∑ i ∈ Finset.range (k - 1), entN (tl k x) i (i + 1) + supFrom k x := by
  unfold supFrom
  rw [← Finset.sum_range_add_sum_Ico _ (show k ≤ N - 1 by omega)]
  congr 1
  rcases k with _ | k
  · simp
  · rw [Finset.sum_range_succ, h0 k (by omega), add_zero, Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [entN_tl _ _ (by omega) (by omega)]

theorem exp_split (k r : ℕ) :
    (∑ b ∈ Finset.range (k + 1 + r), if b = k then 0 else b) =
      (∑ b ∈ Finset.range k, if False then 0 else b) + ((k + 1) * r + r * (r - 1) / 2) := by
  rw [Finset.sum_range_add, Finset.sum_range_succ, if_pos rfl, add_zero, ← Finset.sum_range_id r]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [if_neg (by omega), if_neg id]
  · rw [Finset.sum_congr rfl fun i _ => if_neg (show k + 1 + i ≠ k by omega), Finset.sum_add_distrib]
    simp [mul_comm]

end GlobalTheory.GLm.TraceTail

namespace GlobalTheory.GLm

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm GlobalTheory.GLm.TraceTail
open scoped Classical

theorem tr_eJ'_eq_wh_tail (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (N k : ℕ) (χ : Gn g N → ℂ)
    (hk : k < N) :
    tr (eJ' g N k ψ) χ = wh ψ (fun h : Gn g k => tail ψ (k + 1) χ (diag1 h (k + 1))) := by
  obtain ⟨r, rfl⟩ : ∃ r, N = k + 1 + r := ⟨N - (k + 1), by omega⟩
  have c1 := card_uniUp (g := g) (k + 1 + r) (fun b => b = k)
  have c2 := card_uniUp (g := g) k (fun _ => False)
  simp only [forall_eq] at c1
  simp only [false_imp_iff, implies_true, and_true] at c2
  unfold wh eU eJ'
  rw [tr_eDat, tr_eDat]
  have e1 : ((Finset.univ.filter fun u : Gn g (k + 1 + r) => IsUniUp (u : Mt g (k + 1 + r)) ∧
      ∀ a, a < k → entN (u : Mt g (k + 1 + r)) a k = 0).card : ℂ) =
      ((Finset.univ.filter fun u : Gn g k => IsUniUp (u : Mt g k)).card : ℂ) *
        (g : ℂ) ^ ((k + 1) * r + r * (r - 1) / 2) := by
    have h1 := exp_split k r
    rw [c2]
    refine (congrArg _ (Eq.trans (by congr) c1)).trans ?_
    rw [Nat.cast_pow, Nat.cast_pow, ← pow_add]
    congr 1
    convert h1
  refine Eq.trans (congrArg₂ _ (congrArg _ (Eq.trans (by congr) e1)) rfl) ?_
  rw [mul_inv, mul_assoc]
  congr 1
  unfold tail
  simp only [Nat.add_sub_cancel_left, Nat.add_sub_cancel]
  have : ∀ (c : ℂ) (A : Prop) [Decidable A] (B : Gn g (k + 1 + r) → Prop) [DecidablePred B] (f : Gn g (k + 1 + r) → ℂ) (d : ℂ),
      (if A then d * (c * ∑ x, if B x then f x else 0) else 0) =
        c * ∑ x, if A ∧ B x then d * f x else 0 := by
    intro c A _ B _ f d
    by_cases hA : A
    · simp only [hA, if_true, true_and, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs <;> ring
    · simp [hA]
  simp only [this]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [fibre_iff hk]
  split_ifs with hx
  · have hx' := (isUniUp_iff _).1 hx.1
    have hU : IsUnit (tl k (x : Mt g (k + 1 + r))) := by
      refine isUnit_of_isUniUp ((isUniUp_iff _).2 fun a b ha hb => ?_)
      rw [entN_tl _ _ ha hb]
      exact hx' a b (by omega) (by omega)
    rw [Finset.sum_eq_single (toG (tl k (x : Mt g (k + 1 + r))))]
    · rw [if_pos ⟨hx, val_toG hU⟩, val_toG hU, sup_split hk _ hx.2, AddChar.map_add_eq_mul, mul_inv]
      ring
    · intro u _ hu
      exact if_neg fun h => hu (Units.ext (h.2.trans (val_toG hU).symm))
    · simp
  · simp [hx]

end GlobalTheory.GLm
