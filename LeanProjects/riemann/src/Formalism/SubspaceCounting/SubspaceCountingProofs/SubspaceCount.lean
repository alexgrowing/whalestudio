import Formalism.SubspaceCounting.StatementB

noncomputable section

open scoped BigOperators
open Module

namespace Formalism.G0

namespace SubspaceCountP

theorem gb_zero_right (q n : ℕ) : gaussBinom q n 0 = 1 := by
  cases n <;> rfl

theorem gb_succ_succ (q n k : ℕ) :
    gaussBinom q (n + 1) (k + 1) = gaussBinom q n k + q ^ (k + 1) * gaussBinom q n (k + 1) :=
  rfl

theorem gb_eq_zero (q : ℕ) : ∀ n k : ℕ, n < k → gaussBinom q n k = 0
  | 0, 0, h => absurd h (lt_irrefl 0)
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, k + 1, h => by
    rw [gb_succ_succ, gb_eq_zero q n k (by omega), gb_eq_zero q n (k + 1) (by omega)]
    simp

def P (q : ℤ) (m k : ℕ) : ℤ := ∏ i ∈ Finset.range k, (q ^ m - q ^ i)

theorem P_succ_right (q : ℤ) (m k : ℕ) : P q m (k + 1) = P q m k * (q ^ m - q ^ k) := by
  unfold P; rw [Finset.prod_range_succ]

theorem P_succ_succ (q : ℤ) (m k : ℕ) :
    P q (m + 1) (k + 1) = (q ^ (m + 1) - 1) * (q ^ k * P q m k) := by
  unfold P
  rw [Finset.prod_range_succ', pow_zero, mul_comm]
  congr 1
  rw [← Finset.card_range k, ← Finset.prod_const, Finset.card_range, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  ring

theorem gb_mul_P (q : ℤ) (qn : ℕ) (hq : (qn : ℤ) = q) :
    ∀ n k : ℕ, (gaussBinom qn n k : ℤ) * P q k k = P q n k := by
  intro n
  induction n with
  | zero =>
    intro k
    cases k with
    | zero => simp [P, gb_zero_right]
    | succ k =>
      have : P q 0 (k + 1) = 0 := by
        unfold P
        exact Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.succ_pos k)) (by simp)
      rw [this]; simp [gaussBinom]
  | succ n ih =>
    intro k
    cases k with
    | zero => simp [P, gb_zero_right]
    | succ k =>
      rw [gb_succ_succ]
      push_cast
      rw [hq]
      have h1 := ih k
      have h2 := ih (k + 1)
      rw [P_succ_succ q k k, P_succ_succ q n k]
      rw [P_succ_succ q k k, P_succ_right] at h2
      linear_combination (q ^ (k + 1) - 1) * q ^ k * h1 + q ^ (k + 1) * h2

end SubspaceCountP

namespace SubspaceCountP

abbrev LI (F V : Type) [Field F] [AddCommGroup V] [Module F V] (k : ℕ) :=
  {s : Fin k → V // LinearIndependent F s}

abbrev Gr (F W : Type) [Field F] [AddCommGroup W] [Module F W] (k : ℕ) :=
  {U : Submodule F W // finrank F U = k}

variable {F W : Type} [Field F] [AddCommGroup W] [Module F W]

def spanMap (k : ℕ) (s : LI F W k) : Gr F W k :=
  ⟨Submodule.span F (Set.range s.1), (finrank_span_eq_card s.2).trans (Fintype.card_fin k)⟩

variable [Finite W]

def fiberEquiv (k : ℕ) (U : Gr F W k) : {s : LI F W k // spanMap k s = U} ≃ LI F U.1 k where
  toFun s := ⟨fun i => ⟨s.1.1 i, by
      have h := congrArg Subtype.val s.2
      simp only [spanMap] at h
      rw [← h]
      exact Submodule.subset_span ⟨i, rfl⟩⟩, by
      apply LinearIndependent.of_comp U.1.subtype
      exact s.1.2⟩
  invFun t := ⟨⟨U.1.subtype ∘ t.1, t.2.map' _ (Submodule.ker_subtype _)⟩, by
      apply Subtype.ext
      apply Submodule.eq_of_le_of_finrank_eq
      · show Submodule.span F (Set.range (U.1.subtype ∘ t.1)) ≤ U.1
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact (t.1 i).2
      · rw [(spanMap k _).2, U.2]⟩
  left_inv s := rfl
  right_inv t := rfl

end SubspaceCountP

namespace SubspaceCountP

variable {F W : Type} [Field F] [Fintype F] [AddCommGroup W] [Module F W] [Finite W]

theorem card_LI_eq (k : ℕ) :
    Nat.card (LI F W k) =
      Nat.card (Gr F W k) * ∏ i : Fin k, (Fintype.card F ^ k - Fintype.card F ^ i.val) := by
  classical
  let _ := Fintype.ofFinite (Gr F W k)
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (spanMap (F := F) (W := W) k)), Nat.card_sigma]
  have h : ∀ U : Gr F W k, Nat.card {s // spanMap k s = U} =
      ∏ i : Fin k, (Fintype.card F ^ k - Fintype.card F ^ i.val) := by
    intro U
    rw [Nat.card_congr (fiberEquiv k U), card_linearIndependent (by rw [U.2]), U.2]
  simp only [h, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

theorem cast_prod_eq_P (q m k : ℕ) (hq : 1 ≤ q) (hm : k ≤ m) :
    ((∏ i : Fin k, (q ^ m - q ^ i.val) : ℕ) : ℤ) = P (q : ℤ) m k := by
  rw [Nat.cast_prod, P, ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Nat.cast_sub (Nat.pow_le_pow_right hq (by omega))]
  push_cast
  rfl

end SubspaceCountP

open SubspaceCountP in
theorem countSubspacesEq : SubspaceCount := by
  intro F W _ _ _ _ _ k
  classical
  have hcount : countBelow (⊤ : Submodule F W) k = Nat.card (Gr F W k) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun U => by simp))
  rw [hcount]
  rcases lt_or_ge (finrank F W) k with hnk | hkn
  · rw [gb_eq_zero _ _ _ hnk, Nat.card_eq_zero]
    left
    constructor
    rintro ⟨U, hU⟩
    have := Submodule.finrank_le U
    omega
  · have hq : 1 < Fintype.card F := Fintype.one_lt_card
    have h1 := card_LI_eq (F := F) (W := W) k
    rw [card_linearIndependent hkn] at h1
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h1
    rw [Nat.cast_mul, cast_prod_eq_P _ _ _ hq.le hkn, cast_prod_eq_P _ _ _ hq.le le_rfl] at h2
    have h3 := gb_mul_P (Fintype.card F : ℤ) (Fintype.card F) rfl (finrank F W) k
    have hP : P (Fintype.card F : ℤ) k k ≠ 0 := by
      unfold P
      rw [Finset.prod_ne_zero_iff]
      intro i hi
      have : (Fintype.card F : ℤ) ^ i < (Fintype.card F : ℤ) ^ k :=
        pow_lt_pow_right₀ (by exact_mod_cast hq) (Finset.mem_range.mp hi)
      omega
    have : (Nat.card (Gr F W k) : ℤ) = gaussBinom (Fintype.card F) (finrank F W) k :=
      mul_right_cancel₀ hP (h2.symm.trans h3.symm)
    exact_mod_cast this

end Formalism.G0
