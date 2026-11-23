import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CharIdem
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders

noncomputable section
open Polynomial Classical
namespace GlobalTheory.BadShare.Basic

section Central
variable {G : Type} [Group G] [Fintype G]

end Central

variable {g : ℕ} [Fact g.Prime] {N : ℕ}

open Formalism.MainNotions.ArithmeticCylinders in

theorem isUp_iff_isUniUp (u : GG g N) : IsUp g N u ↔ IsUniUp u.val := by
  unfold IsUp IsUniUp
  constructor
  · rintro ⟨h1, h2⟩ a b
    refine ⟨h2 a b, fun hab => ?_⟩
    subst hab
    exact h1 a
  · intro h
    exact ⟨fun a => (h a a).2 rfl, fun a b hab => (h a b).1 hab⟩

open Formalism.MainNotions.ArithmeticCylinders in

theorem coeff_eDat (P : Matrix (Fin N) (Fin N) (ZMod g) → Prop) (φ : Matrix (Fin N) (Fin N) (ZMod g) → ZMod g)
    (ψ : AddChar (ZMod g) ℂ) (x : GG g N) :
    (eDat g N P φ ψ).coeff x = eps (fun u : GG g N => P u.val) (fun u => ψ (φ u.val)) x := by
  classical
  unfold eDat eps
  simp only [MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.smul_apply,
    Finsupp.finsetSum_apply, Finsupp.single_apply, smul_eq_mul]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs
  · rw [Nat.card_eq_fintype_card, Fintype.card_subtype, div_eq_inv_mul]
  · simp

open Formalism.MainNotions.ArithmeticCylinders in

theorem sum_ite_entN (M : Matrix (Fin N) (Fin N) (ZMod g)) (a : Fin N) (c : ℕ) :
    (∑ b : Fin N, if (b : ℕ) = c then M a b else 0) = entN M a c := by
  unfold entN
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨c, h.2⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro hbc
      exact hb (Fin.ext hbc)
    · simp
  · apply Finset.sum_eq_zero
    intro b _
    rw [if_neg]
    intro hbc
    exact h ⟨a.isLt, hbc ▸ b.isLt⟩

private theorem sum_superdiag_eq_sum_entN (M : Matrix (Fin N) (Fin N) (ZMod g)) (hN : 0 < N) :
    (∑ a : Fin N, ∑ b : Fin N, if (b : ℕ) = a + 1 then M a b else 0) =
      ∑ i ∈ Finset.range (N - 1), Formalism.MainNotions.ArithmeticCylinders.entN M i (i + 1) := by
  simp only [sum_ite_entN]
  rw [Fin.sum_univ_eq_sum_range (fun i => Formalism.MainNotions.ArithmeticCylinders.entN M i (i + 1)) N]
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [Finset.sum_range_succ, Nat.add_sub_cancel,
    show Formalism.MainNotions.ArithmeticCylinders.entN M n (n + 1) = 0 by unfold Formalism.MainNotions.ArithmeticCylinders.entN; rw [dif_neg (by omega)], add_zero]

open Formalism.MainNotions.ArithmeticCylinders in

theorem coeff_eU (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (s k : ℕ) (h : s + k < N) (x : GG g N) :
    (eU g N ψ).coeff x = (levOfChar ψ hψ N false s k h).e x := by
  have hN : 0 < N := by omega
  rw [eU, coeff_eDat]
  unfold levOfChar Lev.e Lev.Mem Lev.chi Lev.Edge
  simp only [Bool.false_eq_true, ↓reduceIte, false_implies, and_true, isUp_iff_isUniUp,
    Units.val_one, one_mul, sum_superdiag_eq_sum_entN _ hN]

private theorem sum_range_eq_sum_split_of_last_eq_zero {R : Type} [AddCommMonoid R] (f F : ℕ → R) (s k N : ℕ) (hN : N = k + 2 * s + 1)
    (hF : ∀ i, F i = if i + 1 ≠ s ∧ ¬(0 < k ∧ i + 1 = s + k) then f i else 0) (hf : f (N - 1) = 0) :
    ∑ i ∈ Finset.range N, F i = ∑ i ∈ Finset.range (s - 1), f i + (if 1 ≤ s then f (s + k) else 0) +
      ∑ i ∈ Finset.range (s - 1), f (s + k + 1 + i) + ∑ a ∈ Finset.range (k - 1), f (s + a) := by
  have pos : ∀ i, i + 1 ≠ s → ¬(0 < k ∧ i + 1 = s + k) → F i = f i := fun i h1 h2 => by
    rw [hF, if_pos ⟨h1, h2⟩]
  have neg : ∀ i, ¬(i + 1 ≠ s ∧ ¬(0 < k ∧ i + 1 = s + k)) → F i = 0 := fun i h => by
    rw [hF, if_neg h]
  subst hN
  rcases s with _ | t <;> rcases k with _ | j
  · rw [show 0 + 2 * 0 + 1 = 1 from rfl, Finset.sum_range_one, pos 0 (by omega) (by omega)]
    simpa using hf
  · rw [show j + 1 + 2 * 0 + 1 = j + 1 + 1 by omega, Finset.sum_range_succ, Finset.sum_range_succ,
      neg j (by omega), pos (j + 1) (by omega) (by omega), show f (j + 1) = 0 by simpa using hf]
    simp only [Nat.zero_sub, Finset.range_zero, Finset.sum_empty, Nat.add_sub_cancel, zero_add, add_zero]
    rw [if_neg (by omega), zero_add]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    exact pos i (by omega) (by omega)
  · rw [show 0 + 2 * (t + 1) + 1 = t + 1 + 1 + t + 1 by omega, Finset.sum_range_succ, Finset.sum_range_add,
      Finset.sum_range_succ, Finset.sum_range_succ, neg t (by omega), pos (t + 1) (by omega) (by omega),
      pos (t + 1 + 1 + t) (by omega) (by omega), show f (t + 1 + 1 + t) = 0 by
        rw [show t + 1 + 1 + t = 0 + 2 * (t + 1) + 1 - 1 by omega]; exact hf]
    rw [Nat.add_sub_cancel, if_pos (by omega), Nat.zero_sub, Finset.range_zero, Finset.sum_empty]
    have e1 : ∑ i ∈ Finset.range t, F i = ∑ i ∈ Finset.range t, f i :=
      Finset.sum_congr rfl (fun i hi => pos i (by simp at hi; omega) (by omega))
    have e2 : ∑ i ∈ Finset.range t, F (t + 1 + 1 + i) = ∑ i ∈ Finset.range t, f (t + 1 + 0 + 1 + i) :=
      Finset.sum_congr rfl (fun i hi => pos _ (by omega) (by omega))
    rw [e1, e2]
    abel_nf
  · rw [show j + 1 + 2 * (t + 1) + 1 = t + 1 + j + 1 + 1 + t + 1 by omega, Finset.sum_range_succ,
      Finset.sum_range_add, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_add,
      Finset.sum_range_succ, neg t (by omega), neg (t + 1 + j) (by omega),
      pos (t + 1 + j + 1) (by omega) (by omega), pos (t + 1 + j + 1 + 1 + t) (by omega) (by omega),
      show f (t + 1 + j + 1 + 1 + t) = 0 by
        rw [show t + 1 + j + 1 + 1 + t = j + 1 + 2 * (t + 1) + 1 - 1 by omega]; exact hf]
    rw [Nat.add_sub_cancel, Nat.add_sub_cancel, if_pos (by omega)]
    have e1 : ∑ i ∈ Finset.range t, F i = ∑ i ∈ Finset.range t, f i :=
      Finset.sum_congr rfl (fun i hi => pos i (by simp at hi; omega) (by simp at hi; omega))
    have e2 : ∑ i ∈ Finset.range j, F (t + 1 + i) = ∑ i ∈ Finset.range j, f (t + 1 + i) :=
      Finset.sum_congr rfl (fun i hi => pos _ (by omega) (by simp at hi; omega))
    have e3 : ∑ i ∈ Finset.range t, F (t + 1 + j + 1 + 1 + i) =
        ∑ i ∈ Finset.range t, f (t + 1 + (j + 1) + 1 + i) :=
      Finset.sum_congr rfl (fun i hi => pos _ (by omega) (by omega))
    rw [e1, e2, e3]
    abel_nf

open Formalism.MainNotions.ArithmeticCylinders in

theorem sum_edge_eq_phiJ (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (s k : ℕ) (hN : N = k + 2 * s + 1) (h : s + k < N)
    (M : Matrix (Fin N) (Fin N) (ZMod g)) :
    (∑ a, ∑ b, if (levOfChar ψ hψ N true s k h).Edge a b then M a b else 0) = phiJ k s M := by
  unfold levOfChar Lev.Edge
  simp only [↓reduceIte]
  have inner : ∀ a : Fin N, (∑ b : Fin N, if ((b : ℕ) = a + 1 ∧ (a : ℕ) + 1 ≠ s ∧ ¬(0 < k ∧ (a : ℕ) + 1 = s + k) ∨
      (a : ℕ) + 1 = s ∧ (b : ℕ) = s + k) then M a b else 0) =
      (if (a : ℕ) + 1 ≠ s ∧ ¬(0 < k ∧ (a : ℕ) + 1 = s + k) then entN M a (a + 1) else 0) +
        (if (a : ℕ) + 1 = s then entN M a (s + k) else 0) := by
    intro a
    have hb : ∀ b : Fin N, (if ((b : ℕ) = a + 1 ∧ (a : ℕ) + 1 ≠ s ∧ ¬(0 < k ∧ (a : ℕ) + 1 = s + k) ∨
        (a : ℕ) + 1 = s ∧ (b : ℕ) = s + k) then M a b else 0) =
        (if (a : ℕ) + 1 ≠ s ∧ ¬(0 < k ∧ (a : ℕ) + 1 = s + k) then (if (b : ℕ) = a + 1 then M a b else 0) else 0) +
          (if (a : ℕ) + 1 = s then (if (b : ℕ) = s + k then M a b else 0) else 0) := by
      intro b
      by_cases p1 : (b : ℕ) = a + 1 <;> by_cases p2 : (a : ℕ) + 1 = s <;>
        by_cases p3 : (0 < k ∧ (a : ℕ) + 1 = s + k) <;> by_cases p4 : (b : ℕ) = s + k <;> simp [p1, p2, p3, p4]
    rw [Finset.sum_congr rfl (fun b _ => hb b), Finset.sum_add_distrib, Finset.sum_ite_irrel, Finset.sum_ite_irrel,
      sum_ite_entN, sum_ite_entN, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl (fun a _ => inner a), Finset.sum_add_distrib,
    Fin.sum_univ_eq_sum_range (fun i => if i + 1 ≠ s ∧ ¬(0 < k ∧ i + 1 = s + k) then entN M i (i + 1) else 0) N,
    Fin.sum_univ_eq_sum_range (fun i => if i + 1 = s then entN M i (s + k) else 0) N,
    sum_range_eq_sum_split_of_last_eq_zero (fun i => entN M i (i + 1)) (fun i => if i + 1 ≠ s ∧ ¬(0 < k ∧ i + 1 = s + k) then entN M i (i + 1) else 0)
      s k N hN (fun i => rfl) (by unfold entN; rw [dif_neg (by omega)])]
  have e2 : ∑ i ∈ Finset.range N, (if i + 1 = s then entN M i (s + k) else 0) =
      if 1 ≤ s then entN M (s - 1) (s + k) else 0 := by
    rcases s with _ | t
    · rw [if_neg (by omega)]
      exact Finset.sum_eq_zero (fun i _ => if_neg (by omega))
    · rw [if_pos (by omega), Nat.add_sub_cancel]
      simp only [Nat.add_right_cancel_iff]
      rw [Finset.sum_ite_eq' (Finset.range N) t, if_pos (Finset.mem_range.mpr (by omega))]
  have e3 : ∑ i ∈ Finset.range (s - 1), entN M (s + k + 1 + i) (s + k + 1 + i + 1) =
      ∑ i ∈ Finset.range (s - 1), entN M (s + k + 1 + i) (s + k + 2 + i) :=
    Finset.sum_congr rfl (fun i _ => by rw [show s + k + 1 + i + 1 = s + k + 2 + i by omega])
  rw [e2, e3]
  unfold phiJ
  by_cases hs : 1 ≤ s
  · simp only [if_pos hs]
    abel
  · simp only [if_neg hs]
    abel

open Formalism.MainNotions.ArithmeticCylinders in

theorem coeff_eJ (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (s k : ℕ) (hN : N = k + 2 * s + 1) (h : s + k < N) (x : GG g N) :
    (eJ g N k s ψ).coeff x = (levOfChar ψ hψ N true s k h).e x := by
  rw [eJ, coeff_eDat]
  unfold Lev.e
  congr 1
  · funext u
    unfold levOfChar Lev.Mem
    simp only [isUp_iff_isUniUp, forall_const]
    apply propext
    apply and_congr_right
    intro _
    constructor
    · intro H a b h1 h2 h3
      rw [show b = ⟨s + k, by omega⟩ from Fin.ext h3]
      have := H a h1 h2
      unfold entN at this
      rw [dif_pos ⟨a.isLt, by omega⟩] at this
      exact this
    · intro H a h1 h2
      unfold entN
      rw [dif_pos ⟨by omega, by omega⟩]
      exact H ⟨a, by omega⟩ ⟨s + k, by omega⟩ h1 h2 rfl
  · funext u
    have hE := sum_edge_eq_phiJ ψ hψ s k hN h (u : Matrix (Fin N) (Fin N) (ZMod g))
    unfold levOfChar at hE
    unfold levOfChar Lev.chi
    simp only [Units.val_one, one_mul]
    rw [hE]

end GlobalTheory.BadShare.Basic
