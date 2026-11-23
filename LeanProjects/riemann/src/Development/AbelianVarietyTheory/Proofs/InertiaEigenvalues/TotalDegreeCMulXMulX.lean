import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch

noncomputable section

namespace GlobalTheory.NormUnits

variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]

def intRing : Subring K where
  carrier := Metric.closedBall 0 1
  mul_mem' {a b} ha hb := by
    simp only [mem_closedBall_zero_iff] at *
    rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [mem_closedBall_zero_iff] at *
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha

theorem norm_le_one (x : intRing K) : ‖(x : K)‖ ≤ 1 := mem_closedBall_zero_iff.1 x.2

def maxIdeal : Ideal (intRing K) where
  carrier := {x | ‖(x : K)‖ < 1}
  add_mem' {a b} ha hb := by
    show ‖(a : K) + b‖ < 1
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)
  zero_mem' := by show ‖((0 : intRing K) : K)‖ < 1; simp
  smul_mem' c x hx := by
    show ‖(c : K) * x‖ < 1
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_le_one K c)).trans_lt hx

theorem mem_maxIdeal (x : intRing K) : x ∈ maxIdeal K ↔ ‖(x : K)‖ < 1 := Iff.rfl

instance maxIdeal_isMaximal : (maxIdeal K).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨fun h => by rw [mem_maxIdeal] at h; simp at h, fun J x hle hx hxJ => ?_⟩
  rw [mem_maxIdeal, not_lt] at hx
  have h1 : ‖(x : K)‖ = 1 := le_antisymm (norm_le_one K x) hx
  have hx0 : (x : K) ≠ 0 := by intro h; rw [h, norm_zero] at h1; exact zero_ne_one h1
  let y : intRing K := ⟨(x : K)⁻¹, mem_closedBall_zero_iff.2 (by rw [norm_inv, h1, inv_one])⟩
  have hyx : y * x = 1 := Subtype.ext (by simp [y, inv_mul_cancel₀ hx0])
  rw [← hyx]; exact J.mul_mem_left y hxJ

theorem finite_res [LocallyCompactSpace K] : Finite (intRing K ⧸ maxIdeal K) := by
  haveI : ProperSpace K := ProperSpace.of_locallyCompactSpace K
  haveI : CompactSpace (intRing K) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : K) 1)
  have hopen : IsOpen ((maxIdeal K : Set (intRing K))) := by
    have e : ((maxIdeal K : Set (intRing K))) = Subtype.val ⁻¹' Metric.ball (0 : K) 1 := by
      ext x; simp [mem_maxIdeal]
    rw [e]; exact Metric.isOpen_ball.preimage continuous_subtype_val
  exact AddSubgroup.quotient_finite_of_isOpen (maxIdeal K).toAddSubgroup hopen

end GlobalTheory.NormUnits

namespace GlobalTheory.NormUnits
open MvPolynomial

variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]

abbrev Res : Type := intRing K ⧸ maxIdeal K

instance : Field (Res K) := Ideal.Quotient.field _

theorem totalDegree_C_mul_X_mul_X {k : Type} [Field k] (r : k) (i j : Fin 3) :
    (C r * (X i * X j) : MvPolynomial (Fin 3) k).totalDegree ≤ 2 := by
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_mul _ _).trans ?_
  simp [totalDegree_X]

theorem exists_point_mod [LocallyCompactSpace K] (s t c : K) (hs : ‖s‖ ≤ 1) (ht : ‖t‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    ∃ a b z : K, ‖a‖ ≤ 1 ∧ ‖b‖ ≤ 1 ∧ ‖z‖ ≤ 1 ∧ (‖a‖ = 1 ∨ ‖b‖ = 1 ∨ ‖z‖ = 1) ∧
      ‖a ^ 2 + s * a * b + t * b ^ 2 - c * z ^ 2‖ < 1 := by
  classical
  haveI := finite_res K
  letI : Fintype (Res K) := Fintype.ofFinite _
  let k := Res K
  let π : intRing K →+* k := Ideal.Quotient.mk _
  let S : intRing K := ⟨s, mem_closedBall_zero_iff.2 hs⟩
  let T : intRing K := ⟨t, mem_closedBall_zero_iff.2 ht⟩
  let Cc : intRing K := ⟨c, mem_closedBall_zero_iff.2 hc⟩
  set p := ringChar k
  haveI : CharP k p := ringChar.charP k
  obtain ⟨n, hpp, -⟩ := FiniteField.card (K := k) p
  let f : MvPolynomial (Fin 3) k := C 1 * (X 0 * X 0) + C (π S) * (X 0 * X 1) + C (π T) * (X 1 * X 1) +
    C (-π Cc) * (X 2 * X 2)
  have hdeg : f.totalDegree < Fintype.card (Fin 3) := by
    have h1 := totalDegree_C_mul_X_mul_X (1 : k) 0 0
    have h2 := totalDegree_C_mul_X_mul_X (π S) 0 1
    have h3 := totalDegree_C_mul_X_mul_X (π T) 1 1
    have h4 := totalDegree_C_mul_X_mul_X (-π Cc) 2 2
    have := (totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans (max_le
      ((totalDegree_add _ _).trans (max_le h1 h2)) h3)) h4)
    simp only [Fintype.card_fin]
    exact lt_of_le_of_lt this (by norm_num)
  have hdvd := char_dvd_card_solutions p hdeg
  have hpos : 0 < Fintype.card {x : Fin 3 → k // eval x f = 0} :=
    Fintype.card_pos_iff.2 ⟨⟨0, by simp [f]⟩⟩
  have h1lt : 1 < Fintype.card {x : Fin 3 → k // eval x f = 0} :=
    lt_of_lt_of_le hpp.one_lt (Nat.le_of_dvd hpos hdvd)
  obtain ⟨x, hx⟩ := Fintype.exists_ne_of_one_lt_card h1lt ⟨0, by simp [f]⟩
  have hx0 : x.1 ≠ 0 := fun h => hx (Subtype.ext h)
  choose l hl using fun i => Ideal.Quotient.mk_surjective (I := maxIdeal K) (x.1 i)
  have hval : π (l 0 * l 0 + S * (l 0 * l 1) + T * (l 1 * l 1) + (-Cc) * (l 2 * l 2)) = 0 := by
    have := x.2
    simp only [f, map_add, map_mul, eval_C, eval_X, map_neg, one_mul] at this
    simp only [map_add, map_mul, map_neg, π, hl]
    linear_combination this
  have hmem := (Ideal.Quotient.eq_zero_iff_mem).1 hval
  rw [mem_maxIdeal] at hmem
  have hunit : ∀ i, x.1 i ≠ 0 → ‖((l i : intRing K) : K)‖ = 1 := by
    intro i hi
    refine le_antisymm (norm_le_one K _) (not_lt.1 fun h => hi ?_)
    rw [← hl i]; exact (Ideal.Quotient.eq_zero_iff_mem).2 ((mem_maxIdeal K _).2 h)
  refine ⟨l 0, l 1, l 2, norm_le_one K _, norm_le_one K _, norm_le_one K _, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hx0
    fin_cases i
    · exact Or.inl (hunit 0 hi)
    · exact Or.inr (Or.inl (hunit 1 hi))
    · exact Or.inr (Or.inr (hunit 2 hi))
  · convert hmem using 2
    simp only [S, T, Cc, Subring.coe_add, Subring.coe_mul, Subring.coe_neg]
    ring

end GlobalTheory.NormUnits

namespace GlobalTheory.NormUnits

variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]

theorem exists_sqrt_mod [LocallyCompactSpace K] (t : K) (ht : ‖t‖ ≤ 1) (h2 : ‖(2 : K)‖ < 1) :
    ∃ r : K, ‖r‖ ≤ 1 ∧ ‖r ^ 2 - t‖ < 1 := by
  classical
  haveI := finite_res K
  letI : Fintype (Res K) := Fintype.ofFinite _
  let T : intRing K := ⟨t, mem_closedBall_zero_iff.2 ht⟩
  have h2k : (2 : Res K) = 0 := by
    have h11 : (((1 + 1 : intRing K)) : K) = 2 := by
      rw [Subring.coe_add, Subring.coe_one]; norm_num
    have : (Ideal.Quotient.mk (maxIdeal K) (1 + 1) : Res K) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).2 ((mem_maxIdeal K _).2 (by rw [h11]; exact h2))
    rw [map_add, map_one] at this
    rw [← one_add_one_eq_two]; exact this
  have hchar : ringChar (Res K) = 2 := by
    have hd : ringChar (Res K) ∣ 2 := ringChar.dvd (by exact_mod_cast h2k)
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
    · exact absurd h (CharP.ringChar_ne_one)
    · exact h
  obtain ⟨y, hy⟩ := FiniteField.isSquare_of_char_two hchar (Ideal.Quotient.mk (maxIdeal K) T)
  obtain ⟨l, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨l, norm_le_one K l, ?_⟩
  have h0 : Ideal.Quotient.mk (maxIdeal K) (l * l - T) = 0 := by
    rw [map_sub, map_mul, ← hy, sub_self]
  have hm := (mem_maxIdeal K _).1 ((Ideal.Quotient.eq_zero_iff_mem).1 h0)
  simpa [sq, T] using hm

end GlobalTheory.NormUnits
