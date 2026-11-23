import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement

noncomputable section

namespace GlobalTheory.ColNorms.SumBound

open NumberField IsDedekindDomain
open Formalism.L2.DIV Formalism.L2.Col GlobalTheory.ColNorms
open scoped ComplexOrder Matrix

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K) (v : InfinitePlace K)

theorem pairAt_add_left (x y z : S.V) : S.pairAt v (x + y) z = S.pairAt v x z + S.pairAt v y z := by
  simp only [GSD.pairAt, map_add, Finsupp.add_apply, add_mul, Finset.sum_add_distrib]

theorem pairAt_add_right (x y z : S.V) : S.pairAt v x (y + z) = S.pairAt v x y + S.pairAt v x z := by
  simp only [GSD.pairAt, map_add, Finsupp.add_apply, mul_add, Finset.sum_add_distrib]

theorem pairAt_smul_left (a : K) (x y : S.V) :
    S.pairAt v (a • x) y = starRingEnd ℂ (v.embedding a) * S.pairAt v x y := by
  simp only [GSD.pairAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem pairAt_smul_right (a : K) (x y : S.V) :
    S.pairAt v x (a • y) = v.embedding a * S.pairAt v x y := by
  simp only [GSD.pairAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem pairAt_zero_left (y : S.V) : S.pairAt v 0 y = 0 := by
  simp [GSD.pairAt]

theorem pairAt_zero_right (y : S.V) : S.pairAt v y 0 = 0 := by
  simp [GSD.pairAt]

theorem pairAt_sum_left {α : Type*} (s : Finset α) (x : α → S.V) (y : S.V) :
    S.pairAt v (∑ i ∈ s, x i) y = ∑ i ∈ s, S.pairAt v (x i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pairAt_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pairAt_add_left, ih]

theorem pairAt_sum_right {α : Type*} (s : Finset α) (x : α → S.V) (y : S.V) :
    S.pairAt v y (∑ i ∈ s, x i) = ∑ i ∈ s, S.pairAt v y (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pairAt_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pairAt_add_right, ih]

theorem pairAt_self_nonneg (h : PosAt S v) (x : S.V) : 0 ≤ (S.pairAt v x x).re := by
  have h1 := h.dotProduct_mulVec_nonneg (fun i => v.embedding (S.bV.repr x i))
  have h2 : S.pairAt v x x = star (fun i => v.embedding (S.bV.repr x i)) ⬝ᵥ
      (S.gramV.map v.embedding) *ᵥ (fun i => v.embedding (S.bV.repr x i)) := by
    simp only [GSD.pairAt, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.map_apply, Pi.star_apply, mul_assoc]
    rfl
  rw [h2]
  exact (Complex.nonneg_iff.mp h1).1

theorem pairAt_smul_self (a : K) (x : S.V) :
    (S.pairAt v (a • x) (a • x)).re = ‖v.embedding a‖ ^ 2 * (S.pairAt v x x).re := by
  rw [pairAt_smul_left, pairAt_smul_right, ← mul_assoc, Complex.conj_mul', ← Complex.ofReal_pow, Complex.re_ofReal_mul]

theorem pairAt_inv_nat_smul_self (n : ℕ) (x : S.V) :
    (S.pairAt v (((n : K))⁻¹ • x) (((n : K))⁻¹ • x)).re = ((n : ℝ)⁻¹) ^ 2 * (S.pairAt v x x).re := by
  rw [pairAt_smul_self]
  simp

theorem pairAt_cross_le (h : PosAt S v) (x y : S.V) :
    (S.pairAt v x y).re + (S.pairAt v y x).re ≤ (S.pairAt v x x).re + (S.pairAt v y y).re := by
  have h1 := pairAt_self_nonneg S v h (x + (-1 : K) • y)
  rw [pairAt_add_left, pairAt_add_right, pairAt_add_right, pairAt_smul_left, pairAt_smul_left,
    pairAt_smul_right, pairAt_smul_right] at h1
  simp at h1
  linarith

theorem pairAt_sum_le (h : PosAt S v) {α : Type*} (s : Finset α) (x : α → S.V) :
    (S.pairAt v (∑ i ∈ s, x i) (∑ i ∈ s, x i)).re ≤ (s.card : ℝ) * ∑ i ∈ s, (S.pairAt v (x i) (x i)).re := by
  have e1 : (S.pairAt v (∑ i ∈ s, x i) (∑ i ∈ s, x i)).re = ∑ i ∈ s, ∑ j ∈ s, (S.pairAt v (x i) (x j)).re := by
    rw [pairAt_sum_left, Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [pairAt_sum_right, Complex.re_sum]
  have e2 : (S.pairAt v (∑ i ∈ s, x i) (∑ i ∈ s, x i)).re = ∑ i ∈ s, ∑ j ∈ s, (S.pairAt v (x j) (x i)).re := by
    rw [e1, Finset.sum_comm]
  have e3 : ∑ i ∈ s, ∑ j ∈ s, ((S.pairAt v (x i) (x j)).re + (S.pairAt v (x j) (x i)).re) ≤
      ∑ i ∈ s, ∑ j ∈ s, ((S.pairAt v (x i) (x i)).re + (S.pairAt v (x j) (x j)).re) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => pairAt_cross_le S v h _ _
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at e3
  linarith

theorem ipAt_re (h : S.Ok) (φ ψ : S.D → S.V) :
    (S.ipAt h v φ ψ).re = ∑ c ∈ @Finset.univ _ h.fintypeCl,
      (((S.toCSD h).wt c : ℕ) : ℝ)⁻¹ * (S.pairAt v (φ (S.outSec.rep c)) (ψ (S.outSec.rep c))).re := by
  unfold GSD.ipAt
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul]

theorem inv_nat_le_one (n : ℕ) : ((n : ℝ))⁻¹ ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact inv_le_one_of_one_le₀ (by exact_mod_cast hn)

theorem ipAt_self_nonneg (h : S.Ok) (hp : PosAt S v) (φ : S.D → S.V) : 0 ≤ (S.ipAt h v φ φ).re := by
  rw [ipAt_re]
  exact Finset.sum_nonneg fun c _ => mul_nonneg (by positivity) (pairAt_self_nonneg S v hp _)

theorem ipAt_self_le (h : S.Ok) (hp : PosAt S v) (φ : S.D → S.V) (B : ℝ)
    (hB : ∀ d, (S.pairAt v (φ d) (φ d)).re ≤ B) : (S.ipAt h v φ φ).re ≤ (Nat.card S.Cl : ℝ) * B := by
  rw [ipAt_re]
  letI := h.fintypeCl
  calc _ ≤ ∑ _c : S.Cl, B := Finset.sum_le_sum fun c _ => by
        have h0 := pairAt_self_nonneg S v hp (φ (S.outSec.rep c))
        exact ((mul_le_mul_of_nonneg_right (inv_nat_le_one _) h0).trans (by rw [one_mul])).trans (hB _)
    _ = _ := by simp [Nat.card_eq_fintype_card]

variable {S} in

theorem appOf_le {S' : GSD K} (A : ClsKer S S') (h : S.Ok) (hp : PosAt S v) (hp' : PosAt S' v) (t : ℝ) (ht : 0 ≤ t)
    (φ : S.D → S.V) (d' : S'.D) (hA : ∀ d, OpLe S S' v (A.k d d') t) :
    (S'.pairAt v (A.appOf h S.outSec φ d') (A.appOf h S.outSec φ d')).re ≤
      (Nat.card S.Cl : ℝ) * (t * (S.ipAt h v φ φ).re) := by
  letI := h.fintypeCl
  unfold ClsKer.appOf
  refine (pairAt_sum_le S' v hp' _ _).trans ?_
  rw [Finset.card_univ, Nat.card_eq_fintype_card, ipAt_re, Finset.mul_sum _ _ t]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => ?_) (by positivity)
  rw [pairAt_inv_nat_smul_self]
  have h0 := pairAt_self_nonneg S v hp (φ (S.outSec.rep c))
  have h1 := hA (S.outSec.rep c) (φ (S.outSec.rep c))
  have h2 := inv_nat_le_one ((S.toCSD h).wt c)
  have h3 : (0 : ℝ) ≤ (((S.toCSD h).wt c : ℕ) : ℝ)⁻¹ := by positivity
  change (((S.toCSD h).wt c : ℕ) : ℝ)⁻¹ ^ 2 * _ ≤ _
  generalize (((S.toCSD h).wt c : ℕ) : ℝ)⁻¹ = w at *
  calc _ ≤ w ^ 2 * (t * (S.pairAt v (φ (S.outSec.rep c)) (φ (S.outSec.rep c))).re) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ w * (t * (S.pairAt v (φ (S.outSec.rep c)) (φ (S.outSec.rep c))).re) :=
        mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    _ = _ := by ring

end GlobalTheory.ColNorms.SumBound
