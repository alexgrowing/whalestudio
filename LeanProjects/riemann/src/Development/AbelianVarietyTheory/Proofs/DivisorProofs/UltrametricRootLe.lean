import Mathlib

namespace GlobalTheory

open Polynomial

theorem ultrametric_sum_le {K : Type} [Field K] (w : AbsoluteValue K ℝ)
    (hw : ∀ x y, w (x + y) ≤ max (w x) (w y)) {ι : Type*} (s : Finset ι) (f : ι → K)
    (C : ℝ) (hC : 0 ≤ C) : (∀ i ∈ s, w (f i) ≤ C) → w (∑ i ∈ s, f i) ≤ C := by
  classical
  refine Finset.induction_on s ?_ ?_
  · intro _; simp [hC]
  · intro a s ha ih h
    rw [Finset.sum_insert ha]
    exact (hw _ _).trans (max_le (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem ultrametric_root_le : ∀ {A K : Type} [CommRing A] [Field K] (w : AbsoluteValue K ℝ), (∀ x y, w (x + y) ≤ max (w x) (w y)) →
    ∀ (ψ : A →+* K) {d : ℕ} (ζ : Fin d → K), (∀ j, w (ζ j) ≤ 1) →
    ∀ (p : Polynomial (MvPolynomial (Fin d) A)), p.Monic → ∀ (α : K),
      p.eval₂ (MvPolynomial.eval₂Hom ψ ζ) α = 0 → ∀ (B : ℝ), 1 ≤ B →
      (∀ l < p.natDegree, ∀ s ∈ (p.coeff l).support, w (ψ ((p.coeff l).coeff s)) ≤ B) → w α ≤ B := by
  intro A K _ _ w hw ψ d ζ hζ p hp α hα B hB hcoef
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB

  have hc : ∀ l < p.natDegree, w (MvPolynomial.eval₂Hom ψ ζ (p.coeff l)) ≤ B := by
    intro l hl
    rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]
    refine ultrametric_sum_le w hw _ _ B hB0 ?_
    intro s hs
    rw [map_mul, map_prod]
    refine (mul_le_mul (hcoef l hl s hs) ?_ (by positivity) hB0).trans_eq (mul_one B)
    refine Finset.prod_le_one (fun i _ => by positivity) (fun i _ => ?_)
    rw [map_pow]
    exact pow_le_one₀ (by positivity) (hζ i)
  by_contra hlt
  push_neg at hlt
  have hα1 : 1 < w α := lt_of_le_of_lt hB hlt
  set n := p.natDegree with hn
  have hn0 : n ≠ 0 := by
    intro h0
    have h1 : p = 1 := (Polynomial.Monic.natDegree_eq_zero hp).mp h0
    rw [h1, Polynomial.eval₂_one] at hα
    exact one_ne_zero hα
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set f := MvPolynomial.eval₂Hom ψ ζ with hf
  rw [Polynomial.eval₂_eq_sum_range, ← hn, Finset.sum_range_succ] at hα
  have hlead : p.coeff n = 1 := hp
  rw [hlead, map_one, one_mul] at hα
  have hαn : α ^ n = -∑ i ∈ Finset.range n, f (p.coeff i) * α ^ i := eq_neg_of_add_eq_zero_right hα
  have hwpos : 0 < w α ^ m := pow_pos (lt_trans zero_lt_one hα1) m
  have hbound : w (α ^ n) ≤ B * w α ^ m := by
    rw [hαn, AbsoluteValue.map_neg]
    refine ultrametric_sum_le w hw _ _ _ (by positivity) ?_
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    rw [map_mul, map_pow]
    exact mul_le_mul (hc i hi') (pow_le_pow_right₀ hα1.le (by omega)) (by positivity) hB0
  rw [map_pow, hm, pow_succ] at hbound
  have : B * w α ^ m < w α ^ m * w α := by
    rw [mul_comm]; exact mul_lt_mul_of_pos_left hlt hwpos
  linarith

end GlobalTheory
