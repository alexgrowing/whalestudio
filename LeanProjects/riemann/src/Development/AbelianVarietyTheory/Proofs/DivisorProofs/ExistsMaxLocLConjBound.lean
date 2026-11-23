import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside

open Complex ComplexConjugate

noncomputable section

namespace GlobalTheory.JSW.LogPos

theorem prod_inv_one_sub_eq_exp (S : Multiset ℂ) (h : ∀ w ∈ S, ‖w‖ < 1) :
    (S.map fun w => (1 - w)⁻¹).prod = exp (S.map fun w => -log (1 - w)).sum := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons, exp_add,
      ih fun w hw => h w (Multiset.mem_cons_of_mem hw)]
    congr 1
    have ha : 1 - a ≠ 0 := by
      intro h0
      have e : a = 1 := by linear_combination -h0
      have := h a (Multiset.mem_cons_self a S)
      simp [e] at this
    rw [exp_neg, exp_log ha]

theorem hasSum_log (S : Multiset ℂ) (h : ∀ w ∈ S, ‖w‖ < 1) :
    HasSum (fun n : ℕ => (S.map fun w => w ^ n).sum / n) (S.map fun w => -log (1 - w)).sum := by
  induction S using Multiset.induction_on with
  | empty => simpa using hasSum_zero
  | cons a S ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, add_div]
    exact (hasSum_taylorSeries_neg_log (h a (Multiset.mem_cons_self a S))).add
      (ih fun w hw => h w (Multiset.mem_cons_of_mem hw))

theorem sum_pow_product (x : ℂ) (n : ℕ) (s t : Multiset ℂˣ) :
    ((s ×ˢ t).map fun p : ℂˣ × ℂˣ => ((p.1 : ℂ) * p.2 * x) ^ n).sum =
      x ^ n * (s.map fun b : ℂˣ => (b : ℂ) ^ n).sum * (t.map fun b : ℂˣ => (b : ℂ) ^ n).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.cons_product, Multiset.map_add, Multiset.sum_add, ih, Multiset.map_map]
    simp only [Function.comp_def, mul_pow]
    rw [Multiset.sum_map_mul_right, Multiset.sum_map_mul_left, Multiset.map_cons, Multiset.sum_cons]
    ring

theorem sum_pow_star (n : ℕ) (B : Multiset ℂˣ) :
    ((B.map star).map fun b : ℂˣ => (b : ℂ) ^ n).sum = conj (B.map fun b : ℂˣ => (b : ℂ) ^ n).sum := by
  rw [map_multiset_sum, Multiset.map_map, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun b _ => ?_
  simp [Units.coe_star, star_pow]

theorem cpow_neg_eq (q : ℕ) (σ : ℝ) : (q : ℂ) ^ (-(σ : ℂ)) = (((q : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  rw [ofReal_cpow (Nat.cast_nonneg _), ofReal_natCast, ofReal_neg]

theorem norm_pair_le {B : Multiset ℂˣ} {M : ℝ} (hM : ∀ b ∈ B, ‖(b : ℂ)‖ ^ 2 ≤ M) {p : ℂˣ × ℂˣ}
    (hp : p ∈ B ×ˢ B.map star) : ‖(p.1 : ℂ)‖ * ‖(p.2 : ℂ)‖ ≤ M := by
  rw [Multiset.mem_product] at hp
  obtain ⟨b', hb', hpb⟩ := Multiset.mem_map.1 hp.2
  have h1 := hM _ hp.1
  have h2 := hM _ hb'
  have e2 : ‖(p.2 : ℂ)‖ = ‖(b' : ℂ)‖ := by rw [← hpb, Units.coe_star, norm_star]
  rw [e2]
  nlinarith [sq_nonneg (‖(p.1 : ℂ)‖ - ‖(b' : ℂ)‖)]

theorem locL_conj_eq_exp (q : ℕ) (B : Multiset ℂˣ) (M : ℝ) (hM : ∀ b ∈ B, ‖(b : ℂ)‖ ^ 2 ≤ M) (σ : ℝ)
    (hσ : M * (q : ℝ) ^ (-σ) < 1) :
    ∃ L : ℝ, HasSum (fun n : ℕ => ((q : ℝ) ^ (-σ)) ^ n * normSq (B.map fun b : ℂˣ => (b : ℂ) ^ n).sum / n) L ∧
      locL q B (B.map star) σ = Real.exp L := by
  set x : ℝ := (q : ℝ) ^ (-σ) with hxdef
  have hx0 : 0 ≤ x := Real.rpow_nonneg (Nat.cast_nonneg _) _
  set S := (B ×ˢ B.map star).map fun p : ℂˣ × ℂˣ => (p.1 : ℂ) * p.2 * x with hSdef
  have hS : ∀ w ∈ S, ‖w‖ < 1 := by
    intro w hw
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hw
    have := norm_pair_le hM hp
    rw [norm_mul, norm_mul, norm_real, Real.norm_of_nonneg hx0]
    nlinarith [mul_le_mul_of_nonneg_right this hx0]
  have hloc : locL q B (B.map star) σ = (S.map fun w => (1 - w)⁻¹).prod := by
    simp only [locL, cpow_neg_eq, ← hxdef, hSdef, Multiset.map_map, Function.comp_def]
  have hterm : ∀ n : ℕ, (S.map fun w => w ^ n).sum / n =
      ((x ^ n * normSq (B.map fun b : ℂˣ => (b : ℂ) ^ n).sum / n : ℝ) : ℂ) := by
    intro n
    simp only [hSdef, Multiset.map_map, Function.comp_def]
    rw [sum_pow_product, sum_pow_star, mul_assoc, mul_conj]
    push_cast
    ring
  have hL := hasSum_log S hS
  simp only [hterm] at hL
  have hre := Complex.hasSum_re hL
  have him := Complex.hasSum_im hL
  simp only [ofReal_re, ofReal_im] at hre him
  have hLim := him.unique hasSum_zero
  refine ⟨_, hre, ?_⟩
  rw [hloc, prod_inv_one_sub_eq_exp S hS, ofReal_exp]
  congr 1
  exact Complex.ext (by rw [ofReal_re]) (by rw [ofReal_im, hLim])

end GlobalTheory.JSW.LogPos
