import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotRedOfMem
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassCurvePointOfLatticeAddOfGeneric

open Formalism.L2.Th1.F GlobalTheory.Klein
open scoped ComplexConjugate BigOperators

namespace GlobalTheory.Klein.DiffUnit

variable {p : ℕ} [Fact p.Prime]

def ball (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := fun {a b} ha hb =>
    (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := fun {a} ha => by simpa using ha

theorem norm_two (hp : p ≠ 2) : ‖(2 : ℂ_[p])‖ = 1 := by
  have h1 : ‖((2 : ℕ) : ℚ_[p])‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff]
    exact (Nat.coprime_primes Fact.out Nat.prime_two).2 hp
  have h2 : (2 : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] ((2 : ℕ) : ℚ_[p]) := by
    rw [map_natCast]; norm_num
  rw [h2, norm_algebraMap', h1]

theorem le_one_of_sq {s : ℂ_[p]} (h : s ^ 2 ∈ ball p) : s ∈ ball p := by
  have h' : ‖s ^ 2‖ ≤ 1 := h
  rw [norm_pow] at h'
  exact (sq_le_one_iff₀ (norm_nonneg s)).1 h'

theorem disc_eq {K : Type*} [Field K] (h r g₂ g₃ P Q y z s t : K) (hh : 2 * h = 1) (hD : P - Q ≠ 0)
    (hy : y ^ 2 = 4 * P ^ 3 - g₂ * P - g₃) (hz : z ^ 2 = 4 * Q ^ 3 - g₂ * Q - g₃)
    (hs : s * (P - Q) = y - z) (ht : t * (P - Q) = y + z) :
    ∃ A B C : K, A = 12 * (P - r) + 12 * r ∧
      B = s * t + (4 * ((Q - r) + 2 * (P - r)) + 12 * r) ∧
      C = h ^ 2 * (s + t) ^ 2 * ((P - r) - (Q - r)) ∧
      g₂ ^ 3 - 27 * g₃ ^ 2 = (P - Q) * (h ^ 4 * (B * (A ^ 2 * (B * ((P - r) - (Q - r)))
        - 16 * (B * ((P - r) - (Q - r))) ^ 2 + 72 * A * (C * ((P - r) - (Q - r))))
        - C * (4 * A ^ 3 + 432 * (C * ((P - r) - (Q - r)))))) := by
  refine ⟨_, _, _, rfl, rfl, rfl, ?_⟩
  set B := s * t + (4 * ((Q - r) + 2 * (P - r)) + 12 * r) with hB
  set C := h ^ 2 * (s + t) ^ 2 * ((P - r) - (Q - r)) with hC
  have e1 : B * (P - Q) = 12 * P ^ 2 - g₂ := by
    apply mul_right_cancel₀ hD
    have : (s * (P - Q)) * (t * (P - Q)) = (y - z) * (y + z) := by rw [hs, ht]
    rw [hB]
    linear_combination this + hy - hz
  have e2 : C * (P - Q) = 4 * P ^ 3 - g₂ * P - g₃ := by
    have : (s + t) * (P - Q) = 2 * y := by linear_combination hs + ht
    have h3 : C * (P - Q) = h ^ 2 * ((s + t) * (P - Q)) ^ 2 := by rw [hC]; ring
    rw [h3, this, ← hy]
    linear_combination y ^ 2 * (2 * h + 1) * hh
  have e3 : (P - r) - (Q - r) = P - Q := by ring
  clear_value B C
  rw [e3, e1, e2]
  have e4 : 16 * h ^ 4 = 1 := by
    have : 16 * h ^ 4 = (2 * h) ^ 4 := by ring
    rw [this, hh, one_pow]
  linear_combination -(g₂ ^ 3 - 27 * g₃ ^ 2) * e4
    - h ^ 4 * ((12 * P) ^ 2 * (12 * P ^ 2 - g₂) - 16 * (12 * P ^ 2 - g₂) ^ 2
        + 72 * (12 * P) * (4 * P ^ 3 - g₂ * P - g₃)) * e1
    + h ^ 4 * (4 * (12 * P) ^ 3 + 432 * (4 * P ^ 3 - g₂ * P - g₃)) * e2

end GlobalTheory.Klein.DiffUnit

namespace GlobalTheory.Klein
open DiffUnit

open scoped ComplexConjugate BigOperators in
variable {p : ℕ} [Fact p.Prime] in
private lemma padicComplex_norm_add_le_of_norm_le {x y : ℂ_[p]} {a : ℝ} (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ a) :
    ‖x + y‖ ≤ a :=
  (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

open scoped ComplexConjugate BigOperators in
variable {p : ℕ} [Fact p.Prime] in
private lemma padicComplex_norm_sub_le_of_norm_le {x y : ℂ_[p]} {a : ℝ} (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ a) :
    ‖x - y‖ ≤ a := by
  rw [sub_eq_add_neg]
  exact padicComplex_norm_add_le_of_norm_le hx (by rwa [norm_neg])

open scoped ComplexConjugate BigOperators in
variable {p : ℕ} [Fact p.Prime] in
private lemma padicComplex_norm_mul_le_of_norm_le_one {x y : ℂ_[p]} {a : ℝ} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ a) :
    ‖x * y‖ ≤ a := by
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hx).trans hy

open scoped ComplexConjugate BigOperators in
variable {p : ℕ} [Fact p.Prime] in
private lemma padicComplex_norm_ofNat_le_one (n : ℕ) [n.AtLeastTwo] : ‖(OfNat.ofNat n : ℂ_[p])‖ ≤ 1 := by
  have := IsUltrametricDist.norm_natCast_le_one ℂ_[p] (OfNat.ofNat n)
  rwa [Nat.cast_ofNat] at this

open scoped ComplexConjugate BigOperators in
variable {p : ℕ} [Fact p.Prime] in
private lemma norm_sub_eq_one_of_discriminant_relations (hp2 : ‖(2 : ℂ_[p])‖ = 1)
    {X₁ X₂ S T Y₁ Y₂ b c D : ℂ_[p]} (hX₁ : ‖X₁‖ ≤ 1) (hX₂ : ‖X₂‖ ≤ 1) (hS : ‖S‖ ≤ 1)
    (hT : ‖T‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) (hD : ‖D‖ = 1) (hne : X₁ - X₂ ≠ 0)
    (hA : (Y₁ - Y₂) ^ 2 = (X₁ - X₂) ^ 2 * (4 * (S + X₁ + X₂) + b))
    (hB : (Y₁ + Y₂) ^ 2 = (X₁ - X₂) ^ 2 * (4 * (T + X₁ + X₂) + b))
    (hsym : (X₁ - X₂) ^ 2 * (S + T - 2 * X₂) =
      (6 * X₂ ^ 2 + b * X₂ + c / 2) * (X₁ - X₂) + Y₂ ^ 2)
    (hdisc : 4 * D = Y₂ ^ 2 * (36 * (12 * X₂ + b) * (6 * X₂ ^ 2 + b * X₂ + c / 2)
        - 108 * Y₂ ^ 2 - (12 * X₂ + b) ^ 3) +
      (6 * X₂ ^ 2 + b * X₂ + c / 2) ^ 2 * ((12 * X₂ + b) ^ 2 - 32 * (6 * X₂ ^ 2 + b * X₂ + c / 2))) :
    ‖X₁ - X₂‖ = 1 := by
  have hc2 : ‖c / 2‖ ≤ 1 := by rw [norm_div, hp2, div_one]; exact hc
  set d := X₁ - X₂ with hd
  set H := 6 * X₂ ^ 2 + b * X₂ + c / 2 with hH
  set K := 12 * X₂ + b with hK
  have h1 : ‖d‖ ≤ 1 := padicComplex_norm_sub_le_of_norm_le hX₁ hX₂
  refine le_antisymm h1 (not_lt.1 fun hlt => ?_)
  have hdpos : 0 < ‖d‖ := norm_pos_iff.2 hne
  have hfour : ∀ {W : ℂ_[p]}, ‖W‖ ≤ 1 → ‖4 * (W + X₁ + X₂) + b‖ ≤ 1 := fun hW =>
    padicComplex_norm_add_le_of_norm_le (padicComplex_norm_mul_le_of_norm_le_one (padicComplex_norm_ofNat_le_one 4)
      (padicComplex_norm_add_le_of_norm_le (padicComplex_norm_add_le_of_norm_le hW hX₁) hX₂)) hb
  have hsq : ∀ {Y W : ℂ_[p]}, Y ^ 2 = d ^ 2 * W → ‖W‖ ≤ 1 → ‖Y‖ ≤ ‖d‖ := fun {Y W} hY hW => by
    have : ‖Y‖ ^ 2 ≤ ‖d‖ ^ 2 := by
      rw [← norm_pow, hY, norm_mul, norm_pow]
      exact mul_le_of_le_one_right (by positivity) hW
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this
  have hm := hsq hA (hfour hS)
  have hp := hsq hB (hfour hT)
  have hY₂ : ‖Y₂‖ ≤ ‖d‖ := by
    have h2 : 2 * Y₂ = (Y₁ + Y₂) - (Y₁ - Y₂) := by ring
    have := padicComplex_norm_sub_le_of_norm_le hp hm
    rwa [← h2, norm_mul, hp2, one_mul] at this
  have hX₂' : ‖2 * X₂‖ ≤ 1 := padicComplex_norm_mul_le_of_norm_le_one (padicComplex_norm_ofNat_le_one 2) hX₂
  have hHd : ‖H‖ ≤ ‖d‖ := by
    have heq : H * d = d ^ 2 * (S + T - 2 * X₂) - Y₂ ^ 2 := by linear_combination -hsym
    have hST : ‖S + T - 2 * X₂‖ ≤ 1 := padicComplex_norm_sub_le_of_norm_le (padicComplex_norm_add_le_of_norm_le hS hT) hX₂'
    have : ‖H‖ * ‖d‖ ≤ ‖d‖ * ‖d‖ := by
      rw [← norm_mul, heq]
      refine padicComplex_norm_sub_le_of_norm_le ?_ ?_
      · rw [norm_mul, norm_pow]
        nlinarith [norm_nonneg (S + T - 2 * X₂), sq_nonneg ‖d‖]
      · rw [norm_pow]
        nlinarith [norm_nonneg Y₂]
    exact le_of_mul_le_mul_right this hdpos
  have hK1 : ‖K‖ ≤ 1 :=
    padicComplex_norm_add_le_of_norm_le (padicComplex_norm_mul_le_of_norm_le_one (padicComplex_norm_ofNat_le_one 12) hX₂) hb
  have hH1 : ‖H‖ ≤ 1 := hHd.trans h1
  have hα : ‖Y₂ ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg Y₂]
  have hH2 : ‖H ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg H]
  have hP : ‖36 * K * H - 108 * Y₂ ^ 2 - K ^ 3‖ ≤ 1 :=
    padicComplex_norm_sub_le_of_norm_le (padicComplex_norm_sub_le_of_norm_le
      (padicComplex_norm_mul_le_of_norm_le_one (padicComplex_norm_mul_le_of_norm_le_one (padicComplex_norm_ofNat_le_one 36) hK1) hH1)
      (padicComplex_norm_mul_le_of_norm_le_one (padicComplex_norm_ofNat_le_one 108) hα.le))
      (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hK1)
  have hQ : ‖K ^ 2 - 32 * H‖ ≤ 1 :=
    padicComplex_norm_sub_le_of_norm_le (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hK1)
      (padicComplex_norm_mul_le_of_norm_le_one (padicComplex_norm_ofNat_le_one 32) hH1)
  have hlt4 : ‖4 * D‖ < 1 := by
    rw [hdisc]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) hP).trans_lt hα
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) hQ).trans_lt hH2
  have h4 : ‖4 * D‖ = 1 := by
    rw [norm_mul, hD, show (4 : ℂ_[p]) = 2 * 2 by norm_num, norm_mul, hp2]
    norm_num
  linarith

open scoped ComplexConjugate BigOperators in
variable {p : ℕ} [Fact p.Prime] in
private lemma padicComplex_norm_two_eq_one_of_ne_two (h : p ≠ 2) : ‖(2 : ℂ_[p])‖ = 1 := by
  have h1 : ‖algebraMap ℚ_[p] ℂ_[p] 2‖ = ‖(2 : ℚ_[p])‖ := norm_algebraMap' _ _
  rw [map_ofNat] at h1
  rw [h1]
  have h2 : ‖(2 : ℚ_[p])‖ = ‖((2 : ℤ) : ℤ_[p])‖ := by
    rw [PadicInt.norm_def, PadicInt.coe_intCast]; norm_num
  rw [h2]
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun hlt => h ?_)
  rw [PadicInt.norm_int_lt_one_iff_dvd] at hlt
  have : p ∣ 2 := by exact_mod_cast hlt
  exact (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this

open scoped ComplexConjugate BigOperators in
variable {p : ℕ} [Fact p.Prime] in

theorem _root_.GlobalTheory.Klein.norm_weierstrassP_sub_eq_one (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p])
    (L : PeriodPair) (r : ℂ)
    (hG : _root_.GlobalTheory.Klein.Good ι L r) (u v : ℂ) (hu : _root_.GlobalTheory.Klein.Red ι L r u)
    (hv : _root_.GlobalTheory.Klein.Red ι L r v)
    (h₁ : _root_.GlobalTheory.Klein.Red ι L r (u + v))
    (h₂ : _root_.GlobalTheory.Klein.Red ι L r (u - v)) :
    ‖ι (L.weierstrassP u - L.weierstrassP v)‖ = 1 := by
  obtain ⟨hp, h12r, hc, -, hΔ⟩ := hG
  obtain ⟨hu, hXu⟩ := hu
  obtain ⟨hv, hXv⟩ := hv
  obtain ⟨hs, hS⟩ := h₁
  obtain ⟨ht, hT⟩ := h₂
  have hne : L.weierstrassP u ≠ L.weierstrassP v := by
    rw [Ne, _root_.GlobalTheory.weierstrassP_eq_iff L hu hv]
    rintro (h | h)
    exacts [ht h, hs h]
  have hd : L.weierstrassP u - L.weierstrassP v ≠ 0 := sub_ne_zero.2 hne
  have hA := (_root_.GlobalTheory.weierstrassP_add L hu hv hne).1
  have hnv : -v ∉ L.lattice := fun h => hv (by simpa using neg_mem h)
  have hne' : L.weierstrassP u ≠ L.weierstrassP (-v) := by rwa [PeriodPair.weierstrassP_neg]
  have hB := (_root_.GlobalTheory.weierstrassP_add L hu hnv hne').1
  rw [PeriodPair.weierstrassP_neg, PeriodPair.derivWeierstrassP_neg, ← sub_eq_add_neg,
    sub_neg_eq_add] at hB
  have hsym := _root_.GlobalTheory.weierstrassP_add_add_sub L hu hv hne
  have hY := L.derivWeierstrassP_sq v hv
  set x₁ := L.weierstrassP u
  set x₂ := L.weierstrassP v
  set s := L.weierstrassP (u + v)
  set t := L.weierstrassP (u - v)
  set y₁ := L.derivWeierstrassP u
  set y₂ := L.derivWeierstrassP v
  have cA : (y₁ - y₂) ^ 2 = ((x₁ - r) - (x₂ - r)) ^ 2 *
      (4 * ((s - r) + (x₁ - r) + (x₂ - r)) + 12 * r) := by
    rw [hA]; field_simp; ring
  have cB : (y₁ + y₂) ^ 2 = ((x₁ - r) - (x₂ - r)) ^ 2 *
      (4 * ((t - r) + (x₁ - r) + (x₂ - r)) + 12 * r) := by
    rw [hB]; field_simp; ring
  have cS : ((x₁ - r) - (x₂ - r)) ^ 2 * ((s - r) + (t - r) - 2 * (x₂ - r)) =
      (6 * (x₂ - r) ^ 2 + 12 * r * (x₂ - r) + (12 * r ^ 2 - L.g₂) / 2) * ((x₁ - r) - (x₂ - r)) +
        y₂ ^ 2 := by
    have e : s = (6 * x₂ ^ 2 - L.g₂ / 2) / (x₁ - x₂) + y₂ ^ 2 / (x₁ - x₂) ^ 2 - t + 2 * x₂ := by
      linear_combination hsym
    rw [e]; field_simp; ring
  have cD : 4 * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) =
      y₂ ^ 2 * (36 * (12 * (x₂ - r) + 12 * r) *
          (6 * (x₂ - r) ^ 2 + 12 * r * (x₂ - r) + (12 * r ^ 2 - L.g₂) / 2)
        - 108 * y₂ ^ 2 - (12 * (x₂ - r) + 12 * r) ^ 3) +
      (6 * (x₂ - r) ^ 2 + 12 * r * (x₂ - r) + (12 * r ^ 2 - L.g₂) / 2) ^ 2 *
        ((12 * (x₂ - r) + 12 * r) ^ 2 -
          32 * (6 * (x₂ - r) ^ 2 + 12 * r * (x₂ - r) + (12 * r ^ 2 - L.g₂) / 2)) := by
    rw [hY]; ring
  have key := norm_sub_eq_one_of_discriminant_relations (padicComplex_norm_two_eq_one_of_ne_two hp) hXu hXv hS hT h12r hc
    hΔ (Y₁ := ι y₁) (Y₂ := ι y₂)
    (by rw [← map_sub]; exact (map_ne_zero ι).2 (by rwa [sub_sub_sub_cancel_right]))
    (by simpa only [map_sub, map_mul, map_add, map_pow, map_ofNat, map_div₀] using congrArg ι cA)
    (by simpa only [map_sub, map_mul, map_add, map_pow, map_ofNat, map_div₀] using congrArg ι cB)
    (by simpa only [map_sub, map_mul, map_add, map_pow, map_ofNat, map_div₀] using congrArg ι cS)
    (by simpa only [map_sub, map_mul, map_add, map_pow, map_ofNat, map_div₀] using congrArg ι cD)
  rwa [← map_sub, sub_sub_sub_cancel_right] at key

end GlobalTheory.Klein
