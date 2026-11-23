import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory

theorem cycloSq_mod_eq_zero_iff {l a b : ℕ} (hl : 0 < l) (ha : a < l) (hb : b < l) :
    (a + (l - 1) * b) % l = 0 ↔ b = a := by
  rw [← Nat.dvd_iff_mod_eq_zero]
  constructor
  · intro h
    have h2 : (l : ℤ) ∣ ((a + (l - 1) * b : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr h
    have h3 : ((a + (l - 1) * b : ℕ) : ℤ) = ((a : ℤ) - b) + l * b := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ l)]; ring
    rw [h3] at h2
    have h' : (l : ℤ) ∣ (a : ℤ) - b := (dvd_add_left (dvd_mul_right _ _)).mp h2
    have := Int.eq_zero_of_abs_lt_dvd h' (by rw [abs_lt]; constructor <;> omega)
    omega
  · rintro rfl
    obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
    exact ⟨b, by simp; ring⟩

theorem cycloSq_coeff_eq {l : ℕ} (hl : l.Prime) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ l) (a : ℕ → ℤ)
    (h : ∑ d ∈ Finset.range l, (a d : ℂ) * ζ ^ d = 0) : ∀ d < l, a d = a (l - 1) := by
  have hl1 : 1 < l := hl.one_lt
  have hgeom : ∑ d ∈ Finset.range l, ζ ^ d = 0 := hζ.geom_sum_eq_zero hl1
  set Q : ℚ[X] := ∑ d ∈ Finset.range (l - 1), C (((a d - a (l - 1) : ℤ)) : ℚ) * X ^ d with hQdef
  have hQ : aeval ζ Q = 0 := by
    have h1 : ∑ d ∈ Finset.range l, (((a d - a (l - 1) : ℤ)) : ℂ) * ζ ^ d = 0 := by
      simp only [Int.cast_sub, sub_mul, Finset.sum_sub_distrib, h, ← Finset.mul_sum, hgeom,
        mul_zero, sub_zero]
    have hl' : l = (l - 1) + 1 := by omega
    rw [hl', Finset.sum_range_succ] at h1
    simp only [Nat.add_sub_cancel, sub_self, Int.cast_zero, zero_mul, add_zero] at h1
    rw [hQdef, map_sum]
    simpa using h1
  have hdvd : minpoly ℚ ζ ∣ Q := minpoly.dvd ℚ ζ hQ
  have hdeg : (minpoly ℚ ζ).natDegree = l - 1 := by
    rw [← cyclotomic_eq_minpoly_rat hζ hl.pos, natDegree_cyclotomic, Nat.totient_prime hl]
  have hQ0 : Q = 0 := by
    by_contra hne
    have h1 := natDegree_le_of_dvd hdvd hne
    have h2 : Q.natDegree ≤ l - 2 := natDegree_sum_le_of_forall_le _ _ (fun d hd =>
      (natDegree_C_mul_X_pow_le _ _).trans (by rw [Finset.mem_range] at hd; omega))
    omega
  intro d hd
  by_cases hd' : d = l - 1
  · rw [hd']
  have h1 : Q.coeff d = 0 := by rw [hQ0]; simp
  rw [hQdef, finset_sum_coeff] at h1
  simp only [coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range] at h1
  rw [if_pos (by omega)] at h1
  have : ((a d - a (l - 1) : ℤ) : ℚ) = 0 := h1
  exact_mod_cast sub_eq_zero.mp (by exact_mod_cast this)

end GlobalTheory

namespace GlobalTheory

def cycloSqCoeff (l : ℕ) (f : ℕ → ℤ) (d : ℕ) : ℤ :=
  ∑ a ∈ Finset.range l, ∑ b ∈ Finset.range l,
    if (a + (l - 1) * b) % l = d then f a * f b else 0

theorem cycloSq_mul_star {l : ℕ} (hl : 0 < l) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ l) (f : ℕ → ℤ) :
    (∑ a ∈ Finset.range l, (f a : ℂ) * ζ ^ a) * star (∑ a ∈ Finset.range l, (f a : ℂ) * ζ ^ a)
      = ∑ d ∈ Finset.range l, (cycloSqCoeff l f d : ℂ) * ζ ^ d := by
  have hnorm : ‖ζ‖ = 1 := hζ.norm'_eq_one hl.ne'
  have hinv : ζ⁻¹ = ζ ^ (l - 1) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', Nat.sub_add_cancel hl, hζ.pow_eq_one]
  have hstar : star ζ = ζ ^ (l - 1) := by
    rw [← hinv, Complex.inv_eq_conj hnorm]; rfl
  have hpow : ∀ m, ζ ^ m = ζ ^ (m % l) := by
    intro m
    conv_lhs => rw [← Nat.div_add_mod m l]
    rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  rw [star_sum, Finset.sum_mul_sum]
  calc ∑ a ∈ Finset.range l, ∑ b ∈ Finset.range l, (f a : ℂ) * ζ ^ a * star ((f b : ℂ) * ζ ^ b)
      = ∑ a ∈ Finset.range l, ∑ b ∈ Finset.range l,
          ((f a * f b : ℤ) : ℂ) * ζ ^ ((a + (l - 1) * b) % l) := by
        refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
        rw [← hpow, star_mul', star_pow, hstar, star_intCast, pow_add, pow_mul]
        push_cast; ring
    _ = ∑ a ∈ Finset.range l, ∑ b ∈ Finset.range l, ∑ d ∈ Finset.range l,
          (if (a + (l - 1) * b) % l = d then ((f a * f b : ℤ) : ℂ) * ζ ^ d else 0) := by
        refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
        rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr (Nat.mod_lt _ hl))]
    _ = ∑ d ∈ Finset.range l, ∑ a ∈ Finset.range l, ∑ b ∈ Finset.range l,
          (if (a + (l - 1) * b) % l = d then ((f a * f b : ℤ) : ℂ) * ζ ^ d else 0) := by
        exact (Finset.sum_congr rfl (fun a _ => Finset.sum_comm)).trans Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl (fun d _ => ?_)
        simp only [cycloSqCoeff, Int.cast_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
        split_ifs <;> simp

theorem cycloSq_sum_coeff {l : ℕ} (hl : 0 < l) (f : ℕ → ℤ) :
    ∑ d ∈ Finset.range l, cycloSqCoeff l f d
      = ∑ a ∈ Finset.range l, ∑ b ∈ Finset.range l, f a * f b := by
  simp only [cycloSqCoeff]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr (Nat.mod_lt _ hl))]

theorem cycloSq_coeff_zero {l : ℕ} (hl : 0 < l) (f : ℕ → ℤ) :
    cycloSqCoeff l f 0 = ∑ a ∈ Finset.range l, f a ^ 2 := by
  simp only [cycloSqCoeff]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [Finset.mem_range] at ha
  rw [Finset.sum_congr rfl (g := fun b => if b = a then f a * f b else 0) (fun b hb => by
    simp only [cycloSq_mod_eq_zero_iff hl ha (Finset.mem_range.mp hb)])]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr ha), sq]

theorem cycloSq_two_mul {l : ℕ} (f : ℕ → ℤ) :
    ∑ a ∈ Finset.range l, ∑ b ∈ Finset.range l, (f a - f b) ^ 2
      = 2 * ((l : ℤ) * ∑ a ∈ Finset.range l, f a ^ 2
          - ∑ a ∈ Finset.range l, ∑ b ∈ Finset.range l, f a * f b) := by
  have : ∀ a b : ℕ, (f a - f b) ^ 2 = f a ^ 2 + f b ^ 2 - 2 * (f a * f b) := fun a b => by ring
  simp only [this, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
  ring

theorem cycloSq_le_of_ne_zero {l : ℕ} (hl : 1 < l) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ l)
    (f : ℕ → ℤ) (hc : ∑ a ∈ Finset.range l, (f a : ℂ) * ζ ^ a ≠ 0) :
    (l : ℤ) ≤ ∑ a ∈ Finset.range l, ∑ b ∈ Finset.range l, (f a - f b) ^ 2 := by
  have hne : ∃ x ∈ Finset.range l, f x ≠ f 0 := by
    by_contra hall
    push_neg at hall
    apply hc
    rw [Finset.sum_congr rfl (fun a ha => by rw [hall a ha]), ← Finset.mul_sum,
      hζ.geom_sum_eq_zero hl, mul_zero]
  obtain ⟨x, hx, hfx⟩ := hne
  have h0 : 0 ∈ Finset.range l := Finset.mem_range.mpr (by omega)
  have hx0 : x ≠ 0 := by rintro rfl; exact hfx rfl
  have hR : ∀ a ∈ Finset.range l, 0 ≤ ∑ b ∈ Finset.range l, (f a - f b) ^ 2 :=
    fun a _ => Finset.sum_nonneg (fun b _ => sq_nonneg _)
  have hsum := Finset.add_le_sum hR hx h0 hx0
  have hxy : (l : ℤ) ≤ ∑ b ∈ Finset.range l, (f x - f b) ^ 2
      + ∑ b ∈ Finset.range l, (f 0 - f b) ^ 2 := by
    rw [← Finset.sum_add_distrib]
    calc (l : ℤ) = ∑ b ∈ Finset.range l, (1 : ℤ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun b _ => by
        have h1 := sq_nonneg (f x - f b)
        have h2 := sq_nonneg (f 0 - f b)
        by_cases h : f x = f b
        · have : f 0 - f b ≠ 0 := by omega
          rcases lt_or_gt_of_ne this with h3 | h3 <;> nlinarith
        · have : f x - f b ≠ 0 := by omega
          rcases lt_or_gt_of_ne this with h3 | h3 <;> nlinarith)
  linarith

end GlobalTheory

namespace GlobalTheory

theorem cyclo_sum_mul_star_eq_one_single : ∀ (l : ℕ) (ζ : ℂ), l.Prime → IsPrimitiveRoot ζ l →
    ∀ (I : Type) (S : Finset I) (n : I → ℕ → ℤ),
      ∑ i ∈ S, (∑ a ∈ Finset.range l, (n i a : ℂ) * ζ ^ a) *
          star (∑ a ∈ Finset.range l, (n i a : ℂ) * ζ ^ a) = 1 →
      ∃ i₀ ∈ S, ∀ i ∈ S, i ≠ i₀ → ∑ a ∈ Finset.range l, (n i a : ℂ) * ζ ^ a = 0 := by
  intro l ζ hl hζ I S n hsum
  have hl0 : 0 < l := hl.pos
  have hl1 : 1 < l := hl.one_lt
  set N : ℕ → ℤ := fun d => ∑ i ∈ S, cycloSqCoeff l (n i) d with hN
  have hT : ∑ d ∈ Finset.range l, (N d : ℂ) * ζ ^ d = 1 := by
    rw [← hsum, Finset.sum_congr rfl (fun i _ => cycloSq_mul_star hl0 hζ (n i))]
    simp only [hN, Int.cast_sum, Finset.sum_mul]
    exact Finset.sum_comm
  set A : ℕ → ℤ := fun d => N d - if d = 0 then 1 else 0 with hAdef
  have hA : ∑ d ∈ Finset.range l, (A d : ℂ) * ζ ^ d = 0 := by
    simp only [hAdef, Int.cast_sub, sub_mul, Finset.sum_sub_distrib, hT]
    simp [hl0]
  have hAeq := cycloSq_coeff_eq hl hζ A hA
  have hNd : ∀ d ∈ (Finset.range l).erase 0, N d = N 0 - 1 := by
    intro d hd
    rw [Finset.mem_erase, Finset.mem_range] at hd
    have h3 : A d = A 0 := (hAeq d hd.2).trans (hAeq 0 hl0).symm
    simp only [hAdef, if_neg hd.1, if_true, sub_zero] at h3
    linarith
  have h0mem : 0 ∈ Finset.range l := Finset.mem_range.mpr hl0
  have hsumN : ∑ d ∈ Finset.range l, N d = N 0 + ((l : ℤ) - 1) * (N 0 - 1) := by
    rw [← Finset.add_sum_erase _ _ h0mem, Finset.sum_congr rfl hNd, Finset.sum_const,
      Finset.card_erase_of_mem h0mem, Finset.card_range, nsmul_eq_mul,
      Nat.cast_sub (by omega : 1 ≤ l)]
    push_cast; ring
  have hsumN' : ∑ d ∈ Finset.range l, N d
      = ∑ i ∈ S, ∑ a ∈ Finset.range l, ∑ b ∈ Finset.range l, n i a * n i b := by
    simp only [hN]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => cycloSq_sum_coeff hl0 (n i))
  have hN0 : N 0 = ∑ i ∈ S, ∑ a ∈ Finset.range l, n i a ^ 2 :=
    Finset.sum_congr rfl (fun i _ => cycloSq_coeff_zero hl0 (n i))
  have hQsum : ∑ i ∈ S, ∑ a ∈ Finset.range l, ∑ b ∈ Finset.range l, (n i a - n i b) ^ 2
      = 2 * ((l : ℤ) - 1) := by
    rw [Finset.sum_congr rfl (fun i _ => cycloSq_two_mul (n i)), ← Finset.mul_sum,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← hN0, ← hsumN', hsumN]
    ring
  have hQnn : ∀ i ∈ S, 0 ≤ ∑ a ∈ Finset.range l, ∑ b ∈ Finset.range l, (n i a - n i b) ^ 2 :=
    fun i _ => Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => sq_nonneg _))
  obtain ⟨i₀, hi₀, hc₀⟩ : ∃ i₀ ∈ S, ∑ a ∈ Finset.range l, (n i₀ a : ℂ) * ζ ^ a ≠ 0 := by
    by_contra H
    push_neg at H
    rw [Finset.sum_eq_zero (fun i hi => by rw [H i hi, zero_mul])] at hsum
    exact zero_ne_one hsum
  refine ⟨i₀, hi₀, fun i hi hne => ?_⟩
  by_contra hci
  have h1 := cycloSq_le_of_ne_zero hl1 hζ (n i) hci
  have h2 := cycloSq_le_of_ne_zero hl1 hζ (n i₀) hc₀
  have h3 := Finset.add_le_sum hQnn hi hi₀ hne
  linarith

end GlobalTheory
