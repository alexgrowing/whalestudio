import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CoPtMu
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoefPosEqZero

open GlobalTheory.KummerEisensteinGalois GlobalTheory.KummerEisensteinGalois.UnitPiece Finset

namespace GlobalTheory.KummerEisensteinGalois.UnitPieceMu

variable {K : Type} [Field K] [CharZero K]

theorem ffMu_eq (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (a₀ : ℤ) (s : ℕ) :
    ffMu N p m k ψ a₀ s = ∑ q ∈ (s : ℤ).divisorsAntidiag,
      if ¬ (p : ℤ) ∣ q.1 ∧ ¬ (p : ℤ) ∣ q.2 ∧ q.1 ≡ a₀ [ZMOD N] then
        (q.2.sign : K) * (ψ (q.1 : ZMod (p ^ m)) * (q.1 : K) ^ (k - 2)) else 0 := by
  rw [sum_antidiag s (fun A d => if ¬ (p : ℤ) ∣ A ∧ ¬ (p : ℤ) ∣ d ∧ A ≡ a₀ [ZMOD N] then
        (d.sign : K) * (ψ (A : ZMod (p ^ m)) * (A : K) ^ (k - 2)) else 0)]
  unfold ffMu
  refine sum_congr rfl fun d hd => ?_
  have hd0 : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  rw [Int.sign_neg, Int.sign_eq_one_of_pos hd0]
  simp only [dvd_neg, Int.natCast_dvd_natCast, Int.cast_neg, Int.cast_natCast, Int.cast_one]
  by_cases h1 : p ∣ d <;> by_cases h2 : p ∣ s / d <;>
    by_cases h3 : ((s / d : ℕ) : ℤ) ≡ a₀ [ZMOD N] <;> by_cases h4 : -((s / d : ℕ) : ℤ) ≡ a₀ [ZMOD N] <;>
    simp [h1, h2, h3, h4, sub_eq_add_neg, -Nat.cast_div_charZero, -Int.natCast_div, -Int.natCast_ediv]

theorem eeMu_eq (N p m : ℕ) (ψ : DirichletCharacter K (p ^ m)) (b₀ : ℤ) (s : ℕ) :
    eeMu N p m ψ b₀ s = ∑ q ∈ (s : ℤ).divisorsAntidiag,
      if ¬ (p : ℤ) ∣ q.1 ∧ ¬ (p : ℤ) ∣ q.2 ∧ q.1 ≡ b₀ [ZMOD N] then
        (q.2.sign : K) * ψ⁻¹ (q.2 : ZMod (p ^ m)) else 0 := by
  rw [sum_antidiag s (fun A d => if ¬ (p : ℤ) ∣ A ∧ ¬ (p : ℤ) ∣ d ∧ A ≡ b₀ [ZMOD N] then
        (d.sign : K) * ψ⁻¹ (d : ZMod (p ^ m)) else 0)]
  unfold eeMu
  refine sum_congr rfl fun d hd => ?_
  have hd0 : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  rw [Int.sign_neg, Int.sign_eq_one_of_pos hd0]
  simp only [dvd_neg, Int.natCast_dvd_natCast, Int.cast_neg, Int.cast_natCast, Int.cast_one]
  by_cases h1 : p ∣ d <;> by_cases h2 : p ∣ s / d <;>
    by_cases h3 : ((s / d : ℕ) : ℤ) ≡ b₀ [ZMOD N] <;> by_cases h4 : -((s / d : ℕ) : ℤ) ≡ b₀ [ZMOD N] <;>
    simp [h1, h2, h3, h4, sub_eq_add_neg, -Nat.cast_div_charZero, -Int.natCast_div, -Int.natCast_ediv]

theorem drop_const (p m N k : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hpN : ¬ p ∣ N) (hk : 3 ≤ k)
    (ψ : DirichletCharacter K (p ^ m)) (hψ : ψ.IsPrimitive) (ζ : K) (x y y₁ y₂ : ℤ) (i j : ℕ) :
    ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m), ψ (u * b - a * v) *
      (eisF (k - 1) (N * p ^ m) ζ (N * u.val + (p : ℤ) ^ m * x) (N * a.val + (p : ℤ) ^ m * y₁) i *
        eisF 1 (N * p ^ m) ζ (N * v.val + (p : ℤ) ^ m * y) (N * b.val + (p : ℤ) ^ m * y₂) j) =
    ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m), ψ (u * b - a * v) *
      (coefPos (k - 1) (N * p ^ m) ζ (N * u.val + (p : ℤ) ^ m * x) (N * a.val + (p : ℤ) ^ m * y₁) i *
        coefPos 1 (N * p ^ m) ζ (N * v.val + (p : ℤ) ^ m * y) (N * b.val + (p : ℤ) ^ m * y₂) j) := by
  have hp : p.Prime := Fact.out
  by_cases hi : i = 0
  · subst hi
    have hk1 : k - 1 ≠ 1 := by omega
    simp only [eisF, const0, if_true, if_neg hk1]
    rw [sum_zero_left p m hm ψ hψ]
    simp [coefPos]
  by_cases hj : j = 0
  · subst hj
    have e : ∀ v ∈ primeTo p m, ∀ z : ℤ, eisF 1 (N * p ^ m) ζ (N * v.val + (p : ℤ) ^ m * y) z 0 =
        ((1 / 2 - frc (N * p ^ m) (N * v.val + (p : ℤ) ^ m * y) : ℚ) : K) := by
      intro v hv z
      have : ¬ ((N * p ^ m : ℕ) : ℤ) ∣ N * v.val + (p : ℤ) ^ m * y := by
        intro h
        have h1 : (p : ℤ) ^ m ∣ N * v.val + (p : ℤ) ^ m * y :=
          (show (p : ℤ) ^ m ∣ ((N * p ^ m : ℕ) : ℤ) by push_cast; exact dvd_mul_left _ _).trans h
        have h2 : (p : ℤ) ∣ (N : ℤ) * v.val := by
          have := dvd_sub h1 (dvd_mul_right ((p : ℤ) ^ m) y)
          rw [add_sub_cancel_right] at this
          exact (dvd_pow_self (p : ℤ) (by omega)).trans this
        rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd h2 with h3 | h3
        · exact hpN (Int.natCast_dvd_natCast.mp h3)
        · exact (mem_filter.mp hv).2 (Int.natCast_dvd_natCast.mp h3)
      simp only [eisF, const0, if_true, if_neg this]
    rw [sum_congr rfl fun u _ => sum_congr rfl fun a _ => sum_congr rfl fun v hv => sum_congr rfl fun b _ => by
      rw [e v hv], sum_zero_right p m hm ψ hψ]
    simp [coefPos]
  simp only [eisF, if_neg hi, if_neg hj]

end GlobalTheory.KummerEisensteinGalois.UnitPieceMu
