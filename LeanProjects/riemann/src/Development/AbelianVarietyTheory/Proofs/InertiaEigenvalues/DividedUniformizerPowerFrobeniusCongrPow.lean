import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffOfW

noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem factorial_pow_dvd_factorial_mul (q k : ℕ) : q.factorial ^ k ∣ (k * q).factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.succ_mul]
    exact (Nat.mul_dvd_mul_right ih _).trans (Nat.factorial_mul_factorial_dvd_factorial_add _ _)

theorem exists_factorial_quot (l q : ℕ) (hl : 0 < l) :
    ∃ (A B : ℕ) (D : ℤ), A * q.factorial = (l * q).factorial ∧ B * q.factorial ^ l = (l * q).factorial ∧
      (A : ℤ) = B + l * D := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · exact ⟨1, 1, 0, by simp, by simp, by simp⟩
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  obtain ⟨c, hc⟩ := factorial_pow_dvd_factorial_mul (p + 1) k
  have h1 := Nat.add_choose_mul_factorial_mul_factorial (k * (p + 1)) (p + 1)
  have h2 := Nat.add_one_mul_choose_eq (k * (p + 1) + p) p
  have h3 : (k * (p + 1) + (p + 1)).choose (p + 1) = (k + 1) * (k * (p + 1) + p).choose p := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.succ_pos p)
    rw [← add_assoc, ← h2]; simp only [Nat.succ_eq_add_one]; ring
  have h4 : (k + 1) * (p + 1) = k * (p + 1) + (p + 1) := by ring
  set m := (k * (p + 1) + p).choose p
  refine ⟨(k + 1) * m * (k * (p + 1)).factorial, (k + 1) * m * c,
    (m * (k * (p + 1)).factorial : ℕ) - (m * c : ℕ), ?_, ?_, ?_⟩
  · rw [h4, ← h1, h3]
  · rw [h4, ← h1, h3, hc]; ring
  · push_cast; ring

section

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  (t : Wq l a →ₐ[ℤ_[l]] O) (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  (e : ℕ) [NeZero e]

theorem intCast_div_factorial_mem_QSet (z : ℤ) (m : ℕ) :
    (fun _ => C (C ((z : K) / (m.factorial : K)) * X ^ (e * m)) : ZMod a → K⟦X⟧⟦X⟧) ∈ QSet t K e := by
  classical
  refine ⟨Pi.single (0, e * m) (z : Wq l a), ?_⟩
  funext τ
  ext i n
  rw [coeff_ofW, coeff_C]
  by_cases hi : i = 0
  · subst hi
    rw [if_pos rfl, coeff_C_mul, coeff_X_pow]
    by_cases hn : n = e * m
    · subst hn
      simp [dpDen, Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero (NeZero.ne e))]
    · rw [if_neg hn, Pi.single_eq_of_ne (by simpa using hn)]; simp
  · rw [if_neg hi, Pi.single_eq_of_ne (by simp [hi])]; simp

end

theorem dFam_mem_goodSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) → φ₂ X = (C X + X) ^ l - C (X ^ l) → ∀ q : ℕ, dFam a K e q ∈ GoodSet t e φ₂ := by
  intro l hl a e _ _ O K _ _ _ _ _ _ _ t φ₂ hC _ q
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  obtain ⟨A, B, D, hA, hB, hD⟩ := exists_factorial_quot l q hl.out.pos
  have hq : (q.factorial : K) ≠ 0 := by exact_mod_cast q.factorial_ne_zero
  have hlq : ((l * q).factorial : K) ≠ 0 := by exact_mod_cast (l * q).factorial_ne_zero
  have hA' : (A : K) * q.factorial = (l * q).factorial := by exact_mod_cast hA
  have hB' : (B : K) * (q.factorial : K) ^ l = (l * q).factorial := by exact_mod_cast hB
  have hD' : (A : K) = B + l * D := by exact_mod_cast hD
  have eA : (q.factorial : K)⁻¹ = ((A : ℤ) : K) / (l * q).factorial := by
    rw [Int.cast_natCast]; field_simp; rw [← hA']; ring
  have eB : ((q.factorial : K)⁻¹) ^ l = (B : K) / (l * q).factorial := by
    rw [eq_div_iff hlq, ← hB', mul_left_comm, ← mul_pow, inv_mul_cancel₀ hq, one_pow, mul_one]
  have hf : frob2 φ₂ (dFam a K e q) =
      fun _ => C (C (((A : ℤ) : K) / ((l * q).factorial : K)) * X ^ (e * (l * q))) := by
    funext τ
    change φ₂ (dFam a K e q (τ - 1)) = _
    simp only [dFam]
    rw [hC, map_mul, map_pow, frob_C, frob_X, ← pow_mul, eA]
    congr 3; ring
  refine ⟨?_, ?_, _, intCast_div_factorial_mem_QSet t K e D (l * q), ?_⟩
  · have := intCast_div_factorial_mem_QSet t K e 1 q
    rw [Int.cast_one, one_div] at this
    exact this
  · rw [hf]; exact intCast_div_factorial_mem_QSet t K e _ _
  · rw [hf]
    funext τ
    simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply, dFam]
    rw [← map_pow, ← map_natCast (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧), ← map_mul, ← map_add, mul_pow, ← map_pow, eB,
      ← pow_mul, ← map_natCast (C : K →+* K⟦X⟧), ← mul_assoc (C (l : K)), ← map_mul,
      show e * q * l = e * (l * q) by ring, ← add_mul, ← map_add, Int.cast_natCast, hD']
    congr 3; ring

end GlobalTheory.CrysPrism
