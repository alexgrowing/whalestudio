import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsOfEmbedding

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.LamEq

theorem pow_prime_step (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (n : ℕ) (hn : 1 ≤ n) (t : ℤ) :
    (p : ℤ) ^ (2 * n + 1) ∣ (1 + (p : ℤ) ^ n * t) ^ p - 1 - (p : ℤ) ^ (n + 1) * t := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by have := hp.two_le; omega⟩
  set P : ℤ := ((q + 2 : ℕ) : ℤ) with hP
  have hexp : (1 + P ^ n * t) ^ (q + 2) =
      ∑ i ∈ Finset.range (q + 1), (P ^ n * t) ^ (i + 2) * ((q + 2).choose (i + 2) : ℤ) + (q + 2 : ℕ) * (P ^ n * t) + 1 := by
    rw [add_comm (1 : ℤ), add_pow, Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [zero_add, one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one, pow_one]
    push_cast; ring
  rw [hexp]
  have hPP : (q + 2 : ℕ) * (P ^ n * t) = P ^ (n + 1) * t := by rw [hP]; ring
  rw [hPP, show ∀ a b : ℤ, a + b + 1 - 1 - b = a from fun a b => by ring]
  apply Finset.dvd_sum
  intro i _
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · have hc : ((q + 2 : ℕ) : ℤ) ∣ ((q + 2).choose 2 : ℤ) := by
      exact_mod_cast hp.dvd_choose_self (by norm_num) (by omega)
    rw [← hP] at hc
    obtain ⟨c, hc⟩ := hc
    exact ⟨t ^ 2 * c, by rw [hc]; ring⟩
  · have h3 : 2 * n + 1 ≤ n * (i + 2) := by nlinarith
    refine Dvd.dvd.mul_right ?_ _
    rw [mul_pow, ← pow_mul]
    exact Dvd.dvd.mul_right (pow_dvd_pow _ h3) _

theorem pow_prime_pow (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ (j n : ℕ), 1 ≤ n → ∀ t : ℤ,
      (p : ℤ) ^ (2 * n + j) ∣ (1 + (p : ℤ) ^ n * t) ^ (p ^ j) - 1 - (p : ℤ) ^ (n + j) * t := by
  intro j
  induction j with
  | zero => intro n _ t; simp
  | succ j ih =>
    intro n hn t
    obtain ⟨w, hw⟩ := pow_prime_step p hp hp2 n hn t
    have h1 : (1 + (p : ℤ) ^ n * t) ^ p = 1 + (p : ℤ) ^ (n + 1) * (t + (p : ℤ) ^ n * w) := by
      linear_combination hw + (0 : ℤ) * w
    obtain ⟨w', hw'⟩ := ih (n + 1) (by omega) (t + (p : ℤ) ^ n * w)
    rw [pow_succ', pow_mul, h1]
    refine ⟨(p : ℤ) * w' + w, ?_⟩
    linear_combination hw'
end GlobalTheory.LamEq

namespace GlobalTheory.LamEq

theorem aut_pow_apply {Ω : Type} [Field Ω] [Algebra ℚ Ω] (s : Ω ≃ₐ[ℚ] Ω) (z : Ω) (c : ℕ) (hc : s z = z ^ c) :
    ∀ k : ℕ, (s ^ k) z = z ^ (c ^ k) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, AlgEquiv.mul_apply, hc, map_pow, ih, ← pow_mul, pow_succ]

theorem lam_eq : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (L n m : ℕ), 1 ≤ m → m ≤ n → n ≤ L → ∀ s : Ω ≃ₐ[ℚ] Ω, s (zt ε p m) = zt ε p m →
  ∀ tt tt' : ZMod (p ^ n), IsLamG ε p n m s tt → (s ^ (p ^ (L - m))) (zt ε p (L + n)) = zt ε p n ^ tt'.val * zt ε p (L + n) → tt = tt' := by
  intro Ω _ _ _ ε p hpf hp2 L n m hm1 hmn hnL s _ tt tt' hlam hL
  have hp : p.Prime := hpf.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨e, rfl⟩ : ∃ e, L = n + e := ⟨L - n, by omega⟩
  set z := zt ε p (n + e + n) with hzdef
  have hz : IsPrimitiveRoot z (p ^ (n + e + n)) := IsNTr.isPrimitiveRoot_zt ε p _
  obtain ⟨c, -, hc⟩ := hz.eq_pow_of_pow_eq_one (ξ := s z) (by rw [← map_pow, hz.pow_eq_one, map_one])
  have hs := aut_pow_apply s z c hc.symm
  have h2n : zt ε p (2 * n) = z ^ (p ^ e) := by
    rw [hzdef, ← IsNTr.zt_pow ε p (2 * n) e]; congr 2; omega
  have hn : zt ε p n = z ^ (p ^ (n + e)) := by
    rw [hzdef, ← IsNTr.zt_pow ε p n (n + e)]; congr 2; omega

  have E1 : z ^ (c ^ (p ^ (n - m)) * p ^ e) = z ^ (p ^ (n + e) * tt.val + p ^ e) := by
    have := hlam
    unfold IsLamG at this
    change (s ^ (p ^ (n - m))) (zt ε p (2 * n)) = zt ε p n ^ tt.val * zt ε p (2 * n) at this
    rw [h2n, hn, map_pow, hs, ← pow_mul, ← pow_mul, ← pow_add] at this
    exact this
  have E2 : z ^ (c ^ (p ^ (n + e - m))) = z ^ (p ^ (n + e) * tt'.val + 1) := by
    rw [← hs, hL, hn, ← pow_mul, pow_succ]
  have hfin : IsOfFinOrder z := isOfFinOrder_iff_pow_eq_one.2 ⟨_, pow_pos hp.pos _, hz.pow_eq_one⟩
  have hmod : ∀ a b : ℕ, z ^ a = z ^ b ↔ a ≡ b [MOD p ^ (n + e + n)] := by
    intro a b; rw [hz.eq_orderOf]; exact hfin.pow_eq_pow_iff_modEq
  rw [hmod, Nat.modEq_iff_dvd] at E1 E2
  obtain ⟨w1, hw1⟩ := E1
  obtain ⟨w3, hw3⟩ := E2
  push_cast at hw1 hw3
  set P : ℤ := (p : ℤ) with hP
  have hP0 : P ≠ 0 := by rw [hP]; exact_mod_cast hp.ne_zero
  set a : ℤ := (c : ℤ) ^ (p ^ (n - m)) with ha
  set v : ℤ := ((tt.val : ℕ) : ℤ)
  set v' : ℤ := ((tt'.val : ℕ) : ℤ)
  have h1 : a = 1 + P ^ n * (v - P ^ n * w1) := by
    apply mul_left_cancel₀ (pow_ne_zero e hP0)
    linear_combination (-1 : ℤ) * hw1
  obtain ⟨w2, hw2⟩ := pow_prime_pow p hp hp2 e n (by omega) (v - P ^ n * w1)
  rw [← h1, ← hP] at hw2
  have hce : (c : ℤ) ^ (p ^ (n + e - m)) = a ^ (p ^ e) := by
    rw [ha, ← pow_mul, ← pow_add]; congr 2; omega
  rw [hce] at hw3
  have hd : v' - v = P ^ n * (w3 - w1 + w2) := by
    apply mul_left_cancel₀ (pow_ne_zero (n + e) hP0)
    linear_combination hw3 + hw2
  have hv : ((v : ℤ) : ZMod (p ^ n)) = ((v' : ℤ) : ZMod (p ^ n)) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2 ⟨w3 - w1 + w2, by push_cast; rw [hd]⟩
  simpa [v, v', ZMod.natCast_zmod_val] using hv

end GlobalTheory.LamEq

example : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (L n m : ℕ), 1 ≤ m → m ≤ n → n ≤ L → ∀ s : Ω ≃ₐ[ℚ] Ω, s (zt ε p m) = zt ε p m →
  ∀ tt tt' : ZMod (p ^ n), IsLamG ε p n m s tt → (s ^ (p ^ (L - m))) (zt ε p (L + n)) = zt ε p n ^ tt'.val * zt ε p (L + n) → tt = tt' :=
  GlobalTheory.LamEq.lam_eq
