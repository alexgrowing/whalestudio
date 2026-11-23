import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsQRootPolyOfFixedGeometricStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralCoeffsOfGeometricFixedQExpansionStatement
open GlobalTheory.K5

noncomputable section

namespace GlobalTheory.K5.Decomp

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem zeta_pow_eq_one' (T : Tower p Ω) (m : ℕ) : T.ζ (m + 1) ^ p ^ m = T.ζ 1 := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ', pow_mul, T.ζpow, ih]

theorem exists_pow_eq_zeta_one (T : Tower p Ω) (N j : ℕ) (hj0 : 0 < j) (hjN : j < p ^ N) :
    ∃ e : ℕ, (T.ζ N ^ j) ^ e = T.ζ 1 := by
  have hN : N ≠ 0 := by rintro rfl; simp at hjN; omega
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hglt : Nat.gcd j (p ^ (M + 1)) < p ^ (M + 1) :=
    lt_of_le_of_lt (Nat.le_of_dvd hj0 (Nat.gcd_dvd_left _ _)) hjN
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_gcd hglt
  obtain ⟨a, ha, hga⟩ := (Nat.dvd_prime_pow hp.out).1 (Nat.gcd_dvd_right j (p ^ (M + 1)))
  have haM : a ≤ M := by
    by_contra h
    have : a = M + 1 := by omega
    subst this
    have h2 : p ^ (M + 1) ∣ j := hga ▸ Nat.gcd_dvd_left _ _
    exact absurd (Nat.le_of_dvd hj0 h2) (by omega)
  obtain ⟨t, ht⟩ : Nat.gcd j (p ^ (M + 1)) ∣ p ^ M := hga ▸ pow_dvd_pow p haM
  refine ⟨m * t, ?_⟩
  rw [← pow_mul, ← zeta_pow_eq_one' T M, Basic.zeta_pow_eq_iff]
  have h1 : j * m ≡ Nat.gcd j (p ^ (M + 1)) [MOD p ^ (M + 1)] := by
    unfold Nat.ModEq; rw [hm, Nat.mod_eq_of_lt hglt]
  have h2 := h1.mul_right t
  rw [← ht] at h2
  rw [← mul_assoc]; exact h2

theorem isInt_zeta (T : Tower p Ω) (N : ℕ) : IsInt p (T.ζ N) := by
  refine IsIntegral.of_pow (pow_pos hp.out.pos N) ?_
  rw [(T.prim N).pow_eq_one]; exact isIntegral_one

theorem ggeo_zeta (T : Tower p Ω) (N : ℕ) {g : Gal p Ω} (hg : g ∈ Ggeo p Ω) : g (T.ζ N) = T.ζ N := by
  apply hg
  refine ⟨Polynomial.X ^ (p ^ N) - 1, Polynomial.X_pow_sub_C_ne_zero (pow_pos hp.out.pos N) 1, ?_⟩
  simp [(T.prim N).pow_eq_one]

end GlobalTheory.K5.Decomp

namespace GlobalTheory.K5.Decomp

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem isInt_qq (T : Tower p Ω) (N : ℕ) : IsInt p (T.qq N) := by
  refine IsIntegral.of_pow (pow_pos hp.out.pos N) ?_
  rw [Basic.qq_pow]; exact isIntegral_algebraMap

theorem exists_mult (T : Tower p Ω) (N j : ℕ) (hj0 : 0 < j) (hjN : j < p ^ N) :
    ∃ s : Ω, IsInt p s ∧ (∀ g ∈ Ggeo p Ω, g s = s) ∧ s * (T.ζ N ^ j - 1) = T.ζ 1 - 1 := by
  obtain ⟨e, he⟩ := exists_pow_eq_zeta_one T N j hj0 hjN
  refine ⟨∑ i ∈ Finset.range e, (T.ζ N ^ j) ^ i, ?_, ?_, ?_⟩
  · exact IsIntegral.sum _ fun i _ => ((isInt_zeta T N).pow j).pow i
  · intro g hg
    simp only [map_sum, map_pow, ggeo_zeta T N hg]
  · rw [geom_sum_mul, he]

end GlobalTheory.K5.Decomp

open GlobalTheory.K5.Decomp in

theorem GlobalTheory.K5.Decomp.decomp : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (τ : Gal p Ω), τ ∈ Ggeo p Ω → (∀ n, τ (T.qq n) = T.ζ n * T.qq n) →
  ∀ (N : ℕ) (y : Ω), IsInt p y → (∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g y = y) →
  ∃ o w : Ω, IsInt p o ∧ (∀ g ∈ Ggeo p Ω, g o = o) ∧ IsInt p w ∧
    (∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g w = w) ∧
    (T.ζ 1 - 1) * y = (T.ζ 1 - 1) * o + (τ w - w) := by
  intro p _ _ Ω _ _ hΩ T τ hτ hτq N y hy hfix
  obtain ⟨c, hc, rfl⟩ := GlobalTheory.T.exists_qRoot_poly_of_fixed_geometric_stabilizer p Ω hΩ T N y hfix
  have hci := GlobalTheory.T.isIntegral_coeffs_of_geometric_fixed_qExpansion p Ω hΩ T N c hc hy
  have hpos : 0 < p ^ N := pow_pos (Fact.out : p.Prime).pos N
  have hs : ∀ j, ∃ s : Ω, IsInt p s ∧ (∀ g ∈ Ggeo p Ω, g s = s) ∧
      (0 < j → j < p ^ N → s * (T.ζ N ^ j - 1) = T.ζ 1 - 1) := by
    intro j
    by_cases h : 0 < j ∧ j < p ^ N
    · obtain ⟨s, h1, h2, h3⟩ := exists_mult T N j h.1 h.2
      exact ⟨s, h1, h2, fun _ _ => h3⟩
    · exact ⟨0, isIntegral_zero, fun g _ => map_zero g, fun a b => absurd ⟨a, b⟩ h⟩
  choose s hsi hsg hse using hs
  refine ⟨c 0, ∑ j ∈ Finset.range (p ^ N), s j * c j * T.qq N ^ j, hci 0 hpos, hc 0, ?_, ?_, ?_⟩
  · refine IsIntegral.sum _ fun j hj => ?_
    exact ((hsi j).mul (hci j (Finset.mem_range.1 hj))).mul ((isInt_qq T N).pow j)
  · intro g hg
    have hg1 := (Subgroup.mem_inf.1 hg).1
    have hg2 : g (T.qq N) = T.qq N := (Subgroup.mem_inf.1 hg).2
    simp only [map_sum, map_mul, map_pow, hsg _ g hg1, hc _ g hg1, hg2]
  · obtain ⟨M, hM⟩ : ∃ M, p ^ N = M + 1 := ⟨p ^ N - 1, by omega⟩
    have key : ∀ i < M, s (i + 1) * (T.ζ N ^ (i + 1) - 1) = T.ζ 1 - 1 := fun i hi =>
      hse (i + 1) (Nat.succ_pos i) (by omega)
    simp only [map_sum, map_mul, map_pow, hsg _ τ hτ, hc _ τ hτ, hτq N]
    rw [hM, Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ']
    have : ∀ i ∈ Finset.range M, s (i + 1) * c (i + 1) * (T.ζ N * T.qq N) ^ (i + 1) =
        s (i + 1) * c (i + 1) * T.qq N ^ (i + 1) + (T.ζ 1 - 1) * (c (i + 1) * T.qq N ^ (i + 1)) := by
      intro i hi
      rw [← key i (Finset.mem_range.1 hi)]; ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
