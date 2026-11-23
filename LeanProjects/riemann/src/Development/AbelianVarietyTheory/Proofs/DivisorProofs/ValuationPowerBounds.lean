import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat
open scoped Classical

set_option autoImplicit false

namespace GlobalTheory.ConstLat

theorem w_prime_lt_one {F : Type} [Field F] [NumberField F] {p : ℕ} {v : HeightOneSpectrum (𝓞 F)}
    (hv : resP v = p) (e : Ext v) : e.w (p : AlgebraicClosure F) < 1 := by
  have hpv : ((p : 𝓞 F)) ∈ v.asIdeal := by
    have h0 : ((p : ℕ) : 𝓞 F ⧸ v.asIdeal) = 0 := (ringChar.spec _ p).2 (by rw [← hv]; rfl)
    rw [← map_natCast (Ideal.Quotient.mk v.asIdeal)] at h0
    exact Ideal.Quotient.eq_zero_iff_mem.1 h0
  have h := e.w_alg (p : F)
  rw [map_natCast] at h
  rw [h, ← map_natCast (algebraMap (𝓞 F) F) p, ← FinitePlace.norm_embedding]
  exact (FinitePlace.norm_lt_one_iff_mem F v _).2 hpv

theorem w_prime_pow_le_w_nat {F : Type} [Field F] [NumberField F] {p : ℕ} (hp : p.Prime) {v : HeightOneSpectrum (𝓞 F)}
    (hv : resP v = p) (e : Ext v) {n : ℕ} (hn : n ≠ 0) :
    e.w (p : AlgebraicClosure F) ^ n ≤ e.w (n : AlgebraicClosure F) := by
  have hna := isNonarchimedean_w e
  have hwp := w_prime_lt_one hv e
  set a := n.factorization p
  set m := n / p ^ a
  have hnm : p ^ a * m = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hcop : m.Coprime p := (Nat.coprime_ordCompl hp hn).symm

  have hm : e.w (m : AlgebraicClosure F) = 1 := by
    refine le_antisymm (hna.apply_natCast_le_one (n := m)) ?_
    have hg : ((Nat.gcd m p : ℕ) : ℤ) = m * Nat.gcdA m p + p * Nat.gcdB m p := Nat.gcd_eq_gcd_ab m p
    rw [hcop, Nat.cast_one] at hg
    have hg' : (1 : AlgebraicClosure F) = (m : AlgebraicClosure F) * ((Nat.gcdA m p : ℤ) : AlgebraicClosure F) +
        (p : AlgebraicClosure F) * ((Nat.gcdB m p : ℤ) : AlgebraicClosure F) := by
      have := congrArg (Int.cast (R := AlgebraicClosure F)) hg
      push_cast at this
      exact this
    have h1 : (1 : ℝ) ≤ max (e.w (m : AlgebraicClosure F)) (e.w (p : AlgebraicClosure F)) := by
      have := hna ((m : AlgebraicClosure F) * ((Nat.gcdA m p : ℤ) : AlgebraicClosure F))
        ((p : AlgebraicClosure F) * ((Nat.gcdB m p : ℤ) : AlgebraicClosure F))
      rw [← hg', map_one, map_mul, map_mul] at this
      refine this.trans (max_le_max ?_ ?_)
      · exact mul_le_of_le_one_right (e.w.nonneg _) hna.apply_intCast_le_one
      · exact mul_le_of_le_one_right (e.w.nonneg _) hna.apply_intCast_le_one
    rcases le_max_iff.1 h1 with h | h
    · exact h
    · exact absurd h (not_le.2 hwp)
  have ha : a ≤ n := by
    have h1 : a < p ^ a := Nat.lt_pow_self hp.one_lt
    have h2 : p ^ a ≤ n := Nat.ordProj_le p hn
    omega
  have hwn : e.w (n : AlgebraicClosure F) = e.w (p : AlgebraicClosure F) ^ a := by
    rw [← hnm, Nat.cast_mul, map_mul, hm, mul_one, Nat.cast_pow, map_pow]
  rw [hwn]
  exact pow_le_pow_of_le_one (e.w.nonneg _) hwp.le ha

theorem exists_prec_consts : ∀ {F : Type} [Field F] [NumberField F] (p n k : ℕ), p.Prime → n ≠ 0 → ∃ k' : ℕ,
    ∀ v : HeightOneSpectrum (𝓞 F), resP v = p → ∀ e : Ext v,
      e.w (p : AlgebraicClosure F) ^ k' / e.w (n : AlgebraicClosure F) ^ 3 ≤ e.w (p : AlgebraicClosure F) ^ k ∧
      e.w (p : AlgebraicClosure F) ^ k' / e.w (n : AlgebraicClosure F) ^ 2 < 1 ∧ e.w (p : AlgebraicClosure F) ^ k' < 1 := by
  intro F _ _ p n k hp hn
  refine ⟨k + 3 * n + 1, fun v hv e => ?_⟩
  have hwp := w_prime_lt_one hv e
  have hP0 : 0 < e.w (p : AlgebraicClosure F) :=
    e.w.pos (Nat.cast_ne_zero.2 hp.ne_zero)
  have hlow := w_prime_pow_le_w_nat hp hv e hn
  set P := e.w (p : AlgebraicClosure F)
  set N := e.w (n : AlgebraicClosure F)
  have hPn : 0 < P ^ n := pow_pos hP0 n
  have hN0 : 0 < N := hPn.trans_le hlow
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_iff₀ (pow_pos hN0 3)]
    calc P ^ (k + 3 * n + 1) = P ^ k * (P ^ n) ^ 3 * P := by ring
      _ ≤ P ^ k * (P ^ n) ^ 3 * 1 := mul_le_mul_of_nonneg_left hwp.le (by positivity)
      _ ≤ P ^ k * N ^ 3 := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hPn.le hlow 3) (by positivity)
  · rw [div_lt_one (pow_pos hN0 2)]
    calc P ^ (k + 3 * n + 1) = (P ^ n) ^ 2 * (P ^ (k + n + 1)) := by ring
      _ < (P ^ n) ^ 2 * 1 := mul_lt_mul_of_pos_left (pow_lt_one₀ hP0.le hwp (by omega)) (by positivity)
      _ ≤ N ^ 2 := by rw [mul_one]; exact pow_le_pow_left₀ hPn.le hlow 2
  · exact pow_lt_one₀ hP0.le hwp (by omega)

end GlobalTheory.ConstLat
