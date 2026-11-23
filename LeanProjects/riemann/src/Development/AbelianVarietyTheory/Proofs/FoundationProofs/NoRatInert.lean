import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdxEqRelIndex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QuadraticCharNegOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsNormCmPrimeInertPrimeSignStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui GlobalTheory.InertParity
open scoped BigOperators Pointwise
open Formalism.FrobeniusOrbits GlobalTheory.NormSign

namespace GlobalTheory.NormSignInert

theorem descent_rat {d q : ℕ} [Fact d.Prime] (hq : q.Prime) (hne : q ≠ d) {u : ℤ}
    (hu : quadraticChar (ZMod d) (-(u : ZMod d)) = -1) (C X Y : ℚ)
    (h : C ^ 2 * u + X ^ 2 = q * d * Y ^ 2) : C = 0 := by
  have key := descent hq hne (quadraticChar_neg_one_iff_not_isSquare.1 hu) _ (C.num * X.den * Y.den)
    (X.num * C.den * Y.den) (Y.num * C.den * X.den) rfl (by
      apply Int.cast_injective (α := ℚ)
      push_cast
      rw [← Rat.mul_den_eq_num C, ← Rat.mul_den_eq_num X, ← Rat.mul_den_eq_num Y]
      linear_combination ((C.den : ℚ) ^ 2 * X.den ^ 2 * Y.den ^ 2) * h)
  simpa [X.den_nz, Y.den_nz] using key

theorem char_eq {d q : ℕ} [Fact d.Prime] [Fact q.Prime] (hd : d % 4 = 3) (h2 : q ≠ 2) (hne : q ≠ d) :
    quadraticChar (ZMod d) q = quadraticChar (ZMod q) (-(d : ZMod q)) := by
  have hl2 : ringChar (ZMod d) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have h := quadraticChar_card_card hl2 (F' := ZMod q) (by rwa [ZMod.ringChar_zmod_n])
    (by rwa [ZMod.ringChar_zmod_n, ZMod.ringChar_zmod_n])
  rw [quadraticChar_neg_one' hd, ZMod.card, ZMod.card] at h
  rw [h]
  congr 1
  push_cast
  ring

theorem no_rat_inert {q d : ℕ} [Fact d.Prime] (h : HostHyp q d) {m : ℕ} (hm : EvenSq d m) {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : Odd f) (hpd : p ≠ d → ¬ IsSquare (-(d : ZMod p))) (A W : ℚ) :
    W ^ 2 ≠ q * d * (A ^ 2 - 4 * (p ^ f * m)) := by
  obtain ⟨hq, hd, hq8, hd16, hj⟩ := h
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, u, rfl, hu⟩ := hm
  have h1 := hq.pos
  have h2 := hd.pos
  intro hW
  push_cast at hW
  by_cases hpd' : p = d
  · subst hpd'
    obtain ⟨j, rfl⟩ := hf
    rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym] at hj
    push_cast at hj
    rw [← char_eq (d := p) (q := q) (by omega) (by omega) (by omega)] at hj
    have key := descent_rat (d := p) hq (by omega) (u := q * u) (by
      rw [← neg_one_mul, map_mul, quadraticChar_neg_one' (by omega)]
      push_cast
      rw [map_mul, hj, hu]; norm_num) (2 * p ^ (j + k + 1)) W A (by
      push_cast
      linear_combination hW)
    have : (0 : ℚ) < 2 * p ^ (j + k + 1) := by positivity
    exact this.ne' key
  · have h3 := quadraticChar_neg_one_iff_not_isSquare.2 (hpd hpd')
    rw [← char_eq (d := d) (q := p) (by omega) hp2 hpd'] at h3
    have key := descent_rat (d := d) hq (by omega) (u := -(p ^ f * u)) (by
      push_cast
      rw [neg_neg, map_mul, map_pow, h3, hu, hf.neg_one_pow]; norm_num) (2 * q * d * d ^ k) (q * d * A) W (by
      push_cast
      linear_combination (-(q * d : ℚ)) * hW)
    have : (0 : ℚ) < 2 * q * d * d ^ k := by positivity
    exact this.ne' key

theorem exists_norm {R : Ranks} (H : Host R) (t : H.E) (ht : H.conj t = t) :
    ∃ n A W : ℚ, (n : H.E) = part H t (1, 1) * part H t (-1, 1) ∧ W ^ 2 = H.q * H.d * (A ^ 2 - 4 * n) := by
  have ha : H.sqq ^ 2 = -(H.q : H.E) := H.sqq_sq
  have hb : H.sqd ^ 2 = -(H.d : H.E) := H.sqd_sq
  set s := part H (t : H.E) (1, 1) with hs
  set s' := part H (t : H.E) (-1, 1) with hs'
  have e1 : part H (t : H.E) (-1, -1) = s := by rw [part_neg H ht]; simp [hs]
  have e2 : part H (t : H.E) (1, -1) = s' := by rw [part_neg H ht]; simp [hs']
  have key : ∀ g : R.GG, (g.1.1 * g.1.2 = 1 ∧ H.sigmaOf g s = s ∧ H.sigmaOf g s' = s') ∨
      (g.1.1 * g.1.2 = -1 ∧ H.sigmaOf g s = s' ∧ H.sigmaOf g s' = s) := by
    rintro ⟨⟨u, v⟩, h⟩
    rw [hs, hs', sigmaOf_part, sigmaOf_part]
    rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or v with rfl | rfl <;>
      simp [e1, e2, ← hs, ← hs']
  obtain ⟨n, hn⟩ := exists_rat H (x := s * s') fun g => by
    rcases key g with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> rw [map_mul, h1, h2]
    ring
  obtain ⟨A, hA⟩ := exists_rat H (x := s + s') fun g => by
    rcases key g with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> rw [map_add, h1, h2]
    ring
  obtain ⟨W, hW⟩ := exists_rat H (x := (s - s') * (H.sqq * H.sqd)) fun g => by
    rw [map_mul, map_mul, map_sub, sigmaOf_aE, sigmaOf_bE, mul_mul_mul_comm, ← Int.cast_mul, ← Units.val_mul]
    rcases key g with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;> rw [h0, h1, h2] <;> push_cast <;> ring
  refine ⟨n, A, W, hn, ?_⟩
  apply Rat.cast_injective (α := H.E)
  push_cast
  rw [hW, hA, hn, mul_pow, mul_pow, ha, hb]
  ring

theorem norm_neg : ∀ (D : D7) (t : 𝓞 D.host.E) (P B : Ideal (𝓞 D.host.E)), t ≠ 0 →
    D.host.conj (t : D.host.E) = t → P.IsMaximal → D.host.conj • P = P →
    Ideal.span {t} = P * B * (D.host.conj • B) → (∏ τ, embT D τ (t : D.host.E)).re < 0 := by
  intro D t P B ht0 ht hP hc hB
  obtain ⟨-, p, f, hp, -, hp2, -, hf, hN, hpd⟩ := (GlobalTheory.T.absNorm_cmPrime_inertPrime_sign D P hP).2.1 hc
  rw [prod_embT]
  generalize D.host = H at *
  haveI : Fact H.d.Prime := ⟨H.hyp.2.1⟩
  have ha : H.sqq ^ 2 = -(H.q : H.E) := H.sqq_sq
  have hb : H.sqd ^ 2 = -(H.d : H.E) := H.sqd_sq
  have hB0 : B ≠ ⊥ := by
    rintro rfl
    exact ht0 (by simpa using hB)
  have hm := evenSq_absNorm H.hyp ha hb B hB0
  have hm0 : 0 < Ideal.absNorm B := Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  obtain ⟨n, A, W, hn, hWn⟩ := exists_norm H (t : H.E) ht
  have hn2 : n ^ 2 = ((p : ℚ) ^ f * (Ideal.absNorm B : ℚ)) ^ 2 := by
    have h1 : Algebra.norm ℚ (t : H.E) = n ^ 2 := by
      apply Rat.cast_injective (α := H.E)
      rw [norm_eq H ht]
      push_cast
      rw [hn]
    have h2 := congrArg Ideal.absNorm hB
    rw [map_mul, map_mul, absNorm_smul, Ideal.absNorm_span_singleton, hN] at h2
    have h3 := congrArg (fun k : ℕ => ((k : ℤ) : ℚ)) h2
    simp only [Int.natCast_natAbs] at h3
    push_cast at h3
    rw [Algebra.coe_norm_int, h1, abs_of_nonneg (sq_nonneg _)] at h3
    rw [h3]; ring
  rw [← hn, map_ratCast, Complex.ratCast_re]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hn2 with h | h
  · exact absurd (by rw [hWn, h]) (no_rat_inert H.hyp hm hp hp2 hf hpd A W)
  · have := hp.pos
    have h0 : (0 : ℚ) < (p : ℚ) ^ f * (Ideal.absNorm B : ℚ) := by positivity
    have h1 : n < 0 := by rw [h]; exact neg_neg_of_pos h0
    exact_mod_cast h1

end GlobalTheory.NormSignInert
