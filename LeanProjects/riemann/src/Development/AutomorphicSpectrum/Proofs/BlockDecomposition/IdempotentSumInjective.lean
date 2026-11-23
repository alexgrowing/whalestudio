import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.FixInj

variable {l : ℕ} [Fact l.Prime]

theorem coeff_zero_eq_zero_of_mem (A : PAlg l) :
    ∀ (n : ℕ) (d : ℤ) (x : A.W), ¬ ((l : ℤ) ^ n ∣ d) →
      (d : A.W) * x ∈ Ideal.span {(l : A.W) ^ n} → x.coeff 0 = 0 := by
  intro n
  induction n with
  | zero => intro d x h; exact absurd (by simp) h
  | succ n ih =>
    intro d x hd hx
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hx
    by_cases hl : (l : ℤ) ∣ d
    · obtain ⟨d', rfl⟩ := hl
      refine ih d' x (fun h => hd ?_) ?_
      · rw [pow_succ']; exact mul_dvd_mul_left _ h
      · refine Ideal.mem_span_singleton'.2 ⟨y, ?_⟩
        have h0 : (l : A.W) * (y * (l : A.W) ^ n - (d' : A.W) * x) = 0 := by
          push_cast at hy
          linear_combination hy
        exact sub_eq_zero.1 (A.l_mul_eq_zero h0)
    · have hc : (d : A.A) * x.coeff 0 = 0 := by
        have h1 := congrArg (WittVector.constantCoeff : A.W →+* A.A) hy
        rw [map_mul, map_mul, map_pow, map_natCast, map_intCast, A.natCast_l,
          zero_pow (Nat.succ_ne_zero n), mul_zero, WittVector.constantCoeff_apply] at h1
        exact h1.symm
      have hcop : IsCoprime d (l : ℤ) :=
        (((Nat.prime_iff_prime_int.1 (Fact.out : l.Prime)).coprime_iff_not_dvd).2 hl).symm
      obtain ⟨u, v, huv⟩ := hcop
      have h2 : (u : A.A) * (d : A.A) + (v : A.A) * (l : A.A) = 1 := by
        have := congrArg (Int.cast : ℤ → A.A) huv
        push_cast at this
        exact this
      rw [A.natCast_l, mul_zero, add_zero] at h2
      calc x.coeff 0 = ((u : A.A) * (d : A.A)) * x.coeff 0 := by rw [h2, one_mul]
        _ = (u : A.A) * ((d : A.A) * x.coeff 0) := mul_assoc _ _ _
        _ = 0 := by rw [hc, mul_zero]

theorem idemSum_mul_teichmuller (A : PAlg l) (n : ℕ) [NeZero (l ^ n)] (e : ZMod (l ^ n) → A.A)
    (he : CompleteOrthogonalIdempotents e) (a : ZMod (l ^ n)) (z : A.A) :
    A.idemSum n e * Ideal.Quotient.mk (Ideal.span {(l : A.W) ^ n})
        (WittVector.teichmuller l (e a * z)) =
      (a.val : A.Wn n) * Ideal.Quotient.mk (Ideal.span {(l : A.W) ^ n})
        (WittVector.teichmuller l (e a * z)) := by
  have hterm : ∀ c : ZMod (l ^ n),
      Ideal.Quotient.mk (Ideal.span {(l : A.W) ^ n}) (WittVector.teichmuller l (e c)) *
        Ideal.Quotient.mk (Ideal.span {(l : A.W) ^ n}) (WittVector.teichmuller l (e a * z)) =
      Ideal.Quotient.mk (Ideal.span {(l : A.W) ^ n})
        (WittVector.teichmuller l (e c * (e a * z))) := by
    intro c
    rw [← map_mul, ← map_mul]
  unfold PAlg.idemSum
  rw [Finset.sum_mul, Finset.sum_eq_single a]
  · rw [mul_assoc, hterm, ← mul_assoc, he.idem a]
  · intro c _ hc
    rw [mul_assoc, hterm, ← mul_assoc, he.ortho hc, zero_mul, WittVector.teichmuller_zero, map_zero,
      mul_zero]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem mul_eq_zero_of_ne (A : PAlg l) (n : ℕ) [NeZero (l ^ n)] (e e' : ZMod (l ^ n) → A.A)
    (he : CompleteOrthogonalIdempotents e) (he' : CompleteOrthogonalIdempotents e')
    (hs : A.idemSum n e = A.idemSum n e') {a b : ZMod (l ^ n)} (hab : a ≠ b) :
    e a * e' b = 0 := by
  have h1 := idemSum_mul_teichmuller A n e he a (e' b)
  have h2 := idemSum_mul_teichmuller A n e' he' b (e a)
  rw [mul_comm (e' b) (e a)] at h2
  rw [hs, h2] at h1
  have hmem : (((a.val : ℤ) - (b.val : ℤ) : ℤ) : A.W) *
      WittVector.teichmuller l (e a * e' b) ∈ Ideal.span {(l : A.W) ^ n} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_intCast]
    push_cast
    exact (sub_mul _ _ _).trans (sub_eq_zero.2 h1.symm)
  have hnd : ¬ ((l : ℤ) ^ n ∣ ((a.val : ℤ) - (b.val : ℤ))) := by
    intro h
    apply hab
    have h3 := (ZMod.intCast_zmod_eq_zero_iff_dvd ((a.val : ℤ) - (b.val : ℤ)) (l ^ n)).2
      (by exact_mod_cast h)
    push_cast at h3
    simpa [sub_eq_zero] using h3
  have := coeff_zero_eq_zero_of_mem A n _ _ hnd hmem
  rwa [WittVector.teichmuller_coeff_zero] at this

theorem idem_unique : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) (e e' : ZMod (l ^ n) → A.A), (haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩; CompleteOrthogonalIdempotents e ∧ CompleteOrthogonalIdempotents e') → A.idemSum n e = A.idemSum n e' → e = e' := by
  intro l _ A n e e' h hs
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨he, he'⟩ : CompleteOrthogonalIdempotents e ∧ CompleteOrthogonalIdempotents e' := h
  funext a
  have h1 : e a = e a * e' a := by
    calc e a = e a * ∑ b, e' b := by rw [he'.complete, mul_one]
      _ = ∑ b, e a * e' b := Finset.mul_sum _ _ _
      _ = e a * e' a := Finset.sum_eq_single a
          (fun b _ hb => mul_eq_zero_of_ne A n e e' he he' hs (Ne.symm hb))
          (fun h => absurd (Finset.mem_univ a) h)
  have h2 : e' a = e a * e' a := by
    calc e' a = (∑ b, e b) * e' a := by rw [he.complete, one_mul]
      _ = ∑ b, e b * e' a := Finset.sum_mul _ _ _
      _ = e a * e' a := Finset.sum_eq_single a
          (fun b _ hb => mul_eq_zero_of_ne A n e e' he he' hs hb)
          (fun h => absurd (Finset.mem_univ a) h)
  exact h1.trans h2.symm

end GlobalTheory.CompanionTheory.FixInj
