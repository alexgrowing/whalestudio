import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.CrisTheta

open Ideal Reformulated.AutPerF

universe u

namespace UpperTheory.RingBr

private theorem geom_sum_eq_pow_poly (p : ℕ) [Fact p.Prime] :
    (∑ i ∈ Finset.range p, (Polynomial.X : Polynomial (ZMod p)) ^ i)
      = (Polynomial.X - 1) ^ (p - 1) := by
  have hp : p.Prime := Fact.out
  have h0 : (Polynomial.X - 1 : Polynomial (ZMod p)) ≠ 0 := by
    simpa using Polynomial.X_sub_C_ne_zero (1 : ZMod p)
  apply mul_right_cancel₀ h0
  rw [geom_sum_mul, ← pow_succ, Nat.sub_add_cancel hp.one_le, sub_pow_char, one_pow]

private theorem cyclotomic_pow_sub_one_nilpotent {B : Type*} [CommRing B] (p : ℕ) [Fact p.Prime] (hB : (p : B) = 0)
    (z : B) (h : (z - 1) ^ p = 0 ∨ (∑ i ∈ Finset.range p, z ^ i) ^ p = 0) :
    (z ^ p - 1) ^ (p - 1) = 0 := by
  have hp : p.Prime := Fact.out
  rcases subsingleton_or_nontrivial B with hs | hn
  · exact Subsingleton.elim _ _
  haveI : CharP B p := (CharP.charP_iff_prime_eq_zero hp).2 hB
  have h1 : z ^ p - 1 = (z - 1) ^ p := by rw [sub_pow_char, one_pow]
  rw [h1]
  rcases h with h | h
  · rw [h, zero_pow]
    have := hp.two_le
    omega
  · letI : Algebra (ZMod p) B := ZMod.algebra B p
    have h2 := congrArg (Polynomial.aeval z) (geom_sum_eq_pow_poly p)
    simp only [map_sum, map_pow, map_sub, map_one, Polynomial.aeval_X] at h2
    rw [h2] at h
    rw [← pow_mul, mul_comm, pow_mul, h]

private theorem dvd_prod_shift_sub_prod {A : Type*} [CommRing A] (p : ℕ) [Fact p.Prime] (z : A)
    (h : (p : A) ∣ (z - 1) ^ p ∨ (p : A) ∣ (∑ i ∈ Finset.range p, z ^ i) ^ p) :
    (p : A) ∣ (z ^ p - 1) ^ (p - 1) := by
  simp only [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, map_pow, map_sub,
    map_one, map_sum] at h ⊢
  refine cyclotomic_pow_sub_one_nilpotent p ?_ _ h
  rw [← map_natCast (Ideal.Quotient.mk (span {(p : A)})), Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]

private theorem p_dvd_pow_of_theta (x : Ainf p R) (hx : Ainf.theta p R x = 0) :
    (p : Acris p R) ∣ (algebraMap (Ainf p R) (Acris p R) x) ^ p := by
  have h := AcrisZero.factorial_dvd_pow_of_mem_pdIdeal (AcrisZero.algebraMap_mem_pdIdeal x hx) p
  have h2 := map_dvd (algebraMap (AcrisZero p R) (Acris p R)) h
  rw [map_natCast, map_pow, ← IsScalarTower.algebraMap_apply] at h2
  exact (Nat.cast_dvd_cast (Nat.dvd_factorial (Fact.out : p.Prime).pos le_rfl)).trans h2

theorem p_dvd_mu_pow [IsDomain R] (η : tateModule p R) :
    (p : Acris p R) ∣ (algebraMap (Ainf p R) (Acris p R) (Ainf.teich p η.1 - 1)) ^ (p - 1) := by
  obtain ⟨y, hy⟩ : ∃ y : Tilt p R, y ^ p = η.1 :=
    ⟨(frobeniusEquiv (Tilt p R) p).symm η.1, frobeniusEquiv_symm_pow_p _ _ _⟩
  have hη : PreTilt.untilt η.1 = 1 := η.2
  have hθ : Ainf.theta p R (Ainf.teich p y) ^ p = 1 := by
    rw [← map_pow, ← map_pow, hy, Ainf.theta_teich, hη]
  rw [← hy, map_pow, map_sub, map_pow, map_one]
  apply dvd_prod_shift_sub_prod
  have hm := geom_sum_mul (Ainf.theta p R (Ainf.teich p y)) p
  rw [hθ, sub_self] at hm
  rcases mul_eq_zero.1 hm with h | h
  · right
    have := p_dvd_pow_of_theta (∑ i ∈ Finset.range p, Ainf.teich p y ^ i)
      (by simpa only [map_sum, map_pow] using h)
    simpa only [map_sum, map_pow] using this
  · left
    have := p_dvd_pow_of_theta (Ainf.teich p y - 1) (by simpa only [map_sub, map_one] using h)
    simpa only [map_sub, map_one] using this

end UpperTheory.RingBr
