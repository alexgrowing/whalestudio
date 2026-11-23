import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.UniformContinuousConstSMulOfIsIsometricSMul
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.ExistsFactorialMulEqPow
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.DeRham
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.DeRhamMap
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Embedding
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.PadicField
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Action
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.MapEqPadicPowCyclotomicCharacter
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.TruncLogEqOfPowEqZero
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Period
namespace PowMulEqZero
section

open Ideal Reformulated.AutPerF
open scoped Nat

namespace Bridge.CrisLoc.PowMulEqZeroLemmas

theorem expand {A : Type*} [CommRing A] {p : ℕ} (hp : p.Prime) (m : A) :
    ∃ h : A, (m + 1) ^ p = m ^ p + 1 + p * m * (1 + m * h) := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (Polynomial.X : Polynomial ℤ) 1
  have h1 := congrArg (fun f => Polynomial.coeff f 1) hr
  have e : (p : Polynomial ℤ) * Polynomial.X * 1 * r = Polynomial.C (p : ℤ) * (Polynomial.X * r) := by
    simp [mul_assoc]
  simp only [e, Polynomial.coeff_X_add_one_pow, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, one_pow, Nat.choose_one_right, Polynomial.coeff_one] at h1
  rw [show (1 : ℕ) = 0 + 1 from rfl, Polynomial.coeff_X_mul] at h1
  have hp1 : ¬ (1 = p) := hp.one_lt.ne
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h2 : r.coeff 0 = 1 := by
    simp [hp1] at h1
    apply mul_left_cancel₀ hp0
    first | simpa using h1.symm | simpa using h1 | (rcases h1 with h1 | h1 <;> simp_all)
  obtain ⟨s, hs⟩ := Polynomial.X_dvd_sub_C (p := r)
  rw [h2, sub_eq_iff_eq_add] at hs
  refine ⟨Polynomial.aeval m s, ?_⟩
  have h3 := congrArg (Polynomial.aeval m) hr
  rw [hs] at h3
  simp at h3
  rw [h3]; ring

theorem val_fact (p : ℕ) [hp : Fact p.Prime] (j : ℕ) :
    p ^ j ≤ padicValNat p (p ^ j * (p - 1))! + 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', mul_assoc, padicValNat_factorial_mul]
    obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.out.pos; omega⟩
    have h1 : p - 1 = q := by omega
    rw [h1] at ih ⊢
    have : p * p ^ j = p ^ j * q + p ^ j := by
      generalize p ^ j = t
      rw [hq]; ring
    omega

variable {p : ℕ} [Fact p.Prime]
variable {R : Type*} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]

theorem isUnit_of_mem {y : Acris p R} (hy : y ∈ (span {(p : Acris p R)}).radical) :
    IsUnit (1 + y) := by
  have h1 : (span {(p : Acris p R)}).radical ≤ Ideal.jacobson ⊥ :=
    (Ideal.isRadical_jacobson ⊥).radical_le_iff.2 (IsAdicComplete.le_jacobson_bot _)
  have := Ideal.mem_jacobson_bot.1 (h1 hy) 1
  rwa [mul_one, add_comm] at this

theorem p_mem : (p : Acris p R) ∈ (span {(p : Acris p R)}).radical :=
  Ideal.le_radical (mem_span_singleton_self _)

theorem fact_dvd (a : Ainf p R) (ha : Ainf.theta p R a = 0) (n : ℕ) :
    (n ! : Acris p R) ∣ algebraMap (Ainf p R) (Acris p R) a ^ n := by
  have := congrArg (algebraMap (AcrisZero p R) (Acris p R)) (AcrisZero.factorial_mul_gamma n a ha)
  rw [map_mul, map_natCast, map_pow] at this
  exact ⟨_, this.symm⟩

theorem mem_rad (a : Ainf p R) (ha : Ainf.theta p R a = 0) :
    algebraMap (Ainf p R) (Acris p R) a ∈ (span {(p : Acris p R)}).radical :=
  ⟨p, Ideal.mem_span_singleton.2 ((Nat.cast_dvd_cast
    (Nat.dvd_factorial (Fact.out : p.Prime).pos le_rfl)).trans (fact_dvd a ha p))⟩

theorem pow_dvd_of_prod (a : Ainf p R) (ha : Ainf.theta p R a = 0) {b : Acris p R}
    (hb : b ∈ (span {(p : Acris p R)}).radical) :
    ∃ k : ℕ, (p : Acris p R) ^ (k + 1) ∣
      ((algebraMap (Ainf p R) (Acris p R) a * b) ^ (p - 1)) ^ k := by
  have hp : p.Prime := Fact.out
  obtain ⟨N, hN⟩ := hb
  rw [Ideal.mem_span_singleton] at hN
  refine ⟨p ^ (N * 2), ?_⟩
  rw [← pow_mul, mul_comm (p - 1), mul_pow]
  have h1 : (p : Acris p R) ^ padicValNat p (p ^ (N * 2) * (p - 1))! ∣
      algebraMap (Ainf p R) (Acris p R) a ^ (p ^ (N * 2) * (p - 1)) := by
    refine Dvd.dvd.trans ?_ (fact_dvd a ha _)
    rw [← Nat.cast_pow]
    exact Nat.cast_dvd_cast pow_padicValNat_dvd
  have h2 : (p : Acris p R) ^ 2 ∣ b ^ (p ^ (N * 2) * (p - 1)) := by
    refine (pow_dvd_pow_of_dvd hN 2).trans ?_
    rw [← pow_mul]
    refine pow_dvd_pow _ ?_
    have h3 : N * 2 < p ^ (N * 2) := Nat.lt_pow_self hp.one_lt
    have h4 : 1 ≤ p - 1 := by have := hp.two_le; omega
    exact h3.le.trans (Nat.le_mul_of_pos_right _ h4)
  refine Dvd.dvd.trans ?_ (mul_dvd_mul h1 h2)
  rw [← pow_add]
  refine pow_dvd_pow _ ?_
  have := val_fact p (N * 2)
  omega

theorem exists_pow_dvd [IsDomain R] (e : Tilt p R) (he : PreTilt.untilt e = 1) :
    ∃ k : ℕ, (p : Acris p R) ^ (k + 1) ∣
      ((algebraMap (Ainf p R) (Acris p R) (Ainf.teich p e) - 1) ^ (p - 1)) ^ k := by
  have hp : p.Prime := Fact.out
  obtain ⟨w, hw⟩ : ∃ w : Ainf p R, w ^ p = Ainf.teich p e :=
    ⟨Ainf.teich p ((frobeniusEquiv (Tilt p R) p).symm e), by
      rw [← map_pow, frobeniusEquiv_symm_pow_p]⟩
  have hg : (∑ i ∈ Finset.range p, w ^ i) * (w - 1) = Ainf.teich p e - 1 := by
    rw [geom_sum_mul, hw]
  have h0 : Ainf.theta p R (Ainf.teich p e - 1) = 0 := by
    rw [map_sub, Ainf.theta_teich, he, map_one, sub_self]
  have hm := mem_rad _ h0
  have hw1 : algebraMap (Ainf p R) (Acris p R) (w - 1) ∈ (span {(p : Acris p R)}).radical := by
    obtain ⟨h, hh⟩ := expand hp (w - 1)
    rw [sub_add_cancel, hw] at hh
    apply Ideal.mem_radical_of_pow_mem (m := p)
    have : (w - 1) ^ p = (Ainf.teich p e - 1) - p * ((w - 1) * (1 + (w - 1) * h)) := by
      linear_combination -hh
    rw [← map_pow, this, map_sub, map_mul, map_natCast]
    exact sub_mem hm (Ideal.mul_mem_right _ _ p_mem)
  have hs : algebraMap (Ainf p R) (Acris p R) (∑ i ∈ Finset.range p, w ^ i) ∈
      (span {(p : Acris p R)}).radical := by
    have : (∑ i ∈ Finset.range p, w ^ i) = p + ∑ i ∈ Finset.range p, (w ^ i - 1) := by
      simp [Finset.sum_sub_distrib]
    rw [this, map_add, map_natCast, map_sum]
    refine add_mem p_mem (Ideal.sum_mem _ fun i _ => ?_)
    obtain ⟨c, hc⟩ := sub_one_dvd_pow_sub_one w i
    rw [hc, map_mul]
    exact Ideal.mul_mem_right _ _ hw1
  have hg' : algebraMap (Ainf p R) (Acris p R) (Ainf.teich p e) - 1 =
      algebraMap (Ainf p R) (Acris p R) (∑ i ∈ Finset.range p, w ^ i) *
        algebraMap (Ainf p R) (Acris p R) (w - 1) := by
    rw [← map_mul, hg, map_sub, map_one]
  rw [← hg, map_mul] at h0
  rcases mul_eq_zero.1 h0 with h | h
  · rw [hg']; exact pow_dvd_of_prod _ h hw1
  · rw [hg', mul_comm]; exact pow_dvd_of_prod _ h hs

theorem step [IsDomain R] (e : Tilt p R) (he : PreTilt.untilt e = 1) {z : Acris p R}
    (hz : (algebraMap (Ainf p R) (Acris p R) (Ainf.teich p e) ^ p - 1) * z = 0) :
    (algebraMap (Ainf p R) (Acris p R) (Ainf.teich p e) - 1) * z = 0 := by
  have hp : p.Prime := Fact.out
  obtain ⟨k, c, hc⟩ := exists_pow_dvd e he
  have hm : algebraMap (Ainf p R) (Acris p R) (Ainf.teich p e) - 1 ∈
      (span {(p : Acris p R)}).radical := by
    have := mem_rad (Ainf.teich p e - 1) (by rw [map_sub, Ainf.theta_teich, he, map_one, sub_self])
    rwa [map_sub, map_one] at this
  obtain ⟨m, hmu⟩ : ∃ m, algebraMap (Ainf p R) (Acris p R) (Ainf.teich p e) = m + 1 :=
    ⟨_, (sub_add_cancel _ 1).symm⟩
  rw [hmu] at hz
  rw [hmu, add_sub_cancel_right] at hc hm ⊢
  obtain ⟨h, hh⟩ := expand hp m
  have hpp : m ^ p = m ^ (p - 1) * m := by rw [pow_sub_one_mul hp.ne_zero]
  have h1 : (p * (1 + m * h) - (-m ^ (p - 1))) * (m * z) = 0 := by
    rw [hh, hpp] at hz
    linear_combination hz
  obtain ⟨d, hd⟩ := sub_dvd_pow_sub_pow (p * (1 + m * h)) (-m ^ (p - 1)) k
  obtain ⟨g, hg⟩ := sub_one_dvd_pow_sub_one (1 + m * h) k
  have h2 : (p : Acris p R) ^ k * ((1 + (m * (h * g) - p * ((-1) ^ k * c))) * (m * z)) =
      p ^ k * 0 := by
    rw [neg_pow, hc, mul_pow] at hd
    linear_combination (m * z) * hd + d * h1 - (p : Acris p R) ^ k * (m * z) * hg
  exact (isUnit_of_mem (sub_mem (Ideal.mul_mem_right _ _ hm)
    (Ideal.mul_mem_right _ _ p_mem))).mul_right_eq_zero.1 (Acris.p_pow_mul_cancel k h2)

theorem tower {A : Type*} [CommRing A] (p : ℕ) (u y : A) (hy : u - 1 = p ^ 2 * y) (n : ℕ) :
    ∃ c : A, u ^ p ^ n - 1 = p ^ n * (u - 1) * (1 + p * c) := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨r, hr⟩ := Polynomial.powAddExpansion (1 : A) (u ^ p ^ n - 1) p
    rw [add_sub_cancel, ← pow_mul, ← pow_succ, one_pow, one_pow, hc] at hr
    refine ⟨c + r * p ^ n * y * (1 + p * c) ^ 2, ?_⟩
    rw [hr, hy]; ring

theorem of_log [IsDomain R] (e : tateModule p R) {z : Acris p R}
    (hz : Acris.logTeich e * z = 0) :
    (algebraMap (Ainf p R) (Acris p R) (Ainf.teich p e.1) - 1) * z = 0 := by
  have he : PreTilt.untilt e.1 = 1 := e.2
  have hu : Ainf.theta p R (Ainf.teich p e.1) = 1 := by rw [Ainf.theta_teich, he]
  have hq : ∀ n, ∃ l d : Acris p R, (p : Acris p R) ^ n * l =
      algebraMap (Ainf p R) (Acris p R) (Ainf.teich p e.1) ^ p ^ n - 1 ∧
      Acris.logTeich e = l + p ^ n * d := fun n => by
    obtain ⟨l, h1, h2⟩ := Acris.exists_quot _ hu n
    obtain ⟨d, hd⟩ := (Acris.eval_eq_zero_iff n (Acris.logTeich e - algebraMap _ _ l)).1
      (by rw [map_sub, Acris.eval_algebraMap, sub_eq_zero]; exact h2)
    refine ⟨algebraMap _ _ l, d, ?_, by linear_combination hd⟩
    have := congrArg (algebraMap (AcrisZero p R) (Acris p R)) h1
    rw [map_mul, map_pow, map_natCast, map_sub, map_pow, map_one] at this
    exact this
  apply step e.1 he
  have h2 := @step p _ R _ _ _ _ (e.1 ^ p) (by rw [map_pow, he, one_pow]) z
  rw [map_pow, map_pow, ← pow_mul, ← sq] at h2
  apply h2
  generalize algebraMap (Ainf p R) (Acris p R) (Ainf.teich p e.1) = u at hq ⊢
  refine Acris.eq_zero_of_forall_dvd fun n => ?_
  obtain ⟨y, -, hy, -⟩ := hq 2
  obtain ⟨c, hc⟩ := tower p (u ^ p ^ 2) y hy.symm n
  obtain ⟨l, d, hl, hd⟩ := hq (2 + n)
  rw [pow_add p 2 n, pow_mul, hc] at hl
  have h3 : (p : Acris p R) ^ 2 * l = (u ^ p ^ 2 - 1) * (1 + p * c) :=
    Acris.p_pow_mul_cancel n (by linear_combination hl)
  have hun : IsUnit (1 + (p : Acris p R) * c) := isUnit_of_mem (Ideal.mul_mem_right _ _ p_mem)
  rw [← hun.dvd_mul_left]
  refine ⟨-(p ^ 4 * d * z), ?_⟩
  rw [hd] at hz
  linear_combination (p : Acris p R) ^ 2 * hz - z * h3

theorem log_change [IsDomain R] (e : tateModule p R) {ε : tateModule p R} (hε : IsPrimitive ε)
    {z : Acris p R} (hz : Acris.logTeich ε * z = 0) : Acris.logTeich e * z = 0 := by
  obtain ⟨a, rfl⟩ := hε.padicPow_surjective e
  refine Acris.eq_zero_of_forall_dvd fun k => ?_
  obtain ⟨η, hη⟩ := tateModule.exists_padicPow_eq ε
    (Ideal.mem_span_singleton.1 (PadicInt.appr_spec k a))
  refine ⟨Acris.logTeich η * z, ?_⟩
  rw [hη, Acris.logTeich_mul, Acris.logTeich_pow, Acris.logTeich_pow]
  push_cast
  linear_combination (a.appr k : Acris p R) * hz

theorem main [IsDomain R] (e : tateModule p R) {m : BcrisPlus p R} (hm : m ∈ BcrisPlus.periods p R) :
    ∀ x : Acris p R, m * algebraMap _ _ x = 0 →
      ∃ n : ℕ, (algebraMap (Ainf p R) (Acris p R) (Ainf.teich p e.1) - 1) ^ n * x = 0 := by
  induction hm using Submonoid.closure_induction_left with
  | one =>
    intro x hx
    refine ⟨0, ?_⟩
    rw [pow_zero, one_mul]
    exact BcrisPlus.algebraMap_injective (by rw [map_zero]; simpa using hx)
  | mul_left a ha b hb ih =>
    intro x hx
    obtain ⟨ε, hε, rfl⟩ := ha
    obtain ⟨n, hn⟩ := ih (Acris.logTeich ε * x) (by rw [map_mul]; linear_combination hx)
    refine ⟨n + 1, ?_⟩
    have := of_log e (log_change e hε (z := _ ^ n * x) (by rw [mul_left_comm]; exact hn))
    rw [pow_succ', mul_assoc]
    exact this

end Bridge.CrisLoc.PowMulEqZeroLemmas

theorem Bridge.CrisLoc.exists_pow_mul_eq_zero : ∀ (l : ℕ) [Fact l.Prime] (e : (Reformulated.AutPerF.Tilt l ↥(PadicComplexInt l))) (he : e.untilt = 1) (hne : e ≠ 1) {x : (Reformulated.AutPerF.Acris l ↥(PadicComplexInt l))} (hx : algebraMap ((Reformulated.AutPerF.Acris l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.Bcris l ↥(PadicComplexInt l))) x = 0), ∃ n : ℕ, algebraMap ((Reformulated.AutPerF.Ainf l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.Acris l ↥(PadicComplexInt l))) (WittVector.teichmuller l e - 1) ^ n * x = 0 := by
  intro l _ e he _ x hx
  rw [IsScalarTower.algebraMap_apply _ (BcrisPlus l ↥(PadicComplexInt l)),
    IsLocalization.map_eq_zero_iff (BcrisPlus.periods l ↥(PadicComplexInt l))] at hx
  obtain ⟨m, hm⟩ := hx
  obtain ⟨n, hn⟩ := Bridge.CrisLoc.PowMulEqZeroLemmas.main ⟨e, he⟩ m.2 x hm
  exact ⟨n, by rw [map_sub, map_one]; exact hn⟩

end
end PowMulEqZero
namespace CrisAway
section

open Ideal Reformulated.AutPerF
open scoped Nat

namespace Bridge.CrisLoc.CrisAwayLemmas

theorem binom_poly {p : ℕ} (hp : p.Prime) :
    ∃ h : Polynomial ℤ, (1 + Polynomial.X) ^ p =
      1 + Polynomial.X ^ p + (p : Polynomial ℤ) * Polynomial.X * (1 + Polynomial.X * h) := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (1 : Polynomial ℤ) Polynomial.X
  obtain ⟨k, hk⟩ := Polynomial.powAddExpansion (1 : Polynomial ℤ) Polynomial.X p
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 2 := ⟨p - 2, by have := hp.two_le; omega⟩
  have h1 : ((m + 2 : ℕ) : Polynomial ℤ) * (r - 1) = Polynomial.X * (k - Polynomial.X ^ m) := by
    apply mul_left_cancel₀ (Polynomial.X_ne_zero (R := ℤ))
    simp only [one_pow] at hr hk
    linear_combination hk - hr
  have h2 : Polynomial.X ∣ r - 1 := by
    rw [Polynomial.X_dvd_iff]
    have := congrArg (fun f => Polynomial.coeff f 0) h1
    simp only [Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, zero_mul,
      Polynomial.coeff_natCast_ite, if_true, mul_eq_zero] at this
    exact this.resolve_left (by simp; omega)
  obtain ⟨h, hh⟩ := h2
  refine ⟨h, ?_⟩
  rw [hr, eq_add_of_sub_eq hh]
  ring

theorem binom {A : Type*} [CommRing A] {p : ℕ} (hp : p.Prime) (x : A) :
    ∃ h : A, (1 + x) ^ p = 1 + x ^ p + (p : A) * x * (1 + x * h) := by
  obtain ⟨h, hh⟩ := binom_poly hp
  refine ⟨Polynomial.aeval x h, ?_⟩
  simpa using congrArg (Polynomial.aeval x) hh

universe u
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]

theorem mem_jac {z : Acris p R} {n : ℕ} (h : (p : Acris p R) ∣ z ^ n) :
    z ∈ (⊥ : Ideal (Acris p R)).jacobson := by
  have hj := IsAdicComplete.le_jacobson_bot (span {(p : Acris p R)})
  exact Ideal.isRadical_jacobson _ ⟨n, hj (mem_span_singleton.2 h)⟩

theorem fact_gamma (n : ℕ) (x : Ainf p R) (hx : Ainf.theta p R x = 0) :
    (n ! : Acris p R) * algebraMap _ _ (AcrisZero.gamma n x hx) =
      algebraMap (Ainf p R) (Acris p R) x ^ n := by
  have := congrArg (algebraMap (AcrisZero p R) (Acris p R)) (AcrisZero.factorial_mul_gamma n x hx)
  rwa [map_mul, map_natCast, map_pow, ← IsScalarTower.algebraMap_apply] at this

theorem p_dvd_pow (x : Ainf p R) (hx : Ainf.theta p R x = 0) :
    (p : Acris p R) ∣ algebraMap (Ainf p R) (Acris p R) x ^ p := by
  rw [← fact_gamma p x hx]
  exact Dvd.dvd.mul_right
    (Nat.cast_dvd_cast (Nat.dvd_factorial (Fact.out : p.Prime).pos le_rfl)) _

theorem p_dvd_gamma_pow (x : Ainf p R) (hx : Ainf.theta p R x = 0) :
    (p : Acris p R) ∣ algebraMap _ (Acris p R) (AcrisZero.gamma p x hx) ^ p := by
  have hp : p.Prime := Fact.out
  have h : AcrisZero.gamma p x hx ^ p =
      (p ! : AcrisZero p R) * ((Nat.uniformBell p p : ℕ) * AcrisZero.gamma (p * p) x hx) := by
    apply Subtype.ext
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, SubringClass.coe_natCast,
      AcrisZero.coe_gamma]
    have hu : IsUnit (p ! : AinfInv p R) := by
      rw [← map_natCast (algebraMap ℚ (AinfInv p R))]
      exact (IsUnit.mk0 _ (by exact_mod_cast Nat.factorial_ne_zero _)).map _
    apply (hu.pow p).mul_left_cancel
    have h1 := AinfInv.factorial_mul_gamma (p * p) (algebraMap (Ainf p R) (AinfInv p R) x)
    rw [← Nat.uniformBell_mul_eq p hp.ne_zero] at h1
    push_cast at h1
    rw [← mul_pow, AinfInv.factorial_mul_gamma, ← pow_mul, ← h1]
    ring
  rw [← map_pow, h, map_mul, map_natCast]
  exact Dvd.dvd.mul_right (Nat.cast_dvd_cast (Nat.dvd_factorial hp.pos le_rfl)) _

theorem theta_mu (η : tateModule p R) : Ainf.theta p R (Ainf.teich p η.1 - 1) = 0 := by
  rw [map_sub, map_one, Ainf.theta_teich, show PreTilt.untilt η.1 = 1 from η.2, sub_self]

variable [IsDomain R] [CharZero R]

theorem exists_congr (η : tateModule p R) : ∃ x c : Ainf p R, Ainf.theta p R x = 0 ∧
    (p : Ainf p R) ∣ (Ainf.teich p η.1 - 1) ^ (p - 1) - x ^ p * c := by
  have hp : p.Prime := Fact.out
  have e1 : ∀ y : Tilt p R, WittVector.constantCoeff (Ainf.teich p y) = y := fun y => by simp
  have e2 : η.1 - 1 = (tateRoot η - 1) ^ p := by rw [sub_pow_char, tateRoot_pow, one_pow]
  by_cases hη : IsPrimitive η
  · refine ⟨Ainf.omega η, 1, Ainf.theta_omega hη, ?_⟩
    rw [Ainf.p_dvd_iff]
    rw [← WittVector.constantCoeff_apply]
    have h := congrArg (WittVector.constantCoeff (p := p) (R := Tilt p R)) (Ainf.omega_mul η)
    rw [map_mul, map_sub, map_sub, map_one, e1, e1, e2] at h
    have hne : tateRoot η - 1 ≠ 0 := fun h0 => hη (by
      change PreTilt.untilt (tateRoot η) = 1
      rw [sub_eq_zero.1 h0, map_one])
    have h3 : WittVector.constantCoeff (Ainf.omega η) = (tateRoot η - 1) ^ (p - 1) := by
      apply mul_right_cancel₀ hne
      rw [h, ← pow_succ, Nat.sub_add_cancel hp.pos]
    rw [mul_one, map_sub, map_pow, map_pow, h3, map_sub, map_one, e1, e2, ← pow_mul, ← pow_mul,
      mul_comm, sub_self]
  · have h1 : PreTilt.untilt (tateRoot η) = 1 := not_not.1 hη
    refine ⟨Ainf.teich p (tateRoot η) - 1, ((Ainf.teich p (tateRoot η) - 1) ^ p) ^ (p - 2),
      by rw [map_sub, map_one, Ainf.theta_teich, h1, sub_self], ?_⟩
    rw [Ainf.p_dvd_iff]
    rw [← WittVector.constantCoeff_apply]
    rw [← pow_succ', show p - 2 + 1 = p - 1 by have := hp.two_le; omega]
    simp only [map_sub, map_pow, map_one, e1, e2, sub_self]

theorem exists_pow_eq_p_mul (η : tateModule p R) : ∃ y ∈ (⊥ : Ideal (Acris p R)).jacobson,
    algebraMap (Ainf p R) (Acris p R) (Ainf.teich p η.1 - 1) ^ (p - 1) = p * y := by
  have hp : p.Prime := Fact.out
  obtain ⟨x, c, hx, a, ha⟩ := exists_congr η
  have h0 : Ainf.theta p R a = 0 := by
    have := congrArg (Ainf.theta p R) ha
    rw [map_sub, map_pow, theta_mu, map_mul, map_pow, hx, zero_pow hp.ne_zero,
      zero_pow (by have := hp.two_le; omega), zero_mul, sub_zero, map_mul, map_natCast] at this
    exact (mul_eq_zero.1 this.symm).resolve_left (Nat.cast_ne_zero.2 hp.ne_zero)
  refine ⟨algebraMap _ _ a + algebraMap _ _ (AcrisZero.gamma p x hx) *
    (((p - 1)! : ℕ) * algebraMap _ _ c), add_mem (mem_jac (p_dvd_pow a h0))
      (Ideal.mul_mem_right _ _ (mem_jac (p_dvd_gamma_pow x hx))), ?_⟩
  have h1 := fact_gamma p x hx
  rw [← Nat.mul_factorial_pred hp.ne_zero, Nat.cast_mul] at h1
  rw [← map_pow, eq_add_of_sub_eq ha, map_add, map_mul, map_mul, map_pow, map_natCast, ← h1]
  ring

theorem assoc_pow (η : tateModule p R) :
    Associated ((p : Acris p R) * (algebraMap (Ainf p R) (Acris p R) (Ainf.teich p η.1) - 1))
      (algebraMap (Ainf p R) (Acris p R) (Ainf.teich p η.1) ^ p - 1) := by
  have hp : p.Prime := Fact.out
  obtain ⟨y, hy, e⟩ := exists_pow_eq_p_mul η
  have hm := mem_jac (p_dvd_pow _ (theta_mu η))
  rw [map_sub, map_one] at e hm
  generalize algebraMap (Ainf p R) (Acris p R) (Ainf.teich p η.1) = U at *
  obtain ⟨h, hh⟩ := binom hp (U - 1)
  have hu := Ideal.mem_jacobson_bot.1 (add_mem hy (Ideal.mul_mem_right h _ hm)) 1
  refine ⟨hu.unit, ?_⟩
  have e' : (U - 1) ^ p = (U - 1) * (p * y) := by
    rw [← e, ← pow_succ', Nat.sub_add_cancel hp.pos]
  rw [add_sub_cancel] at hh
  rw [IsUnit.unit_spec, hh, e']
  ring

omit [IsDomain R] [CharZero R] in
theorem exists_assoc_log (u : Ainf p R) (hu : Ainf.theta p R u = 1) :
    ∃ l : Acris p R, (p : Acris p R) ^ 2 * l = algebraMap (Ainf p R) _ u ^ p ^ 2 - 1 ∧
      Associated l (Acris.log u hu) := by
  have hp : p.Prime := Fact.out
  have h : ∀ n, ∃ l : Acris p R, (p : Acris p R) ^ n * l = algebraMap (Ainf p R) _ u ^ p ^ n - 1 ∧
      (p : Acris p R) ^ n ∣ Acris.log u hu - l := fun n => by
    obtain ⟨l, h1, h2⟩ := Acris.exists_quot u hu n
    refine ⟨algebraMap _ _ l, ?_, ?_⟩
    · have := congrArg (algebraMap (AcrisZero p R) (Acris p R)) h1
      rwa [map_mul, map_pow, map_natCast, map_sub, map_pow, map_one,
        ← IsScalarTower.algebraMap_apply] at this
    · rw [← Acris.eval_eq_zero_iff, map_sub, h2, Acris.eval_algebraMap, sub_self]
  choose l hl ht using h
  generalize Acris.log u hu = t at *
  generalize algebraMap (Ainf p R) (Acris p R) u = U at *
  have step : ∀ n, ∃ c, l (n + 3) = l (n + 2) * (1 + p ^ (n + 1) * c) := fun n => by
    obtain ⟨h, hh⟩ := binom hp ((p : Acris p R) ^ (n + 2) * l (n + 2))
    have e' : ((p : Acris p R) ^ (n + 2) * l (n + 2)) ^ p =
        ((p : Acris p R) ^ (n + 2) * l (n + 2)) ^ 2 * (p ^ (n + 2) * l (n + 2)) ^ (p - 2) := by
      rw [← pow_add, Nat.add_sub_cancel' hp.two_le]
    refine ⟨l (n + 2) * (p ^ (n + 2) * l (n + 2)) ^ (p - 2) + p * l (n + 2) * h,
      Acris.p_pow_mul_cancel (n + 3) ?_⟩
    have e2 : U ^ p ^ (n + 3) = (1 + (p : Acris p R) ^ (n + 2) * l (n + 2)) ^ p := by
      rw [hl, add_sub_cancel, ← pow_mul, ← pow_succ]
    rw [hl (n + 3), e2, hh, e']
    ring
  have hd : ∀ n, l 2 ∣ l (n + 2) := fun n => by
    induction n with
    | zero => exact dvd_rfl
    | succ n ih =>
      obtain ⟨c, hc⟩ := step n
      rw [show n + 1 + 2 = n + 3 from rfl, hc]
      exact ih.mul_right _
  refine ⟨l 2, hl 2, ?_⟩
  obtain ⟨z, hz⟩ := ht 2
  have hm : (p : Acris p R) * z ∈ span {l 2} := by
    refine mem_span_of_approx (p : Acris p R) (l 2)
      {x | ∃ n, (p : Acris p R) ^ (n + 1) * x = t - l (n + 2)} ?_ ⟨0, by rw [hz]; ring⟩
    rintro x ⟨n, hx⟩
    obtain ⟨c, hc⟩ := step n
    obtain ⟨W, hW⟩ := hd n
    obtain ⟨z, hz⟩ := ht (n + 3)
    refine ⟨W * c, p * z, ⟨n + 1, ?_⟩, Acris.p_pow_mul_cancel (n + 1) ?_⟩
    · rw [show n + 1 + 2 = n + 3 from rfl, hz]; ring
    · rw [hx]
      linear_combination hz + hc + (p : Acris p R) ^ (n + 1) * c * hW
  obtain ⟨a, ha⟩ := mem_span_singleton.1 hm
  have hu := Ideal.mem_jacobson_bot.1 (mem_jac (p := p) (R := R) (z := p) (n := 1) (by simp)) a
  refine ⟨hu.unit, ?_⟩
  rw [IsUnit.unit_spec]
  linear_combination -hz - (p : Acris p R) * ha

theorem assoc_log (η : tateModule p R) :
    Associated (algebraMap (Ainf p R) (Acris p R) (Ainf.teich p η.1 - 1)) (Acris.logTeich η) := by
  obtain ⟨l, hl, hl'⟩ := exists_assoc_log (Ainf.teich p η.1)
    (by rw [Ainf.theta_teich]; exact η.2)
  refine Associated.trans ?_ hl'
  obtain ⟨v, hv⟩ := assoc_pow η
  obtain ⟨w, hw⟩ := assoc_pow (η ^ p)
  rw [SubmonoidClass.coe_pow, map_pow, map_pow, ← pow_mul, ← sq, ← hl, ← hv] at hw
  refine ⟨v * w, Acris.p_pow_mul_cancel 2 ?_⟩
  rw [← hw, map_sub, map_one]
  push_cast
  ring

omit [CharZero R] in
theorem isUnit_log_iff {B : Type*} [CommRing B] (g : Acris p R →+* B) (hp : IsUnit (p : B))
    {ε η : tateModule p R} (hε : IsPrimitive ε) (hη : η ≠ 1) :
    IsUnit (g (Acris.logTeich η)) ↔ IsUnit (g (Acris.logTeich ε)) := by
  obtain ⟨a, rfl⟩ := hε.padicPow_surjective η
  have ha : a ≠ 0 := fun h => hη (by rw [h, tateModule.padicPow_zero])
  have hu : IsUnit (g (algebraMap ℤ_[p] (Acris p R) a)) := by
    rw [PadicInt.unitCoeff_spec ha]
    simp only [map_mul, map_pow, map_natCast]
    exact (((Units.isUnit _).map _).map g).mul (hp.pow _)
  rw [Acris.logTeich_padicPow, map_mul, IsUnit.mul_iff]
  exact and_iff_right hu

theorem away [ValuationRing R] [IsAlgClosed (FractionRing R)] (η : tateModule p R) (hη : η ≠ 1) :
    IsLocalization.Away (algebraMap (Ainf p R) (Acris p R) (Ainf.teich p η.1 - 1))
      (Bcris p R) := by
  have h1 := assoc_log η
  have h2 := p_dvd_pow _ (theta_mu η)
  generalize algebraMap (Ainf p R) (Acris p R) (Ainf.teich p η.1 - 1) = μ at *
  have hμ : IsUnit (algebraMap (Acris p R) (Localization.Away μ) μ) :=
    IsLocalization.Away.algebraMap_isUnit μ
  have hp : IsUnit (p : Localization.Away μ) := by
    have := map_dvd (algebraMap (Acris p R) (Localization.Away μ)) h2
    rw [map_natCast, map_pow] at this
    exact isUnit_of_dvd_unit this (hμ.pow _)
  have hB : IsUnit (algebraMap (Acris p R) (Bcris p R) μ) :=
    isUnit_of_dvd_unit (map_dvd _ h1.dvd)
      ((isUnit_log_iff _ Bcris.isUnit_p (isPrimitive_eps p R) hη).2
        (Bcris.isUnit_logTeich (isPrimitive_eps p R)))
  let f : Bcris p R →+* Localization.Away μ :=
    Bcris.lift (BcrisPlus.lift (algebraMap _ _) hp) fun ε hε => by
      rw [BcrisPlus.lift_algebraMap]
      exact (isUnit_log_iff _ hp hε hη).1 (isUnit_of_dvd_unit (map_dvd _ h1.symm.dvd) hμ)
  have hf : ∀ x : Acris p R, f (algebraMap _ _ x) = algebraMap _ _ x := fun x => by
    rw [IsScalarTower.algebraMap_apply (Acris p R) (BcrisPlus p R) (Bcris p R)]
    exact (Bcris.lift_algebraMap _ _ _).trans (BcrisPlus.lift_algebraMap _ _ _)
  let g : Localization.Away μ →+* Bcris p R := IsLocalization.Away.lift μ hB
  have hg : ∀ x : Acris p R, g (algebraMap _ _ x) = algebraMap _ _ x := fun x =>
    IsLocalization.Away.lift_eq _ _ x
  have hfg : f.comp g = RingHom.id _ :=
    IsLocalization.ringHom_ext (Submonoid.powers μ) (RingHom.ext fun x => by
      simp only [RingHom.comp_apply, RingHom.id_apply, hg, hf])
  have hgf : g.comp f = RingHom.id _ := by
    refine Bcris.hom_ext fun y => ?_
    refine RingHom.congr_fun (BcrisPlus.hom_ext
      (f := (g.comp f).comp (algebraMap (BcrisPlus p R) (Bcris p R)))
      (g := algebraMap (BcrisPlus p R) (Bcris p R)) fun x => ?_) y
    rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply, RingHom.comp_apply, hf, hg]
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers μ)
    (AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom g f hgf hfg) hg)

end Bridge.CrisLoc.CrisAwayLemmas

theorem Bridge.CrisLoc.bcris_away : ∀ (l : ℕ) [Fact l.Prime] (e : (Reformulated.AutPerF.Tilt l ↥(PadicComplexInt l))) (he : e.untilt = 1) (hne : e ≠ 1), IsLocalization.Away (algebraMap ((Reformulated.AutPerF.Ainf l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.Acris l ↥(PadicComplexInt l))) (WittVector.teichmuller l e - 1)) ((Reformulated.AutPerF.Bcris l ↥(PadicComplexInt l))) := by
  intro l _ e he hne
  exact Bridge.CrisLoc.CrisAwayLemmas.away (p := l) (R := PadicComplexInt l) ⟨e, he⟩
    fun h => hne (congrArg Subtype.val h)

end
end CrisAway
namespace MulPowEq
section

open Ideal Reformulated.AutPerF
open scoped Nat

namespace Bridge.CrisLoc.MulPowEqLemmas

section General

variable {A : Type*} [CommRing A]

theorem mem_jac_of_pow {x : A} {n : ℕ} (h : x ^ n ∈ jacobson (⊥ : Ideal A)) :
    x ∈ jacobson (⊥ : Ideal A) := by
  rw [Ideal.jacobson, Ideal.mem_sInf] at h ⊢
  intro J hJ
  exact hJ.2.isPrime.mem_of_pow_mem n (h hJ)

theorem isUnit_of_sub_one_mem {x : A} (h : x - 1 ∈ jacobson (⊥ : Ideal A)) : IsUnit x := by
  simpa using Ideal.mem_jacobson_bot.1 h 1

theorem exists_limit (a : A) [IsAdicComplete (span {a}) A] (d : ℕ → A)
    (h : ∀ n, a ^ n ∣ d (n + 1) - d n) : ∃ L, ∀ n, a ^ n ∣ d n - L := by
  have key : ∀ (n : ℕ) (x : A), x ∈ (span {a} ^ n • ⊤ : Submodule A A) ↔ a ^ n ∣ x := by
    intro n x
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := span {a}) d (fun {m n} hmn => by
    rw [SModEq.sub_mem, key]
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have := dvd_sub ih ((pow_dvd_pow a hmn).trans (h n))
      rwa [sub_sub, add_sub_cancel] at this)
  exact ⟨L, fun n => (key n _).1 (SModEq.sub_mem.1 (hL n))⟩

theorem geom_sum_eq (n : ℕ) (v : A) : ∃ g, ∑ i ∈ Finset.range n, v ^ i = n + (v - 1) * g := by
  have : v - 1 ∣ ∑ i ∈ Finset.range n, (v ^ i - 1) :=
    Finset.dvd_sum fun i _ => by simpa using sub_dvd_pow_sub_pow v 1 i
  obtain ⟨g, hg⟩ := this
  refine ⟨g, ?_⟩
  rw [← hg, Finset.sum_sub_distrib]
  simp

open Polynomial in
theorem geom_sum_frob (p : ℕ) [Fact p.Prime] (v : A) : ∃ g,
    ∑ i ∈ Finset.range p, (v ^ p) ^ i =
      (∑ i ∈ Finset.range p, v ^ i) ^ p + p * (1 - p ^ (p - 1) + (v - 1) * g) := by
  have hp : p.Prime := Fact.out
  set F : ℤ[X] := ∑ i ∈ Finset.range p, X ^ i with hF
  have h1 : C (p : ℤ) ∣ expand ℤ p F - F ^ p := by
    rw [C_dvd_iff_dvd_coeff]
    intro i
    have : (expand ℤ p F - F ^ p).map (Int.castRingHom (ZMod p)) = 0 := by
      rw [Polynomial.map_sub, map_expand, ZMod.expand_card, Polynomial.map_pow, sub_self]
    have h2 := congrArg (fun f => coeff f i) this
    simp only [coeff_map, coeff_zero, eq_intCast] at h2
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h2
  obtain ⟨D, hD⟩ := h1
  have h3 : D.eval 1 = 1 - p ^ (p - 1) := by
    have := congrArg (eval 1) hD
    simp [hF, eval_finset_sum] at this
    apply mul_left_cancel₀ (show (p : ℤ) ≠ 0 by exact_mod_cast hp.ne_zero)
    rw [← this, mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel hp.one_le]
  obtain ⟨G, hG⟩ := X_sub_C_dvd_sub_C_eval (a := 1) (p := D)
  refine ⟨aeval v G, ?_⟩
  have h4 := congrArg (aeval v) hD
  have h5 := congrArg (aeval v) hG
  rw [h3] at h5
  simp [hF] at h4 h5
  linear_combination h4 + p * h5

end General

variable {p : ℕ} [Fact p.Prime]
variable {R : Type*} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]

theorem p_mem_jac : (p : Acris p R) ∈ jacobson (⊥ : Ideal (Acris p R)) :=
  IsAdicComplete.le_jacobson_bot (span {(p : Acris p R)}) (mem_span_singleton_self _)

theorem factorial_dvd (n : ℕ) (x : Ainf p R) (hx : Ainf.theta p R x = 0) :
    (n ! : Acris p R) ∣ algebraMap (Ainf p R) (Acris p R) x ^ n := by
  have := congrArg (algebraMap (AcrisZero p R) (Acris p R)) (AcrisZero.factorial_mul_gamma n x hx)
  rw [map_mul, map_pow, map_natCast, ← IsScalarTower.algebraMap_apply] at this
  exact ⟨_, this.symm⟩

theorem p_dvd_pow (x : Ainf p R) (hx : Ainf.theta p R x = 0) :
    (p : Acris p R) ∣ algebraMap (Ainf p R) (Acris p R) x ^ p :=
  (Nat.cast_dvd_cast (Nat.dvd_factorial (Fact.out : p.Prime).pos le_rfl)).trans
    (factorial_dvd p x hx)

theorem mem_jac_of_theta (x : Ainf p R) (hx : Ainf.theta p R x = 0) :
    algebraMap (Ainf p R) (Acris p R) x ∈ jacobson (⊥ : Ideal (Acris p R)) := by
  obtain ⟨c, hc⟩ := p_dvd_pow x hx
  exact mem_jac_of_pow (n := p) (by rw [hc]; exact mul_mem_right _ _ p_mem_jac)

theorem exists_pow_eq_mul (x : Ainf p R) (hx : Ainf.theta p R x = 0) :
    ∃ c ∈ jacobson (⊥ : Ideal (Acris p R)), algebraMap (Ainf p R) (Acris p R) x ^ p = p * c := by
  have hp : p.Prime := Fact.out
  obtain ⟨c, hc⟩ := p_dvd_pow x hx
  refine ⟨c, mem_jac_of_pow (n := p) ?_, hc⟩
  have h1 : p ^ (p + 1) ∣ (p * p)! := by
    rw [padicValNat_dvd_iff_le (Nat.factorial_ne_zero _), padicValNat_factorial_mul]
    have : 1 ≤ padicValNat p p ! := by
      rw [← padicValNat_dvd_iff_le (Nat.factorial_ne_zero _), pow_one]
      exact Nat.dvd_factorial hp.pos le_rfl
    omega
  obtain ⟨d, hd⟩ := (Nat.cast_dvd_cast (α := Acris p R) h1).trans (factorial_dvd (p * p) x hx)
  rw [pow_mul, hc, mul_pow, Nat.cast_pow, pow_succ, mul_assoc] at hd
  rw [Acris.p_pow_mul_cancel p hd]
  exact mul_mem_right _ _ p_mem_jac

theorem theta_teich_sub_one (η : tateModule p R) : Ainf.theta p R (Ainf.teich p η.1 - 1) = 0 := by
  rw [map_sub, map_one, Ainf.theta_teich, tateModule.untilt_eq_one, sub_self]

theorem exists_unit [IsDomain R] {ε : tateModule p R} (hε : IsPrimitive ε) :
    ∃ w : Acris p R, IsUnit w ∧
      ∑ i ∈ Finset.range p, algebraMap (Ainf p R) (Acris p R) (Ainf.teich p ε.1) ^ i = p * w := by
  have hp : p.Prime := Fact.out
  set v := algebraMap (Ainf p R) (Acris p R) (Ainf.teich p (tateRoot ε)) with hv
  have h1 : algebraMap (Ainf p R) (Acris p R) (Ainf.teich p ε.1) = v ^ p := by
    rw [hv, ← map_pow, ← map_pow, tateRoot_pow]
  obtain ⟨g, hg⟩ := geom_sum_frob p v
  obtain ⟨c, hc, hc'⟩ := exists_pow_eq_mul _ (Ainf.theta_omega hε)
  have h2 : algebraMap (Ainf p R) (Acris p R) (Ainf.omega ε) = ∑ i ∈ Finset.range p, v ^ i := by
    simp [Ainf.omega, hv]
  have h3 : v - 1 ∈ jacobson (⊥ : Ideal (Acris p R)) := by
    have h4 := mem_jac_of_theta _ (theta_teich_sub_one ε)
    rw [map_sub, map_one, h1] at h4
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (v - 1) 1
    refine mem_jac_of_pow (n := p) ?_
    have : (v - 1) ^ p = (v ^ p - 1) - p * ((v - 1) * r) := by
      rw [sub_add_cancel, one_pow] at hr
      linear_combination -hr
    rw [this]
    exact sub_mem h4 (mul_mem_right _ _ p_mem_jac)
  refine ⟨c + (1 - p ^ (p - 1) + (v - 1) * g), isUnit_of_sub_one_mem ?_, ?_⟩
  · have : c + (1 - p ^ (p - 1) + (v - 1) * g) - 1 = c - p ^ (p - 1) + (v - 1) * g := by ring
    rw [this]
    refine add_mem (sub_mem hc ?_) (mul_mem_right _ _ h3)
    exact Ideal.pow_mem_of_mem _ p_mem_jac _ (by have := hp.two_le; omega)
  · rw [h1, hg, ← h2, hc']
    ring

theorem exists_log_eq (u : Ainf p R) (hu : Ainf.theta p R u = 1) :
    ∃ l d : Acris p R, IsUnit d ∧
      (p : Acris p R) ^ 2 * l = algebraMap (Ainf p R) (Acris p R) u ^ p ^ 2 - 1 ∧
      Acris.log u hu = l * d := by
  set U := algebraMap (Ainf p R) (Acris p R) u with hU
  have h0 : ∀ n, ∃ l : Acris p R, (p : Acris p R) ^ n * l = U ^ p ^ n - 1 ∧
      (p : Acris p R) ^ n ∣ Acris.log u hu - l := by
    intro n
    obtain ⟨l, hl, hl'⟩ := Acris.exists_quot u hu n
    refine ⟨algebraMap _ _ l, ?_, ?_⟩
    · have := congrArg (algebraMap (AcrisZero p R) (Acris p R)) hl
      rwa [map_mul, map_pow, map_natCast, map_sub, map_one, map_pow,
        ← IsScalarTower.algebraMap_apply] at this
    · rw [← Acris.eval_eq_zero_iff, map_sub, hl', Acris.eval_algebraMap, sub_self]
  choose l hl hl' using h0
  have h1 : ∀ n, ∃ c, l (n + 3) = l (n + 2) * (1 + (p : Acris p R) ^ (n + 1) * c) := by
    intro n
    obtain ⟨g, hg⟩ := geom_sum_eq p (U ^ p ^ (n + 2))
    refine ⟨l (n + 2) * g, Acris.p_pow_mul_cancel (n + 3) ?_⟩
    have h2 := mul_geom_sum (U ^ p ^ (n + 2)) p
    rw [hg, ← pow_mul, ← pow_succ, ← hl, ← hl] at h2
    rw [← h2]
    ring
  choose c hc using h1
  let d : ℕ → Acris p R := fun n => ∏ i ∈ Finset.range n, (1 + (p : Acris p R) ^ (i + 1) * c i)
  have hd : ∀ n, d (n + 1) = d n * (1 + (p : Acris p R) ^ (n + 1) * c n) := fun n =>
    Finset.prod_range_succ _ _
  have hld : ∀ n, l (n + 2) = l 2 * d n := by
    intro n
    induction n with
    | zero => simp [d]
    | succ n ih => rw [hd, ← mul_assoc, ← ih]; exact hc n
  obtain ⟨D, hD⟩ := exists_limit (p : Acris p R) d fun n =>
    ⟨d n * p * c n, by rw [hd]; ring⟩
  refine ⟨l 2, D, isUnit_of_sub_one_mem ?_, hl 2, ?_⟩
  · obtain ⟨z, hz⟩ := hD 1
    have : D - 1 = p * (c 0 - z) := by
      have h3 : d 1 = 1 + p * c 0 := by simp [d]
      rw [h3] at hz
      linear_combination -hz
    rw [this]
    exact mul_mem_right _ _ p_mem_jac
  · rw [← sub_eq_zero]
    refine Acris.eq_zero_of_forall_dvd fun n => ?_
    have : Acris.log u hu - l 2 * D = (Acris.log u hu - l (n + 2)) + l 2 * (d n - D) := by
      rw [hld n]; ring
    rw [this]
    exact dvd_add ((pow_dvd_pow _ (by omega)).trans (hl' (n + 2))) ((hD n).mul_left _)

theorem logTeich_dvd [IsDomain R] {ε : tateModule p R} (hε : IsPrimitive ε) :
    Acris.logTeich ε ∣ algebraMap (Ainf p R) (Acris p R) (Ainf.teich p ε.1) - 1 := by
  obtain ⟨w, hw, h⟩ := exists_unit hε
  obtain ⟨l, d, hd, hl, hlog⟩ := exists_log_eq (Ainf.teich p ε.1)
    (by rw [Ainf.theta_teich]; exact ε.2)
  have h' := congrArg (Acris.frob p R) h
  simp only [map_sum, map_pow, map_mul, map_natCast, Acris.frob_algebraMap, Ainf.frob_teich] at h'
  set U := algebraMap (Ainf p R) (Acris p R) (Ainf.teich p ε.1) with hU
  have h1 := mul_geom_sum U p
  have h2 := mul_geom_sum (U ^ p) p
  rw [h', ← h1, h, ← pow_mul, ← sq, ← hl] at h2
  have h3 : l = (U - 1) * (w * Acris.frob p R w) :=
    Acris.p_pow_mul_cancel 2 (by rw [← h2]; ring)
  rw [Acris.logTeich, hlog, h3, mul_assoc]
  exact ((hw.mul (hw.map _)).mul hd).mul_right_dvd.2 dvd_rfl

theorem log_linear (η : tateModule p R) (a : ℤ_[p]) :
    Acris.logTeich (tateModule.padicPow η a) =
      algebraMap ℤ_[p] (Acris p R) a * Acris.logTeich η := by
  refine sub_eq_zero.1 (Acris.eq_zero_of_forall_dvd fun k => ?_)
  have h : (p : ℤ_[p]) ^ k ∣ a - (a.appr k : ℕ) := mem_span_singleton.1 (PadicInt.appr_spec k a)
  obtain ⟨ζ, hζ⟩ := tateModule.exists_padicPow_eq η h
  have h2 := map_dvd (algebraMap ℤ_[p] (Acris p R)) h
  rw [map_pow, map_natCast, map_sub, map_natCast] at h2
  have h3 := dvd_sub (dvd_mul_right ((p : Acris p R) ^ k) (Acris.logTeich ζ))
    (h2.mul_right (Acris.logTeich η))
  convert h3 using 1
  simp only [hζ, Acris.logTeich_mul, Acris.logTeich_pow, Nat.cast_pow]
  ring

theorem logTeich_dvd_of_ne_one [IsDomain R] {ε : tateModule p R} (hε : IsPrimitive ε)
    (η : tateModule p R) (hη : η ≠ 1) :
    Acris.logTeich ε ∣ algebraMap (Ainf p R) (Acris p R) (Ainf.teich p η.1 - 1) := by
  obtain ⟨a, rfl⟩ := hε.padicPow_surjective η
  have ha : a ≠ 0 := by rintro rfl; exact hη (tateModule.padicPow_zero ε)
  have h1 := logTeich_dvd ((hε.padicPow_iff (PadicInt.unitCoeff ha)).2 (Units.isUnit _))
  rw [log_linear] at h1
  refine ((dvd_mul_left _ _).trans h1).trans ?_
  conv_rhs => rw [PadicInt.unitCoeff_spec ha, tateModule.padicPow_mul, ← Nat.cast_pow,
    tateModule.padicPow_natCast, SubmonoidClass.coe_pow, map_pow, map_sub, map_one, map_pow]
  exact sub_one_dvd_pow_sub_one _ _

theorem main [IsDomain R] (η : tateModule p R) (hη : η ≠ 1) (b : Bcris p R) :
    ∃ (n : ℕ) (x : Acris p R), b * algebraMap (Acris p R) (Bcris p R)
      (algebraMap (Ainf p R) (Acris p R) (Ainf.teich p η.1 - 1)) ^ n =
      algebraMap (Acris p R) (Bcris p R) x := by
  set μ := algebraMap (Ainf p R) (Acris p R) (Ainf.teich p η.1 - 1) with hμ
  obtain ⟨⟨x, s, hs⟩, hb⟩ := IsLocalization.surj (BcrisPlus.periods p R) b
  have h1 : ∃ (n : ℕ) (y : Acris p R), algebraMap (Acris p R) (BcrisPlus p R) μ ^ n =
      s * algebraMap (Acris p R) (BcrisPlus p R) y := by
    clear hb
    induction hs using Submonoid.closure_induction with
    | mem s hs =>
      obtain ⟨ε, hε, rfl⟩ := hs
      obtain ⟨y, hy⟩ := logTeich_dvd_of_ne_one hε η hη
      exact ⟨1, y, by rw [pow_one, ← map_mul, ← hy]⟩
    | one => exact ⟨0, 1, by simp⟩
    | mul s t _ _ hs ht =>
      obtain ⟨m, y, hy⟩ := hs
      obtain ⟨n, z, hz⟩ := ht
      exact ⟨m + n, y * z, by rw [pow_add, hy, hz, map_mul]; ring⟩
  obtain ⟨n, y, hy⟩ := h1
  obtain ⟨k, z, hz⟩ := IsLocalization.Away.surj (S := BcrisPlus p R) (p : Acris p R) x
  obtain ⟨g, hg⟩ := p_dvd_pow _ (theta_teich_sub_one η)
  rw [← hμ] at hg
  refine ⟨n + p * k, z * y * g ^ k, ?_⟩
  have e1 := congrArg (algebraMap (BcrisPlus p R) (Bcris p R)) hy
  have e2 := congrArg (algebraMap (BcrisPlus p R) (Bcris p R)) hz
  have e3 := congrArg (algebraMap (Acris p R) (Bcris p R)) hg
  simp only [map_mul, map_pow, ← IsScalarTower.algebraMap_apply] at e1 e2 e3 hb ⊢
  rw [pow_add, pow_mul, e1, e3, ← e2, ← hb]
  ring

end Bridge.CrisLoc.MulPowEqLemmas

theorem Bridge.CrisLoc.exists_mul_pow_eq : ∀ (l : ℕ) [Fact l.Prime] (e : (Reformulated.AutPerF.Tilt l ↥(PadicComplexInt l))) (he : e.untilt = 1) (hne : e ≠ 1) (b : (Reformulated.AutPerF.Bcris l ↥(PadicComplexInt l))), ∃ (n : ℕ) (x : (Reformulated.AutPerF.Acris l ↥(PadicComplexInt l))), b * algebraMap ((Reformulated.AutPerF.Acris l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.Bcris l ↥(PadicComplexInt l))) (algebraMap ((Reformulated.AutPerF.Ainf l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.Acris l ↥(PadicComplexInt l))) (WittVector.teichmuller l e - 1)) ^ n = algebraMap ((Reformulated.AutPerF.Acris l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.Bcris l ↥(PadicComplexInt l))) x := by
  intro l _ e he hne b
  exact Bridge.CrisLoc.MulPowEqLemmas.main ⟨e, he⟩ (fun h => hne (congrArg Subtype.val h)) b

end
end MulPowEq
namespace UnitOfRootAlt
section

noncomputable section

open Ideal Reformulated.AutPerF
open scoped Nat

namespace Bridge.CrisLoc.unitOfRootSeries

theorem bound {p v n k : ℕ} (hp : 2 ≤ p) (hv : p ^ v ≤ k + 1) (hk : p * (2 * n + 2) ≤ k) :
    p * (v + n) ≤ k := by
  rcases le_or_gt v (n + 2) with h | h
  · exact (Nat.mul_le_mul_left p (by omega)).trans hk
  · obtain ⟨w, rfl⟩ : ∃ w, v = w + 2 := ⟨v - 2, by omega⟩
    have h1 : w + 1 ≤ p ^ w := Nat.lt_pow_self (by omega)
    have h2 : w + 2 + n + 1 ≤ p ^ w * p :=
      (by omega : w + 2 + n + 1 ≤ (w + 1) * 2).trans (Nat.mul_le_mul h1 hp)
    have h3 : p * (w + 2 + n + 1) ≤ p ^ (w + 2) := by
      rw [pow_succ, pow_succ, mul_comm]
      exact Nat.mul_le_mul_right p h2
    have h4 : p * (w + 2 + n + 1) = p * (w + 2 + n) + p := by ring
    omega

theorem term_dvd {p : ℕ} [Fact p.Prime] {A : Type*} [CommRing A] (f : ℤ_[p] →+* A)
    (hc : ∀ (m : ℕ) (y z : A), (p : A) ^ m * y = (p : A) ^ m * z → y = z)
    {x : A} (hx : (p : A) ∣ x ^ p) {k n : ℕ} (hk : p * (2 * n + 2) ≤ k) {a : A}
    (ha : ((k + 1 : ℕ) : A) * a = x ^ (k + 1)) : x * (p : A) ^ n ∣ a := by
  have hp : p.Prime := Fact.out
  obtain ⟨v, m, hm, h⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.succ_ne_zero k) p hp.ne_one
  have hv : p ^ v ≤ k + 1 := Nat.le_of_dvd k.succ_pos ⟨m, h⟩
  have hu : IsUnit (m : A) := by
    have : IsUnit (m : ℤ_[p]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
      exact hp.coprime_iff_not_dvd.2 hm
    simpa using this.map f
  have hd : (p : A) ^ (v + n) ∣ x ^ k := by
    refine (pow_dvd_pow_of_dvd hx (v + n)).trans ?_
    rw [← pow_mul]
    exact pow_dvd_pow x (bound hp.two_le hv hk)
  obtain ⟨c, hc'⟩ := hd
  rw [← hu.dvd_mul_left]
  refine ⟨c, hc v _ _ ?_⟩
  have h' : ((k + 1 : ℕ) : A) = (p : A) ^ v * m := by
    rw [show k + 1 = p ^ v * m from h, Nat.cast_mul, Nat.cast_pow]
  rw [← mul_assoc, ← h', ha, pow_succ, hc']
  ring

variable {p : ℕ} [Fact p.Prime]
variable {R : Type} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]

def term (u : Ainf p R) (hu : Ainf.theta p R u = 1) (k : ℕ) : Acris p R :=
  algebraMap (AcrisZero p R) (Acris p R)
    ((k ! : AcrisZero p R) * AcrisZero.gamma (k + 1) (u - 1) (by simp [hu]))

theorem succ_mul_term (u : Ainf p R) (hu : Ainf.theta p R u = 1) (k : ℕ) :
    ((k + 1 : ℕ) : Acris p R) * term u hu k =
      algebraMap (Ainf p R) (Acris p R) (u - 1) ^ (k + 1) := by
  rw [term, ← map_natCast (algebraMap (AcrisZero p R) (Acris p R)), ← map_mul, ← mul_assoc,
    ← Nat.cast_mul, ← Nat.factorial_succ, AcrisZero.factorial_mul_gamma, map_pow,
    ← IsScalarTower.algebraMap_apply]

theorem partial_eq (u : Ainf p R) (hu : Ainf.theta p R u = 1) (N : ℕ) :
    algebraMap (AcrisZero p R) (Acris p R) (Acris.logPartial N u hu) =
      ∑ k ∈ Finset.range N, (-1) ^ k * term u hu k := by
  rw [Acris.logPartial, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [term, mul_assoc, map_mul, map_pow, map_neg, map_one]

theorem p_dvd_pow (u : Ainf p R) (hu : Ainf.theta p R u = 1) :
    (p : Acris p R) ∣ algebraMap (Ainf p R) (Acris p R) (u - 1) ^ p := by
  have h := congrArg (algebraMap (AcrisZero p R) (Acris p R))
    (AcrisZero.factorial_mul_gamma p (u - 1) (by simp [hu]))
  rw [map_mul, map_natCast, map_pow, ← IsScalarTower.algebraMap_apply] at h
  rw [← h]
  exact (Nat.cast_dvd_cast (Nat.dvd_factorial (Fact.out : p.Prime).pos le_rfl)).mul_right _

theorem dvd_tail (u : Ainf p R) (hu : Ainf.theta p R u = 1) :
    ∃ N, algebraMap (Ainf p R) (Acris p R) (u - 1) ∣
      Acris.log u hu - ∑ k ∈ Finset.range N, (-1) ^ k * term u hu k := by
  have hp : p.Prime := Fact.out
  let M : ℕ → ℕ := fun n => p ^ n + p * (2 * n + 2)
  have hM : ∀ n, M n ≤ M (n + 1) := fun n =>
    Nat.add_le_add (Nat.pow_le_pow_right hp.pos n.le_succ) (Nat.mul_le_mul_left p (by omega))
  let s : ℕ → Acris p R := fun n => ∑ k ∈ Finset.range (M n), (-1) ^ k * term u hu k
  have h1 : ∀ n, (p : Acris p R) ^ n ∣ Acris.log u hu - s n := fun n => by
    rw [← Acris.eval_eq_zero_iff, map_sub, Acris.eval_log u hu (Nat.le_add_right _ _ : p ^ n ≤ M n)]
    simp only [s]
    rw [← partial_eq, Acris.eval_algebraMap, sub_self]
  have h2 : ∀ n, algebraMap (Ainf p R) (Acris p R) (u - 1) * (p : Acris p R) ^ n ∣
      s (n + 1) - s n := fun n => by
    simp only [s]
    rw [← Finset.sum_Ico_eq_sub _ (hM n)]
    refine Finset.dvd_sum fun k hk => Dvd.dvd.mul_left ?_ _
    exact term_dvd (algebraMap ℤ_[p] (Acris p R)) (fun m _ _ h => Acris.p_pow_mul_cancel m h)
      (p_dvd_pow u hu) ((Nat.le_add_left _ _).trans (Finset.mem_Ico.1 hk).1)
      (succ_mul_term u hu k)
  refine ⟨M 0, mem_span_singleton.1 (mem_span_of_approx (p : Acris p R) _
    {y | ∃ n, (p : Acris p R) ^ n * y = Acris.log u hu - s n} ?_ ⟨0, by simp [s]⟩)⟩
  rintro y ⟨n, hy⟩
  obtain ⟨z, hz⟩ := h1 (n + 1)
  obtain ⟨b, hb⟩ := h2 n
  refine ⟨b, z, ⟨n + 1, hz.symm⟩, Acris.p_pow_mul_cancel n ?_⟩
  rw [pow_succ] at hz
  linear_combination hy + hz + hb

theorem dvd_log (u : Ainf p R) (hu : Ainf.theta p R u = 1) :
    algebraMap (Acris p R) (Bcris p R) (algebraMap (Ainf p R) (Acris p R) (u - 1)) ∣
      algebraMap (Acris p R) (Bcris p R) (Acris.log u hu) := by
  obtain ⟨N, hN⟩ := dvd_tail u hu
  have h := map_dvd (algebraMap (Acris p R) (Bcris p R)) hN
  rw [map_sub _ (Acris.log u hu)] at h
  rw [← sub_add_cancel (algebraMap (Acris p R) (Bcris p R) (Acris.log u hu))
    (algebraMap (Acris p R) (Bcris p R) (∑ k ∈ Finset.range N, (-1) ^ k * term u hu k))]
  refine dvd_add h ?_
  rw [map_sum]
  refine Finset.dvd_sum fun k _ => ?_
  rw [map_mul]
  refine Dvd.dvd.mul_left ?_ _
  have hk : IsUnit ((k + 1 : ℕ) : Bcris p R) := by
    rw [← map_natCast (algebraMap ℚ_[p] (Bcris p R))]
    exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 k.succ_ne_zero)).map _
  rw [← hk.dvd_mul_left, ← map_natCast (algebraMap (Acris p R) (Bcris p R)), ← map_mul,
    succ_mul_term, map_pow]
  exact dvd_pow_self _ k.succ_ne_zero

theorem isUnit_logTeich [IsDomain R] [ValuationRing R] [IsAlgClosed (FractionRing R)] [CharZero R]
    (η : tateModule p R) (h : η ≠ 1) : IsUnit (Bcris.logTeich η) := by
  obtain ⟨a, rfl⟩ := (isPrimitive_eps p R).padicPow_surjective η
  have ha : a ≠ 0 := by
    rintro rfl
    exact h (tateModule.padicPow_zero _)
  rw [PadicInt.unitCoeff_spec ha, tateModule.padicPow_mul, ← Nat.cast_pow,
    tateModule.padicPow_natCast, Bcris.logTeich_pow, Nat.cast_pow]
  exact (Bcris.isUnit_p.pow _).mul
    (Bcris.isUnit_logTeich (((isPrimitive_eps p R).padicPow_iff _).2 (Units.isUnit _)))

end Bridge.CrisLoc.unitOfRootSeries

theorem Bridge.CrisLoc.unit_of_root : ∀ (l : ℕ) [Fact l.Prime] (e : (Reformulated.AutPerF.Tilt l ↥(PadicComplexInt l))) (he : e.untilt = 1) (hne : e ≠ 1), IsUnit (algebraMap ((Reformulated.AutPerF.Acris l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.Bcris l ↥(PadicComplexInt l))) (algebraMap ((Reformulated.AutPerF.Ainf l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.Acris l ↥(PadicComplexInt l))) (WittVector.teichmuller l e - 1))) := by
  intro l _ e he hne
  have h := Bridge.CrisLoc.unitOfRootSeries.isUnit_logTeich
    (⟨e, he⟩ : tateModule l ↥(PadicComplexInt l)) (fun h => hne (congrArg Subtype.val h))
  exact isUnit_of_dvd_unit (Bridge.CrisLoc.unitOfRootSeries.dvd_log _ _) h

end
end
end UnitOfRootAlt
namespace PowDivFactorialAlt
section

theorem Bridge.RingBasics.exists_pow_div_factorial : ∀ (l : ℕ) [Fact l.Prime] (n : ℕ), ∃ c : ℤ_[l], ((n.factorial : ℕ) : ℤ_[l]) * c = ((l : ℕ) : ℤ_[l]) ^ n := by
  intro l hl n
  obtain ⟨m, hm⟩ : l ^ padicValNat l n.factorial ∣ n.factorial := pow_padicValNat_dvd
  have hle : padicValNat l n.factorial ≤ n := padicValNat_factorial_le l n
  have hnd : ¬ l ∣ m := by
    rintro ⟨k, hk⟩
    apply pow_succ_padicValNat_not_dvd (p := l) (Nat.factorial_ne_zero n)
    refine ⟨k, ?_⟩
    rw [pow_succ, mul_assoc, ← hk]
    exact hm
  have hu : IsUnit ((m : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    apply le_antisymm (PadicInt.norm_le_one _)
    by_contra h
    have h' : ‖(((m : ℕ) : ℤ) : ℤ_[l])‖ < 1 := by simpa using not_le.mp h
    rw [PadicInt.norm_int_lt_one_iff_dvd] at h'
    exact hnd (by exact_mod_cast h')
  obtain ⟨u, hu'⟩ := hu.exists_right_inv
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  generalize padicValNat l n.factorial = v at hm hd
  refine ⟨u * ((l : ℕ) : ℤ_[l]) ^ d, ?_⟩
  rw [hm]
  push_cast
  calc ((l : ℕ) : ℤ_[l]) ^ v * (m : ℤ_[l]) * (u * ((l : ℕ) : ℤ_[l]) ^ d)
      = ((l : ℕ) : ℤ_[l]) ^ v * ((m : ℤ_[l]) * u) * ((l : ℕ) : ℤ_[l]) ^ d := by ring
    _ = ((l : ℕ) : ℤ_[l]) ^ n := by rw [hu', mul_one, ← pow_add, ← hd]

end
end PowDivFactorialAlt
namespace CrisExtension
section

noncomputable section

open Ideal Reformulated.AutPerF
open scoped Nat

namespace Bridge.CrisLoc.CrisExtensionLemmas

theorem exists_one_add_pow {p : ℕ} (hp : p.Prime) {A : Type*} [CommRing A] (y : A) :
    ∃ s : A, (1 + y) ^ p - 1 = y * (y ^ (p - 1) + p * (1 + y * s)) := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 2 := ⟨p - 2, by have := hp.two_le; omega⟩
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (1 : Polynomial ℤ) Polynomial.X
  obtain ⟨k, hk⟩ := Polynomial.powAddExpansion (1 : Polynomial ℤ) Polynomial.X (m + 2)
  have h1 : ((m + 2 : ℕ) : Polynomial ℤ) * (r - 1) =
      Polynomial.X * (k - Polynomial.X ^ m) := by
    apply mul_left_cancel₀ (Polynomial.X_ne_zero (R := ℤ))
    simp only [one_pow, mul_one] at hr hk
    linear_combination hk - hr
  have h2 : Polynomial.eval 0 (r - 1) = 0 := by
    have h3 := congrArg (Polynomial.eval 0) h1
    rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_X, zero_mul,
      Polynomial.eval_natCast] at h3
    exact (mul_eq_zero.1 h3).resolve_left (by positivity)
  have h4 : Polynomial.X ∣ r - 1 := by
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero, h2]
  obtain ⟨s, hs⟩ := h4
  refine ⟨Polynomial.aeval y s, ?_⟩
  rw [eq_add_of_sub_eq hs] at hr
  have h5 := congrArg (Polynomial.aeval y) hr
  simp only [map_pow, map_add, map_mul, map_one, Polynomial.aeval_X, map_natCast] at h5
  rw [show m + 2 - 1 = m + 1 from rfl]
  linear_combination h5

theorem mem_jac_of_pow {A : Type*} [CommRing A] {x : A} {n : ℕ}
    (h : x ^ n ∈ jacobson (⊥ : Ideal A)) : x ∈ jacobson (⊥ : Ideal A) :=
  Ideal.mem_sInf.2 fun _ hJ => hJ.2.isPrime.mem_of_pow_mem n (Ideal.mem_sInf.1 h hJ)

theorem isUnit_one_add {A : Type*} [CommRing A] {x : A} (h : x ∈ jacobson (⊥ : Ideal A)) :
    IsUnit (1 + x) := by
  have := Ideal.mem_jacobson_bot.1 h 1
  rwa [mul_one, add_comm] at this

variable {p : ℕ} [Fact p.Prime]
variable {R : Type} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]

theorem p_mem_jac : (p : Acris p R) ∈ jacobson (⊥ : Ideal (Acris p R)) :=
  IsAdicComplete.le_jacobson_bot (span {(p : Acris p R)}) (mem_span_singleton_self _)

theorem gamma_mul (a b : ℕ) (x : Ainf p R) (hx : Ainf.theta p R x = 0) :
    AcrisZero.gamma a x hx * AcrisZero.gamma b x hx =
      ((a + b).choose a : ℕ) * AcrisZero.gamma (a + b) x hx := by
  apply Subtype.ext
  simp only [MulMemClass.coe_mul, SubringClass.coe_natCast, AcrisZero.coe_gamma]
  have hq : ((a ! : ℚ)⁻¹ * (b ! : ℚ)⁻¹) = ((a + b).choose a : ℚ) * ((a + b)! : ℚ)⁻¹ := by
    rw [Nat.cast_choose ℚ (Nat.le_add_right a b), Nat.add_sub_cancel_left]
    have : ((a + b)! : ℚ) ≠ 0 := by positivity
    field_simp
  unfold AinfInv.gamma
  rw [smul_mul_smul_comm, hq, ← pow_add, mul_smul, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

theorem gamma_pow (k : ℕ) (x : Ainf p R) (hx : Ainf.theta p R x = 0) :
    ∃ c : AcrisZero p R, AcrisZero.gamma p x hx ^ (k + 1) =
      c * AcrisZero.gamma (p * (k + 1)) x hx := by
  induction k with
  | zero => exact ⟨1, by simp⟩
  | succ k ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c * ((p + p * (k + 1)).choose p : ℕ), ?_⟩
    rw [pow_succ', hc, mul_left_comm, gamma_mul, show p * (k + 1 + 1) = p + p * (k + 1) by ring,
      mul_assoc]

theorem p_dvd_gamma_pow (x : Ainf p R) (hx : Ainf.theta p R x = 0) :
    (p : AcrisZero p R) ∣ AcrisZero.gamma p x hx ^ p := by
  have hp : p.Prime := Fact.out
  obtain ⟨c, hc⟩ := gamma_pow (p - 2) x hx
  have h2 := hp.two_le
  have e1 : AcrisZero.gamma p x hx ^ p =
      AcrisZero.gamma p x hx * AcrisZero.gamma p x hx ^ (p - 2 + 1) := by
    rw [← pow_succ']; congr 1; omega
  have e2 : p + p * (p - 2 + 1) = p ^ 2 := by
    obtain ⟨m, hm⟩ : ∃ m, p = m + 2 := ⟨p - 2, by omega⟩
    rw [show p - 2 = m by omega, hm]; ring
  rw [e1, hc, mul_left_comm, gamma_mul]
  refine Dvd.dvd.mul_left (Dvd.dvd.mul_right (Nat.cast_dvd_cast ?_) _) _
  rw [e2]
  exact hp.dvd_choose_pow hp.ne_zero (by nlinarith)

theorem exists_pow_eq_p_mul (x : Ainf p R) (hx : Ainf.theta p R x = 0) :
    ∃ z ∈ jacobson (⊥ : Ideal (Acris p R)), algebraMap (Ainf p R) (Acris p R) x ^ p = p * z := by
  have hp : p.Prime := Fact.out
  refine ⟨((p - 1)! : ℕ) * algebraMap (AcrisZero p R) _ (AcrisZero.gamma p x hx), ?_, ?_⟩
  · refine Ideal.mul_mem_left _ _ (mem_jac_of_pow (n := p) ?_)
    obtain ⟨c, hc⟩ := p_dvd_gamma_pow x hx
    rw [← map_pow, hc, map_mul, map_natCast]
    exact Ideal.mul_mem_right _ _ p_mem_jac
  · have h := congrArg (algebraMap (AcrisZero p R) (Acris p R))
      (AcrisZero.factorial_mul_gamma p x hx)
    rw [map_mul, map_pow, map_natCast, ← IsScalarTower.algebraMap_apply] at h
    rw [← h, ← mul_assoc, ← Nat.cast_mul, Nat.mul_factorial_pred hp.ne_zero]

theorem mem_jac_of_theta (x : Ainf p R) (hx : Ainf.theta p R x = 0) :
    algebraMap (Ainf p R) (Acris p R) x ∈ jacobson (⊥ : Ideal (Acris p R)) := by
  obtain ⟨z, hz, h⟩ := exists_pow_eq_p_mul x hx
  exact mem_jac_of_pow (n := p) (by rw [h]; exact Ideal.mul_mem_left _ _ hz)

theorem log_eq (u : Ainf p R) (hu : Ainf.theta p R u = 1) (a : Acris p R)
    (ha : a ∈ jacobson (⊥ : Ideal (Acris p R)))
    (h : algebraMap (Ainf p R) (Acris p R) u - 1 = p * a) :
    ∃ L : Acris p R, IsUnit L ∧ Acris.log u hu = p * a * L := by
  have hp : p.Prime := Fact.out
  set U := algebraMap (Ainf p R) (Acris p R) u with hU
  have step : ∀ (n : ℕ) (w : Acris p R), ∃ c : Acris p R,
      U ^ p ^ n - 1 = (p : Acris p R) ^ n * (p * a * w) →
      U ^ p ^ (n + 1) - 1 = (p : Acris p R) ^ (n + 1) * (p * a * (w + p ^ n * (a * c))) := by
    intro n w
    obtain ⟨s, hs⟩ := exists_one_add_pow hp (U ^ p ^ n - 1)
    refine ⟨w * (w * (U ^ p ^ n - 1) ^ (p - 2) + p * w * s), fun hy => ?_⟩
    rw [add_sub_cancel, ← pow_mul, ← pow_succ,
      show p - 1 = (p - 2) + 1 by have := hp.two_le; omega, pow_succ _ (p - 2)] at hs
    rw [hs]
    generalize (U ^ p ^ n - 1) ^ (p - 2) = t
    rw [hy]
    ring
  choose c hc using step
  let W : ℕ → Acris p R := fun n => Nat.rec 1 (fun n w => w + p ^ n * (a * c n w)) n
  have W0 : W 0 = 1 := rfl
  have WS : ∀ n, W (n + 1) = W n + p ^ n * (a * c n (W n)) := fun n => rfl
  have hW : ∀ n, U ^ p ^ n - 1 = (p : Acris p R) ^ n * (p * a * W n) := by
    intro n
    induction n with
    | zero => rw [W0]; simpa using h
    | succ n ih => rw [WS]; exact hc n _ ih
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := span {(p : Acris p R)}) W (fun {m n} hmn => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      rw [WS, ← sub_sub]
      exact dvd_sub ih ((pow_dvd_pow _ hn).mul_right _))
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at hL
  refine ⟨L, ?_, ?_⟩
  · obtain ⟨d, hd⟩ := hL 1
    rw [show W 1 = _ from WS 0, W0] at hd
    have : L = 1 + (a * c 0 1 - p * d) := by linear_combination -hd
    rw [this]
    exact isUnit_one_add (sub_mem (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_right _ _ p_mem_jac))
  · rw [← sub_eq_zero]
    refine Acris.eq_zero_of_forall_dvd fun n => ?_
    obtain ⟨l, hl, hl'⟩ := Acris.exists_quot u hu n
    have h1 := congrArg (algebraMap (AcrisZero p R) (Acris p R)) hl
    rw [map_mul, map_pow, map_natCast, map_sub, map_pow, map_one, ← IsScalarTower.algebraMap_apply,
      ← hU, hW] at h1
    have h2 := Acris.p_pow_mul_cancel n h1
    have h3 : (p : Acris p R) ^ n ∣ Acris.log u hu - algebraMap (AcrisZero p R) _ l :=
      (Acris.eval_eq_zero_iff n _).1 (by rw [map_sub, hl', Acris.eval_algebraMap, sub_self])
    have : Acris.log u hu - p * a * L =
        (Acris.log u hu - algebraMap (AcrisZero p R) _ l) + p * a * (W n - L) := by
      rw [h2]; ring
    rw [this]
    exact dvd_add h3 ((hL n).mul_left _)

theorem teich_pow_sub_one [IsDomain R] (e : Tilt p R) (he : e.untilt = 1)
    (h1 : Tilt.seq 1 e ≠ 1) : ∃ w : Acris p R, IsUnit w ∧
      algebraMap (Ainf p R) (Acris p R) (Ainf.teich p e) ^ p - 1 =
        p * (algebraMap (Ainf p R) (Acris p R) (Ainf.teich p e - 1) * w) := by
  have hp : p.Prime := Fact.out
  set v : Ainf p R := Ainf.teich p ((frobeniusEquiv (Tilt p R) p).symm e) with hv
  have hvp : v ^ p = Ainf.teich p e := by rw [hv, ← map_pow, frobeniusEquiv_symm_pow_p]
  have hθv : Ainf.theta p R (v - 1) ≠ 0 := by
    rw [map_sub, map_one, hv, Ainf.theta_teich, ← Tilt.seq_zero, Tilt.seq_frobeniusEquiv_symm]
    exact sub_ne_zero.2 h1
  obtain ⟨s, hs⟩ := exists_one_add_pow hp (v - 1)
  rw [add_sub_cancel, hvp] at hs
  set ξ : Ainf p R := (v - 1) ^ (p - 1) + p * (1 + (v - 1) * s) with hξ
  have hθx : Ainf.theta p R (Ainf.teich p e - 1) = 0 := by
    rw [map_sub, map_one, Ainf.theta_teich, he, sub_self]
  have hθξ : Ainf.theta p R ξ = 0 := by
    have := hθx
    rw [hs, map_mul] at this
    exact (mul_eq_zero.1 this).resolve_left hθv
  obtain ⟨z, hz, hz'⟩ := exists_pow_eq_p_mul ξ hθξ
  have hξJ := mem_jac_of_theta ξ hθξ
  have hxJ := mem_jac_of_theta _ hθx
  have key : (Ainf.teich p e - 1) ^ (p - 1) =
      ξ ^ p - p * (ξ * (ξ ^ (p - 2) * (1 + (v - 1) * s))) := by
    have e1 : (v - 1) ^ (p - 1) = ξ - p * (1 + (v - 1) * s) := by rw [hξ]; ring
    have e2 : ξ ^ (p - 1) = ξ * ξ ^ (p - 2) := by
      rw [← pow_succ']; congr 1; have := hp.two_le; omega
    have e3 : ξ ^ p = ξ * (ξ * ξ ^ (p - 2)) := by
      rw [← pow_succ', ← pow_succ']; congr 1; have := hp.two_le; omega
    rw [hs, mul_pow, e1, e2, e3]
    ring
  have key' := congrArg (algebraMap (Ainf p R) (Acris p R)) key
  rw [map_pow, map_sub _ (ξ ^ p), map_pow, hz', map_mul, map_natCast, map_mul] at key'
  set x := algebraMap (Ainf p R) (Acris p R) (Ainf.teich p e - 1) with hx
  obtain ⟨t, ht⟩ := exists_one_add_pow hp x
  refine ⟨1 + (x * t + z - algebraMap (Ainf p R) (Acris p R) ξ *
    algebraMap (Ainf p R) (Acris p R) (ξ ^ (p - 2) * (1 + (v - 1) * s))), isUnit_one_add
      (sub_mem (add_mem (Ideal.mul_mem_right _ _ hxJ) hz) (Ideal.mul_mem_right _ _ hξJ)), ?_⟩
  have hx' : algebraMap (Ainf p R) (Acris p R) (Ainf.teich p e) = 1 + x := by
    rw [hx, map_sub, map_one]; ring
  rw [hx', ht, key']
  ring

theorem exists_primitive (n : ℕ) : ∀ e : Tilt p R, e.untilt = 1 → Tilt.seq n e ≠ 1 →
    ∃ (e' : Tilt p R) (k : ℕ), e = e' ^ k ∧ e'.untilt = 1 ∧ Tilt.seq 1 e' ≠ 1 := by
  induction n with
  | zero => intro e he h; exact absurd (by rw [Tilt.seq_zero, he]) h
  | succ n ih =>
    intro e he h
    by_cases h1 : Tilt.seq 1 e = 1
    · obtain ⟨e', k, hk, h2, h3⟩ := ih ((frobeniusEquiv (Tilt p R) p).symm e)
        (by rw [← Tilt.seq_zero, Tilt.seq_frobeniusEquiv_symm]; exact h1)
        (by rw [Tilt.seq_frobeniusEquiv_symm]; exact h)
      exact ⟨e', k * p, by rw [pow_mul, ← hk, frobeniusEquiv_symm_pow_p], h2, h3⟩
    · exact ⟨e, 1, (pow_one e).symm, he, h1⟩

theorem logTeich_padicPow' (η : tateModule p R) (a : ℤ_[p]) :
    Acris.logTeich η ∣ Acris.logTeich (tateModule.padicPow η a) := by
  refine ⟨algebraMap ℤ_[p] (Acris p R) a, sub_eq_zero.1 (Acris.eq_zero_of_forall_dvd fun k => ?_)⟩
  have h := Ideal.mem_span_singleton.1 (PadicInt.appr_spec k a)
  obtain ⟨η', hη'⟩ := tateModule.exists_padicPow_eq η h
  have h2 := map_dvd (algebraMap ℤ_[p] (Acris p R)) h
  rw [map_pow, map_natCast, map_sub, map_natCast] at h2
  obtain ⟨b, hb⟩ := h2
  rw [hη', Acris.logTeich_mul, Acris.logTeich_pow, Acris.logTeich_pow, eq_add_of_sub_eq hb,
    Nat.cast_pow]
  exact ⟨Acris.logTeich η' - Acris.logTeich η * b, by ring⟩

theorem main [IsDomain R] (e : Tilt p R) (he : e.untilt = 1) (hne : e ≠ 1) {B : Type} [CommRing B]
    (g : Acris p R →+* B)
    (hg : IsUnit (g (algebraMap (Ainf p R) (Acris p R) (Ainf.teich p e - 1)))) :
    ∃ F : Bcris p R →+* B, ∀ x : Acris p R, F (algebraMap _ _ x) = g x := by
  have hp : p.Prime := Fact.out
  obtain ⟨n, hn⟩ : ∃ n, Tilt.seq n e ≠ 1 := by
    by_contra hc
    push_neg at hc
    exact hne (Tilt.ext_seq fun n => by rw [hc, map_one])
  obtain ⟨e', k, rfl, he', h1⟩ := exists_primitive n e he hn
  have hg' : IsUnit (g (algebraMap (Ainf p R) (Acris p R) (Ainf.teich p e' - 1))) := by
    refine isUnit_of_dvd_unit (map_dvd g (map_dvd _ ?_)) hg
    rw [map_pow]
    exact sub_one_dvd_pow_sub_one _ _
  have hθx : Ainf.theta p R (Ainf.teich p e' - 1) = 0 := by
    rw [map_sub, map_one, Ainf.theta_teich, he', sub_self]
  have hpu : IsUnit (p : B) := by
    obtain ⟨z, -, hz⟩ := exists_pow_eq_p_mul _ hθx
    have := hg'.pow p
    rw [← map_pow, hz, map_mul, map_natCast] at this
    exact isUnit_of_mul_isUnit_left this
  obtain ⟨w, hw, hw'⟩ := teich_pow_sub_one e' he' h1
  let η : tateModule p R := ⟨e', he'⟩
  have hlog : IsUnit (g (Acris.logTeich η)) := by
    obtain ⟨L, hL, hL'⟩ := log_eq (Ainf.teich p (η ^ p).1)
      (by rw [Ainf.theta_teich]; exact (η ^ p).2) _
      (Ideal.mul_mem_right w _ (mem_jac_of_theta _ hθx))
      (by rw [← hw', SubmonoidClass.coe_pow, map_pow, map_pow])
    change Acris.logTeich (η ^ p) = _ at hL'
    rw [Acris.logTeich_pow] at hL'
    have h2 := congrArg g hL'
    simp only [map_mul, map_natCast] at h2
    have h3 : IsUnit ((p : B) * g (Acris.logTeich η)) := by
      rw [h2]
      exact (hpu.mul (hg'.mul (hw.map g))).mul (hL.map g)
    exact isUnit_of_mul_isUnit_right h3
  refine ⟨Bcris.lift (BcrisPlus.lift g hpu) (fun ε hε => ?_), fun x => ?_⟩
  · rw [BcrisPlus.lift_algebraMap]
    obtain ⟨a, ha⟩ := hε.padicPow_surjective η
    rw [← ha] at hlog
    exact isUnit_of_dvd_unit (map_dvd g (logTeich_padicPow' ε a)) hlog
  · rw [IsScalarTower.algebraMap_apply (Acris p R) (BcrisPlus p R) (Bcris p R),
      Bcris.lift_algebraMap, BcrisPlus.lift_algebraMap]

end Bridge.CrisLoc.CrisExtensionLemmas

theorem Bridge.CrisLoc.exists_extension : ∀ (l : ℕ) [Fact l.Prime] (e : (Reformulated.AutPerF.Tilt l ↥(PadicComplexInt l))) (he : e.untilt = 1) (hne : e ≠ 1) {R : Type} [CommRing R] (g : (Reformulated.AutPerF.Acris l ↥(PadicComplexInt l)) →+* R) (hg : IsUnit (g (algebraMap ((Reformulated.AutPerF.Ainf l ↥(PadicComplexInt l))) ((Reformulated.AutPerF.Acris l ↥(PadicComplexInt l))) (WittVector.teichmuller l e - 1)))), ∃ F : (Reformulated.AutPerF.Bcris l ↥(PadicComplexInt l)) →+* R, ∀ x : (Reformulated.AutPerF.Acris l ↥(PadicComplexInt l)), F (algebraMap _ _ x) = g x := by
  intro l _ e he hne R _ g hg
  exact Bridge.CrisLoc.CrisExtensionLemmas.main e he hne g hg

end
end
end CrisExtension
