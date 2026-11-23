import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.TupleConstantsNeZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.ProdFormula

open NumberField IsDedekindDomain Finset GlobalTheory.Square
open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)

noncomputable section

namespace GlobalTheory.Square.AwayClosure

variable {K : Type} [Field K] [NumberField K]

open NumberField IsDedekindDomain Finset in
open scoped nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in

theorem _root_.GlobalTheory.Square.AwayClosure.of_integral {m k l : ℕ} {x : K} (hx : x ≠ 0) {a b : 𝓞 K}
    (ha : x * (m : K) ^ k = a) (hb : x⁻¹ * (m : K) ^ l = b) : _root_.GlobalTheory.Square.IsAwayUnit m x := by
  have hab : ((m : K)) ^ (k + l) = (a : K) * (b : K) := by
    rw [← ha, ← hb, pow_add]
    field_simp
  refine ⟨a, k, k + l, ⟨b, RingOfIntegers.coe_injective ?_⟩, ha⟩
  simpa using hab

open NumberField IsDedekindDomain Finset in
open scoped nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
theorem _root_.GlobalTheory.Square.AwayClosure.of_pow_eq_one (m : ℕ) {x : K} {k : ℕ} (hk : 0 < k) (h : x ^ k = 1) :
    _root_.GlobalTheory.Square.IsAwayUnit m x := by
  have hx : x ≠ 0 := by
    rintro rfl
    simp [zero_pow hk.ne'] at h
  have hxi : IsIntegral ℤ x := IsIntegral.of_pow hk (h ▸ isIntegral_one)
  have hxinv : IsIntegral ℤ x⁻¹ :=
    IsIntegral.of_pow hk (by rw [inv_pow, h, inv_one]; exact isIntegral_one)
  exact _root_.GlobalTheory.Square.AwayClosure.of_integral (k := 0) (l := 0) (a := ⟨x, hxi⟩)
    (b := ⟨x⁻¹, hxinv⟩) hx (by rw [pow_zero, mul_one]; rfl) (by rw [pow_zero, mul_one]; rfl)

open NumberField IsDedekindDomain Finset in
open scoped nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
theorem _root_.GlobalTheory.Square.AwayClosure.of_dvd {m k : ℕ} {a : 𝓞 K} (h : a ∣ (m : 𝓞 K) ^ k) :
    _root_.GlobalTheory.Square.IsAwayUnit m (a : K) :=
  _root_.GlobalTheory.Square.IsAwayUnit.of_dvd h

open NumberField IsDedekindDomain Finset in
open scoped nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
theorem _root_.GlobalTheory.Square.AwayClosure.mul {m : ℕ} {x y : K} (hx : _root_.GlobalTheory.Square.IsAwayUnit m x)
    (hy : _root_.GlobalTheory.Square.IsAwayUnit m y) : _root_.GlobalTheory.Square.IsAwayUnit m (x * y) :=
  _root_.GlobalTheory.Square.IsAwayUnit.mul hx hy

open NumberField IsDedekindDomain Finset in
open scoped nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
theorem _root_.GlobalTheory.Square.AwayClosure.inv {m : ℕ} (hm : 0 < m) {x : K} (hx : _root_.GlobalTheory.Square.IsAwayUnit m x) :
    _root_.GlobalTheory.Square.IsAwayUnit m x⁻¹ := by
  obtain ⟨a, k, k', ⟨c, hc⟩, hxa⟩ := hx
  have hcK : (m : K) ^ k' = (a : K) * (c : K) := by
    have := congrArg (fun t : 𝓞 K => (t : K)) hc
    simpa using this
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hxa
    rw [← hxa, zero_mul] at hcK
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr hm.ne') hcK
  refine ⟨(m : 𝓞 K) ^ k * c, k', k + k', ⟨a, by rw [pow_add, hc]; ring⟩, ?_⟩
  push_cast
  rw [hcK, ← hxa]
  field_simp

end GlobalTheory.Square.AwayClosure

namespace GlobalTheory.Square

open NumberField IsDedekindDomain Finset in
open scoped nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
private lemma valuation_coe_integer_eq_exp_neg_count (v : HeightOneSpectrum (𝓞 K)) {r : 𝓞 K} (hr : r ≠ 0) :
    v.valuation K (r : K) =
      WithZero.exp (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (r : K))) := by
  have hspan : Ideal.span {r} ≠ 0 := by simpa using hr
  rw [show (r : K) = algebraMap (𝓞 K) K r from rfl, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_if_neg _ hr, ← FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.count_coe K v hspan]

open NumberField IsDedekindDomain Finset in
open scoped nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
private lemma valuation_eq_exp_neg_count_spanSingleton_foundation (v : HeightOneSpectrum (𝓞 K)) {y : K} (hy : y ≠ 0) :
    v.valuation K y =
      WithZero.exp (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ y)) := by
  obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) y
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hsK : algebraMap (𝓞 K) K s ≠ 0 := by simpa using hs0
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hy
  have hmul : FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s) *
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K s) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K r) := by
    rw [FractionalIdeal.spanSingleton_mul_spanSingleton, div_mul_cancel₀ _ hsK]
  have hcount := congrArg (FractionalIdeal.count K v) hmul
  rw [FractionalIdeal.count_mul K v (by rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff])
    (by rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff])] at hcount
  have hr' := valuation_coe_integer_eq_exp_neg_count v hr0
  have hs' := valuation_coe_integer_eq_exp_neg_count v hs0
  simp only [show ∀ t : 𝓞 K, (t : K) = algebraMap (𝓞 K) K t from fun _ => rfl] at hr' hs'
  rw [map_div₀, hr', hs', div_eq_iff (by simp), ← WithZero.exp_add, ← hcount]
  congr 1
  ring

open NumberField IsDedekindDomain Finset in
open scoped nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
private lemma exists_integer_eq_of_count_nonneg {y : K} (hy : y ≠ 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K),
      0 ≤ FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ y)) :
    ∃ b : 𝓞 K, y = b := by
  obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K y fun v => by
    rw [valuation_eq_exp_neg_count_spanSingleton_foundation v hy, ← WithZero.exp_zero, WithZero.exp_le_exp]
    linarith [h v]
  exact ⟨b, hb.symm⟩

open NumberField IsDedekindDomain Finset in
open scoped nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
private lemma exists_mul_pow_integer_of_count_eq_zero_coprime {m : ℕ} (hm : 0 < m) {y : K} (hy : y ≠ 0)
    (h : ∀ w : HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∉ w.asIdeal →
      FractionalIdeal.count K w (FractionalIdeal.spanSingleton (𝓞 K)⁰ y) = 0) :
    ∃ n : ℕ, ∃ b : 𝓞 K, y * (m : K) ^ n = b := by
  set I := FractionalIdeal.spanSingleton (𝓞 K)⁰ y with hIdef
  have hI : I ≠ 0 := by rwa [Ne, hIdef, FractionalIdeal.spanSingleton_eq_zero_iff]
  have hfin : {w | FractionalIdeal.count K w I ≠ 0}.Finite :=
    Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors I)
  set n := ∑ w ∈ hfin.toFinset, (FractionalIdeal.count K w I).natAbs
  have hbound : ∀ w, -(n : ℤ) ≤ FractionalIdeal.count K w I := by
    intro w
    by_cases hw : FractionalIdeal.count K w I = 0
    · rw [hw]
      simp
    · have hmem : w ∈ hfin.toFinset := by simpa using hw
      have hle : (FractionalIdeal.count K w I).natAbs ≤ n :=
        Finset.single_le_sum (f := fun w => (FractionalIdeal.count K w I).natAbs)
          (fun _ _ => Nat.zero_le _) hmem
      omega
  have hmK : (m : K) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hm0 : (m : 𝓞 K) ≠ 0 := fun h0 => hmK (by simpa using congrArg (fun t : 𝓞 K => (t : K)) h0)
  have hmalg : (m : K) = algebraMap (𝓞 K) K (m : 𝓞 K) := by simp
  obtain ⟨b, hb⟩ := exists_integer_eq_of_count_nonneg (y := y * (m : K) ^ n)
    (mul_ne_zero hy (pow_ne_zero _ hmK)) fun w => by
      rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, ← FractionalIdeal.spanSingleton_pow,
        FractionalIdeal.count_mul K w hI
          (pow_ne_zero _ (by rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff])),
        FractionalIdeal.count_pow]
      have hc0 : 0 ≤ FractionalIdeal.count K w (FractionalIdeal.spanSingleton (𝓞 K)⁰ (m : K)) := by
        rw [hmalg, ← FractionalIdeal.coeIdeal_span_singleton]
        exact FractionalIdeal.count_coe_nonneg K w _
      by_cases hw : (m : 𝓞 K) ∈ w.asIdeal
      · have h1 : 1 ≤ FractionalIdeal.count K w (FractionalIdeal.spanSingleton (𝓞 K)⁰ (m : K)) := by
          rw [hmalg]
          exact _root_.Formalism.DivisionValues.idxChange_cnt_mem w hm0 hw
        nlinarith [hbound w]
      · rw [h w hw]
        positivity
  exact ⟨n, b, hb⟩

open NumberField IsDedekindDomain Finset in
open scoped nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in

theorem _root_.GlobalTheory.Square.isAwayUnit_closure : ∀ (K : Type) [Field K] [NumberField K]
    [StarRing K] (m : ℕ), 0 < m →
    (∀ (x : K) (k : ℕ), 0 < k → x ^ k = 1 → _root_.GlobalTheory.Square.IsAwayUnit m x) ∧
    (∀ (a : 𝓞 K) (k : ℕ), a ∣ (m : 𝓞 K) ^ k → _root_.GlobalTheory.Square.IsAwayUnit m (a : K)) ∧
    (∀ x y : K, _root_.GlobalTheory.Square.IsAwayUnit m x → _root_.GlobalTheory.Square.IsAwayUnit m y →
      _root_.GlobalTheory.Square.IsAwayUnit m (x * y)) ∧
    (∀ x : K, _root_.GlobalTheory.Square.IsAwayUnit m x → _root_.GlobalTheory.Square.IsAwayUnit m x⁻¹) ∧
    (∀ x : K, x ≠ 0 → (∀ w : _root_.Formalism.PairingDivisionLocalBalance.Pl K, (m : 𝓞 K) ∉ w.asIdeal → _root_.Formalism.DivisionValues.vw w x = 0) →
      _root_.GlobalTheory.Square.IsAwayUnit m x) := by
  intro K _ _ _ m hm
  refine ⟨fun x k hk h => _root_.GlobalTheory.Square.AwayClosure.of_pow_eq_one m hk h,
    fun a k h => _root_.GlobalTheory.Square.AwayClosure.of_dvd h,
    fun x y hx hy => _root_.GlobalTheory.Square.AwayClosure.mul hx hy,
    fun x hx => _root_.GlobalTheory.Square.AwayClosure.inv hm hx, fun x hx hv => ?_⟩
  have hI : ∀ w : HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∉ w.asIdeal →
      FractionalIdeal.count K w (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) = 0 :=
    fun w hw => hv w hw
  have hI' : ∀ w : HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∉ w.asIdeal →
      FractionalIdeal.count K w (FractionalIdeal.spanSingleton (𝓞 K)⁰ x⁻¹) = 0 := by
    intro w hw
    rw [← FractionalIdeal.spanSingleton_inv, FractionalIdeal.count_inv, hI w hw, neg_zero]
  obtain ⟨k, a, ha⟩ := exists_mul_pow_integer_of_count_eq_zero_coprime hm hx hI
  obtain ⟨l, b, hb⟩ := exists_mul_pow_integer_of_count_eq_zero_coprime hm (inv_ne_zero hx) hI'
  exact _root_.GlobalTheory.Square.AwayClosure.of_integral hx ha hb

end GlobalTheory.Square
