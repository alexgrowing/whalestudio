import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EmbeddingMemCoefficientField
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsRingEquivOfIsTranscendenceBasis
open Polynomial

noncomputable section

namespace GlobalTheory.TeichGalois

variable {g : ℕ} [Fact g.Prime]

theorem map_zero_eq_zero (t : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) : t 0 = 0 := by
  classical
  have h2 : t 0 * (t 0 - 1) = 0 := by
    rw [mul_sub, mul_one, ← map_mul, mul_zero, sub_self]
  rcases mul_eq_zero.1 h2 with h | h
  · exact h
  · exfalso
    have h1 : t 0 = 1 := sub_eq_zero.1 h
    have hall : ∀ x, t x = 1 := fun x => by
      have : t (x * 0) = t x * t 0 := map_mul t x 0
      rw [mul_zero, h1, mul_one] at this
      exact this.symm
    obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset (Formalism.CyclotomicNorms.Fbar g))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
    exact hy.2 (ht y 1 hy.1 one_ne_zero (by rw [hall, hall]))

theorem exists_coprime_pow_eq_one {x : Formalism.CyclotomicNorms.Fbar g} (hx : x ≠ 0) :
    ∃ m : ℕ, g.Coprime m ∧ x ^ m = 1 := by
  let K := IntermediateField.adjoin (ZMod g) ({x} : Set (Formalism.CyclotomicNorms.Fbar g))
  haveI : FiniteDimensional (ZMod g) K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  have hxK : (⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩ : K) ≠ 0 := by
    intro h; apply hx; simpa using congrArg Subtype.val h
  let u := Units.mk0 _ hxK
  have hn : x ^ orderOf u = 1 := by
    have h3 : (u : K) ^ orderOf u = 1 := by
      rw [← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
    have h4 : ((u : K) : Formalism.CyclotomicNorms.Fbar g) ^ orderOf u = 1 := by
      rw [← IntermediateField.coe_pow, h3, IntermediateField.coe_one]
    exact h4
  have hpos : 0 < orderOf u := orderOf_pos u
  obtain ⟨a, m, hm, heq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hpos.ne' g (Fact.out : g.Prime).ne_one
  refine ⟨m, (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm, ?_⟩
  have h2 : (x ^ m - 1) ^ (g ^ a) = 0 := by
    rw [sub_pow_char_pow, one_pow, ← pow_mul, mul_comm, ← heq, hn, sub_self]
  exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero _ (Fact.out : g.Prime).ne_zero) |>.1 h2)

theorem exists_common_exponent (s : Finset (Formalism.CyclotomicNorms.Fbar g)) (hs : ∀ x ∈ s, x ≠ 0) :
    ∃ m : ℕ, g.Coprime m ∧ ∀ x ∈ s, x ^ m = 1 := by
  have h := fun x (hx : x ∈ s) => exists_coprime_pow_eq_one (hs x hx)
  choose! e he using h
  refine ⟨∏ x ∈ s, e x, Nat.Coprime.prod_right fun x hx => (he x hx).1, fun x hx => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem e hx
  rw [hc, pow_mul, (he x hx).2, one_pow]

theorem isPrimitiveRoot_map (t : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) {u : Formalism.CyclotomicNorms.Fbar g} {m : ℕ}
    (hm : 0 < m) (hu : IsPrimitiveRoot u m) : IsPrimitiveRoot (t u) m := by
  have hu0 : u ≠ 0 := hu.ne_zero hm.ne'
  refine ⟨by rw [← map_pow, hu.pow_eq_one, map_one], fun l hl => hu.dvd_of_pow_eq_one l ?_⟩
  exact ht _ _ (pow_ne_zero _ hu0) one_ne_zero (by rw [map_pow, hl, map_one])

theorem lift_apply_eq_sum (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) (f : MonoidAlgebra ℤ (Formalism.CyclotomicNorms.Fbar g)) :
    MonoidAlgebra.lift ℤ ℂ (Formalism.CyclotomicNorms.Fbar g) t f = ∑ x ∈ f.coeff.support, (f.coeff x : ℂ) * t x := by
  rw [MonoidAlgebra.lift_apply, Finsupp.sum]
  simp [zsmul_eq_mul]

theorem lift_eq_zero_of_lift_eq_zero (t t' : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y)
    (ht' : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t' x = t' y → x = y)
    (f : MonoidAlgebra ℤ (Formalism.CyclotomicNorms.Fbar g)) (h : MonoidAlgebra.lift ℤ ℂ (Formalism.CyclotomicNorms.Fbar g) t' f = 0) :
    MonoidAlgebra.lift ℤ ℂ (Formalism.CyclotomicNorms.Fbar g) t f = 0 := by
  classical
  set s := f.coeff.support.filter (· ≠ 0) with hs
  obtain ⟨m, hmc, hpow⟩ := exists_common_exponent s (fun x hx => (Finset.mem_filter.1 hx).2)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact (Fact.out : g.Prime).ne_one (Nat.coprime_zero_right _ |>.1 hmc)
  have hm : 0 < m := Nat.pos_of_ne_zero hm0
  haveI : NeZero m := ⟨hm0⟩
  haveI : NeZero (m : Formalism.CyclotomicNorms.Fbar g) := ⟨by
    rw [Ne, CharP.cast_eq_zero_iff (Formalism.CyclotomicNorms.Fbar g) g]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).1 hmc⟩
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_root (cyclotomic m (Formalism.CyclotomicNorms.Fbar g))
    (degree_cyclotomic_pos m _ hm).ne'
  have hu : IsPrimitiveRoot u m := isRoot_cyclotomic_iff.1 hu
  have hk : ∀ x ∈ s, ∃ i : ℕ, u ^ i = x := fun x hx => by
    obtain ⟨i, -, hi⟩ := hu.eq_pow_of_pow_eq_one (hpow x hx)
    exact ⟨i, hi⟩
  choose! k hk using hk
  let P : ℤ[X] := ∑ x ∈ s, C (f.coeff x) * X ^ (k x)
  have heval : ∀ τ : Formalism.CyclotomicNorms.Fbar g →* ℂ, τ 0 = 0 →
      MonoidAlgebra.lift ℤ ℂ (Formalism.CyclotomicNorms.Fbar g) τ f = aeval (τ u) P := by
    intro τ hτ
    rw [lift_apply_eq_sum, ← Finset.sum_filter_of_ne (p := (· ≠ 0)) (fun x _ hx h0 => hx (by rw [h0, hτ, mul_zero]))]
    simp only [P, map_sum, map_mul, aeval_C, map_pow, aeval_X, algebraMap_int_eq, eq_intCast, map_intCast]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [← map_pow, hk x hx]
  have hζ := isPrimitiveRoot_map t ht hm hu
  have hζ' := isPrimitiveRoot_map t' ht' hm hu
  have h1 : aeval (t' u) P = 0 := by rw [← heval t' (map_zero_eq_zero t' ht'), h]
  have hdvd : minpoly ℤ (t' u) ∣ P := minpoly.isIntegrallyClosed_dvd (hζ'.isIntegral hm) h1
  rw [← cyclotomic_eq_minpoly hζ' hm, cyclotomic_eq_minpoly hζ hm] at hdvd
  rw [heval t (map_zero_eq_zero t ht)]
  exact aeval_eq_zero_of_dvd_aeval_eq_zero hdvd (minpoly.aeval ℤ (t u))

instance countable_fbar : Countable (Formalism.CyclotomicNorms.Fbar g) :=
  Cardinal.mk_le_aleph0_iff.1 ((Algebra.IsAlgebraic.cardinalMk_le_max (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).trans
    (max_le Cardinal.mk_le_aleph0 le_rfl))

theorem exists_ringEquiv_comp_eq : ∀ (g : ℕ) [Fact g.Prime] (t t' : Formalism.CyclotomicNorms.Fbar g →* ℂ), (∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) → (∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t' x = t' y → x = y) → ∃ σ : ℂ ≃+* ℂ, ∀ x, σ (t' x) = t x := by
  intro g _ t t' ht ht'
  let α : MonoidAlgebra ℤ (Formalism.CyclotomicNorms.Fbar g) →+* ℂ := (MonoidAlgebra.lift ℤ ℂ (Formalism.CyclotomicNorms.Fbar g) t').toRingHom
  let β : MonoidAlgebra ℤ (Formalism.CyclotomicNorms.Fbar g) →+* ℂ := (MonoidAlgebra.lift ℤ ℂ (Formalism.CyclotomicNorms.Fbar g) t).toRingHom
  have hker : RingHom.ker α ≤ RingHom.ker β := fun f hf =>
    lift_eq_zero_of_lift_eq_zero t t' ht ht' f hf
  have hker' : RingHom.ker β ≤ RingHom.ker α := fun f hf =>
    lift_eq_zero_of_lift_eq_zero t' t ht' ht f hf
  haveI : (RingHom.ker α).IsPrime := RingHom.ker_isPrime α
  let Q := MonoidAlgebra ℤ (Formalism.CyclotomicNorms.Fbar g) ⧸ RingHom.ker α
  let α' : Q →+* ℂ := RingHom.kerLift α
  let β' : Q →+* ℂ := Ideal.Quotient.lift (RingHom.ker α) β hker
  have hα' : Function.Injective α' := RingHom.kerLift_injective α
  have hβ' : Function.Injective β' := by
    rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
    have : β f = 0 := hq
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hker' this)
  haveI : Countable (MonoidAlgebra ℤ (Formalism.CyclotomicNorms.Fbar g)) :=
    Function.Injective.countable (f := MonoidAlgebra.coeff) (fun a b h => by ext x; rw [h])
  haveI : Countable Q := Function.Surjective.countable Ideal.Quotient.mk_surjective
  haveI : Countable (FractionRing Q) :=
    Function.Surjective.countable (IsLocalization.mk'_surjective (nonZeroDivisors Q) (S := FractionRing Q))
  let a : FractionRing Q →+* ℂ := IsFractionRing.lift hα'
  let b : FractionRing Q →+* ℂ := IsFractionRing.lift hβ'
  obtain ⟨σ, hσ⟩ := GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq a b
  refine ⟨σ, fun x => ?_⟩
  have h := hσ (algebraMap Q (FractionRing Q) (Ideal.Quotient.mk _ (MonoidAlgebra.single x 1)))
  have ha : a (algebraMap Q (FractionRing Q) (Ideal.Quotient.mk _ (MonoidAlgebra.single x 1))) = t' x := by
    simp only [a]
    rw [IsFractionRing.lift_algebraMap]
    simp only [α']
    rw [RingHom.kerLift_mk]
    simp [α, MonoidAlgebra.lift_single]
  have hb : b (algebraMap Q (FractionRing Q) (Ideal.Quotient.mk _ (MonoidAlgebra.single x 1))) = t x := by
    simp only [b]
    rw [IsFractionRing.lift_algebraMap]
    show β (MonoidAlgebra.single x 1) = t x
    simp [β, MonoidAlgebra.lift_single]
  rw [ha, hb] at h
  exact h

end GlobalTheory.TeichGalois
