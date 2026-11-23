import Mathlib

open scoped BigOperators

namespace GlobalTheory

theorem exists_mul_eq_natCast_of_isIntegral_int {S : Type*} [CommRing S] [IsDomain S]
    {y : S} (hy : IsIntegral ℤ y) (hy0 : y ≠ 0) :
    ∃ (t : S) (n : ℕ), 0 < n ∧ y * t = n := by
  obtain ⟨m, hm, t, ht⟩ :=
    hy.isAlgebraic.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hy0)
  have ht' : (m : S) = y * t := by simpa using ht
  refine ⟨(m.sign : S) * t, m.natAbs, Int.natAbs_pos.mpr hm, ?_⟩
  have h1 : ((m.natAbs : ℤ) : S) = ((m.sign * m : ℤ) : S) := by
    rw [Int.sign_mul_self_eq_natAbs]
  have h2 : (m.natAbs : S) = (m.sign : S) * (m : S) := by
    rw [← Int.cast_mul, ← h1, Int.cast_natCast]
  rw [h2, ht']; ring

theorem exists_field_of_isIntegral_image :
    ∀ (R : Type) [CommRing R] (φ : R →+* ℂ), (∀ r, IsIntegral ℤ (φ r)) → ∃ (F : Type) (_ : Field F) (_ : CharZero F) (φ' : R →+* F), (∀ x : F, ∃ (r : R) (n : ℕ), 0 < n ∧ φ' r = n * x) ∧ ∀ (A : Type) [CommRing A] [Algebra ℚ A] (χ : R →+* A), (∀ r, φ r = 0 → χ r = 0) → ∃ χ' : F →+* A, χ'.comp φ' = χ := by
  intro R _ φ hφ
  let S := R ⧸ RingHom.ker φ
  have hinj : Function.Injective (RingHom.kerLift φ) := RingHom.kerLift_injective φ
  haveI : IsDomain S := hinj.isDomain (RingHom.kerLift φ)
  haveI : CharZero S := (RingHom.kerLift φ).charZero
  have hint : ∀ y : S, @IsIntegral ℤ S _ _ (Ring.toIntAlgebra S) y := by
    intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← isIntegral_algHom_iff (RingHom.kerLift φ).toIntAlgHom hinj]
    exact hφ r
  haveI : CharZero (FractionRing S) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective S (FractionRing S))
  refine ⟨FractionRing S, inferInstance, inferInstance,
    (algebraMap S (FractionRing S)).comp (Ideal.Quotient.mk _), ?_, ?_⟩
  · intro x
    obtain ⟨a, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := S) x
    have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    obtain ⟨t, n, hn, ht⟩ := exists_mul_eq_natCast_of_isIntegral_int (hint y) hy0
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (a * t)
    refine ⟨r, n, hn, ?_⟩
    have hy' : algebraMap S (FractionRing S) y ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective S (FractionRing S))).mpr hy0
    have hn' : (n : FractionRing S) =
        algebraMap S (FractionRing S) y * algebraMap S (FractionRing S) t := by
      rw [← map_mul, ht, map_natCast]
    rw [RingHom.comp_apply, hr, hn', map_mul]
    field_simp
  · intro A _ _ χ hχ
    let ψ : S →+* A := Ideal.Quotient.lift (RingHom.ker φ) χ (fun r hr => hχ r hr)
    have hu : ∀ y : nonZeroDivisors S, IsUnit (ψ y) := by
      intro y
      obtain ⟨t, n, hn, ht⟩ :=
        exists_mul_eq_natCast_of_isIntegral_int (hint y) (nonZeroDivisors.ne_zero y.2)
      have hnu : IsUnit (n : A) := by
        have : IsUnit (n : ℚ) := IsUnit.mk0 _ (Nat.cast_ne_zero.mpr hn.ne')
        simpa using this.map (algebraMap ℚ A)
      have : ψ y * ψ t = n := by rw [← map_mul, ht, map_natCast]
      exact isUnit_of_mul_isUnit_left (this ▸ hnu)
    refine ⟨IsLocalization.lift (M := nonZeroDivisors S) (S := FractionRing S) hu, ?_⟩
    ext r
    simp only [RingHom.comp_apply, IsLocalization.lift_eq]
    rfl

end GlobalTheory
