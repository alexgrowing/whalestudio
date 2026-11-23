import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsDenominatorPrimesPrescribed
open NumberField GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.Lines

theorem ideal_eq_of_pow_eq {R : Type} [CommRing R] [IsDedekindDomain R] {a b : Ideal R} {h : ℕ}
    (hh : h ≠ 0) (ha : a ≠ ⊥) (hb : b ≠ ⊥) (hab : a ^ h = b ^ h) : a = b := by
  classical
  have h1 := congrArg UniqueFactorizationMonoid.normalizedFactors hab
  rw [UniqueFactorizationMonoid.normalizedFactors_pow,
    UniqueFactorizationMonoid.normalizedFactors_pow] at h1
  have h2 : UniqueFactorizationMonoid.normalizedFactors a
      = UniqueFactorizationMonoid.normalizedFactors b := by
    ext p
    have h3 := congrArg (Multiset.count p) h1
    rw [Multiset.count_nsmul, Multiset.count_nsmul] at h3
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hh) h3
  exact associated_iff_eq.mp
    ((UniqueFactorizationMonoid.associated_iff_normalizedFactors_eq_normalizedFactors ha hb).mpr h2)

theorem principal_of_root (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K']
    [Algebra K K'] (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (h : ℕ) (hh : h ≠ 0) (c : 𝓞 K)
    (hc : I ^ h = Ideal.span {c}) (z : K') (hz : z ^ h = algebraMap K K' (c : K)) :
    ∃ y : 𝓞 K', y ≠ 0 ∧ y ∈ I.map (algebraMap (𝓞 K) (𝓞 K')) ∧
      |((Algebra.norm ℚ (y : K') : ℚ) : ℝ)| = (I.absNorm : ℝ) ^ Module.finrank K K' := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_zero] at hc
    exact pow_ne_zero h hI hc
  have hcK : (c : K) ≠ 0 := fun h0 => hc0 (RingOfIntegers.ext h0)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hh] at hz
    exact hcK ((map_eq_zero _).mp hz.symm)
  have hint : IsIntegral ℤ z := by
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero hh) ?_
    rw [hz]
    exact (c.2 : IsIntegral ℤ (c : K)).map (IsScalarTower.toAlgHom ℤ K K')
  let y : 𝓞 K' := ⟨z, hint⟩
  have hyz : (y : K') = z := rfl
  have hy0 : y ≠ 0 := fun h0 => hz0 (by rw [← hyz, h0]; rfl)
  have hyc : y ^ h = algebraMap (𝓞 K) (𝓞 K') c := by
    apply RingOfIntegers.ext
    exact (map_pow (algebraMap (𝓞 K') K') y h).trans hz
  have hspan : Ideal.span {y} ^ h = (I.map (algebraMap (𝓞 K) (𝓞 K'))) ^ h := by
    rw [Ideal.span_singleton_pow, hyc, ← Ideal.map_pow, hc, Ideal.map_span, Set.image_singleton]
  have heq : Ideal.span {y} = I.map (algebraMap (𝓞 K) (𝓞 K')) := by
    have hs0 : Ideal.span {y} ≠ ⊥ := by simpa using hy0
    refine ideal_eq_of_pow_eq hh hs0 ?_ hspan
    intro h0
    rw [h0, ← Ideal.zero_eq_bot, zero_pow hh] at hspan
    exact pow_ne_zero h hs0 hspan
  refine ⟨y, hy0, heq ▸ Ideal.mem_span_singleton_self y, ?_⟩
  have hnc : |((Algebra.norm ℚ (c : K) : ℚ) : ℝ)| = (I.absNorm : ℝ) ^ h := by
    have h1 : I.absNorm ^ h = (Algebra.norm ℤ c).natAbs := by
      rw [← map_pow, hc, Ideal.absNorm_span_singleton]
    rw [← Algebra.coe_norm_int]
    have h2 : ((I.absNorm : ℝ)) ^ h = ((Algebra.norm ℤ c).natAbs : ℝ) := by exact_mod_cast h1
    rw [h2, Nat.cast_natAbs]
    simp
  have hN : Algebra.norm ℚ (z ^ h) = (Algebra.norm ℚ (c : K)) ^ Module.finrank K K' := by
    rw [hz, ← Algebra.norm_norm (R := ℚ) (S := K) (A := K'), Algebra.norm_algebraMap, map_pow]
  have hpow : |((Algebra.norm ℚ z : ℚ) : ℝ)| ^ h
      = ((I.absNorm : ℝ) ^ Module.finrank K K') ^ h := by
    rw [← abs_pow, ← Rat.cast_pow, ← map_pow, hN, Rat.cast_pow, abs_pow, hnc, ← pow_mul, ← pow_mul,
      mul_comm]
  exact (pow_left_inj₀ (abs_nonneg _) (by positivity) hh).mp hpow

theorem exists_principal_extension : ∀ (K : Type) [Field K] [NumberField K] (I : Ideal (𝓞 K)),
    I ≠ ⊥ → ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (y : 𝓞 K'),
      y ≠ 0 ∧ y ∈ I.map (algebraMap (𝓞 K) (𝓞 K')) ∧
        |((Algebra.norm ℚ (y : K') : ℚ) : ℝ)| = (I.absNorm : ℝ) ^ Module.finrank K K' := by
  intro K _ _ I hI
  obtain ⟨h, c, hh, hc⟩ := GlobalTheory.UnRep.exists_pow_eq_span_singleton K I hI
  let p : Polynomial K := Polynomial.X ^ h - Polynomial.C (c : K)
  have hdeg : p.degree ≠ 0 := by
    rw [Polynomial.degree_X_pow_sub_C (Nat.pos_of_ne_zero hh)]
    exact_mod_cast hh
  haveI : FiniteDimensional ℚ p.SplittingField := FiniteDimensional.trans ℚ K p.SplittingField
  haveI : NumberField p.SplittingField := NumberField.mk
  obtain ⟨z, hz⟩ := (Polynomial.SplittingField.splits p).exists_eval_eq_zero
    (by rwa [Polynomial.degree_map])
  have hz' : z ^ h = algebraMap K p.SplittingField (c : K) := by
    simpa [p, sub_eq_zero] using hz
  obtain ⟨y, h1, h2, h3⟩ := principal_of_root K p.SplittingField I hI h hh c hc z hz'
  exact ⟨p.SplittingField, inferInstance, inferInstance, inferInstance, y, h1, h2, h3⟩

end GlobalTheory.CompanionTheory.Lines
