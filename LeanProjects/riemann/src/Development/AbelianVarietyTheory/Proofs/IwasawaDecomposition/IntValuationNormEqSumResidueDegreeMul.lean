import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

noncomputable section

namespace GlobalTheory.NormValuation

def exponent {R : Type} [CommRing R] [IsDedekindDomain R] (w : HeightOneSpectrum R) (I : Ideal R) : ℕ :=
  (Associates.mk w.asIdeal).count (Associates.mk I).factors

section
variable {R : Type} [CommRing R] [IsDedekindDomain R] (w : HeightOneSpectrum R)

theorem exponent_mul {I J : Ideal R} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    exponent w (I * J) = exponent w I + exponent w J := by
  unfold exponent
  rw [← Associates.mk_mul_mk, Associates.count_mul (Associates.mk_ne_zero.2 hI)
    (Associates.mk_ne_zero.2 hJ) w.associates_irreducible]

theorem exponent_pow {I : Ideal R} (hI : I ≠ ⊥) (n : ℕ) :
    exponent w (I ^ n) = n * exponent w I := by
  unfold exponent
  rw [Associates.mk_pow, Associates.count_pow (Associates.mk_ne_zero.2 hI) w.associates_irreducible]

theorem exponent_self : exponent w w.asIdeal = 1 :=
  Associates.count_self w.associates_irreducible

theorem exponent_top : exponent w ⊤ = 0 := by
  unfold exponent
  rw [← Ideal.one_eq_top, Associates.mk_one, Associates.factors_one,
    Associates.count_zero w.associates_irreducible]

theorem exponent_prime_of_ne (p : Ideal R) [p.IsPrime] (hp : p ≠ ⊥) (h : p ≠ w.asIdeal) :
    exponent w p = 0 := by
  unfold exponent
  refine Associates.count_eq_zero_of_ne w.associates_irreducible
    (HeightOneSpectrum.associates_irreducible ⟨p, inferInstance, hp⟩) ?_
  intro h1
  exact h (associated_iff_eq.1 (Associates.mk_eq_mk_iff_associated.1 h1)).symm

theorem log_valuation_of_integer (F : Type) [Field F] [Algebra R F] [IsFractionRing R F] (x : R) (hx : x ≠ 0) :
    WithZero.log (w.valuation F (algebraMap R F x)) = -(exponent w (Ideal.span {x}) : ℤ) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap, w.intValuation_if_neg hx, WithZero.log_exp, exponent]

end

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

theorem exponent_relNorm_prime (v : HeightOneSpectrum (𝓞 E)) (s : Finset (HeightOneSpectrum (𝓞 K)))
    (hs : ∀ w, w ∈ s ↔ w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal)
    (p : Ideal (𝓞 K)) [p.IsPrime] (hp : p ≠ ⊥) :
    (exponent v (Ideal.relNorm (𝓞 E) p) : ℤ) =
      ∑ w ∈ s, (w.asIdeal.inertiaDeg (𝓞 E) : ℤ) * (exponent w p : ℤ) := by
  have : p.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hp inferInstance
  have hq : p.under (𝓞 E) ≠ ⊥ := Ideal.under_ne_bot (𝓞 E) hp
  have : (p.under (𝓞 E)).IsMaximal := Ring.DimensionLEOne.maximalOfPrime hq inferInstance
  rw [Ideal.relNorm_eq_pow_of_isMaximal p (p.under (𝓞 E)), exponent_pow v hq]
  by_cases h : p.under (𝓞 E) = v.asIdeal
  · let w0 : HeightOneSpectrum (𝓞 K) := ⟨p, inferInstance, hp⟩
    have hw0 : w0 ∈ s := (hs w0).2 h
    rw [Finset.sum_eq_single w0]
    · rw [h, exponent_self, exponent_self]
      simp [w0]
    · intro w _ hw
      rw [exponent_prime_of_ne w p hp, Nat.cast_zero, mul_zero]
      intro he
      exact hw (HeightOneSpectrum.ext he.symm)
    · intro h'; exact absurd hw0 h'
  · rw [exponent_prime_of_ne v _ hq h, mul_zero, Nat.cast_zero]
    refine (Finset.sum_eq_zero fun w hw => ?_).symm
    rw [exponent_prime_of_ne w p hp, Nat.cast_zero, mul_zero]
    intro he
    apply h
    rw [← (hs w).1 hw, he]

theorem exponent_relNorm (v : HeightOneSpectrum (𝓞 E)) (s : Finset (HeightOneSpectrum (𝓞 K)))
    (hs : ∀ w, w ∈ s ↔ w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal)
    (I : Ideal (𝓞 K)) : I ≠ ⊥ →
    (exponent v (Ideal.relNorm (𝓞 E) I) : ℤ) =
      ∑ w ∈ s, (w.asIdeal.inertiaDeg (𝓞 E) : ℤ) * (exponent w I : ℤ) := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact fun h => absurd rfl h
  | h₂ x hx =>
    intro _
    rw [Ideal.isUnit_iff.1 hx, Ideal.relNorm_top, exponent_top]
    simp [exponent_top]
  | h₃ a p ha hp ih =>
    intro _
    have : p.IsPrime := Ideal.isPrime_of_prime hp
    have hp0 : p ≠ ⊥ := hp.ne_zero
    rw [map_mul, exponent_mul v (Ideal.relNorm_eq_bot_iff.not.2 hp0)
      (Ideal.relNorm_eq_bot_iff.not.2 ha), Nat.cast_add, exponent_relNorm_prime v s hs p hp0, ih ha,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [exponent_mul w hp0 ha, Nat.cast_add, mul_add]

end GlobalTheory.NormValuation

namespace GlobalTheory.NormValuation

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

theorem log_valuation_norm_integer (v : HeightOneSpectrum (𝓞 E)) (s : Finset (HeightOneSpectrum (𝓞 K)))
    (hs : ∀ w, w ∈ s ↔ w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal)
    (x : 𝓞 K) (hx : x ≠ 0) :
    WithZero.log (v.valuation E (Algebra.norm E (algebraMap (𝓞 K) K x))) =
      ∑ w ∈ s, (w.asIdeal.inertiaDeg (𝓞 E) : ℤ) * WithZero.log (w.valuation K (algebraMap (𝓞 K) K x)) := by
  have h1 : algebraMap (𝓞 E) E (Algebra.intNorm (𝓞 E) (𝓞 K) x) = Algebra.norm E (algebraMap (𝓞 K) K x) :=
    Algebra.algebraMap_intNorm (A := 𝓞 E) (K := E) (L := K) (B := 𝓞 K) x
  have h2 : Algebra.intNorm (𝓞 E) (𝓞 K) x ≠ 0 := by
    intro h0
    have : Algebra.norm E (algebraMap (𝓞 K) K x) = 0 := by rw [← h1, h0, map_zero]
    rw [Algebra.norm_eq_zero_iff] at this
    exact hx ((FaithfulSMul.algebraMap_eq_zero_iff (𝓞 K) K).1 this)
  have hI : Ideal.span {x} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  rw [← h1, log_valuation_of_integer v E _ h2, ← Ideal.relNorm_singleton,
    exponent_relNorm v s hs _ hI, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [log_valuation_of_integer w K x hx, mul_neg]

theorem log_valuation_norm (v : HeightOneSpectrum (𝓞 E)) (a : Kˣ) (s : Finset (HeightOneSpectrum (𝓞 K)))
    (hs : ∀ w, w ∈ s ↔ w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal) :
    WithZero.log (v.valuation E (Algebra.norm E (a : K))) =
      ∑ w ∈ s, (w.asIdeal.inertiaDeg (𝓞 E) : ℤ) * WithZero.log (w.valuation K (a : K)) := by
  obtain ⟨b, c, hc, h⟩ := IsFractionRing.div_surjective (A := 𝓞 K) (a : K)
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hb0 : b ≠ 0 := by
    rintro rfl
    apply a.ne_zero
    rw [← h, map_zero, zero_div]
  have hK : ∀ y : 𝓞 K, y ≠ 0 → algebraMap (𝓞 K) K y ≠ 0 := fun y hy =>
    (FaithfulSMul.algebraMap_eq_zero_iff (𝓞 K) K).not.2 hy
  have hN : ∀ y : 𝓞 K, y ≠ 0 → Algebra.norm E (algebraMap (𝓞 K) K y) ≠ 0 := fun y hy =>
    Algebra.norm_ne_zero_iff.2 (hK y hy)
  have hdiv : Algebra.norm E (algebraMap (𝓞 K) K b / algebraMap (𝓞 K) K c) =
      Algebra.norm E (algebraMap (𝓞 K) K b) / Algebra.norm E (algebraMap (𝓞 K) K c) := by
    rw [eq_div_iff (hN c hc0), ← map_mul, div_mul_cancel₀ _ (hK c hc0)]
  rw [← h, hdiv, map_div₀, WithZero.log_div ((Valuation.ne_zero_iff _).2 (hN b hb0))
    ((Valuation.ne_zero_iff _).2 (hN c hc0)), log_valuation_norm_integer v s hs b hb0,
    log_valuation_norm_integer v s hs c hc0, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [map_div₀, WithZero.log_div ((Valuation.ne_zero_iff _).2 (hK b hb0))
    ((Valuation.ne_zero_iff _).2 (hK c hc0)), mul_sub]

end GlobalTheory.NormValuation

theorem GlobalTheory.NormValuation.log_valuation_norm_eq_sum : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (v : HeightOneSpectrum (𝓞 E)) (a : Kˣ) (s : Finset (HeightOneSpectrum (𝓞 K))), (∀ w, w ∈ s ↔ w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal) → WithZero.log (v.valuation E (Algebra.norm E (a : K))) = ∑ w ∈ s, (w.asIdeal.inertiaDeg (𝓞 E) : ℤ) * WithZero.log (w.valuation K (a : K)) :=
  fun _ _ _ _ _ _ _ v a s hs => GlobalTheory.NormValuation.log_valuation_norm v a s hs
