import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.PatchOneAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormMemOfUnderEq

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RealGal
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.V.Af.Bc (res)
open UpperTheory.Gal.Int.Core

private theorem exists_intCast_eq_of_card_prime (k : Type) [Ring k] (p : ℕ) (hp : Nat.Prime p) (hk : Nat.card k = p)
    (y : k) : ∃ n : ℤ, (n : k) = y := by
  haveI : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact hp.ne_zero)
  haveI : Nontrivial k := by
    rw [← Finite.one_lt_card_iff_nontrivial, hk]; exact hp.one_lt
  have htop : AddSubgroup.zmultiples (1 : k) = ⊤ := by
    apply AddSubgroup.eq_top_of_card_eq
    have hdvd := AddSubgroup.card_addSubgroup_dvd_card (AddSubgroup.zmultiples (1 : k))
    rw [hk] at hdvd ⊢
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · exfalso
      rw [AddSubgroup.card_eq_one] at h
      have : (1 : k) ∈ AddSubgroup.zmultiples (1 : k) := AddSubgroup.mem_zmultiples 1
      rw [h] at this
      exact one_ne_zero this
    · exact h
  have hy : y ∈ AddSubgroup.zmultiples (1 : k) := by rw [htop]; trivial
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
  exact ⟨n, by simpa using hn⟩

private theorem complexConj_eq_neg_of_sq_eq_neg_natCast (E : Type) [Field E] [NumberField E] [IsCMField E] (d : ℕ) (hd0 : 0 < d)
    (x : E) (hx : x ^ 2 = -(d : E)) : IsCMField.complexConj E x = -x := by
  obtain ⟨φ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj, map_neg]
  have h2 : (φ x) ^ 2 = -(d : ℂ) := by rw [← map_pow, hx]; simp
  have hre : (φ x).re = 0 := by
    have him := congrArg Complex.im h2
    have hre2 := congrArg Complex.re h2
    simp [pow_two] at him hre2
    have hm : (φ x).re * (φ x).im = 0 := by linarith
    rcases mul_eq_zero.mp hm with h | h
    · exact h
    · rw [h] at hre2
      have : (0:ℝ) < d := by exact_mod_cast hd0
      nlinarith [sq_nonneg (φ x).re]
  apply Complex.ext <;> simp [hre]

private theorem prime_dvd_of_intCast_mem_of_natCast_mem {R : Type} [CommRing R] (P : Ideal R) [P.IsPrime] (q : ℕ)
    (hq : Nat.Prime q) (hqP : (q : R) ∈ P) (m : ℤ) (hm : (m : R) ∈ P) : (q : ℤ) ∣ m := by
  by_contra h
  have hirr : Irreducible (q : ℤ) := (Nat.prime_iff_prime_int.mp hq).irreducible
  obtain ⟨a, b, hab⟩ := (Irreducible.coprime_iff_not_dvd hirr).mpr h
  have h1 : ((a * q + b * m : ℤ) : R) ∈ P := by
    push_cast
    exact P.add_mem (P.mul_mem_left _ hqP) (P.mul_mem_left _ hm)
  rw [hab, Int.cast_one] at h1
  exact (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one P).mpr h1)

private theorem isSquare_neg_padic_of_dvd_sq_add_of_not_dvd (q : ℕ) [Fact q.Prime] (d n : ℤ) (h1 : (q : ℤ) ∣ n ^ 2 + d)
    (h2 : ¬ (q : ℤ) ∣ 2 * n) : IsSquare (-(d : ℚ_[q])) := by
  have hnorm : ‖(Polynomial.X ^ 2 + Polynomial.C d : Polynomial ℤ).aeval (n : ℤ_[q])‖ <
      ‖(Polynomial.X ^ 2 + Polynomial.C d : Polynomial ℤ).derivative.aeval (n : ℤ_[q])‖ ^ 2 := by
    have e1 : (Polynomial.X ^ 2 + Polynomial.C d : Polynomial ℤ).aeval (n : ℤ_[q]) =
        ((n ^ 2 + d : ℤ) : ℤ_[q]) := by
      simp
    have e2 : (Polynomial.X ^ 2 + Polynomial.C d : Polynomial ℤ).derivative.aeval (n : ℤ_[q]) =
        ((2 * n : ℤ) : ℤ_[q]) := by
      simp [Polynomial.derivative_X_pow]
      left
      exact map_ofNat _ 2
    rw [e1, e2]
    have a1 : ‖((n ^ 2 + d : ℤ) : ℤ_[q])‖ < 1 := (PadicInt.norm_int_lt_one_iff_dvd _).mpr h1
    have a2 : ‖((2 * n : ℤ) : ℤ_[q])‖ = 1 := by
      have hle : ‖((2 * n : ℤ) : ℤ_[q])‖ ≤ 1 := PadicInt.norm_le_one _
      have hnlt : ¬ ‖((2 * n : ℤ) : ℤ_[q])‖ < 1 :=
        fun h => h2 ((PadicInt.norm_int_lt_one_iff_dvd _).mp h)
      linarith [not_lt.mp hnlt]
    rw [a2]
    simpa using a1
  obtain ⟨z, hz, -⟩ := hensels_lemma hnorm
  refine ⟨(z : ℚ_[q]), ?_⟩
  have hz' : z ^ 2 + (d : ℤ_[q]) = 0 := by simpa using hz
  have hz'' : ((z ^ 2 + (d : ℤ_[q]) : ℤ_[q]) : ℚ_[q]) = 0 := by rw [hz']; simp
  push_cast at hz''
  linear_combination -hz''

theorem UpperTheory.Gal.Int.Core.oneUs_holds :
    OneUs := by
  unfold OneUs
  intro E _ _ _ d hd
  obtain ⟨hd0, x, hx⟩ := hd
  have hint : IsIntegral ℤ x := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [hx]
    apply IsIntegral.neg
    have := isIntegral_algebraMap (R := ℤ) (A := E) (x := (d:ℤ))
    simpa using this
  let xo : 𝓞 E := ⟨x, hint⟩
  have hxo : xo ^ 2 = -(d : 𝓞 E) := by
    apply RingOfIntegers.ext
    push_cast
    exact hx
  let cO := RingOfIntegers.mapAlgEquiv (IsCMField.complexConj E)
  have hcxo : cO xo = -xo := by
    apply RingOfIntegers.ext
    change IsCMField.complexConj E x = -x
    exact complexConj_eq_neg_of_sq_eq_neg_natCast E d hd0 x hx
  have hne : Ideal.span {((2 * d : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (by omega : 2 * d ≠ 0)
  rw [Filter.eventually_cofinite]
  refine (Ideal.finite_factors hne).subset ?_
  intro w hw
  simp only [Set.mem_setOf_eq] at hw ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  by_contra h2d
  apply hw
  intro hprime
  obtain ⟨n, hn⟩ := exists_intCast_eq_of_card_prime (𝓞 E ⧸ w.asIdeal) (normV w) hprime rfl
    (Ideal.Quotient.mk _ xo)
  have hxn : xo - n ∈ w.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hn]
    simp
  unfold UsPl
  refine ⟨?_, ?_⟩
  · unfold IsSplitAt
    let u : HeightOneSpectrum (𝓞 E) :=
      { asIdeal := w.asIdeal.comap (cO.toRingEquiv : 𝓞 E →+* 𝓞 E)
        isPrime := Ideal.comap_isPrime _ _
        ne_bot := by
          intro h
          apply w.ne_bot
          have := Ideal.map_comap_of_surjective (cO.toRingEquiv : 𝓞 E →+* 𝓞 E)
            cO.surjective w.asIdeal
          rw [h, Ideal.map_bot] at this
          exact this.symm }
    refine ⟨u, ?_, ?_⟩
    · intro huw
      have hmem : ∀ a, a ∈ w.asIdeal → cO a ∈ w.asIdeal := by
        intro a ha
        have : a ∈ u.asIdeal := by rw [huw]; exact ha
        exact this
      have h1 := hmem _ hxn
      rw [map_sub, hcxo, map_intCast] at h1
      have h2 : 2 * xo ∈ w.asIdeal := by
        have := w.asIdeal.sub_mem hxn h1
        convert this using 1
        ring
      apply h2d
      have h3 := w.asIdeal.mul_mem_right (-xo) h2
      convert h3 using 1
      have : ((2 * d : ℕ) : 𝓞 E) = -2 * (-(d : 𝓞 E)) := by push_cast; ring
      rw [this, ← hxo]
      ring
    · apply HeightOneSpectrum.ext
      change Ideal.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))
          (Ideal.comap (cO.toRingEquiv : 𝓞 E →+* 𝓞 E) w.asIdeal) =
        Ideal.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) w.asIdeal
      rw [Ideal.comap_comap]
      congr 1
      ext y
      exact congrArg Subtype.val (cO.commutes y)
  · intro q hq hqw
    haveI := Fact.mk hq
    unfold SqAt
    have hm : ((n ^ 2 + d : ℤ) : 𝓞 E) ∈ w.asIdeal := by
      have : ((n ^ 2 + d : ℤ) : 𝓞 E) = (xo - n) * (-(xo + n)) := by
        push_cast
        linear_combination hxo
      rw [this]
      exact w.asIdeal.mul_mem_right _ hxn
    have hdiv := prime_dvd_of_intCast_mem_of_natCast_mem w.asIdeal q hq hqw _ hm
    have hq2d : ¬ (q : ℤ) ∣ 2 * d := by
      rintro ⟨k, hk⟩
      apply h2d
      have : ((2 * d : ℕ) : 𝓞 E) = (q : 𝓞 E) * (k : 𝓞 E) := by
        have := congrArg (fun z : ℤ => (z : 𝓞 E)) hk
        push_cast at this ⊢
        exact this
      rw [this]
      exact w.asIdeal.mul_mem_right _ hqw
    have h2n : ¬ (q : ℤ) ∣ 2 * n := by
      intro h
      apply hq2d
      have e : (2 * d : ℤ) = 2 * (n ^ 2 + d) - (2 * n) * n := by ring
      rw [e]
      exact dvd_sub (dvd_mul_of_dvd_right hdiv 2) (dvd_mul_of_dvd_left h n)
    exact isSquare_neg_padic_of_dvd_sq_add_of_not_dvd q (d : ℤ) n hdiv h2n
