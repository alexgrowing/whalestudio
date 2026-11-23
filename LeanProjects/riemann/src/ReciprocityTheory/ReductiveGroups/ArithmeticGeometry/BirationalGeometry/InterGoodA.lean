import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.Geo

open Ideal

theorem exists_ltSeries_lift {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S)) :
    ∀ (n : ℕ) (p : LTSeries (PrimeSpectrum R)), p.length = n →
      ∃ q : LTSeries (PrimeSpectrum S), q.length = n ∧
        q.last.asIdeal.comap (algebraMap R S) = p.last.asIdeal := by
  intro n
  induction n with
  | zero =>
    intro p _
    have hker : RingHom.ker (algebraMap R S) ≤ p.last.asIdeal := by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
      exact bot_le
    obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.last.asIdeal (⊥ : Ideal S)
      (by rw [← RingHom.ker_eq_comap_bot]; exact hker)
    exact ⟨RelSeries.singleton _ ⟨Q, hQ⟩, rfl, hQc⟩
  | succ n ih =>
    intro p hp
    obtain ⟨q', hq'len, hq'c⟩ := ih p.eraseLast (by
      first
      | (show p.length - 1 = n; omega)
      | simp [hp])
    have hlt : p.eraseLast.last < p.last := p.eraseLast_last_rel_last (by omega)
    obtain ⟨Q, hQle, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime
      p.last.asIdeal q'.last.asIdeal (by rw [hq'c]; exact hlt.le)
    have hlt' : q'.last.asIdeal < Q := by
      refine lt_of_le_of_ne hQle fun h => hlt.ne ?_
      ext1
      rw [← hq'c, h, hQc]
    refine ⟨q'.snoc ⟨Q, hQ⟩ hlt', ?_, ?_⟩
    · show q'.length + 1 = n + 1
      rw [hq'len]
    · first
      | (rw [RelSeries.last_snoc]; exact hQc)
      | simpa using hQc

theorem le_ringKrullDim_of_isIntegral {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : f.IsIntegral) (hinj : Function.Injective f) (n : ℕ)
    (h : (n : WithBot ℕ∞) ≤ ringKrullDim R) : (n : WithBot ℕ∞) ≤ ringKrullDim S := by
  letI := f.toAlgebra
  haveI : Algebra.IsIntegral R S := ⟨hf⟩
  obtain ⟨p, hp⟩ := Order.le_krullDim_iff.mp h
  obtain ⟨q, hq, -⟩ := exists_ltSeries_lift hinj n p hp
  exact Order.le_krullDim_iff.mpr ⟨q, hq⟩

theorem int_isJacobsonRing : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases hb : P = ⊥
  · subst hb
    refine le_antisymm (fun x hx => ?_) bot_le
    rw [Ideal.mem_jacobson_bot] at hx
    have h1 := Int.isUnit_iff.mp (by simpa using hx 1)
    have h2 := Int.isUnit_iff.mp (hx 2)
    rw [Ideal.mem_bot]
    omega
  · haveI : P.IsMaximal := hP.isMaximal hb
    exact Ideal.jacobson_eq_self_of_isMaximal

theorem exists_gt_of_comap_int_eq_bot {σ A : Type*} [Finite σ] [CommRing A]
    (g : MvPolynomial σ ℤ →+* A) (hg : Function.Surjective g) (p : Ideal A) (hp : p.IsPrime)
    (hb : p.comap (g.comp MvPolynomial.C) = ⊥) : ∃ q : Ideal A, q.IsPrime ∧ p < q := by
  haveI := int_isJacobsonRing
  have hnm : ¬ p.IsMaximal := by
    intro hm
    haveI := hm
    letI : Field (A ⧸ p) := Ideal.Quotient.field p
    let f : MvPolynomial σ ℤ →+* A ⧸ p := (Ideal.Quotient.mk p).comp g
    have hf : Function.Surjective f := Ideal.Quotient.mk_surjective.comp hg
    have hint : (f.comp MvPolynomial.C).IsIntegral := by
      first
      | exact MvPolynomial.comp_C_integral_of_surjective_of_isJacobsonRing f hf
      | exact Ideal.MvPolynomial.comp_C_integral_of_surjective_of_isJacobsonRing f hf
      | exact MvPolynomial.comp_C_integral_of_surjective_of_isJacobson f hf
    have hinj : Function.Injective (f.comp MvPolynomial.C) := by
      rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
      intro x hx
      rw [RingHom.mem_ker] at hx
      have hx' : x ∈ p.comap (g.comp MvPolynomial.C) := by
        rw [Ideal.mem_comap]
        exact Ideal.Quotient.eq_zero_iff_mem.mp hx
      rw [hb] at hx'
      exact hx'
    letI := (f.comp MvPolynomial.C).toAlgebra
    haveI : Algebra.IsIntegral ℤ (A ⧸ p) := ⟨hint⟩
    have hZ : IsField ℤ := isField_of_isIntegral_of_isField hinj (Field.toIsField (A ⧸ p))
    obtain ⟨y, hy⟩ := hZ.mul_inv_cancel (two_ne_zero : (2 : ℤ) ≠ 0)
    omega
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p hp.ne_top
  refine ⟨m, hm.isPrime, lt_of_le_of_ne hpm ?_⟩
  rintro rfl
  exact hnm hm

theorem succ_le_ringKrullDim_of_isLocalization {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (M : Submonoid A) [IsLocalization M B]
    (hext : ∀ p : Ideal A, p.IsPrime → Disjoint (M : Set A) p → ∃ q : Ideal A, q.IsPrime ∧ p < q)
    (n : ℕ) (h : (n : WithBot ℕ∞) ≤ ringKrullDim B) :
    ((n + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim A := by
  let φ : PrimeSpectrum B → PrimeSpectrum A := fun q => ⟨q.asIdeal.comap (algebraMap A B), inferInstance⟩
  have hsm : StrictMono φ := fun a b hab => by
    refine lt_of_le_of_ne (Ideal.comap_mono hab.le) fun e => hab.ne ?_
    have e' : (φ a).asIdeal = (φ b).asIdeal := congrArg PrimeSpectrum.asIdeal e
    ext1
    rw [← IsLocalization.map_comap M B a.asIdeal, ← IsLocalization.map_comap M B b.asIdeal]
    exact congrArg (Ideal.map (algebraMap A B)) e'
  obtain ⟨p, hp⟩ := Order.le_krullDim_iff.mp h
  let p' := p.map φ hsm
  have hdisj : Disjoint (M : Set A) (p'.last.asIdeal : Set A) :=
    ((IsLocalization.isPrime_iff_isPrime_disjoint M B p.last.asIdeal).mp inferInstance).2
  obtain ⟨q, hq, hlt⟩ := hext p'.last.asIdeal inferInstance hdisj
  have hlen : (p'.snoc ⟨q, hq⟩ hlt).length = n + 1 := by
    show p.length + 1 = n + 1
    rw [hp]
  exact Order.le_krullDim_iff.mpr ⟨_, hlen⟩

end ReciprocityTheory.ChartRestriction.G.Geo
