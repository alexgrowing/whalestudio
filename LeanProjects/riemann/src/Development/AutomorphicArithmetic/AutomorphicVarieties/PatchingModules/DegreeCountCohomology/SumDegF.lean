import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.sumDegF :
    ∀ (l : ℕ) [Fact l.Prime] (F : Type) [Field F] [NumberField F], ∑ᶠ v : {v : HeightOneSpectrum (𝓞 F) // ((l : ℕ) : 𝓞 F) ∈ v.asIdeal}, locDeg v.1 = Module.finrank ℚ F := by
  intro l _ F _ _
  classical
  have hl : l.Prime := Fact.out
  let p : Ideal ℤ := Ideal.span {(l : ℤ)}
  haveI hpmax : p.IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible
  have hp0 : p ≠ ⊥ := by
    simp only [p, ne_eq, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact hl.ne_zero
  let e1 : {v : HeightOneSpectrum (𝓞 F) // ((l : ℕ) : 𝓞 F) ∈ v.asIdeal} ≃
      {v : HeightOneSpectrum (𝓞 F) // v.asIdeal ∣ Ideal.map (algebraMap ℤ (𝓞 F)) p} :=
    Equiv.subtypeEquivRight (fun v => by
      rw [Ideal.dvd_iff_le, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem,
        map_natCast])
  let e := e1.trans (HeightOneSpectrum.equivPrimesOver (𝓞 F) hp0)
  have h1 : ∑ᶠ v : {v : HeightOneSpectrum (𝓞 F) // ((l : ℕ) : 𝓞 F) ∈ v.asIdeal}, locDeg v.1
      = ∑ᶠ q : p.primesOver (𝓞 F), q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
    rw [← finsum_comp_equiv e]
    rfl
  rw [h1, finsum_eq_sum_of_fintype, Ideal.sum_ramification_inertia_eq_finrank,
    NumberField.RingOfIntegers.rank]
