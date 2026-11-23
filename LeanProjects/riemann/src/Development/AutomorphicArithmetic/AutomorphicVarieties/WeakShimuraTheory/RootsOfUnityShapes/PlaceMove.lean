import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.PlacesQ

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
open scoped Pointwise

private theorem prime_p (l : ℕ) [hl : Fact l.Prime] : Prime ((l : ℕ) : 𝓞 ℚ) := by
  have h : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl.out
  have e : Rat.ringOfIntegersEquiv.symm (l : ℤ) = ((l : ℕ) : 𝓞 ℚ) := by simp
  rw [← e]
  exact (MulEquiv.prime_iff (Rat.ringOfIntegersEquiv.symm : ℤ ≃* 𝓞 ℚ)).mpr h

private theorem exists_move {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    (A A' : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) (hA' : A'.valuation ((l : ℕ) : Ω) < 1) :
    ∃ g : G ℚ Ω, ∀ x, g x ∈ A ↔ x ∈ A' := by
  have hpr : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : l.Prime)
  have key : ∀ B : ValuationSubring Ω, B.valuation ((l : ℕ) : Ω) < 1 →
      ∀ n : ℤ, B.valuation (n : Ω) < 1 ↔ (l : ℤ) ∣ n := by
    intro B hB n
    have hle : ∀ m : ℤ, B.valuation (m : Ω) ≤ 1 := by
      intro m
      have := B.valuation_le_one (m : B)
      simpa using this
    have hB' : B.valuation ((l : ℤ) : Ω) < 1 := by simpa using hB
    constructor
    · intro hn
      by_contra hd
      obtain ⟨a, b, hab⟩ := hpr.irreducible.coprime_iff_not_dvd.mpr hd
      have h1 : B.valuation ((a : Ω) * (l : ℤ)) < 1 := by
        rw [map_mul]
        calc B.valuation (a : Ω) * B.valuation ((l : ℤ) : Ω) ≤ 1 * B.valuation ((l : ℤ) : Ω) :=
              mul_le_mul_left (hle a) _
          _ < 1 := by rwa [one_mul]
      have h2 : B.valuation ((b : Ω) * n) < 1 := by
        rw [map_mul]
        calc B.valuation (b : Ω) * B.valuation (n : Ω) ≤ 1 * B.valuation (n : Ω) :=
              mul_le_mul_left (hle b) _
          _ < 1 := by rwa [one_mul]
      have h3 := Valuation.map_add_lt _ h1 h2
      have e : ((a : Ω) * (l : ℤ) + (b : Ω) * n) = 1 := by
        exact_mod_cast congrArg (fun z : ℤ => (z : Ω)) hab
      rw [e, map_one] at h3
      exact lt_irrefl _ h3
    · rintro ⟨m, rfl⟩
      rw [Int.cast_mul, map_mul]
      calc B.valuation ((l : ℤ) : Ω) * B.valuation (m : Ω) ≤ B.valuation ((l : ℤ) : Ω) * 1 :=
            mul_le_mul_right (hle m) _
        _ < 1 := by rwa [mul_one]
  have hne : ((l : ℕ) : 𝓞 ℚ) ≠ 0 := (prime_p l).ne_zero
  let v : HeightOneSpectrum (𝓞 ℚ) :=
    ⟨Ideal.span {((l : ℕ) : 𝓞 ℚ)}, (Ideal.span_singleton_prime hne).mpr (prime_p l),
      by simpa [Ideal.span_singleton_eq_bot] using hne⟩
  have hpl : ∀ B : ValuationSubring Ω, B.valuation ((l : ℕ) : Ω) < 1 → IsPlaceOver B v := by
    intro B hB x
    have hx : algebraMap ℚ Ω (x : ℚ) = ((Rat.ringOfIntegersEquiv x : ℤ) : Ω) := by
      rw [← map_intCast (algebraMap ℚ Ω), Rat.ringOfIntegersEquiv_apply_coe]
    rw [hx, key B hB]
    change _ ↔ x ∈ Ideal.span {((l : ℕ) : 𝓞 ℚ)}
    rw [Ideal.mem_span_singleton, ← map_dvd_iff Rat.ringOfIntegersEquiv, map_natCast]
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver (hpl A' hA') (hpl A hA)
  refine ⟨σ, fun x => ?_⟩
  rw [← hσ, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
    ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

theorem UpperTheory.V.Ws.Rq.placeMove :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω) [NumberField F] (p : ℕ), p.Prime →
      ∀ A A' : ValuationSubring Ω, A.valuation (p : Ω) < 1 → A'.valuation (p : Ω) < 1 → ∃ g : G ℚ Ω, (∀ x, g x ∈ A ↔ x ∈ A') ∧
        (∀ s ∈ Dec (F := F) A, g⁻¹ * resQ F s * g ∈ Dec (F := ℚ) A') ∧ ∀ s ∈ Ine (F := F) A, g⁻¹ * resQ F s * g ∈ Ine (F := ℚ) A' := by
  intro Ω _ _ _ F _ p hp A A' hA hA'
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_move p A A' hA hA'
  have hL : UpperTheory.V.IsLift (RingEquiv.refl ℚ) (g : Ω ≃+* Ω) := fun x => by simp
  have hc : ∀ t : G ℚ Ω, UpperTheory.V.conjGal hL t = g⁻¹ * t * g := by
    intro t
    ext x
    rw [UpperTheory.V.conjGal_apply]
    rfl
  have hsm : ∀ s : G F Ω, resQ F s • A = s • A := by
    intro s
    ext x
    simp only [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  refine ⟨g, hg, fun s hs => ?_, fun s hs => ?_⟩
  · rw [← hc]
    apply UpperTheory.V.conjGal_mem_Dec hL hg
    rw [mem_Dec] at hs ⊢
    rw [hsm, hs]
  · rw [← hc]
    apply UpperTheory.V.conjGal_mem_Ine hL hg
    rw [mem_Ine] at hs ⊢
    obtain ⟨h1, h2⟩ := hs
    refine ⟨?_, h2⟩
    rw [MulAction.mem_stabilizer_iff] at h1 ⊢
    rw [hsm, h1]
