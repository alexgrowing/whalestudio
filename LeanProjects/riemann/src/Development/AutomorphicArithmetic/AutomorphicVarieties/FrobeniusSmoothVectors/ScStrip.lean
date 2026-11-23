import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharInertiaSurjectiveStatement

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem valuation_not_lt_one_of_coprime {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {l N : ℕ} (h : Nat.Coprime l N)
    (hl : B.valuation (l : Ω) < 1) : ¬ B.valuation (N : Ω) < 1 := by
  intro hN
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  have e : (a : Ω) * (l : Ω) + (b : Ω) * (N : Ω) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  have key : ∀ (c : ℤ) (x : Ω), B.valuation x < 1 → B.valuation ((c : Ω) * x) < 1 := by
    intro c x hx
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ((B.valuation_le_one_iff _).2 (intCast_mem B c))) hx
  have := B.valuation.map_add_lt (key a _ hl) (key b _ hN)
  rw [e, map_one] at this
  exact lt_irrefl _ this

private theorem eq_idempotent_mul_add_of_mul_sub_eq {Ω : Type} [Field Ω] {a b : ℕ} (h : Nat.Coprime a b) {x y : Ω} (hy : y ≠ 0)
    (ha : x ^ a = y ^ a) (hb : x ^ b = y ^ b) : x = y := by
  have h1 : (x / y) ^ a = 1 := by rw [div_pow, ha, div_self (pow_ne_zero _ hy)]
  have h2 : (x / y) ^ b = 1 := by rw [div_pow, hb, div_self (pow_ne_zero _ hy)]
  have h3 : (x / y) ^ (Nat.gcd a b) = 1 := pow_gcd_eq_one.2 ⟨h1, h2⟩
  rw [h.gcd_eq_one, pow_one] at h3
  exact (div_eq_one_iff_eq hy).1 h3

theorem UpperTheory.V.Fr.sc_strip :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (C : Type) [Group C] (χ : G ℚ Ω →* C) (r N : ℕ), N ≠ 0 → ¬ l ∣ N → Af.KillsMu (l ^ r * N) χ → ∀ B : ValuationSubring Ω, B.valuation (l : Ω) < 1 → Ine (F := ℚ) B ≤ χ.ker → Af.KillsMu N χ := by
  intro Ω _ _ _ l hl C _ χ r N hN hlN hχ B hB hI s hs
  haveI : NeZero N := ⟨hN⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => by
    haveI : NeZero ((l ^ i : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (pow_ne_zero _ hl.out.ne_zero)⟩
    infer_instance
  have hcop : Nat.Coprime l N := (Nat.Prime.coprime_iff_not_dvd hl.out).2 hlN
  obtain ⟨σ, hσ, hc⟩ := GlobalTheory.T.cyclotomicChar_inertia_surjective Ω l B hB (cycZ ℚ Ω l s)
  have hker := (UpperTheory.V.Chr.clsFacts ℚ Ω N).2.2.2.2 B (valuation_not_lt_one_of_coprime B hcop hB) hσ
  have hone := (UpperTheory.V.Chr.clsFacts ℚ Ω N).2.2.2.2 B (valuation_not_lt_one_of_coprime B hcop hB) (Ine (F := ℚ) B).one_mem
  have hσN : ∀ ζ : Ω, ζ ^ N = 1 → σ ζ = ζ := by
    intro ζ hζ
    have h1 := UpperTheory.V.Chr.cls_spec (k := ℚ) N σ ζ hζ
    have h2 := UpperTheory.V.Chr.cls_spec (k := ℚ) N 1 ζ hζ
    rw [MonoidHom.mem_ker] at hker hone
    rw [hker] at h1
    rw [hone] at h2
    rw [h1, ← h2]
    rfl
  have hσl : ∀ ζ : Ω, ζ ^ l ^ r = 1 → s ζ = σ ζ := by
    intro ζ hζ
    have h1 : s ζ = ζ ^ ((cycZ ℚ Ω l s).val.toZModPow r).val :=
      cyclotomicCharacter.spec l s.toRingEquiv ζ hζ
    have h2 : σ ζ = ζ ^ ((cycZ ℚ Ω l σ).val.toZModPow r).val :=
      cyclotomicCharacter.spec l σ.toRingEquiv ζ hζ
    rw [h1, h2, hc]
  have h1 : χ (σ⁻¹ * s) = 1 := by
    refine hχ _ fun ζ hζ => ?_
    have h0 : ζ ≠ 0 := by
      rintro rfl
      rw [zero_pow (mul_ne_zero (pow_ne_zero _ hl.out.ne_zero) hN)] at hζ
      exact zero_ne_one hζ
    have e : s ζ = σ ζ := by
      refine eq_idempotent_mul_add_of_mul_sub_eq (Nat.Coprime.pow_left r hcop) ((map_ne_zero σ).2 h0) ?_ ?_
      · have hz : (ζ ^ l ^ r) ^ N = 1 := by rw [← pow_mul, hζ]
        rw [← map_pow, ← map_pow, hs _ hz, hσN _ hz]
      · have hz : (ζ ^ N) ^ l ^ r = 1 := by rw [← pow_mul, mul_comm, hζ]
        rw [← map_pow, ← map_pow, hσl _ hz]
    rw [AlgEquiv.mul_apply, e, ← AlgEquiv.mul_apply, inv_mul_cancel]
    rfl
  have h2 : χ σ = 1 := hI hσ
  rw [map_mul, map_inv, h2, inv_one, one_mul] at h1
  exact h1
