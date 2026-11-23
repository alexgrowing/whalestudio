import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.MuZeroCong

theorem locK_eq_of_sub_mem : ∀ {R : Ranks} {H : Host R} (P : PiBar H) (W : Omg H) (e : ↥(R.Psi) → ℚ) (j : ℕ) (χ : HChar H.E), IsMu0 P W e j χ → ∀ (k : Fin 2) (w : HeightOneSpectrum (𝓞 H.E)), P.Div k w → ∀ (u : 𝓞 H.E) (hu : (u : H.E) ≠ 0) (a : ℕ) (ha : a.Coprime (H.g k)), u - (a : 𝓞 H.E) ∈ w.asIdeal → χ.locK w (Units.mk0 (u : H.E) hu) = (W.om k (ZMod.unitOfCoprime a ha) ^ (2 * (j + 1)))⁻¹ := by
  intro R H P W e j χ hχ k w hw u hu a ha hua
  have hg : ((H.g k : ℕ) : 𝓞 H.E) ∈ w.asIdeal := by
    have h1 := P.pb_over k
    rw [← hw, HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast] at h1
    exact h1
  have ha_nm : ((a : ℕ) : 𝓞 H.E) ∉ w.asIdeal := by
    intro haw
    apply w.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have hb := Nat.gcd_eq_gcd_ab a (H.g k)
    rw [Nat.Coprime.gcd_eq_one ha, Nat.cast_one] at hb
    have h1 : (1 : 𝓞 H.E) = ((a : ℕ) : 𝓞 H.E) * ((Nat.gcdA a (H.g k) : ℤ) : 𝓞 H.E)
        + ((H.g k : ℕ) : 𝓞 H.E) * ((Nat.gcdB a (H.g k) : ℤ) : 𝓞 H.E) := by
      have := congrArg (Int.cast : ℤ → 𝓞 H.E) hb
      push_cast at this
      exact this
    rw [h1]
    exact add_mem (Ideal.mul_mem_right _ _ haw) (Ideal.mul_mem_right _ _ hg)
  have hu_nm : u ∉ w.asIdeal := by
    intro huw
    apply ha_nm
    have := Ideal.sub_mem _ huw hua
    simpa using this
  have ha0 : ((a : ℕ) : H.E) ≠ 0 := by
    intro h0
    apply ha_nm
    have : ((a : ℕ) : 𝓞 H.E) = 0 := by
      apply RingOfIntegers.coe_injective
      push_cast
      exact h0
    rw [this]
    exact zero_mem _
  set A : H.Eˣ := Units.mk0 ((a : ℕ) : H.E) ha0 with hA
  set U : H.Eˣ := Units.mk0 (u : H.E) hu with hU
  have hsplit : U = (U * A⁻¹) * A := by group
  have hval : ∀ r : 𝓞 H.E, Valued.v (((r : H.E)) : w.adicCompletion H.E) = w.intValuation r := by
    intro r
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact w.valuation_of_algebraMap r
  have hYval : ((U * A⁻¹ : H.Eˣ) : H.E) = (u : H.E) * ((a : ℕ) : H.E)⁻¹ := by
    simp [hA, hU]
  have hvu : w.intValuation u = 1 := (w.intValuation_eq_one_iff_mem_primeCompl u).mpr hu_nm
  have hva : w.intValuation ((a : ℕ) : 𝓞 H.E) = 1 :=
    (w.intValuation_eq_one_iff_mem_primeCompl _).mpr ha_nm
  have hvd : w.intValuation (u - ((a : ℕ) : 𝓞 H.E)) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    rw [w.intValuation_le_pow_iff_mem, pow_one]
    exact hua
  have hacoe : (((a : ℕ) : 𝓞 H.E) : H.E) = ((a : ℕ) : H.E) := by push_cast; rfl
  have hv' : ∀ x : H.E, Valued.v (algebraMap H.E (w.adicCompletion H.E) x) = w.valuation H.E x :=
    fun x => w.valuedAdicCompletion_eq_valuation' x
  have hY1 : χ.locK w (U * A⁻¹) = 1 := by
    show χ.loc w (atFin w (U * A⁻¹)) = 1
    apply hχ.tame w
    · show Valued.v (algebraMap H.E (w.adicCompletion H.E) ((U * A⁻¹ : H.Eˣ) : H.E)) = 1
      rw [hv', hYval, Valuation.map_mul, Valuation.map_inv, ← hacoe]
      rw [show (u : H.E) = algebraMap (𝓞 H.E) H.E u from rfl,
        show (((a : ℕ) : 𝓞 H.E) : H.E) = algebraMap (𝓞 H.E) H.E ((a : ℕ) : 𝓞 H.E) from rfl,
        w.valuation_of_algebraMap, w.valuation_of_algebraMap, hvu, hva, inv_one, mul_one]
    · show Valued.v (algebraMap H.E (w.adicCompletion H.E) ((U * A⁻¹ : H.Eˣ) : H.E) - 1) ≤ _
      rw [← map_one (algebraMap H.E (w.adicCompletion H.E)), ← map_sub, hv', hYval]
      have hq : (u : H.E) * ((a : ℕ) : H.E)⁻¹ - 1
          = algebraMap (𝓞 H.E) H.E (u - ((a : ℕ) : 𝓞 H.E)) * (algebraMap (𝓞 H.E) H.E ((a : ℕ) : 𝓞 H.E))⁻¹ := by
        rw [map_sub, map_natCast]
        field_simp
      rw [hq, Valuation.map_mul, Valuation.map_inv, w.valuation_of_algebraMap, w.valuation_of_algebraMap, hva,
        inv_one, mul_one]
      exact hvd
  have hAv := hχ.atg k w hw a ha A rfl
  rw [hsplit, map_mul, hY1, one_mul, hAv]

end GlobalTheory.MuZeroCong
