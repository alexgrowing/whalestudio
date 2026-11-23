import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowValuationLtOfIntegralAlgClosurePlaceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TwoPlaces

theorem exists_deep_one_sub :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A A' : ValuationSubring Ω)
      (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A P → IsPlaceOver (F := E) A' P → A ≠ A' →
      ∀ c : Ω, IsIntegral ℤ c → c ≠ 0 →
        ∃ e : Ω, IsIntegral ℤ e ∧ A.valuation e < A.valuation c ∧ A'.valuation (1 - e) < 1 := by
  intro E Ω _ _ _ _ _ A A' P hA hA' hne c hc hc0
  have hQ : (primeBelow (F := E) A).under (𝓞 E) = P.asIdeal := under_primeBelow hA
  have hQ' : (primeBelow (F := E) A').under (𝓞 E) = P.asIdeal := under_primeBelow hA'
  haveI : (primeBelow (F := E) A).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := 𝓞 E) _
      (by change (Ideal.under (𝓞 E) (primeBelow (F := E) A)).IsMaximal; rw [hQ]; exact P.isMaximal)
  haveI : (primeBelow (F := E) A').IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := 𝓞 E) _
      (by change (Ideal.under (𝓞 E) (primeBelow (F := E) A')).IsMaximal; rw [hQ']; exact P.isMaximal)
  have hQne : primeBelow (F := E) A ≠ primeBelow (F := E) A' := by
    intro h
    apply hne
    refine eq_of_valuation_lt_one_iff E fun b hb => ?_
    have hb' : IsIntegral (𝓞 E) b := hb.tower_top
    have := congrArg (fun I : Ideal (IntCl E Ω) => (⟨b, hb'⟩ : IntCl E Ω) ∈ I) h
    simpa [mem_primeBelow] using this
  have hnle : ¬ primeBelow (F := E) A ≤ primeBelow (F := E) A' := fun h =>
    hQne (Ideal.IsMaximal.eq_of_le inferInstance (Ideal.IsPrime.ne_top inferInstance) h)
  obtain ⟨x, hxQ, hxQ'⟩ := SetLike.not_le_iff_exists.mp hnle
  rw [mem_primeBelow] at hxQ
  obtain ⟨k, hk⟩ := GlobalTheory.T.exists_pow_valuation_lt_of_integral_algClosure_place E Ω A P hA (x : Ω) c (isIntegral_int_of_isIntegral x.2) hc hc0 hxQ
  have hxk : x ^ k ∉ primeBelow (F := E) A' := fun h => hxQ' (Ideal.IsPrime.mem_of_pow_mem inferInstance k h)
  obtain ⟨y, i, hi, hyi⟩ := Ideal.IsMaximal.exists_inv inferInstance hxk
  refine ⟨((y * x ^ k : IntCl E Ω) : Ω), isIntegral_int_of_isIntegral (y * x ^ k).2, ?_, ?_⟩
  · rw [MulMemClass.coe_mul, Valuation.map_mul, SubmonoidClass.coe_pow, Valuation.map_pow]
    calc A.valuation (y : Ω) * A.valuation (x : Ω) ^ k ≤ 1 * A.valuation (x : Ω) ^ k :=
          mul_le_mul_left (valuation_le_one_intCl A y) _
      _ < A.valuation c := by rw [one_mul]; exact hk
  · have e1 : (1 : Ω) - ((y * x ^ k : IntCl E Ω) : Ω) = (i : Ω) := by
      have := congrArg (fun z : IntCl E Ω => (z : Ω)) hyi
      simp only [AddMemClass.coe_add, OneMemClass.coe_one] at this
      rw [← this]; ring
    rw [e1]
    exact hi

end GlobalTheory.TwoPlaces
