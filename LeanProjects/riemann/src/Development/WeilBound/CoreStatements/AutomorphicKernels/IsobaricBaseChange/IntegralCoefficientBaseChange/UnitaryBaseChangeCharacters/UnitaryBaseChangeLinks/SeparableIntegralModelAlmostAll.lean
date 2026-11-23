import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.LocalTwistContinuousInvolutionIntegralProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AevalRootEqZeroIff

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GoodPlaces

theorem eventually_valued_le_one {E : Type} [Field E] [NumberField E] (x : E) :
    ∀ᶠ w in Filter.cofinite (α := HeightOneSpectrum (𝓞 E)),
      Valued.v (algebraMap E (w.adicCompletion E) x) ≤ 1 := by
  have h := HeightOneSpectrum.Support.finite (𝓞 E) x
  rw [Filter.eventually_cofinite]
  refine h.subset ?_
  intro w hw
  simp only [Set.mem_setOf_eq, not_le] at hw ⊢
  have e : Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := E) w x
  rwa [e] at hw

theorem eventually_coeffs_integral {E : Type} [Field E] [NumberField E] (P : E[X]) :
    ∀ᶠ w in Filter.cofinite (α := HeightOneSpectrum (𝓞 E)),
      ((P.map (algebraMap E (w.adicCompletion E))).coeffs : Set (w.adicCompletion E)) ⊆
        intL (w.adicCompletion E) := by
  have hall : ∀ᶠ w in Filter.cofinite (α := HeightOneSpectrum (𝓞 E)),
      ∀ n ∈ P.support, Valued.v (algebraMap E (w.adicCompletion E) (P.coeff n)) ≤ 1 :=
    (Filter.eventually_all_finset P.support).2 fun n _ => eventually_valued_le_one (P.coeff n)
  filter_upwards [hall] with w hw
  intro c hc
  rw [Finset.mem_coe, Polynomial.mem_coeffs_iff] at hc
  obtain ⟨n, -, rfl⟩ := hc
  rw [Polynomial.coeff_map]
  change Valued.v (algebraMap E (w.adicCompletion E) (P.coeff n)) ≤ 1
  by_cases h0 : P.coeff n = 0
  · rw [h0, map_zero, map_zero]
    exact zero_le'
  · exact hw n (Polynomial.mem_support_iff.2 h0)

theorem goodPlaces (E : Type) [Field E] [NumberField E] (P : E[X]) (hP : P.Separable) :
    ∀ᶠ w in (cofinite : Filter (Pl E)), ∃ Q₀ : (intL (w.adicCompletion E))[X], Q₀.Separable ∧
      Q₀.map (intL (w.adicCompletion E)).subtype = P.map (algebraMap E (w.adicCompletion E)) := by
  obtain ⟨a, b, hab⟩ := hP
  filter_upwards [eventually_coeffs_integral P, eventually_coeffs_integral a,
    eventually_coeffs_integral b] with w hPw haw hbw
  have lift : ∀ p : E[X],
      ((p.map (algebraMap E (w.adicCompletion E))).coeffs : Set (w.adicCompletion E)) ⊆
        intL (w.adicCompletion E) →
      ∃ q : (intL (w.adicCompletion E))[X],
        q.map (intL (w.adicCompletion E)).subtype = p.map (algebraMap E (w.adicCompletion E)) := by
    intro p hp
    have hl : p.map (algebraMap E (w.adicCompletion E)) ∈
        Polynomial.lifts (intL (w.adicCompletion E)).subtype := by
      rw [Polynomial.lifts_iff_coeffs_subset_range]
      intro c hc
      exact ⟨⟨c, hp hc⟩, rfl⟩
    exact (Polynomial.mem_lifts _).1 hl
  obtain ⟨Q, hQ⟩ := lift P hPw
  obtain ⟨A, hA⟩ := lift a haw
  obtain ⟨B, hB⟩ := lift b hbw
  refine ⟨Q, ⟨A, B, ?_⟩, hQ⟩
  apply Polynomial.map_injective (intL (w.adicCompletion E)).subtype Subtype.val_injective
  have h2 := congrArg (Polynomial.map (algebraMap E (w.adicCompletion E))) hab
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one] at h2 ⊢
  rw [← Polynomial.derivative_map] at h2 ⊢
  rw [hQ, hA, hB]
  exact h2

end GlobalTheory.GoodPlaces
