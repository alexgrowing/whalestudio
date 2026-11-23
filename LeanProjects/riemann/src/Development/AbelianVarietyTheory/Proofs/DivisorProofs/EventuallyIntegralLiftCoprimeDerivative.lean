import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IntCop

theorem lift_of_val_le {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (Q : E[X]) (h : ∀ n, w.valuation E (Q.coeff n) ≤ 1) :
    ∃ Q₀ : (w.adicCompletionIntegers E)[X],
      Q₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) =
        Q.map (algebraMap E (w.adicCompletion E)) := by
  have : Q.map (algebraMap E (w.adicCompletion E)) ∈
      Polynomial.lifts (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_map]
    refine ⟨⟨algebraMap E (w.adicCompletion E) (Q.coeff n),
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_⟩, rfl⟩
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (Q.coeff n)).trans_le (h n)
  obtain ⟨Q₀, hQ₀⟩ := (Polynomial.mem_lifts _).1 this
  exact ⟨Q₀, hQ₀⟩

theorem finite_bad {E : Type} [Field E] [NumberField E] (Q : E[X]) :
    {w : HeightOneSpectrum (𝓞 E) | ¬ ∀ n, w.valuation E (Q.coeff n) ≤ 1}.Finite := by
  refine ((Finset.range (Q.natDegree + 1)).finite_toSet.biUnion
    fun n _ => HeightOneSpectrum.Support.finite (𝓞 E) (Q.coeff n)).subset ?_
  intro w hw
  simp only [Set.mem_setOf_eq, not_forall, not_le] at hw
  obtain ⟨n, hn⟩ := hw
  have hn' : n < Q.natDegree + 1 := by
    by_contra hc
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero] at hn
    exact (not_lt.2 zero_le') hn
  simp only [Set.mem_iUnion]
  exact ⟨n, by simpa using hn', hn⟩

end GlobalTheory.IntCop

namespace GlobalTheory.IntCop

theorem eventually_integral_coprime : ∀ (E : Type) [Field E] [NumberField E] (P : E[X]), P.Separable →
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∃ P₀ : (w.adicCompletionIntegers E)[X],
      P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) = P.map (algebraMap E (w.adicCompletion E)) ∧
      IsCoprime P₀ (derivative P₀) := by
  intro E _ _ P hP
  obtain ⟨a, b, hab⟩ := hP
  have hfin := ((finite_bad P).union (finite_bad a)).union (finite_bad b)
  refine Filter.eventually_cofinite.2 (hfin.subset ?_)
  intro w hw
  by_contra hc
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
  obtain ⟨⟨hPw, haw⟩, hbw⟩ := hc
  apply hw
  obtain ⟨P₀, hP₀⟩ := lift_of_val_le w P hPw
  obtain ⟨a₀, ha₀⟩ := lift_of_val_le w a haw
  obtain ⟨b₀, hb₀⟩ := lift_of_val_le w b hbw
  refine ⟨P₀, hP₀, a₀, b₀, ?_⟩
  have hinj : Function.Injective
      (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) := Subtype.val_injective
  apply Polynomial.map_injective _ hinj
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map,
    ha₀, hb₀, hP₀, Polynomial.derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul,
    ← Polynomial.map_add, hab, Polynomial.map_one, Polynomial.map_one]

end GlobalTheory.IntCop
