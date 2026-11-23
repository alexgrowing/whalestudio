import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

private theorem coeff_mem_eventually {E : Type} [Field E] [NumberField E] (R : E[X]) :
    ∀ᶠ w : Pl E in cofinite, ∀ n, algebraMap E (w.adicCompletion E) (R.coeff n) ∈ Ov E w := by
  have h : ∀ᶠ w : Pl E in cofinite, ∀ n ∈ R.support,
      algebraMap E (w.adicCompletion E) (R.coeff n) ∈ Ov E w := by
    refine (Filter.eventually_all_finset _).2 fun n _ => ?_
    filter_upwards [(HeightOneSpectrum.Support.finite (𝓞 E) (R.coeff n)).compl_mem_cofinite] with w hw
    have hv : Valued.v (algebraMap E (w.adicCompletion E) (R.coeff n)) = w.valuation E (R.coeff n) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (R.coeff n)
    have hle : Valued.v (algebraMap E (w.adicCompletion E) (R.coeff n)) ≤ 1 :=
      hv.trans_le (not_lt.mp hw)
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hle
  filter_upwards [h] with w hw n
  by_cases hn : n ∈ R.support
  · exact hw n hn
  · rw [Polynomial.notMem_support_iff.mp hn, map_zero]
    exact zero_mem _

private theorem exists_lift {E : Type} [Field E] [NumberField E] (w : Pl E) (R : E[X])
    (h : ∀ n, algebraMap E (w.adicCompletion E) (R.coeff n) ∈ Ov E w) :
    ∃ R₀ : (Ov E w)[X], R₀.map (Ov E w).subtype = R.map (algebraMap E (w.adicCompletion E)) := by
  have hl : R.map (algebraMap E (w.adicCompletion E)) ∈ Polynomial.lifts (Ov E w).subtype := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_map]
    exact ⟨⟨_, h n⟩, rfl⟩
  exact (Polynomial.mem_lifts _).1 hl

theorem UpperTheory.eventually_separable_of_integral_model :
    ∀ (E : Type) [Field E] [NumberField E] (P : E[X]), P.Separable → ∀ᶠ w : Pl E in cofinite,
        ∀ Q : (Ov E w)[X], Q.map (Ov E w).subtype = P.map (algebraMap E (w.adicCompletion E)) → Q.Separable := by
  intro E _ _ P hP
  obtain ⟨a, b, hab⟩ := hP
  filter_upwards [coeff_mem_eventually a, coeff_mem_eventually b] with w ha hb Q hQ
  obtain ⟨a₀, ha₀⟩ := exists_lift w a ha
  obtain ⟨b₀, hb₀⟩ := exists_lift w b hb
  refine ⟨a₀, b₀, Polynomial.map_injective (Ov E w).subtype Subtype.val_injective ?_⟩
  have hd : (derivative Q).map (Ov E w).subtype =
      (derivative P).map (algebraMap E (w.adicCompletion E)) := by
    rw [← Polynomial.derivative_map, hQ, Polynomial.derivative_map]
  have := congrArg (Polynomial.map (algebraMap E (w.adicCompletion E))) hab
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one] at this ⊢
  rw [ha₀, hb₀, hQ, hd, this]
