import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaDecompositionOffFinsetStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaCellsDisjointOffFinsetStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOpenAdelicUnipotentTimesIntegralOutsideSetStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUniformizerTorusTranslateUnipotentQuotiStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumUnfoldingOfComplexInvariantIntegrableStatement

noncomputable section
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CellDec
variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem cell_lintegral [MeasurableSpace (GA E n)] [BorelSpace (GA E n)] (μ : Measure (GA E n)) [μ.IsHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 E))) (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ)
    (hϖ : ∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) (𝓕 : Set (GA E n)) (h𝓕 : IsFundamentalDomain (NE E n) 𝓕 μ)
    (B : GA E n → ℝ≥0∞) (hB : Measurable B) (hinv : ∀ u ∈ NA E n, ∀ g, B (u * g) = B g) :
    ∫⁻ g in 𝓕, B g ∂μ =
      ∑' l : abelian₂ E n S, ENNReal.ofReal (dinv n l.1) * ∫⁻ g in 𝓕 ∩ C0 E n S, B (tl n ϖ l.1 * g) ∂μ := by
  have hC : MeasurableSet (C0 E n S) := (GlobalTheory.T.isOpen_C0 E n S).measurableSet
  let cellS : abelian₂ E n S → Set (GA E n) := fun l => {g | (tl n ϖ l.1)⁻¹ * g ∈ C0 E n S}
  have hmeas : ∀ l, MeasurableSet (cellS l) := fun l =>
    ((GlobalTheory.T.isOpen_C0 E n S).preimage (continuous_const.mul continuous_id)).measurableSet
  have hpart : ∀ g, ∑' l : abelian₂ E n S, (cellS l).indicator B g = B g := by
    intro g
    obtain ⟨l0, hl0S, hl0⟩ := GlobalTheory.T.exists_tl_inv_mul_mem_C0_off_finset E n S ϖ hϖ g
    have hz : ∀ l : abelian₂ E n S, l ≠ (⟨l0, hl0S⟩ : abelian₂ E n S) → (cellS l).indicator B g = 0 := fun l hl =>
      Set.indicator_of_notMem (show g ∉ cellS l from fun hg => hl (Subtype.ext (GlobalTheory.T.adelic_iwasawa_cells_disjoint_off_finset E n S ϖ hϖ l.1 l0 g l.2 hl0S hg hl0))) B
    rw [tsum_eq_single _ hz]
    exact Set.indicator_of_mem (show g ∈ cellS ⟨l0, hl0S⟩ from hl0) _
  calc ∫⁻ g in 𝓕, B g ∂μ = ∫⁻ g in 𝓕, ∑' l, (cellS l).indicator B g ∂μ := by simp_rw [hpart]
    _ = ∑' l, ∫⁻ g in 𝓕, (cellS l).indicator B g ∂μ :=
        lintegral_tsum fun l => (hB.indicator (hmeas l)).aemeasurable
    _ = _ := tsum_congr fun l => ?_
  let t := tl n ϖ l.1
  let F : GA E n → ℝ≥0∞ := (C0 E n S).indicator fun h => B (t * h)
  have e : (cellS l).indicator B = fun g => F (t⁻¹ * g) := by
    funext g
    show (cellS l).indicator B g = (C0 E n S).indicator (fun h => B (t * h)) (t⁻¹ * g)
    by_cases hg : t⁻¹ * g ∈ C0 E n S
    · rw [Set.indicator_of_mem (show g ∈ cellS l from hg), Set.indicator_of_mem hg, mul_inv_cancel_left]
    · rw [Set.indicator_of_notMem (show g ∉ cellS l from hg), Set.indicator_of_notMem hg]
  have hF : Measurable F := (hB.comp (measurable_const_mul t)).indicator hC
  have hFinv : ∀ u ∈ NA E n, ∀ g, F (u * g) = F g := by
    intro u hu g
    show (C0 E n S).indicator (fun h => B (t * h)) (u * g) = (C0 E n S).indicator (fun h => B (t * h)) g
    by_cases hg : g ∈ C0 E n S
    · rw [Set.indicator_of_mem (adelicUnitriangular_mul_mem_unipotentTimesIntegral hu hg), Set.indicator_of_mem hg]
      change B (t * (u * g)) = B (t * g)
      rw [show t * (u * g) = (t * u * t⁻¹) * (t * g) by group]
      exact hinv _ (tl_conj_mem ϖ l.1 hu) _
    · have : u * g ∉ C0 E n S := fun h => hg (by simpa using adelicUnitriangular_mul_mem_unipotentTimesIntegral (inv_mem hu) h)
      rw [Set.indicator_of_notMem this, Set.indicator_of_notMem hg]
  rw [e, GlobalTheory.T.lintegral_uniformizerTorus_translate_unipotentQuotient E n μ ϖ hϖ l.1 𝓕 h𝓕 F hF hFinv]
  congr 1
  rw [lintegral_indicator hC, Measure.restrict_restrict hC, Set.inter_comm]

theorem cell_integral [MeasurableSpace (GA E n)] [BorelSpace (GA E n)] (μ : Measure (GA E n)) [μ.IsHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 E))) (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ)
    (hϖ : ∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) (𝓕 : Set (GA E n)) (h𝓕 : IsFundamentalDomain (NE E n) 𝓕 μ)
    (B : GA E n → ℂ) (hB : Measurable B) (hBi : Integrable B (μ.restrict 𝓕))
    (hinv : ∀ u ∈ NA E n, ∀ g, B (u * g) = B g) :
    (∀ l : abelian₂ E n S, Integrable (fun g => B (tl n ϖ l.1 * g)) (μ.restrict (𝓕 ∩ C0 E n S))) ∧
      HasSum (fun l : abelian₂ E n S => (dinv n l.1 : ℂ) * ∫ g in 𝓕 ∩ C0 E n S, B (tl n ϖ l.1 * g) ∂μ)
        (∫ g in 𝓕, B g ∂μ) := by
  have hpos : ∀ l : abelian₂ E n S, 0 < dinv n l.1 := fun l =>
    Finset.prod_pos fun v _ => zpow_pos (by exact_mod_cast (GlobalTheory.LFun.qV_ne_zero v).bot_lt) _
  exact GlobalTheory.T.hasSum_unfolding_of_complex_invariant_integrable μ 𝓕 (𝓕 ∩ C0 E n S) (fun l : abelian₂ E n S => dinv n l.1) hpos (fun l g => tl n ϖ l.1 * g)
    (fun l => measurable_const_mul _) ((fun u : GA E n => fun g => u * g) '' (NA E n : Set (GA E n)))
    (fun f hf hfi => cell_lintegral μ S ϖ hϖ 𝓕 h𝓕 f hf fun u hu g => hfi _ ⟨u, hu, rfl⟩ g)
    B hB hBi (by rintro _ ⟨u, hu, rfl⟩ x; exact hinv u hu x)

end GlobalTheory.CellDec
