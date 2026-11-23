import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActFromBlocks
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarAdelicVectorsBoundsPureTensorsSlices
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurableEmbeddingAdelicTupleLocalComponents
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductIntegralPureTensorEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralFiniteAdelicFactorOffPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAdelicHaarSplitArchimedeanFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicHaarIntegralPointsOneStatement
open scoped Matrix GlobalTheory.VacAny ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

noncomputable section

namespace GlobalTheory.AdelicHaarPure

theorem measurableSet_box (F : Type) [Field F] [NumberField F] (κ : Type) [MeasurableSpace (κ → Af F)] [BorelSpace (κ → Af F)]
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    MeasurableSet {y : κ → Af F | ∀ v ∉ S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F} := by
  have : {y : κ → Af F | ∀ v ∉ S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F} =
      ⋂ v, ⋂ (_ : v ∉ S), ⋂ i, (fun y : κ → Af F => evalV F v (y i)) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext y; simp
  rw [this]
  refine IsClosed.measurableSet (isClosed_iInter fun v => isClosed_iInter fun _ => isClosed_iInter fun i => ?_)
  exact (Valued.isClosed_integer (v.adicCompletion F)).preimage ((GlobalTheory.GaugeGlue.continuous_evalV v).comp (continuous_apply i))

theorem evalV_add_singleFin_ne {F : Type} [Field F] [NumberField F] {v w : HeightOneSpectrum (𝓞 F)} (h : v ≠ w)
    (a : Af F) (t : Fv F w) : evalV F v (a + singleFin w t) = evalV F v a := by
  rw [map_add, evalV_singleFin_ne h, add_zero]

theorem finPart (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [MeasurableSpace (κ → Af F)] [BorelSpace (κ → Af F)]
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (κ → Fv F v)] [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (κ → Fv F v)]
    (μf : Measure (κ → Af F)) [μf.IsAddHaarMeasure]
    (hμf : μf {y | ∀ i (v : HeightOneSpectrum (𝓞 F)), evalV F v (y i) ∈ v.adicCompletionIntegers F} = 1)
    (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (κ → Fv F v)) [∀ v, (μv v).IsAddHaarMeasure]
    (hμv : ∀ v, μv v {x | ∀ i, x i ∈ v.adicCompletionIntegers F} = 1)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (f : ∀ v : HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℝ≥0∞)
    (hf : ∀ v, Measurable (f v)) :
    ∫⁻ y, {y : κ → Af F | ∀ v ∉ S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F}.indicator 1 y *
        ∏ v ∈ S, f v (fun i => evalV F v (y i)) ∂μf = ∏ v ∈ S, ∫⁻ t, f v t ∂(μv v) := by
  classical
  have hcw : ∀ v, Measurable fun y : κ → Af F => fun i => evalV F v (y i) := fun v =>
    (continuous_pi fun i => (GlobalTheory.GaugeGlue.continuous_evalV v).comp (continuous_apply i)).measurable
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, mul_one]
    rw [lintegral_indicator_one (measurableSet_box F κ ∅), ← hμf]
    congr 1
    ext y
    simp only [Finset.notMem_empty, not_false_eq_true, forall_const, Set.mem_setOf_eq]
    exact forall_comm
  | insert w S hw ih =>
    set K : (κ → Af F) → ℝ≥0∞ := fun y =>
      {y : κ → Af F | ∀ v ∉ insert w S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F}.indicator 1 y *
        ∏ v ∈ S, f v (fun i => evalV F v (y i)) with hK
    have hKm : Measurable K :=
      (measurable_one.indicator (measurableSet_box F κ _)).mul
        (Finset.measurable_prod _ fun v _ => (hf v).comp (hcw v))
    have hKi : ∀ (y : κ → Af F) (t : κ → Fv F w), K (fun i => y i + singleFin w (t i)) = K y := by
      intro y t
      have h1 : ∀ v ∈ S, (fun i => evalV F v (y i + singleFin w (t i))) = fun i => evalV F v (y i) := fun v hv =>
        funext fun i => evalV_add_singleFin_ne (by rintro rfl; exact hw hv) _ _
      have h2 : ({y : κ → Af F | ∀ v ∉ insert w S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F}.indicator 1
          (fun i => y i + singleFin w (t i)) : ℝ≥0∞) =
          {y : κ → Af F | ∀ v ∉ insert w S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F}.indicator 1 y := by
        have : ((fun i => y i + singleFin w (t i)) ∈
            {y : κ → Af F | ∀ v ∉ insert w S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F}) ↔
            (y ∈ {y : κ → Af F | ∀ v ∉ insert w S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F}) := by
          simp only [Set.mem_setOf_eq]
          refine forall_congr' fun v => imp_congr_right fun hv => forall_congr' fun i => ?_
          rw [evalV_add_singleFin_ne (by rintro rfl; exact hv (Finset.mem_insert_self _ S))]
        by_cases hy : y ∈ {y : κ → Af F | ∀ v ∉ insert w S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F}
        · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (this.2 hy)]; rfl
        · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (fun h => hy (this.1 h))]
      simp only [hK, h2]
      congr 1
      exact Finset.prod_congr rfl fun v hv => by rw [h1 v hv]
    have hstep := GlobalTheory.T.lintegral_finiteAdelic_factor_offPlace F κ w μf (μv w) (hμv w) K hKm hKi (f w) (hf w)
    have e1 : ∀ y : κ → Af F,
        {y : κ → Af F | ∀ v ∉ insert w S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F}.indicator 1 y *
          ∏ v ∈ insert w S, f v (fun i => evalV F v (y i)) = f w (fun i => evalV F w (y i)) * K y := by
      intro y
      rw [Finset.prod_insert hw, hK]
      ring
    have hiff : ∀ y : κ → Af F, (∀ v ∉ S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F) ↔
        (∀ i, evalV F w (y i) ∈ w.adicCompletionIntegers F) ∧
          ∀ v ∉ insert w S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F := by
      intro y
      constructor
      · intro h
        exact ⟨h w hw, fun v hv => h v fun h' => hv (Finset.mem_insert_of_mem h')⟩
      · rintro ⟨h1, h2⟩ v hv
        by_cases hvw : v = w
        · subst hvw; exact h1
        · exact h2 v (by simp [hvw, hv])
    have e2 : ∀ y : κ → Af F, {t : κ → Fv F w | ∀ i, t i ∈ w.adicCompletionIntegers F}.indicator 1
        (fun i => evalV F w (y i)) * K y =
        {y : κ → Af F | ∀ v ∉ S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F}.indicator 1 y *
          ∏ v ∈ S, f v (fun i => evalV F v (y i)) := by
      intro y
      rw [hK, ← mul_assoc]
      congr 1
      by_cases h : y ∈ {y : κ → Af F | ∀ v ∉ S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F}
      · have h' := (hiff y).1 h
        rw [Set.indicator_of_mem h, Set.indicator_of_mem (show (fun i => evalV F w (y i)) ∈
          {t : κ → Fv F w | ∀ i, t i ∈ w.adicCompletionIntegers F} from h'.1),
          Set.indicator_of_mem (show y ∈ {y : κ → Af F | ∀ v ∉ insert w S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F}
            from h'.2)]
        simp
      · rw [Set.indicator_of_notMem h]
        by_cases h1 : ∀ i, evalV F w (y i) ∈ w.adicCompletionIntegers F
        · have h2 : y ∉ {y : κ → Af F | ∀ v ∉ insert w S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F} :=
            fun h2 => h ((hiff y).2 ⟨h1, h2⟩)
          rw [Set.indicator_of_notMem h2, mul_zero]
        · rw [Set.indicator_of_notMem (show (fun i => evalV F w (y i)) ∉
            {t : κ → Fv F w | ∀ i, t i ∈ w.adicCompletionIntegers F} from h1), zero_mul]
    simp_rw [e1]
    rw [hstep, Finset.prod_insert hw]
    simp_rw [e2]
    rw [ih]

theorem integral_pure_haar : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)]
    [MeasurableSpace (κ → mixedEmbedding.mixedSpace F)] [BorelSpace (κ → mixedEmbedding.mixedSpace F)]
    [∀ v : Pl F, MeasurableSpace (κ → Fv F v)] [∀ v : Pl F, BorelSpace (κ → Fv F v)]
    (μ : Measure (κ → AF F)) [μ.IsAddHaarMeasure] (μi : Measure (κ → mixedEmbedding.mixedSpace F)) [μi.IsAddHaarMeasure]
    (μv : ∀ v : Pl F, Measure (κ → Fv F v)) [∀ v, (μv v).IsAddHaarMeasure],
    (∀ v, μv v {x | ∀ i, x i ∈ v.adicCompletionIntegers F} = 1) → ∃ c : ℂ, c ≠ 0 ∧
      ∀ (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), Continuous f → Integrable f μi → IsFam φ →
        Integrable (fun x : κ → AF F => f (fun i => evI F (x i)) * ∏ᶠ v, φ v fun i => evFin F v (x i)) μ ∧
        ∫ x, f (fun i => evI F (x i)) * ∏ᶠ v, φ v (fun i => evFin F v (x i)) ∂μ = c * (∫ x, f x ∂μi) * ∏ᶠ v, ∫ x, φ v x ∂(μv v) := by
  intro F _ _ κ _ _ _ _ _ _ _ μ _ μi _ μv _ hμv
  classical
  letI : MeasurableSpace (κ → Af F) := borel _
  haveI : BorelSpace (κ → Af F) := ⟨rfl⟩
  haveI : ∀ v : Pl F, ProperSpace (Fv F v) := fun v => GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  obtain ⟨μf, hμfH, hμf1⟩ := GlobalTheory.T.exists_finiteAdelicHaar_integralPoints_one F κ
  obtain ⟨c, hc0, hctop, hc⟩ := GlobalTheory.T.lintegral_adelicHaar_split_archimedean_finite F κ μ μi μf
  refine ⟨(c.toReal : ℂ), Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨hc0, hctop⟩), fun f φ hfc hfi hφ => ?_⟩
  have hfinS := Filter.eventually_cofinite.1 hφ.2
  set S := hfinS.toFinset with hS
  have hout : ∀ v ∉ S, φ v = ind κ v := by
    intro v hv
    by_contra hne
    exact hv (by simpa [hS] using hne)
  have hpi : Continuous fun x : κ → AF F => fun i => evI F (x i) :=
    continuous_pi fun i => (GlobalTheory.Core.Rk.RapidInt.continuous_toMixed F).comp (continuous_fst.comp (continuous_apply i))
  have hpv : ∀ v : Pl F, Continuous fun x : κ → AF F => fun i => evFin F v (x i) := fun v =>
    continuous_pi fun i => (GlobalTheory.GaugeGlue.continuous_evalV v).comp (continuous_snd.comp (continuous_apply i))
  set B : Set (κ → AF F) := {x | ∀ v ∉ S, ∀ i, evFin F v (x i) ∈ v.adicCompletionIntegers F} with hB
  have hBm : MeasurableSet B := by
    have : B = (fun x : κ → AF F => fun i => sndA F (x i)) ⁻¹'
        {y : κ → Af F | ∀ v ∉ S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F} := rfl
    rw [this]
    have hsnd : Continuous (fun x : κ → AF F => fun i => sndA F (x i)) :=
      continuous_pi fun i => continuous_snd.comp (continuous_apply i)
    exact hsnd.measurable (measurableSet_box F κ S)
  have hlin : ∀ (fi : (κ → mixedEmbedding.mixedSpace F) → ℝ≥0∞) (fv : ∀ v : Pl F, (κ → Fv F v) → ℝ≥0∞),
      Measurable fi → (∀ v, Measurable (fv v)) →
      ∫⁻ x, fi (fun i => evI F (x i)) * ∏ v ∈ S, fv v (fun i => evFin F v (x i)) ∂(μ.restrict B) =
        (∫⁻ z, fi z ∂μi) * (∏ v ∈ S, ∫⁻ t, fv v t ∂(μv v)) * c := by
    intro fi fv hfi hfv
    rw [← lintegral_indicator hBm]
    have e : ∀ x : κ → AF F, B.indicator (fun x => fi (fun i => evI F (x i)) * ∏ v ∈ S, fv v (fun i => evFin F v (x i))) x =
        fi (fun i => evI F (x i)) *
          ({y : κ → Af F | ∀ v ∉ S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F}.indicator 1 (fun i => sndA F (x i)) *
            ∏ v ∈ S, fv v (fun i => evalV F v (sndA F (x i)))) := by
      intro x
      by_cases hx : x ∈ B
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show (fun i => sndA F (x i)) ∈
          {y : κ → Af F | ∀ v ∉ S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F} from hx)]
        simp only [Pi.one_apply, one_mul]
        rfl
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show (fun i => sndA F (x i)) ∉
          {y : κ → Af F | ∀ v ∉ S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F} from hx)]
        simp
    simp_rw [e]
    have hcw : ∀ v, Measurable fun y : κ → Af F => fun i => evalV F v (y i) := fun v =>
      (continuous_pi fun i => (GlobalTheory.GaugeGlue.continuous_evalV v).comp (continuous_apply i)).measurable
    have hgm : Measurable fun y : κ → Af F =>
        {y : κ → Af F | ∀ v ∉ S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F}.indicator 1 y *
          ∏ v ∈ S, fv v (fun i => evalV F v (y i)) :=
      (measurable_one.indicator (measurableSet_box F κ S)).mul
        (Finset.measurable_prod _ fun v _ => (hfv v).comp (hcw v))
    rw [hc fi _ hfi hgm,
      finPart F κ μf hμf1 μv hμv S fv hfv]
    ring
  have hint : ∀ v, Integrable (φ v) (μv v) := fun v =>
    (hφ.1 v).1.continuous.integrable_of_hasCompactSupport (hφ.1 v).2
  obtain ⟨h1, h2⟩ := GlobalTheory.GaugeEx.ProdInt.integral_tensor (μ.restrict B) μi μv (fun x : κ → AF F => fun i => evI F (x i))
    (fun v x i => evFin F v (x i)) hpi.measurable (fun v => (hpv v).measurable) S c hctop hlin f φ hfi hint
  have hΦB : (fun x : κ → AF F => f (fun i => evI F (x i)) * ∏ᶠ v, φ v fun i => evFin F v (x i)) =
      B.indicator fun x => f (fun i => evI F (x i)) * ∏ v ∈ S, φ v (fun i => evFin F v (x i)) := by
    funext x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, finprod_eq_prod_of_mulSupport_subset (s := S)]
      intro v hv
      by_contra hvS
      apply hv
      simp only [hout v hvS, ind]
      exact Set.indicator_of_mem (show (fun i => evFin F v (x i)) ∈ {x | ∀ i, x i ∈ v.adicCompletionIntegers F} from
        hx v hvS) _
    · rw [Set.indicator_of_notMem hx]
      simp only [hB, Set.mem_setOf_eq, not_forall] at hx
      obtain ⟨v, hvS, i, hv⟩ := hx
      have hev : ∀ᶠ v in Filter.cofinite, φ v (fun i => evFin F v (x i)) = 1 := by
        have h1 : ∀ᶠ v in Filter.cofinite, ∀ i, evFin F v (x i) ∈ v.adicCompletionIntegers F :=
          Filter.eventually_all.2 fun i => (sndA F (x i)).2
        filter_upwards [hφ.2, h1] with w h2 h3
        rw [h2]
        exact Set.indicator_of_mem (show (fun i => evFin F w (x i)) ∈ {x | ∀ i, x i ∈ w.adicCompletionIntegers F} from h3) _
      rw [finprod_eq_zero _ v (by rw [hout v hvS]; exact Set.indicator_of_notMem (show (fun i => evFin F v (x i)) ∉
          {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from fun h => hv (h i)) _)
        (Filter.eventually_cofinite.1 hev), mul_zero]
  have hprod : ∏ᶠ v, ∫ x, φ v x ∂(μv v) = ∏ v ∈ S, ∫ x, φ v x ∂(μv v) := by
    rw [finprod_eq_prod_of_mulSupport_subset (s := S)]
    intro v hv
    by_contra hvS
    apply hv
    have hm : MeasurableSet {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := by
      have : {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} =
          ⋂ i, (fun x : κ → Fv F v => x i) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v)) := by ext; simp
      rw [this]
      exact (isClosed_iInter fun i => (Valued.isClosed_integer (v.adicCompletion F)).preimage (continuous_apply i)).measurableSet
    have := integral_indicator_const (μ := μv v) (1 : ℂ) hm
    simp only [hout v hvS, ind]
    simpa [Measure.real, Pi.one_def, hμv v] using this
  rw [hΦB, hprod]
  refine ⟨(integrable_indicator_iff hBm).2 h1, ?_⟩
  rw [integral_indicator hBm, h2]
  ring

end GlobalTheory.AdelicHaarPure

end
