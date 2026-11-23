import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRestrictedProdFinAwayIffIsProdMeasureFinAway
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set Topology
open scoped ENNReal

namespace GlobalTheory.RestrMeas

section Pi

theorem lintegral_fin_prod_eq_prod {n : ℕ} {E : Fin n → Type} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : ∀ i, Measure (E i)} [∀ i, SigmaFinite (μ i)] {f : ∀ i, E i → ℝ≥0∞} (hf : ∀ i, AEMeasurable (f i) (μ i)) :
    ∫⁻ x : ∀ i, E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _),
      Fin.prod_univ_succ, ← ih fun i => hf _, ← lintegral_prod_mul (hf 0)]
    · refine lintegral_congr fun a => ?_
      rw [Fin.prod_univ_succ]
      rfl
    · exact Finset.aemeasurable_fun_prod _ fun i _ =>
        (hf _).comp_quasiMeasurePreserving (quasiMeasurePreserving_eval (fun i : Fin n => μ i.succ) i)

theorem lintegral_fintype_prod_eq_prod {ι : Type} [Fintype ι] {E : ι → Type} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : ∀ i, Measure (E i)} [∀ i, SigmaFinite (μ i)] {f : ∀ i, E i → ℝ≥0∞} (hf : ∀ i, AEMeasurable (f i) (μ i)) :
    ∫⁻ x : ∀ i, E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_prod_eq_prod fun i => hf _

end Pi

theorem one_add_sum_le_prod_one_add {ι : Type} (s : Finset ι) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) :
    1 + ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 + a i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
    rw [Finset.sum_cons, Finset.prod_cons]
    nlinarith [ha i, Finset.sum_nonneg fun j (_ : j ∈ s) => ha j]

variable {X W V : Type} {Ya : W → Type} {Yf : V → Type} {pa : ∀ w, X → Ya w} {pf : ∀ v, X → Yf v}
  {K : ∀ v, Set (Yf v)}

theorem finprod_eq_prod_of_mem {M : Type} [CommMonoid M] {ff : ∀ v, Yf v → M} {S : Finset V}
    (h1 : ∀ v ∉ S, ∀ y ∈ K v, ff v y = 1) {x : X} (hx : ∀ v ∉ S, pf v x ∈ K v) :
    ∏ᶠ v, ff v (pf v x) = ∏ v ∈ S, ff v (pf v x) :=
  finprod_eq_prod_of_mulSupport_subset _ fun v hv => by_contra fun h' => hv (h1 v h' _ (hx v h'))

theorem finprod_eq_zero_of_notMem {M : Type} [CommMonoidWithZero M] {ff : ∀ v, Yf v → M} {S : Finset V}
    (h1 : ∀ v ∉ S, ff v = (K v).indicator 1) {x : X} (hx : ∀ᶠ v in cofinite, pf v x ∈ K v)
    (hx' : ¬ ∀ v ∉ S, pf v x ∈ K v) : ∏ᶠ v, ff v (pf v x) = 0 := by
  classical
  obtain ⟨T, hT⟩ := exists_finset_of_eventually hx
  push Not at hx'
  obtain ⟨u, hu, hu'⟩ := hx'
  rw [finprod_eq_prod_of_mem (K := K) (S := S ∪ T)
    (fun v hv y hy => by rw [h1 v fun h' => hv (Finset.mem_union_left _ h'), indicator_of_mem hy, Pi.one_apply])
    fun v hv => hT v fun h' => hv (Finset.mem_union_right _ h')]
  exact Finset.prod_eq_zero (Finset.mem_union_right _ (by_contra fun h' => hu' (hT u h')))
    (by rw [h1 u hu, indicator_of_notMem hu'])

theorem monotone_level : Monotone fun S : Finset V => {x | ∀ v ∉ S, pf v x ∈ K v} :=
  fun _ _ h _ hx v hv => hx v fun h' => hv (h h')

theorem iUnion_level (hX : ∀ x, ∀ᶠ v in cofinite, pf v x ∈ K v) (S₀ : Finset V) :
    ⋃ S : {S : Finset V // S₀ ⊆ S}, {x | ∀ v ∉ S.1, pf v x ∈ K v} = univ := by
  classical
  refine eq_univ_of_forall fun x => ?_
  obtain ⟨T, hT⟩ := exists_finset_of_eventually (hX x)
  exact mem_iUnion.2 ⟨⟨S₀ ∪ T, Finset.subset_union_left⟩, fun v hv => hT v fun h' => hv (Finset.mem_union_right _ h')⟩

theorem directed_level (S₀ : Finset V) :
    Directed (· ⊆ ·) fun S : {S : Finset V // S₀ ⊆ S} => {x | ∀ v ∉ S.1, pf v x ∈ K v} := by
  classical
  exact fun S T => ⟨⟨S ∪ T, S.2.trans Finset.subset_union_left⟩, monotone_level Finset.subset_union_left,
    monotone_level Finset.subset_union_right⟩

variable [MeasurableSpace X] [∀ w, MeasurableSpace (Ya w)] [∀ v, MeasurableSpace (Yf v)] [Countable V]

theorem measurableSet_level (hf : ∀ v, Measurable (pf v)) (hK : ∀ v, MeasurableSet (K v)) (S : Finset V) :
    MeasurableSet {x | ∀ v ∉ S, pf v x ∈ K v} := by
  simp only [setOf_forall]
  exact MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ => hf v (hK v)

variable [Fintype W] {μa : ∀ w, Measure (Ya w)} {μf : ∀ v, Measure (Yf v)} {μ : Measure X}
  [∀ w, SigmaFinite (μa w)] [∀ v, SigmaFinite (μf v)]

omit [Countable V] in

theorem IsCylProd.measurePreserving_level (h : IsCylProd pa pf K μa μf μ) (ha : ∀ w, Measurable (pa w))
    (hf : ∀ v, Measurable (pf v)) {S : Finset V} (hS : ∀ v ∉ S, μf v (K v) = 1) :
    MeasurePreserving (fun x => (fun w => pa w x, fun v : S => pf v x)) (μ.restrict {x | ∀ v ∉ S, pf v x ∈ K v})
      ((Measure.pi μa).prod (Measure.pi fun v : S => μf v)) := by
  classical
  have hπ : Measurable fun x => (fun w => pa w x, fun v : S => pf v x) :=
    (measurable_pi_lambda _ ha).prodMk (measurable_pi_lambda _ fun v => hf v)
  refine ⟨hπ, (prod_eq_generateFrom generateFrom_pi generateFrom_pi isPiSystem_pi isPiSystem_pi
    (FiniteSpanningSetsIn.pi fun w => (μa w).toFiniteSpanningSetsIn)
    (FiniteSpanningSetsIn.pi fun v : S => (μf v).toFiniteSpanningSetsIn) ?_).symm⟩
  rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩
  have hm := (MeasurableSet.univ_pi fun w => hA w (mem_univ _)).prod (MeasurableSet.univ_pi fun v => hB v (mem_univ _))
  have e := h.2 S hS A (fun v => if hv : v ∈ S then B ⟨v, hv⟩ else univ) (fun w => hA w (mem_univ _))
    fun v hv => by simp only [dif_pos hv]; exact hB ⟨v, hv⟩ (mem_univ _)
  rw [Measure.map_apply hπ hm, Measure.restrict_apply (hπ hm), Measure.pi_pi, Measure.pi_pi]
  convert e using 2
  · ext x
    simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ_pi, mem_cyl, mem_setOf_eq, and_assoc, Subtype.forall]
    exact and_congr_right fun _ => and_congr_left fun _ => forall₂_congr fun v hv => by rw [dif_pos hv]
  · rw [← Finset.prod_coe_sort S]
    exact Finset.prod_congr rfl fun v _ => by rw [dif_pos v.2]

variable (h : IsCylProd pa pf K μa μf μ) (ha : ∀ w, Measurable (pa w)) (hf : ∀ v, Measurable (pf v))
  (hK : ∀ v, MeasurableSet (K v))

include h ha hf hK

section Nonneg

variable {fa : ∀ w, Ya w → ℝ≥0∞} {ff : ∀ v, Yf v → ℝ≥0∞}

theorem IsCylProd.setLIntegral_tensor {S : Finset V} (hS : ∀ v ∉ S, μf v (K v) = 1)
    (h1 : ∀ v ∉ S, ∀ y ∈ K v, ff v y = 1) (hfa : ∀ w, AEMeasurable (fa w) (μa w))
    (hff : ∀ v ∈ S, AEMeasurable (ff v) (μf v)) :
    ∫⁻ x in {x | ∀ v ∉ S, pf v x ∈ K v}, (∏ w, fa w (pa w x)) * ∏ᶠ v, ff v (pf v x) ∂μ =
      (∏ w, ∫⁻ y, fa w y ∂μa w) * ∏ v ∈ S, ∫⁻ y, ff v y ∂μf v := by
  have ma : AEMeasurable (fun y : ∀ w, Ya w => ∏ w, fa w (y w)) (Measure.pi μa) :=
    Finset.aemeasurable_fun_prod _ fun w _ => (hfa w).comp_quasiMeasurePreserving (quasiMeasurePreserving_eval μa w)
  have mf : AEMeasurable (fun y : ∀ v : S, Yf v => ∏ v : S, ff v (y v)) (Measure.pi fun v : S => μf v) :=
    Finset.aemeasurable_fun_prod _ fun v _ =>
      (hff v v.2).comp_quasiMeasurePreserving (quasiMeasurePreserving_eval (fun v : S => μf v) v)
  have hp := h.measurePreserving_level ha hf hS
  rw [← Finset.prod_coe_sort S, ← lintegral_fintype_prod_eq_prod hfa,
    ← lintegral_fintype_prod_eq_prod fun v : S => hff v v.2, ← lintegral_prod_mul ma mf, ← hp.map_eq,
    lintegral_map' (hp.map_eq ▸ ma.comp_fst.mul mf.comp_snd) hp.aemeasurable]
  refine setLIntegral_congr_fun (measurableSet_level hf hK S) fun x hx => ?_
  simp only [finprod_eq_prod_of_mem h1 hx, ← Finset.prod_coe_sort S]

theorem IsCylProd.lintegral_tensor (hX : ∀ x, ∀ᶠ v in cofinite, pf v x ∈ K v) {S₀ : Finset V}
    (hS : ∀ v ∉ S₀, μf v (K v) = 1) (h1 : ∀ v ∉ S₀, ∀ y ∈ K v, ff v y = 1)
    (hfa : ∀ w, AEMeasurable (fa w) (μa w)) (hff : ∀ v, AEMeasurable (ff v) (μf v)) :
    ∫⁻ x, (∏ w, fa w (pa w x)) * ∏ᶠ v, ff v (pf v x) ∂μ =
      ⨆ (S : Finset V) (_ : S₀ ⊆ S), (∏ w, ∫⁻ y, fa w y ∂μa w) * ∏ v ∈ S, ∫⁻ y, ff v y ∂μf v := by
  rw [← setLIntegral_univ, ← iUnion_level hX S₀, setLIntegral_iUnion_of_directed _ (directed_level S₀), iSup_subtype']
  exact iSup_congr fun S => h.setLIntegral_tensor ha hf hK (fun v hv => hS v fun h' => hv (S.2 h'))
    (fun v hv => h1 v fun h' => hv (S.2 h')) hfa fun v _ => hff v

theorem IsCylProd.lintegral_tensor_indicator (hX : ∀ x, ∀ᶠ v in cofinite, pf v x ∈ K v) {S : Finset V}
    (hS : ∀ v ∉ S, μf v (K v) = 1) (h1 : ∀ v ∉ S, ff v = (K v).indicator 1)
    (hfa : ∀ w, AEMeasurable (fa w) (μa w)) (hff : ∀ v ∈ S, AEMeasurable (ff v) (μf v)) :
    ∫⁻ x, (∏ w, fa w (pa w x)) * ∏ᶠ v, ff v (pf v x) ∂μ =
      (∏ w, ∫⁻ y, fa w y ∂μa w) * ∏ v ∈ S, ∫⁻ y, ff v y ∂μf v := by
  rw [← h.setLIntegral_tensor ha hf hK hS (fun v hv y hy => by rw [h1 v hv, indicator_of_mem hy, Pi.one_apply]) hfa hff,
    ← lintegral_indicator (measurableSet_level hf hK S)]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ {x | ∀ v ∉ S, pf v x ∈ K v}
  · rw [indicator_of_mem hx]
  · rw [indicator_of_notMem hx, finprod_eq_zero_of_notMem h1 (hX x) hx, mul_zero]

end Nonneg

variable {𝕜 : Type} [RCLike 𝕜] {fa : ∀ w, Ya w → 𝕜} {ff : ∀ v, Yf v → 𝕜}

theorem IsCylProd.setIntegral_tensor {S : Finset V} (hS : ∀ v ∉ S, μf v (K v) = 1)
    (h1 : ∀ v ∉ S, ∀ y ∈ K v, ff v y = 1) (hfa : ∀ w, Integrable (fa w) (μa w))
    (hff : ∀ v ∈ S, Integrable (ff v) (μf v)) :
    IntegrableOn (fun x => (∏ w, fa w (pa w x)) * ∏ᶠ v, ff v (pf v x)) {x | ∀ v ∉ S, pf v x ∈ K v} μ ∧
    ∫ x in {x | ∀ v ∉ S, pf v x ∈ K v}, (∏ w, fa w (pa w x)) * ∏ᶠ v, ff v (pf v x) ∂μ =
      (∏ w, ∫ y, fa w y ∂μa w) * ∏ v ∈ S, ∫ y, ff v y ∂μf v := by
  have hp := h.measurePreserving_level ha hf hS
  have hi := (Integrable.fintype_prod_dep hfa).mul_prod
    (Integrable.fintype_prod_dep (μ := fun v : S => μf v) fun v : S => hff v v.2)
  have e : EqOn (fun x => (∏ w, fa w (pa w x)) * ∏ v : S, ff v (pf v x))
      (fun x => (∏ w, fa w (pa w x)) * ∏ᶠ v, ff v (pf v x)) {x | ∀ v ∉ S, pf v x ∈ K v} := fun x hx => by
    simp only [finprod_eq_prod_of_mem h1 hx, ← Finset.prod_coe_sort S]
  refine ⟨IntegrableOn.congr_fun (hp.integrable_comp_of_integrable hi) e (measurableSet_level hf hK S), ?_⟩
  rw [← setIntegral_congr_fun (measurableSet_level hf hK S) e, ← Finset.prod_coe_sort S,
    ← integral_fintype_prod_eq_prod, ← integral_fintype_prod_eq_prod, ← integral_prod_mul, ← hp.map_eq,
    integral_map hp.aemeasurable (hp.map_eq ▸ hi.aestronglyMeasurable)]

theorem IsCylProd.integral_tensor_indicator (hX : ∀ x, ∀ᶠ v in cofinite, pf v x ∈ K v) {S : Finset V}
    (hS : ∀ v ∉ S, μf v (K v) = 1) (h1 : ∀ v ∉ S, ff v = (K v).indicator 1)
    (hfa : ∀ w, Integrable (fa w) (μa w)) (hff : ∀ v ∈ S, Integrable (ff v) (μf v)) :
    Integrable (fun x => (∏ w, fa w (pa w x)) * ∏ᶠ v, ff v (pf v x)) μ ∧
    ∫ x, (∏ w, fa w (pa w x)) * ∏ᶠ v, ff v (pf v x) ∂μ =
      (∏ w, ∫ y, fa w y ∂μa w) * ∏ v ∈ S, ∫ y, ff v y ∂μf v := by
  obtain ⟨hi, e⟩ := h.setIntegral_tensor ha hf hK hS
    (fun v hv y hy => by rw [h1 v hv, indicator_of_mem hy, Pi.one_apply]) hfa hff
  have h0 : ∀ x ∉ {x | ∀ v ∉ S, pf v x ∈ K v}, (∏ w, fa w (pa w x)) * ∏ᶠ v, ff v (pf v x) = 0 := fun x hx => by
    rw [finprod_eq_zero_of_notMem h1 (hX x) hx, mul_zero]
  exact ⟨hi.integrable_of_forall_notMem_eq_zero h0, by rw [← e, setIntegral_eq_integral_of_forall_compl_eq_zero h0]⟩

theorem IsCylProd.integrable_tensor (hX : ∀ x, ∀ᶠ v in cofinite, pf v x ∈ K v) {S₀ : Finset V}
    (hS : ∀ v ∉ S₀, μf v (K v) = 1) (h1 : ∀ v ∉ S₀, ∀ y ∈ K v, ff v y = 1)
    (hfa : ∀ w, Integrable (fa w) (μa w)) (hff : ∀ v, Integrable (ff v) (μf v)) {C : ℝ}
    (hC : ∀ S : Finset V, S₀ ⊆ S → ∏ v ∈ S, ∫ y, ‖ff v y‖ ∂μf v ≤ C) :
    Integrable (fun x => (∏ w, fa w (pa w x)) * ∏ᶠ v, ff v (pf v x)) μ := by
  have hi := fun S : {S : Finset V // S₀ ⊆ S} => (h.setIntegral_tensor ha hf hK
    (fun v hv => hS v fun h' => hv (S.2 h')) (fun v hv => h1 v fun h' => hv (S.2 h')) hfa fun v _ => hff v).1
  have hn := fun S : {S : Finset V // S₀ ⊆ S} => (h.setIntegral_tensor ha hf hK (fa := fun w y => ‖fa w y‖)
    (ff := fun v y => ‖ff v y‖) (fun v hv => hS v fun h' => hv (S.2 h'))
    (fun v hv y hy => by rw [h1 v (fun h' => hv (S.2 h')) y hy, norm_one])
    (fun w => (hfa w).norm) fun v _ => (hff v).norm).2
  rw [← integrableOn_univ, ← iUnion_level hX S₀]
  refine ⟨AEStronglyMeasurable.iUnion fun S => (hi S).1, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, setLIntegral_iUnion_of_directed _ (directed_level S₀)]
  refine (iSup_le fun S => ?_).trans_lt (ENNReal.ofReal_lt_top (r := (∏ w, ∫ y, ‖fa w y‖ ∂μa w) * C))
  rw [← ofReal_integral_norm_eq_lintegral_enorm (hi S)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq_of_le (Eq.trans ?_ (hn S)) (mul_le_mul_of_nonneg_left (hC S S.2)
    (Finset.prod_nonneg fun w _ => integral_nonneg fun _ => norm_nonneg _)))
  refine setIntegral_congr_fun (measurableSet_level hf hK S) fun x hx => ?_
  have h2 : ∀ v ∉ S.1, ∀ y ∈ K v, ff v y = 1 := fun v hv => h1 v fun h' => hv (S.2 h')
  simp only [finprod_eq_prod_of_mem h2 hx, norm_mul, norm_prod, finprod_eq_prod_of_mem (ff := fun v y => ‖ff v y‖)
    (fun v hv y hy => by rw [h2 v hv y hy, norm_one]) hx]

theorem IsCylProd.tendsto_integral_tensor (hX : ∀ x, ∀ᶠ v in cofinite, pf v x ∈ K v) {S₀ : Finset V}
    (hS : ∀ v ∉ S₀, μf v (K v) = 1) (h1 : ∀ v ∉ S₀, ∀ y ∈ K v, ff v y = 1)
    (hfa : ∀ w, Integrable (fa w) (μa w)) (hff : ∀ v, Integrable (ff v) (μf v))
    (hi : Integrable (fun x => (∏ w, fa w (pa w x)) * ∏ᶠ v, ff v (pf v x)) μ) :
    Tendsto (fun S : Finset V => (∏ w, ∫ y, fa w y ∂μa w) * ∏ v ∈ S, ∫ y, ff v y ∂μf v) atTop
      (𝓝 (∫ x, (∏ w, fa w (pa w x)) * ∏ᶠ v, ff v (pf v x) ∂μ)) := by
  have hu : ⋃ S : Finset V, {x | ∀ v ∉ S, pf v x ∈ K v} = univ :=
    eq_univ_of_forall fun x => mem_iUnion.2 (exists_finset_of_eventually (hX x))
  have := tendsto_setIntegral_of_monotone (measurableSet_level hf hK) monotone_level hi.integrableOn
  rw [hu, Measure.restrict_univ] at this
  refine this.congr' ((eventually_ge_atTop S₀).mono fun S hs => ?_)
  exact (h.setIntegral_tensor ha hf hK (fun v hv => hS v fun h' => hv (hs h'))
    (fun v hv => h1 v fun h' => hv (hs h')) hfa fun v _ => hff v).2

omit h ha hf [Countable V] [∀ v, SigmaFinite (μf v)] in

theorem multipliable_integral {S₀ : Finset V} (hS : ∀ v ∉ S₀, μf v (K v) = 1)
    (h1 : ∀ v ∉ S₀, ∀ y ∈ K v, ff v y = 1) (hff : ∀ v, Integrable (ff v) (μf v)) {C : ℝ}
    (hC : ∀ S : Finset V, S₀ ⊆ S → ∏ v ∈ S, ∫ y, ‖ff v y‖ ∂μf v ≤ C) :
    Multipliable fun v => ∫ y, ff v y ∂μf v := by
  classical
  have h0 : ∀ v, 0 ≤ ∫ y, ‖ff v y‖ ∂μf v := fun v => integral_nonneg fun _ => norm_nonneg _
  rcases (Finset.prod_nonneg fun v (_ : v ∈ S₀) => h0 v).eq_or_lt with hP | hP
  · obtain ⟨v, -, hv⟩ := Finset.prod_eq_zero_iff.1 hP.symm
    exact multipliable_of_exists_eq_zero ⟨v, norm_le_zero_iff.1 ((norm_integral_le_integral_norm _).trans hv.le)⟩
  have hb : ∀ v ∉ S₀, 1 + ‖∫ y, ff v y ∂μf v - 1‖ ≤ ∫ y, ‖ff v y‖ ∂μf v := fun v hv => by
    have e1 : ∫ y in K v, ff v y ∂μf v = 1 := by
      rw [setIntegral_congr_fun (hK v) (g := fun _ => 1) (h1 v hv)]
      simp [measureReal_def, hS v hv]
    have e2 : ∫ y in K v, ‖ff v y‖ ∂μf v = 1 := by
      rw [setIntegral_congr_fun (hK v) (g := fun _ => 1) fun y hy => by simp [h1 v hv y hy]]
      simp [measureReal_def, hS v hv]
    rw [← integral_add_compl (hK v) (hff v), ← integral_add_compl (hK v) (hff v).norm, e1, e2, add_sub_cancel_left]
    exact add_le_add_right (norm_integral_le_integral_norm _) _
  have hs : Summable fun v => ‖∫ y, ff v y ∂μf v - 1‖ := by
    refine summable_of_sum_le (c := ∑ v ∈ S₀, ‖∫ y, ff v y ∂μf v - 1‖ + C / ∏ v ∈ S₀, ∫ y, ‖ff v y‖ ∂μf v)
      (fun _ => norm_nonneg _) fun T => ?_
    refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_right (s₁ := S₀))
      fun _ _ _ => norm_nonneg _).trans ?_
    rw [← Finset.union_sdiff_self_eq_union, Finset.sum_union Finset.disjoint_sdiff]
    refine add_le_add_right ?_ _
    have e := hC (S₀ ∪ T \ S₀) Finset.subset_union_left
    rw [Finset.prod_union Finset.disjoint_sdiff, ← le_div_iff₀' hP] at e
    refine le_trans ?_ ((Finset.prod_le_prod (fun v _ => by positivity)
      fun v hv => hb v (Finset.mem_sdiff.1 hv).2).trans e)
    exact (le_add_of_nonneg_left zero_le_one).trans (one_add_sum_le_prod_one_add _ fun _ => norm_nonneg _)
  simpa using multipliable_one_add_of_summable hs

theorem IsCylProd.integral_tensor_eq_tprod (hX : ∀ x, ∀ᶠ v in cofinite, pf v x ∈ K v) {S₀ : Finset V}
    (hS : ∀ v ∉ S₀, μf v (K v) = 1) (h1 : ∀ v ∉ S₀, ∀ y ∈ K v, ff v y = 1)
    (hfa : ∀ w, Integrable (fa w) (μa w)) (hff : ∀ v, Integrable (ff v) (μf v)) {C : ℝ}
    (hC : ∀ S : Finset V, S₀ ⊆ S → ∏ v ∈ S, ∫ y, ‖ff v y‖ ∂μf v ≤ C) :
    ∫ x, (∏ w, fa w (pa w x)) * ∏ᶠ v, ff v (pf v x) ∂μ = (∏ w, ∫ y, fa w y ∂μa w) * ∏' v, ∫ y, ff v y ∂μf v :=
  tendsto_nhds_unique (h.tendsto_integral_tensor ha hf hK hX hS h1 hfa hff
    (h.integrable_tensor ha hf hK hX hS h1 hfa hff hC))
    (Tendsto.const_mul _ (multipliable_integral hK hS h1 hff hC).hasProd)

end GlobalTheory.RestrMeas

namespace GlobalTheory.AdelicU

open NumberField IsDedekindDomain GlobalTheory.RestrMeas

theorem IsRestrictedProd.euler_product {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
    [Submodule.IsLattice E L] {μa : ∀ w, Measure (GArch σ J w)} {μf : ∀ v, Measure (GLoc σ J v)}
    {μ : Measure (GAd σ J)} (h : IsRestrictedProd σ J L μa μf μ) (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v ∉ S₀, μf v (stabLoc σ J L v) = 1) :
    (∀ (fa : ∀ w, GArch σ J w → ℂ) (ff : ∀ v, GLoc σ J v → ℂ), (∀ w, Integrable (fa w) (μa w)) →
      ((∀ v ∉ S₀, ∀ y ∈ stabLoc σ J L v, ff v y = 1) →
        ∀ S : Finset (HeightOneSpectrum (𝓞 F)), S₀ ⊆ S → (∀ v ∈ S, Integrable (ff v) (μf v)) →
          IntegrableOn (fun g => (∏ w, fa w (projArch σ J w g)) * ∏ᶠ v, ff v (proj σ J v g))
            {g | ∀ v ∉ S, proj σ J v g ∈ stabLoc σ J L v} μ ∧
          ∫ g in {g | ∀ v ∉ S, proj σ J v g ∈ stabLoc σ J L v},
              (∏ w, fa w (projArch σ J w g)) * ∏ᶠ v, ff v (proj σ J v g) ∂μ =
            (∏ w, ∫ y, fa w y ∂μa w) * ∏ v ∈ S, ∫ y, ff v y ∂μf v) ∧
      ((∀ v ∉ S₀, ff v = (stabLoc σ J L v : Set (GLoc σ J v)).indicator 1) →
        (∀ v ∈ S₀, Integrable (ff v) (μf v)) →
          Integrable (fun g => (∏ w, fa w (projArch σ J w g)) * ∏ᶠ v, ff v (proj σ J v g)) μ ∧
          ∫ g, (∏ w, fa w (projArch σ J w g)) * ∏ᶠ v, ff v (proj σ J v g) ∂μ =
            (∏ w, ∫ y, fa w y ∂μa w) * ∏ v ∈ S₀, ∫ y, ff v y ∂μf v) ∧
      ((∀ v ∉ S₀, ∀ y ∈ stabLoc σ J L v, ff v y = 1) → (∀ v, Integrable (ff v) (μf v)) →
        (∃ C : ℝ, ∀ S : Finset (HeightOneSpectrum (𝓞 F)), S₀ ⊆ S → ∏ v ∈ S, ∫ y, ‖ff v y‖ ∂μf v ≤ C) →
          Integrable (fun g => (∏ w, fa w (projArch σ J w g)) * ∏ᶠ v, ff v (proj σ J v g)) μ ∧
          Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) =>
              (∏ w, ∫ y, fa w y ∂μa w) * ∏ v ∈ S, ∫ y, ff v y ∂μf v) atTop
            (𝓝 (∫ g, (∏ w, fa w (projArch σ J w g)) * ∏ᶠ v, ff v (proj σ J v g) ∂μ)) ∧
          (Multipliable fun v => ∫ y, ff v y ∂μf v) ∧
          ∫ g, (∏ w, fa w (projArch σ J w g)) * ∏ᶠ v, ff v (proj σ J v g) ∂μ =
            (∏ w, ∫ y, fa w y ∂μa w) * ∏' v, ∫ y, ff v y ∂μf v)) ∧
    ∀ (fa : ∀ w, GArch σ J w → ℝ≥0∞) (ff : ∀ v, GLoc σ J v → ℝ≥0∞), (∀ w, AEMeasurable (fa w) (μa w)) →
      ((∀ v ∉ S₀, ∀ y ∈ stabLoc σ J L v, ff v y = 1) →
        ∀ S : Finset (HeightOneSpectrum (𝓞 F)), S₀ ⊆ S → (∀ v ∈ S, AEMeasurable (ff v) (μf v)) →
          ∫⁻ g in {g | ∀ v ∉ S, proj σ J v g ∈ stabLoc σ J L v},
              (∏ w, fa w (projArch σ J w g)) * ∏ᶠ v, ff v (proj σ J v g) ∂μ =
            (∏ w, ∫⁻ y, fa w y ∂μa w) * ∏ v ∈ S, ∫⁻ y, ff v y ∂μf v) ∧
      ((∀ v ∉ S₀, ff v = (stabLoc σ J L v : Set (GLoc σ J v)).indicator 1) →
        (∀ v ∈ S₀, AEMeasurable (ff v) (μf v)) →
          ∫⁻ g, (∏ w, fa w (projArch σ J w g)) * ∏ᶠ v, ff v (proj σ J v g) ∂μ =
            (∏ w, ∫⁻ y, fa w y ∂μa w) * ∏ v ∈ S₀, ∫⁻ y, ff v y ∂μf v) ∧
      ((∀ v ∉ S₀, ∀ y ∈ stabLoc σ J L v, ff v y = 1) → (∀ v, AEMeasurable (ff v) (μf v)) →
          ∫⁻ g, (∏ w, fa w (projArch σ J w g)) * ∏ᶠ v, ff v (proj σ J v g) ∂μ =
            ⨆ (S : Finset (HeightOneSpectrum (𝓞 F))) (_ : S₀ ⊆ S),
              (∏ w, ∫⁻ y, fa w y ∂μa w) * ∏ v ∈ S, ∫⁻ y, ff v y ∂μf v) := by
  have := h.haar_arch
  have := h.haar_loc
  have := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum F
  have hc := h.isCylProd
  have ha := fun w => (continuous_projArch σ J w).measurable
  have hf := fun v => (continuous_proj σ J v).measurable
  have hK := fun v => (isOpen_stabLoc σ J L v).measurableSet
  have hX := eventually_proj_mem_stabLoc σ J L
  refine ⟨fun fa ff hfa => ⟨fun h1 S hs hff => ?_, fun h1 hff => hc.integral_tensor_indicator ha hf hK hX hS h1 hfa hff,
    fun h1 hff ⟨C, hC⟩ => ?_⟩, fun fa ff hfa => ⟨fun h1 S hs hff => ?_,
    fun h1 hff => hc.lintegral_tensor_indicator ha hf hK hX hS h1 hfa hff,
    fun h1 hff => hc.lintegral_tensor ha hf hK hX hS h1 hfa hff⟩⟩
  · exact hc.setIntegral_tensor ha hf hK (fun v hv => hS v fun h' => hv (hs h'))
      (fun v hv => h1 v fun h' => hv (hs h')) hfa hff
  · have hi := hc.integrable_tensor ha hf hK hX hS h1 hfa hff hC
    exact ⟨hi, hc.tendsto_integral_tensor ha hf hK hX hS h1 hfa hff hi, multipliable_integral hK hS h1 hff hC,
      hc.integral_tensor_eq_tprod ha hf hK hX hS h1 hfa hff hC⟩
  · exact hc.setLIntegral_tensor ha hf hK (fun v hv => hS v fun h' => hv (hs h'))
      (fun v hv => h1 v fun h' => hv (hs h')) hfa hff

end GlobalTheory.AdelicU

end
