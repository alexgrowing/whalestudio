import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.AbsProd

theorem lintegral_prod_infinitePi {ι : Type} {V : ι → Type} [∀ i, MeasurableSpace (V i)]
    (P : ∀ i, Measure (V i)) [∀ i, IsProbabilityMeasure (P i)] (S : Finset ι)
    (f : ∀ i, V i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ Y, ∏ i ∈ S, f i (Y i) ∂(Measure.infinitePi P) = ∏ i ∈ S, ∫⁻ y, f i y ∂(P i) := by
  rw [ProbabilityTheory.lintegral_prod_eq_prod_lintegral_of_indepFun S (fun i (Y : ∀ i, V i) => f i (Y i))
    (ProbabilityTheory.iIndepFun_infinitePi (P := P) hf)
    (fun i => (hf i).comp (measurable_pi_apply i))]
  exact Finset.prod_congr rfl fun i _ =>
    (measurePreserving_eval_infinitePi P i).lintegral_comp (hf i)

theorem tail_split {ι : Type} [DecidableEq ι] (c : ι → ℝ) (hs : Summable fun i => |c i - 1|)
    {T S : Finset ι} (h : T ⊆ S) :
    ∏' i : {i : ι // i ∉ T}, c i.1 = (∏ i ∈ S \ T, c i) * ∏' i : {i : ι // i ∉ S}, c i.1 := by
  have key : ∀ U : Finset ι, ∏' i : {i : ι // i ∉ U}, c i.1 = ∏' i, (if i ∈ U then 1 else c i) := by
    intro U
    have := tprod_subtype {i | i ∉ U} c
    refine this.trans (tprod_congr fun i => ?_)
    by_cases hi : i ∈ U <;> simp [Set.mulIndicator, hi]
  have hm : Multipliable fun i => (if i ∈ S then 1 else c i) := by
    have h1 : Summable fun i => (if i ∈ S then (0 : ℝ) else c i - 1) := by
      refine Summable.of_norm_bounded hs fun i => ?_
      by_cases hi : i ∈ S <;> simp [hi]
    refine (Real.multipliable_one_add_of_summable h1).congr fun i => ?_
    by_cases hi : i ∈ S <;> simp [hi]
  have hf : HasProd (fun i => if i ∈ S \ T then c i else 1) (∏ i ∈ S \ T, c i) := by
    have := hasProd_prod_of_ne_finset_one (f := fun i => if i ∈ S \ T then c i else 1)
      (s := S \ T) (L := SummationFilter.unconditional ι) (fun b hb => if_neg hb)
    rwa [Finset.prod_congr rfl (fun i hi => if_pos hi)] at this
  rw [key, key, ← hf.tprod_eq, ← hf.multipliable.tprod_mul hm]
  refine tprod_congr fun i => ?_
  by_cases hT : i ∈ T
  · simp [hT, h hT]
  · by_cases hS : i ∈ S <;> simp [hT, hS]

theorem exists_piece {ι : Type} {V : ι → Type} [∀ i, MeasurableSpace (V i)]
    (a : ∀ i, Measure (V i)) (hσ : ∀ i, SigmaFinite (a i)) (T : Finset ι) (c : ι → ℝ)
    (hc0 : ∀ i, 0 ≤ c i) (hs : Summable fun i => |c i - 1|)
    (ha : ∀ i ∉ T, a i Set.univ = ENNReal.ofReal (c i)) :
    ∃ ν : Measure (∀ i, V i), SFinite ν ∧ ∀ S : Finset ι, T ⊆ S → ∀ f : ∀ i, V i → ℝ≥0∞,
      (∀ i, Measurable (f i)) → ∫⁻ Y, ∏ i ∈ S, f i (Y i) ∂ν =
        (∏ i ∈ S, ∫⁻ y, f i y ∂(a i)) * ENNReal.ofReal (∏' i : {i : ι // i ∉ S}, c i.1) := by
  classical
  by_cases h0 : ∃ i, a i = 0
  · obtain ⟨i, hi⟩ := h0
    refine ⟨0, inferInstance, fun S hS f _ => ?_⟩
    rw [lintegral_zero_measure]
    by_cases hiS : i ∈ S
    · rw [Finset.prod_eq_zero hiS (by simp [hi]), zero_mul]
    · have h1 := ha i (fun h => hiS (hS h))
      have h2 : c i = 0 := by
        rw [hi] at h1
        exact le_antisymm (ENNReal.ofReal_eq_zero.1 h1.symm) (hc0 i)
      rw [tail_split c hs (Finset.subset_insert i S),
        Finset.prod_eq_zero (s := insert i S \ S) (i := i) (by simp [hiS]) h2]
      simp
  push Not at h0
  have hP : ∀ i, ∃ (P : Measure (V i)) (g : V i → ℝ≥0∞), IsProbabilityMeasure P ∧ Measurable g ∧
      (i ∉ T → ∀ y, g y = 1) ∧ ∀ f : V i → ℝ≥0∞, Measurable f →
        ∫⁻ y, f y ∂(a i) = (if i ∈ T then 1 else ENNReal.ofReal (c i)) * ∫⁻ y, g y * f y ∂P := by
    intro i
    haveI : NeZero (a i) := ⟨h0 i⟩
    by_cases hi : i ∈ T
    · refine ⟨(a i).toFinite, (a i).rnDeriv (a i).toFinite, inferInstance,
        Measure.measurable_rnDeriv _ _, fun h => (h hi).elim, fun f hf => ?_⟩
      rw [if_pos hi, one_mul]
      conv_lhs => rw [← Measure.withDensity_rnDeriv_eq (a i) (a i).toFinite
        (absolutelyContinuous_toFinite _)]
      rw [lintegral_withDensity_eq_lintegral_mul _ (Measure.measurable_rnDeriv _ _) hf]
      rfl
    · haveI : IsFiniteMeasure (a i) := ⟨by rw [ha i hi]; exact ENNReal.ofReal_lt_top⟩
      refine ⟨(a i Set.univ)⁻¹ • a i, fun _ => 1, inferInstance, measurable_const,
        fun _ _ => rfl, fun f _ => ?_⟩
      rw [if_neg hi, ← ha i hi, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
        ENNReal.mul_inv_cancel (by simpa using h0 i) (measure_ne_top _ _)]
      simp
  choose P g hP hg hg1 hint using hP
  have hG : Measurable fun Y : ∀ i, V i =>
      ENNReal.ofReal (∏' i : {i : ι // i ∉ T}, c i.1) * ∏ i ∈ T, g i (Y i) :=
    (Finset.measurable_prod _ fun i _ => (hg i).comp (measurable_pi_apply i)).const_mul _
  refine ⟨(Measure.infinitePi P).withDensity
    (fun Y => ENNReal.ofReal (∏' i : {i : ι // i ∉ T}, c i.1) * ∏ i ∈ T, g i (Y i)),
    inferInstance, fun S hS f hf => ?_⟩
  have hF : Measurable fun Y : ∀ i, V i => ∏ i ∈ S, f i (Y i) :=
    Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)
  rw [lintegral_withDensity_eq_lintegral_mul _ hG hF]
  have h1 : ∀ Y : ∀ i, V i, ((fun Y : ∀ i, V i =>
      ENNReal.ofReal (∏' i : {i : ι // i ∉ T}, c i.1) * ∏ i ∈ T, g i (Y i)) *
      fun Y : ∀ i, V i => ∏ i ∈ S, f i (Y i)) Y =
      ENNReal.ofReal (∏' i : {i : ι // i ∉ T}, c i.1) * ∏ i ∈ S, (g i (Y i) * f i (Y i)) := by
    intro Y
    rw [Pi.mul_apply, Finset.prod_mul_distrib, mul_assoc,
      Finset.prod_subset hS (fun i _ hi => hg1 i hi (Y i))]
  simp_rw [h1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_prod_infinitePi P S (fun i y => g i y * f i y) (fun i => (hg i).mul (hf i)),
    Finset.prod_congr rfl (fun i _ => hint i (f i) (hf i)), Finset.prod_mul_distrib,
    tail_split c hs hS, ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => hc0 i),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => hc0 i)]
  have h2 : ∏ i ∈ S, (if i ∈ T then 1 else ENNReal.ofReal (c i)) =
      ∏ i ∈ S \ T, ENNReal.ofReal (c i) := by
    rw [← Finset.prod_subset (Finset.sdiff_subset (s := S) (t := T))
      (fun i hi hi' => if_pos (by simpa [hi] using hi'))]
    exact Finset.prod_congr rfl fun i hi => if_neg (Finset.mem_sdiff.1 hi).2
  rw [h2]
  ring

theorem exists_restricted_product : ∀ (ι : Type) [Countable ι] (V₀ : Type) [MeasurableSpace V₀] (V : ι → Type) [∀ i, MeasurableSpace (V i)] (L : ∀ i, Set (V i)) (m₀ : Measure V₀) (m : ∀ i, Measure (V i)), SigmaFinite m₀ → (∀ i, SigmaFinite (m i)) → (∀ i, MeasurableSet (L i)) → (∀ i, m i (L i) ≠ ∞) → (Summable fun i => |(m i (L i)).toReal - 1|) → ∃ ν : Measure (V₀ × ∀ i, V i), ν {Y | ¬ ∀ᶠ i in Filter.cofinite, Y.2 i ∈ L i} = 0 ∧ ∀ (S : Finset ι) (f₀ : V₀ → ℝ≥0∞) (f : ∀ i, V i → ℝ≥0∞), Measurable f₀ → (∀ i, Measurable (f i)) → ∫⁻ Y in {Y | ∀ i ∉ S, Y.2 i ∈ L i}, f₀ Y.1 * ∏ i ∈ S, f i (Y.2 i) ∂ν = (∫⁻ y, f₀ y ∂m₀) * (∏ i ∈ S, ∫⁻ y, f i y ∂(m i)) * ENNReal.ofReal (∏' i : {i : ι // i ∉ S}, (m i.1 (L i.1)).toReal) := by
  intro ι _ V₀ _ V _ L m₀ m h₀ hm hL hfin hs
  classical
  let a : Finset ι → ∀ i, Measure (V i) := fun T i =>
    (m i).restrict (if i ∈ T then (L i)ᶜ else L i)
  have hex := fun T : Finset ι => exists_piece (a T) (fun i => by dsimp only [a]; infer_instance) T
    (fun i => (m i (L i)).toReal) (fun i => ENNReal.toReal_nonneg) hs
    (fun i hi => by simp [a, hi, ENNReal.ofReal_toReal (hfin i)])
  choose ν hν hint using hex
  have hnull : ∀ (T : Finset ι) (i : ι) (N : Set (V i)), MeasurableSet N → a T i N = 0 →
      ν T {Y | Y i ∈ N} = 0 := by
    intro T i N hN h
    have hm' : ∀ j, Measurable (Function.update (fun j (_ : V j) => (1 : ℝ≥0∞)) i
        (N.indicator 1) j) := by
      intro j
      by_cases hj : j = i
      · subst hj
        rw [Function.update_self]
        exact measurable_const.indicator hN
      · rw [Function.update_of_ne hj]
        exact measurable_const
    have h1 := hint T (insert i T) (Finset.subset_insert i T) _ hm'
    rw [Finset.prod_eq_zero (Finset.mem_insert_self i T)
      (by rw [Function.update_self, lintegral_indicator_one hN, h]), zero_mul] at h1
    have hN' : MeasurableSet {Y : ∀ i, V i | Y i ∈ N} := measurable_pi_apply i hN
    rw [← lintegral_indicator_one hN', ← h1]
    refine lintegral_congr fun Y => ?_
    rw [Finset.prod_eq_single i (fun j _ hj => by rw [Function.update_of_ne hj])
      (fun h => (h (Finset.mem_insert_self i T)).elim), Function.update_self]
    rfl
  let B : Finset ι → Set (∀ i, V i) := fun S => {Y | ∀ i ∉ S, Y i ∈ L i}
  have hB : ∀ S, MeasurableSet (B S) := by
    intro S
    have : B S = ⋂ i, ⋂ (_ : i ∉ S), {Y | Y i ∈ L i} := by ext; simp [B]
    rw [this]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => measurable_pi_apply i (hL i)
  have hin : ∀ T S : Finset ι, T ⊆ S → ν T (B S)ᶜ = 0 := by
    intro T S h
    have : (B S)ᶜ = ⋃ i, ⋃ (_ : i ∉ S), {Y | Y i ∈ (L i)ᶜ} := by ext; simp [B]
    rw [this]
    refine measure_iUnion_null fun i => measure_iUnion_null fun hi => hnull T i _ (hL i).compl ?_
    have hT : i ∉ T := fun h' => hi (h h')
    simp [a, hT, Measure.restrict_apply (hL i).compl]
  have hout : ∀ T S : Finset ι, ¬ T ⊆ S → ν T (B S) = 0 := by
    intro T S h
    obtain ⟨i, hT, hS⟩ := Finset.not_subset.1 h
    refine measure_mono_null (t := {Y | Y i ∈ L i}) (fun Y hY => hY i hS) (hnull T i _ (hL i) ?_)
    simp [a, hT, Measure.restrict_apply (hL i)]
  refine ⟨m₀.prod (Measure.sum ν), ?_, fun S f₀ f hf₀ hf => ?_⟩
  · refine measure_mono_null (t := Set.univ ×ˢ ⋂ S, (B S)ᶜ) (fun Y hY => ?_) ?_
    · refine ⟨trivial, Set.mem_iInter.2 fun S hS => hY ?_⟩
      exact S.eventually_cofinite_notMem.mono fun i hi => hS i hi
    · rw [Measure.prod_prod, Measure.sum_apply_eq_zero.2
        (fun T => measure_mono_null (Set.iInter_subset _ T) (hin T T subset_rfl)), mul_zero]
  · have hF : Measurable fun Y : ∀ i, V i => ∏ i ∈ S, f i (Y i) :=
      Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)
    have e : {Y : V₀ × ∀ i, V i | ∀ i ∉ S, Y.2 i ∈ L i} = Set.univ ×ˢ B S := by ext; simp [B]
    rw [e, ← Measure.prod_restrict, Measure.restrict_univ,
      lintegral_prod_mul hf₀.aemeasurable hF.aemeasurable, mul_assoc]
    congr 1
    rw [Measure.restrict_sum _ (hB S), lintegral_sum_measure,
      tsum_eq_sum (s := S.powerset) (fun T hT => by
        rw [Measure.restrict_eq_zero.2 (hout T S (by simpa using hT)), lintegral_zero_measure])]
    have h1 : ∀ i ∈ S, ∫⁻ y, f i y ∂(m i) =
        ∫⁻ y in (L i)ᶜ, f i y ∂(m i) + ∫⁻ y in L i, f i y ∂(m i) := fun i _ => by
      rw [add_comm, lintegral_add_compl _ (hL i)]
    rw [Finset.prod_congr rfl h1, Finset.prod_add, Finset.sum_mul]
    refine Finset.sum_congr rfl fun T hT => ?_
    have hTS : T ⊆ S := Finset.mem_powerset.1 hT
    rw [Measure.restrict_eq_self_of_ae_mem (s := B S) (hin T S hTS), hint T S hTS f hf,
      ← Finset.prod_sdiff hTS, mul_comm (∏ i ∈ S \ T, _)]
    congr 2
    · exact Finset.prod_congr rfl fun i hi => by simp [a, hi]
    · exact Finset.prod_congr rfl fun i hi => by simp [a, (Finset.mem_sdiff.1 hi).2]

end GlobalTheory.GaugeEx.AbsProd
