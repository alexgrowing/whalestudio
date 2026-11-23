import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.prodExt :
    ∀ (Ω X Z : Type) [MeasurableSpace Ω] [MeasurableSpace X] [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    [SecondCountableTopology Z] [T2Space Z] (ν : Measure Ω) (r : Ω → X) (s : Ω → Z) (ρ : Ω → ℂ),
    TopologicalSpace.IsTopologicalBasis {T : Set Z | IsCompact T ∧ IsOpen T} → Measurable r → Measurable s → Integrable ρ ν →
    (∀ (S : Set X) (T : Set Z), MeasurableSet S → IsCompact T → IsOpen T → ∫ ω, S.indicator 1 (r ω) * (T.indicator 1 (s ω) * ρ ω) ∂ν = 0) →
    ∀ Q : X × Z → ℂ, Measurable Q → (∀ x, ‖Q x‖ ≤ 1) → ∫ ω, Q (r ω, s ω) * ρ ω ∂ν = 0 := by
  intro Ω X Z _ _ _ _ _ _ _ ν r s ρ hB hr hs hρ H Q hQ hQ1
  have hφ : Measurable (fun ω => (r ω, s ω)) := hr.prodMk hs

  obtain ⟨e, he, heU⟩ : ∃ e : ℕ → Set Z, (∀ n, IsCompact (e n) ∧ IsOpen (e n)) ∧ ⋃ n, e n = Set.univ := by
    obtain ⟨T, hTc, hTs, hTU⟩ := TopologicalSpace.isOpen_sUnion_countable
      {T : Set Z | IsCompact T ∧ IsOpen T} (fun t ht => ht.2)
    have hne : (insert ∅ T).Nonempty := Set.insert_nonempty _ _
    obtain ⟨e, he⟩ := (hTc.insert ∅).exists_eq_range hne
    refine ⟨e, fun n => ?_, ?_⟩
    · have hn : e n ∈ insert ∅ T := he ▸ Set.mem_range_self n
      rcases hn with hn | hn
      · rw [hn]; exact ⟨isCompact_empty, isOpen_empty⟩
      · exact hTs hn
    · rw [← Set.sUnion_range, ← he, Set.sUnion_insert, Set.empty_union, hTU, hB.sUnion_eq]

  have hmass : ∫ ω, ρ ω ∂ν = 0 := by
    have hF : ∀ n, ∫ ω, (Set.accumulate e n).indicator (1 : Z → ℂ) (s ω) * ρ ω ∂ν = 0 := by
      intro n
      have hc : IsCompact (Set.accumulate e n) := isCompact_accumulate (fun i => (he i).1) n
      have ho : IsOpen (Set.accumulate e n) := by
        rw [Set.accumulate_def]
        exact isOpen_biUnion (fun i _ => (he i).2)
      have := H Set.univ (Set.accumulate e n) MeasurableSet.univ hc ho
      simpa using this
    have hlim : Tendsto (fun n => ∫ ω, (Set.accumulate e n).indicator (1 : Z → ℂ) (s ω) * ρ ω ∂ν)
        atTop (𝓝 (∫ ω, ρ ω ∂ν)) := by
      refine tendsto_integral_of_dominated_convergence (fun ω => ‖ρ ω‖) ?_ hρ.norm ?_ ?_
      · intro n
        have hm : MeasurableSet (Set.accumulate e n) :=
          (isCompact_accumulate (fun i => (he i).1) n).isClosed.measurableSet
        exact (((measurable_one.indicator hm).comp hs).aestronglyMeasurable).mul hρ.1
      · intro n
        refine Eventually.of_forall (fun ω => ?_)
        by_cases h : s ω ∈ Set.accumulate e n <;> simp [h]
      · refine Eventually.of_forall (fun ω => ?_)
        have hmem : s ω ∈ ⋃ n, e n := heU ▸ Set.mem_univ _
        obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hmem
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop n] with m hm
        have : s ω ∈ Set.accumulate e m := Set.mem_accumulate.2 ⟨n, hm, hn⟩
        simp [this]
    have := tendsto_nhds_unique hlim (by simp only [hF]; exact tendsto_const_nhds)
    exact this

  have hgen : (inferInstance : MeasurableSpace (X × Z)) =
      MeasurableSpace.generateFrom (Set.image2 (· ×ˢ ·) {S : Set X | MeasurableSet S}
        {T : Set Z | IsCompact T ∧ IsOpen T}) := by
    have hD : IsCountablySpanning {T : Set Z | IsCompact T ∧ IsOpen T} := ⟨e, he, heU⟩
    have h1 : ‹MeasurableSpace Z› = MeasurableSpace.generateFrom {T : Set Z | IsCompact T ∧ IsOpen T} :=
      (BorelSpace.measurable_eq).trans hB.borel_eq_generateFrom
    have := generateFrom_prod_eq (isCountablySpanning_measurableSet (α := X)) hD
    rw [MeasurableSpace.generateFrom_measurableSet, ← h1] at this
    exact this
  have hpi : IsPiSystem (Set.image2 (· ×ˢ ·) {S : Set X | MeasurableSet S}
      {T : Set Z | IsCompact T ∧ IsOpen T}) :=
    MeasurableSpace.isPiSystem_measurableSet.prod
      (fun a ha b hb _ => ⟨ha.1.inter hb.1, ha.2.inter hb.2⟩)
  have hset : ∀ A : Set (X × Z), MeasurableSet A → ∫ ω in (fun ω => (r ω, s ω)) ⁻¹' A, ρ ω ∂ν = 0 := by
    intro A hA
    induction A, hA using MeasurableSpace.induction_on_inter hgen hpi with
    | empty => simp
    | basic t ht =>
      obtain ⟨S, hS, T, hT, rfl⟩ := ht
      have hTm : MeasurableSet T := hT.2.measurableSet
      have hm : MeasurableSet ((fun ω => (r ω, s ω)) ⁻¹' (S ×ˢ T)) := hφ (hS.prod hTm)
      rw [← integral_indicator hm, ← H S T hS hT.1 hT.2]
      congr 1
      funext ω
      by_cases h1 : r ω ∈ S <;> by_cases h2 : s ω ∈ T <;> simp [Set.indicator, h1, h2]
    | compl t htm ih =>
      rw [Set.preimage_compl, setIntegral_compl (hφ htm) hρ, ih, hmass, sub_zero]
    | iUnion f hd hm ih =>
      rw [Set.preimage_iUnion, integral_iUnion (fun i => hφ (hm i))
        (fun i j hij => (hd hij).preimage _) hρ.integrableOn]
      simp [ih]

  have hint : ∀ (f : Ω → ℂ) (C : ℝ), Measurable f → (∀ ω, ‖f ω‖ ≤ C) →
      Integrable (fun ω => f ω * ρ ω) ν := fun f C hf hC =>
    hρ.bdd_mul hf.aestronglyMeasurable (Eventually.of_forall hC)
  have hsimple : ∀ g : SimpleFunc (X × Z) ℂ, ∫ ω, g (r ω, s ω) * ρ ω ∂ν = 0 := by
    intro g
    induction g using SimpleFunc.induction with
    | const c hA =>
      rename_i A
      have hm : MeasurableSet ((fun ω => (r ω, s ω)) ⁻¹' A) := hφ hA
      have h0 := hset A hA
      rw [← integral_indicator hm] at h0
      have : (fun ω => (SimpleFunc.piecewise A hA (SimpleFunc.const _ c) (SimpleFunc.const _ 0)) (r ω, s ω) * ρ ω)
          = fun ω => c * ((fun ω => (r ω, s ω)) ⁻¹' A).indicator ρ ω := by
        funext ω
        by_cases h : (r ω, s ω) ∈ A <;> simp [Set.indicator, h, Set.piecewise]
      rw [this, integral_const_mul, h0, mul_zero]
    | add hd hf hg =>
      rename_i f g
      obtain ⟨Cf, hCf⟩ := f.exists_forall_norm_le
      obtain ⟨Cg, hCg⟩ := g.exists_forall_norm_le
      have hif := hint (fun ω => f (r ω, s ω)) Cf (f.measurable.comp hφ) (fun ω => hCf _)
      have hig := hint (fun ω => g (r ω, s ω)) Cg (g.measurable.comp hφ) (fun ω => hCg _)
      simp only [SimpleFunc.coe_add, Pi.add_apply, add_mul]
      rw [integral_add hif hig, hf, hg, add_zero]

  have hSM : StronglyMeasurable Q := hQ.stronglyMeasurable
  have hlim : Tendsto (fun n => ∫ ω, hSM.approxBounded 1 n (r ω, s ω) * ρ ω ∂ν) atTop
      (𝓝 (∫ ω, Q (r ω, s ω) * ρ ω ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence (fun ω => ‖ρ ω‖) ?_ hρ.norm ?_ ?_
    · intro n
      exact (((hSM.approxBounded 1 n).measurable.comp hφ).aestronglyMeasurable).mul hρ.1
    · intro n
      refine Eventually.of_forall (fun ω => ?_)
      rw [norm_mul]
      have := hSM.norm_approxBounded_le zero_le_one n (r ω, s ω)
      calc _ ≤ 1 * ‖ρ ω‖ := by gcongr
        _ = ‖ρ ω‖ := one_mul _
    · refine Eventually.of_forall (fun ω => ?_)
      exact (hSM.tendsto_approxBounded_of_norm_le (hQ1 _)).mul_const _
  exact tendsto_nhds_unique hlim (by simp only [hsimple]; exact tendsto_const_nhds)
