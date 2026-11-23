import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.ConvExpandStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MaMeasureEqOfConst
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsCompactRWSublevel
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CompactPartIntegralsTendsto
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocDensAddOfFunContinuousOn
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem maMeasure_bdry_eq_zero {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) {n : ℕ}
    (m : Fin n → ℕ) (W : Fin n → Set X) (hS : IsSection A L s) (hSNC : IsSNC A L s m W)
    (Φ : Fin e → LocPot X) : maMeasure A Φ (bdry s) = 0 := by
  have hB := LeviFormBoundaryTopology.isClosed_bdry hS
  have hAn : A.IsAnalyticSubset (bdry s) := by
    intro x
    refine ⟨L.U x, L.isOpen_U x, L.mem_U x, 1, fun _ => s x, fun _ => hS.1 x, ?_⟩
    ext z
    constructor
    · rintro ⟨hz, hzU⟩
      exact ⟨hzU, fun _ => (LeviFormBoundaryTopology.bdry_iff hS hzU).1 hz⟩
    · rintro ⟨hzU, hz⟩
      exact ⟨(LeviFormBoundaryTopology.bdry_iff hS hzU).2 (hz 0), hzU⟩
  have hInt : interior (bdry s) = ∅ := LeviFormBoundaryTopology.interior_bdry_eq_empty hS hSNC
  unfold maMeasure
  split_ifs with h
  · simp only [Measure.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hT := (A.chart j).open_target.measurableSet
    rw [Measure.map_apply_of_aemeasurable (((A.chart j).continuousOn_symm.aemeasurable hT).mono_ac
      (withDensity_absolutelyContinuous _ _)) hB.measurableSet]
    refine withDensity_absolutelyContinuous _ _ ?_
    rw [Measure.restrict_apply' hT]
    have := analyticNull A (bdry s) hAn hInt j
    rw [Set.inter_comm, (A.chart j).image_source_inter_eq'] at this
    rwa [Set.inter_comm]
  · simp

theorem tail_lintegral_le_of_eventually {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (L : LocPot X)
    (s : X → X → ℂ) (hL : IsPotential A L) (hS : IsSection A L s) (Φ : Fin e → LocPot X)
    (ΦT : ℝ → Fin e → LocPot X)
    (hc : ∀ j, ContinuousOn (locDens A Φ j) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (bdry s)ᶜ))
    (hpot : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, IsPotential A (ΦT t i))
    (hunif : ∀ j, ∀ K ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (bdry s)ᶜ, IsCompact K →
      TendstoUniformlyOn (fun t => locDens A (ΦT t) j) (locDens A Φ j) (𝓝[>] 0) K)
    (g : X → ℝ) (hgm : Measurable g) (hgc : ContinuousOn g (bdry s)ᶜ)
    (R B : ℝ)
    (hg1 : ∀ y ∉ bdry s, R ≤ rW L s y → 0 ≤ g y)
    (hB : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∫⁻ y in (bdry s)ᶜ ∩ {y | R ≤ rW L s y}, ENNReal.ofReal (g y)
      ∂maMeasure A (ΦT t) ≤ ENNReal.ofReal B) :
    ∫⁻ y in (bdry s)ᶜ ∩ {y | R ≤ rW L s y}, ENNReal.ofReal (g y) ∂maMeasure A Φ ≤
      ENNReal.ofReal B := by
  have hU : IsOpen (bdry s)ᶜ := (LeviFormBoundaryTopology.isClosed_bdry hS).isOpen_compl
  obtain ⟨hbm, hrm⟩ := TailBoundAlt.bdry_rW_meas A L s hL hS
  let Es : ℕ → Set X := fun N => ((bdry s)ᶜ ∩ {y | R ≤ rW L s y}) ∩ {y | rW L s y ≤ (N : ℝ)}
  have hun : (bdry s)ᶜ ∩ {y | R ≤ rW L s y} = ⋃ N, Es N := by
    ext y
    constructor
    · intro h
      obtain ⟨N, hN⟩ := exists_nat_ge (rW L s y)
      exact Set.mem_iUnion.2 ⟨N, h, hN⟩
    · intro h
      obtain ⟨N, hN⟩ := Set.mem_iUnion.1 h
      exact hN.1
  have hmono : Monotone Es := fun a b hab y hy =>
    ⟨hy.1, show rW L s y ≤ (b : ℝ) from
      le_trans (show rW L s y ≤ (a : ℝ) from hy.2) (Nat.cast_le.2 hab)⟩
  rw [hun, setLIntegral_iUnion_of_directed _ hmono.directed_le]
  refine iSup_le fun N => ?_
  have hEm : MeasurableSet (Es N) :=
    (hbm.compl.inter (measurableSet_le measurable_const hrm)).inter
      (measurableSet_le hrm measurable_const)
  have hKU : {y | y ∉ bdry s ∧ rW L s y ≤ (N : ℝ)} ⊆ (bdry s)ᶜ := fun y hy => hy.1
  have hEK : Es N ⊆ {y | y ∉ bdry s ∧ rW L s y ≤ (N : ℝ)} := fun y hy => ⟨hy.1.1, hy.2⟩
  obtain ⟨-, hint, hlim⟩ := compact_part_integrals_tendsto A (bdry s)ᶜ Φ ΦT hU hc hpot hunif g
    (fun _ => g) (fun _ => hgc)
    (fun u hu x _ => ⟨Set.univ, Filter.univ_mem,
      Eventually.of_forall fun t y _ => refl_mem_uniformity hu⟩)
    _ (Es N) (isCompact_rW_sublevel A L s hL hS (N : ℝ)) hKU hEm hEK
  have hnn : ∀ μ : Measure X, 0 ≤ᵐ[μ.restrict (Es N)] g := fun μ =>
    (ae_restrict_iff' hEm).2 (Eventually.of_forall fun y hy => hg1 y hy.1.1 hy.1.2)
  have hle : ∫ y in Es N, g y ∂maMeasure A Φ ≤ max B 0 := by
    refine le_of_tendsto hlim ?_
    filter_upwards [hB] with t ht
    rw [integral_eq_lintegral_of_nonneg_ae (hnn _) hgm.aestronglyMeasurable,
      ← ENNReal.toReal_ofReal']
    exact ENNReal.toReal_mono ENNReal.ofReal_ne_top
      ((lintegral_mono_set (fun y hy => hy.1)).trans ht)
  rw [← ofReal_integral_eq_lintegral_ofReal (hint.mono_set hEK) (hnn _)]
  refine (ENNReal.ofReal_le_ofReal hle).trans (le_of_eq ?_)
  rcases le_total B 0 with h | h
  · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
  · rw [max_eq_left h]

theorem limit_measure_tail : TailBoundStatement → ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ) (W : Fin n → Set X), IsPotential A Θ → IsPosPot A Θ → IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → ∀ (th : Fin e → LocPot X) (ph : Fin e → X → ℝ) (phT : Fin e → ℝ → X → ℝ) (C₅ C t₀ : ℝ), (∀ i, IsSingWeight A L s (th i) (ph i) C₅) → (∀ i, IsRegFamily A Θ L s (th i) (ph i) (phT i) C t₀) → (∀ i, IsRegFamilyC2 A s (ph i) (phT i)) → IsFiniteMeasure (maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ)) ∧ ∃ K : ℝ, ∀ R : ℝ, Real.exp 1 ≤ R → maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ) (bdry s ∪ {y | R ≤ rW L s y}) ≤ ENNReal.ofReal (K * Real.log R / R) ∧ ∫⁻ y in (bdry s)ᶜ ∩ {y | R ≤ rW L s y}, ENNReal.ofReal (Real.log (rW L s y)) ∂maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ) ≤ ENNReal.ofReal (K * Real.log R ^ 2 / R) := by
  intro hTB e X _ _ _ _ _ A Θ L s n m W hΘ hpos hL hS hSNC hnorm th ph phT C₅ C t₀ hW hR hC2
  obtain ⟨K, t₁, ht₁, -, hT⟩ :=
    tail_uniform hTB A Θ L s m W hΘ hpos hL hS hSNC hnorm th ph phT C₅ C t₀ hW hR
  have hB := LeviFormBoundaryTopology.isClosed_bdry hS
  obtain ⟨-, hrm⟩ := TailBoundAlt.bdry_rW_meas A L s hL hS
  have hrc := (rW_open A L s hL hS).1
  have hge := rW_ge L s hnorm
  have hc := locDens_add_ofFun_continuousOn A (bdry s)ᶜ th ph Θ hB.isOpen_compl
    (fun i => (hW i).1) hΘ (fun i => (hW i).2.1)
  have hsm : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, A.Smooth (phT i t) := eventually_all.2 fun i => by
    filter_upwards [Ioc_mem_nhdsGT (hR i).1] with t ht
    exact ((hR i).2.2 t ht.1 ht.2).1
  have hunif := conv_dens A Θ s th ph phT hB hΘ (fun i => (hW i).1) (fun i => (hW i).2.1) hsm hC2
  have hbd : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Set.Ioc 0 t₁ := Ioc_mem_nhdsGT ht₁
  have hpot : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, IsPotential A (th i + LocPot.ofFun (phT i t) + Θ) := by
    filter_upwards [hbd] with t ht
    exact fun i => ((hT (fun _ => t) fun _ => ht).1 i).1
  have tail1 : ∀ R : ℝ, Real.exp 1 ≤ R →
      maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ) ((bdry s)ᶜ ∩ {y | R ≤ rW L s y}) ≤
        ENNReal.ofReal (K * Real.log R / R) := by
    intro R hRe
    have h := tail_lintegral_le_of_eventually A L s hL hS
      (fun i => th i + LocPot.ofFun (ph i) + Θ) (fun t i => th i + LocPot.ofFun (phT i t) + Θ)
      hc hpot hunif (fun _ => 1) measurable_const continuousOn_const
      R (K * Real.log R / R)
      (fun _ _ _ => zero_le_one) (by
        filter_upwards [hbd] with t ht
        have h1 := ((hT (fun _ => t) fun _ => ht).2 R hRe).1
        simp only [ENNReal.ofReal_one, lintegral_const, one_mul, Measure.restrict_apply,
          MeasurableSet.univ, Set.univ_inter]
        exact (measure_mono fun y hy => Or.inr hy.2).trans h1)
    simpa using h
  have tail : ∀ R : ℝ, Real.exp 1 ≤ R →
      maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ) (bdry s ∪ {y | R ≤ rW L s y}) ≤
        ENNReal.ofReal (K * Real.log R / R) := by
    intro R hRe
    refine (measure_mono (t := bdry s ∪ ((bdry s)ᶜ ∩ {y | R ≤ rW L s y})) ?_).trans
      ((measure_union_le _ _).trans ?_)
    · rintro y (hy | hy)
      · exact Or.inl hy
      · by_cases hb : y ∈ bdry s
        · exact Or.inl hb
        · exact Or.inr ⟨hb, hy⟩
    · rw [maMeasure_bdry_eq_zero A L s m W hS hSNC, zero_add]
      exact tail1 R hRe
  refine ⟨⟨?_⟩, K, fun R hRe => ⟨tail R hRe, ?_⟩⟩
  · refine lt_of_le_of_lt ((measure_mono fun y _ => Or.inr (hge y)).trans (tail _ le_rfl))
      ENNReal.ofReal_lt_top
  · refine tail_lintegral_le_of_eventually A L s hL hS
      (fun i => th i + LocPot.ofFun (ph i) + Θ) (fun t i => th i + LocPot.ofFun (phT i t) + Θ)
      hc hpot hunif (fun y => Real.log (rW L s y)) hrm.log ?_
      R _ ?_ ?_
    · exact hrc.log fun y hy => ((Real.exp_pos 1).trans_le (hge y)).ne'
    · intro y _ _
      exact Real.log_nonneg (le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) (hge y))
    · filter_upwards [hbd] with t ht
      exact ((hT (fun _ => t) fun _ => ht).2 R hRe).2

end GlobalTheory.CompanionTheory.Ar.Giv
