import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.LeviForms.ConvExpandStatement
import ReciprocityTheory.AnalyticForms.LeviForms.TailCut
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CompactPartIntegralsTendsto
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocDensAddOfFunContinuousOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsCompactRWSublevel
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MaMeasureEqOfConst
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TailBoundStatementHolds
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedEnergyRegularizationBoundStatement
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem conv_tail_split : ∀ {X : Type} [MeasurableSpace X] {l : Filter ℝ} (μT : ℝ → Measure X) (μ : Measure X) (gT : ℝ → X → ℝ) (g : X → ℝ) (E : ℝ → Set X) (b : ℝ → ℝ), Tendsto b atTop (𝓝 0) → (∀ R, MeasurableSet (E R)) → AEStronglyMeasurable g μ → (∀ᶠ t in l, AEStronglyMeasurable (gT t) (μT t)) → (∀ᶠ R in atTop, IntegrableOn g (E R) μ ∧ ∫⁻ y in (E R)ᶜ, ‖g y‖ₑ ∂μ ≤ ENNReal.ofReal (b R) ∧ (∀ᶠ t in l, IntegrableOn (gT t) (E R) (μT t) ∧ ∫⁻ y in (E R)ᶜ, ‖gT t y‖ₑ ∂μT t ≤ ENNReal.ofReal (b R)) ∧ Tendsto (fun t => ∫ y in E R, gT t y ∂μT t) l (𝓝 (∫ y in E R, g y ∂μ))) → Integrable g μ ∧ (∀ᶠ t in l, Integrable (gT t) (μT t)) ∧ Tendsto (fun t => ∫ y, gT t y ∂μT t) l (𝓝 (∫ y, g y ∂μ)) := by
  intro X _ l μT μ gT g E b hb hE hg hgT h
  have key : ∀ (ν : Measure X) (f : X → ℝ) (R : ℝ), AEStronglyMeasurable f ν →
      IntegrableOn f (E R) ν → ∫⁻ y in (E R)ᶜ, ‖f y‖ₑ ∂ν ≤ ENNReal.ofReal (b R) →
      Integrable f ν := by
    intro ν f R hm h1 h2
    have h3 : IntegrableOn f (E R)ᶜ ν := ⟨hm.restrict, lt_of_le_of_lt h2 ENNReal.ofReal_lt_top⟩
    have := h1.union h3
    rwa [Set.union_compl_self, integrableOn_univ] at this
  have tb : ∀ (ν : Measure X) (f : X → ℝ) (R : ℝ),
      ∫⁻ y in (E R)ᶜ, ‖f y‖ₑ ∂ν ≤ ENNReal.ofReal (b R) →
      ‖∫ y in (E R)ᶜ, f y ∂ν‖ ≤ max (b R) 0 := by
    intro ν f R h2
    have h5 := (enorm_integral_le_lintegral_enorm (μ := ν.restrict (E R)ᶜ) f).trans h2
    rw [← ofReal_norm_eq_enorm] at h5
    rcases (ENNReal.ofReal_le_ofReal_iff').1 h5 with h6 | h6
    · exact h6.trans (le_max_left _ _)
    · exact h6.trans (le_max_right _ _)
  obtain ⟨R₀, hR₀⟩ := h.exists
  have hgi₀ := key μ g R₀ hg hR₀.1 hR₀.2.1
  refine ⟨hgi₀, ?_, ?_⟩
  · filter_upwards [hR₀.2.2.1, hgT] with t h1 h2
    exact key _ _ R₀ h2 h1.1 h1.2
  · rw [Metric.tendsto_nhds]
    intro ε hε
    have hε3 : 0 < ε / 3 := by positivity
    have hbs : ∀ᶠ R in atTop, b R < ε / 3 := hb (Iio_mem_nhds hε3)
    obtain ⟨R, hR, hbR⟩ := (h.and hbs).exists
    have hgi := key μ g R hg hR.1 hR.2.1
    have hlim := Metric.tendsto_nhds.1 hR.2.2.2 (ε / 3) hε3
    filter_upwards [hR.2.2.1, hgT, hlim] with t h1 h2 h3
    have hti := key _ _ R h2 h1.1 h1.2
    rw [← integral_add_compl (hE R) hti, ← integral_add_compl (hE R) hgi]
    have e1 := tb (μT t) (gT t) R h1.2
    have e2 := tb μ g R hR.2.1
    have hm : max (b R) 0 < ε / 3 := max_lt hbR hε3
    rw [Real.dist_eq] at h3 ⊢
    rw [Real.norm_eq_abs] at e1 e2
    obtain ⟨a1, a2⟩ := abs_lt.1 h3
    obtain ⟨b1, b2⟩ := abs_le.1 e1
    obtain ⟨c1, c2⟩ := abs_le.1 e2
    rw [abs_lt]
    constructor <;> linarith

theorem conv_tail_enorm : ∀ {X : Type} [MeasurableSpace X] (ν : Measure X) (B : Set X) (r f : X → ℝ) (c R M : ℝ), MeasurableSet (Bᶜ ∩ {y | R ≤ r y}) → ν B = 0 → (∀ y ∉ B, |f y| ≤ c * Real.log (r y)) → (∀ y ∉ B, 0 ≤ Real.log (r y)) → ∫⁻ y in Bᶜ ∩ {y | R ≤ r y}, ENNReal.ofReal (Real.log (r y)) ∂ν ≤ ENNReal.ofReal M → ∫⁻ y in {y | y ∉ B ∧ r y ≤ R}ᶜ, ‖f y‖ₑ ∂ν ≤ ENNReal.ofReal (|c| * M) := by
  intro X _ ν B r f c R M hSm hB hf hl hM
  have hsub : {y | y ∉ B ∧ r y ≤ R}ᶜ ⊆ B ∪ (Bᶜ ∩ {y | R ≤ r y}) := by
    intro y hy
    by_cases hyB : y ∈ B
    · exact Or.inl hyB
    · refine Or.inr ⟨hyB, ?_⟩
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_and, not_le] at hy
      exact (hy hyB).le
  calc ∫⁻ y in {y | y ∉ B ∧ r y ≤ R}ᶜ, ‖f y‖ₑ ∂ν
      ≤ ∫⁻ y in B ∪ (Bᶜ ∩ {y | R ≤ r y}), ‖f y‖ₑ ∂ν := lintegral_mono_set hsub
    _ ≤ ∫⁻ y in B, ‖f y‖ₑ ∂ν + ∫⁻ y in Bᶜ ∩ {y | R ≤ r y}, ‖f y‖ₑ ∂ν := lintegral_union_le _ _ _
    _ = ∫⁻ y in Bᶜ ∩ {y | R ≤ r y}, ‖f y‖ₑ ∂ν := by
        rw [Measure.restrict_eq_zero.2 hB, lintegral_zero_measure, zero_add]
    _ ≤ ∫⁻ y in Bᶜ ∩ {y | R ≤ r y}, ENNReal.ofReal |c| * ENNReal.ofReal (Real.log (r y)) ∂ν := by
        refine setLIntegral_mono' hSm fun y hy => ?_
        rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (abs_nonneg c)]
        exact ENNReal.ofReal_le_ofReal ((hf y hy.1).trans
          (mul_le_mul_of_nonneg_right (le_abs_self c) (hl y hy.1)))
    _ = ENNReal.ofReal |c| * ∫⁻ y in Bᶜ ∩ {y | R ≤ r y}, ENNReal.ofReal (Real.log (r y)) ∂ν :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal |c| * ENNReal.ofReal M := by gcongr
    _ = ENNReal.ofReal (|c| * M) := (ENNReal.ofReal_mul (abs_nonneg c)).symm

theorem conv_mass_approx : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (th : Fin e → LocPot X) (u : Fin e → X → ℝ) (Θ : LocPot X), (∀ i, IsPotential A (th i)) → IsPotential A Θ → (∀ i, A.Smooth (u i)) → (∀ i, IsPsh A (th i + LocPot.ofFun (u i) + Θ)) → (maMeasure A (fun i => th i + LocPot.ofFun (u i) + Θ) Set.univ).toReal = mInt A (fun i => th i + Θ) (fun _ => 1) := by
  intro e X _ _ _ _ _ A th u Θ hth hΘ hu hpsh
  have hpot : ∀ i, IsPotential A (th i + LocPot.ofFun (u i) + Θ) := fun i =>
    isPotentialAdd A _ _ (isPotentialAdd A _ _ (hth i) (isPotential_ofFun A _ (hu i))) hΘ
  obtain ⟨hfin, hint⟩ := maMeasure_thm A _ hpot hpsh
  have h1 := hint (fun _ => 1) measurable_const
  have hI : MIntegrable A (fun i => th i + LocPot.ofFun (u i) + Θ) (fun _ => 1) :=
    h1.1.2 (integrable_const 1)
  have hm := h1.2 hI
  rw [integral_const, smul_eq_mul, mul_one, measureReal_def] at hm
  rw [← hm, ← massIndep A (fun i => th i + Θ) u (fun i => isPotentialAdd A _ _ (hth i) hΘ) hu]
  have hD : ∀ j, locDens A (fun i => th i + LocPot.ofFun (u i) + Θ) j =
      locDens A (fun i => th i + Θ + LocPot.ofFun (u i)) j := by
    intro j
    funext y
    unfold locDens
    congr 1
    funext i y'
    show (th i).φ _ _ + u i _ + Θ.φ _ _ = (th i).φ _ _ + Θ.φ _ _ + u i _
    ring
  unfold mInt integralWith
  simp only [hD]

theorem conv_null_of_log_div {X : Type} [MeasurableSpace X] (ν : Measure X) (B : Set X) (K : ℝ)
    (h : ∀ R : ℝ, Real.exp 1 ≤ R → ν B ≤ ENNReal.ofReal (K * Real.log R / R)) : ν B = 0 := by
  have ht : Tendsto (fun R : ℝ => ENNReal.ofReal (K * Real.log R / R)) atTop (𝓝 0) := by
    have h1 := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).const_mul K
    simp only [pow_one, one_mul, add_zero, mul_zero] at h1
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal (h1.congr fun R => ?_)
    ring
  refine le_antisymm (ge_of_tendsto ht ?_) bot_le
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with R hR
  exact h R hR

theorem conv_aesm {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X)
    {B : Set X} (hB : IsClosed B) (hν : ν B = 0) {f : X → ℝ} (hf : ContinuousOn f Bᶜ) :
    AEStronglyMeasurable f ν := by
  have h := hf.aestronglyMeasurable (μ := ν) hB.isOpen_compl.measurableSet
  rwa [Measure.restrict_eq_self_of_ae_mem (s := Bᶜ) (compl_mem_ae_iff.2 hν)] at h

theorem conv_limit_props {X : Type} [TopologicalSpace X] (U : Set X) (g : X → ℝ) (gT : ℝ → X → ℝ)
    (b : X → ℝ) (hc : ∀ t, ContinuousOn (gT t) U) (hb : ∀ t y, y ∈ U → |gT t y| ≤ b y)
    (hl : TendstoLocallyUniformlyOn gT g (𝓝[>] 0) U) :
    ContinuousOn g U ∧ ∀ y ∈ U, |g y| ≤ b y := by
  refine ⟨hl.continuousOn (Frequently.of_forall hc), fun y hy => ?_⟩
  have ht : Tendsto (fun t => gT t y) (𝓝[>] 0) (𝓝 (g y)) := hl.tendsto_at hy
  exact le_of_tendsto ht.abs (Eventually.of_forall fun t => hb t y hy)

theorem conv_core {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) {n : ℕ}
    (m : Fin n → ℕ) (W : Fin n → Set X) (hΘ : IsPotential A Θ) (hpos : IsPosPot A Θ)
    (hL : IsPotential A L) (hS : IsSection A L s) (hSNC : IsSNC A L s m W)
    (hnorm : ∀ y, logNormSec L s y ≤ 0)
    (th : Fin e → LocPot X) (ph : Fin e → X → ℝ) (phT : Fin e → ℝ → X → ℝ) (C₅ C t₀ : ℝ)
    (hW : ∀ i, IsSingWeight A L s (th i) (ph i) C₅)
    (hR : ∀ i, IsRegFamily A Θ L s (th i) (ph i) (phT i) C t₀)
    (hC2 : ∀ i, IsRegFamilyC2 A s (ph i) (phT i))
    (g : X → ℝ) (gT : ℝ → X → ℝ) (C₆ : ℝ) (hgc : ∀ t, ContinuousOn (gT t) (bdry s)ᶜ)
    (hgb : ∀ t y, y ∉ bdry s → |gT t y| ≤ C₆ * Real.log (rW L s y))
    (hgl : TendstoLocallyUniformlyOn gT g (𝓝[>] 0) (bdry s)ᶜ) :
    Integrable g (maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ)) ∧
    (∀ᶠ t in 𝓝[>] 0, Integrable (gT t) (maMeasure A (fun i => th i + LocPot.ofFun (phT i t) + Θ))) ∧
    Tendsto (fun t => ∫ y, gT t y ∂maMeasure A (fun i => th i + LocPot.ofFun (phT i t) + Θ))
      (𝓝[>] 0) (𝓝 (∫ y, g y ∂maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ))) := by
  obtain ⟨-, K₁, hK₁⟩ := GlobalTheory.T.mixed_energy_regularization_bound tailBound_holds A Θ L s m W hΘ hpos hL hS hSNC hnorm
    th ph phT C₅ C t₀ hW hR hC2
  obtain ⟨K₂, t₁, ht₁, ht₁₀, hU⟩ := tail_uniform tailBound_holds A Θ L s m W hΘ hpos hL hS hSNC
    hnorm th ph phT C₅ C t₀ hW hR
  have hB : IsClosed (bdry s) := LeviFormBoundaryTopology.isClosed_bdry hS
  have hUo : IsOpen (bdry s)ᶜ := hB.isOpen_compl
  have hlog : ∀ y, 0 ≤ Real.log (rW L s y) := fun y =>
    Real.log_nonneg (by linarith [rW_ge L s hnorm y, Real.add_one_le_exp (1 : ℝ)])
  obtain ⟨hgcont, hgbd⟩ := conv_limit_props (bdry s)ᶜ g gT (fun y => C₆ * Real.log (rW L s y))
    hgc (fun t y hy => hgb t y hy) hgl
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t ≤ t₁ := by
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT ht₁] with t ht ht'
    exact ⟨ht, ht'.2.le⟩
  have hpot : ∀ t, 0 < t ∧ t ≤ t₁ → ∀ i, IsPotential A (th i + LocPot.ofFun (phT i t) + Θ) ∧
      IsPsh A (th i + LocPot.ofFun (phT i t) + Θ) := fun t ht => (hU (fun _ => t) (fun _ => ht)).1
  have htail : ∀ t, 0 < t ∧ t ≤ t₁ → ∀ R, Real.exp 1 ≤ R →
      ∫⁻ y in (bdry s)ᶜ ∩ {y | R ≤ rW L s y}, ENNReal.ofReal (Real.log (rW L s y))
        ∂maMeasure A (fun i => th i + LocPot.ofFun (phT i t) + Θ) ≤
        ENNReal.ofReal (K₂ * Real.log R ^ 2 / R) := fun t ht R hR =>
    ((hU (fun _ => t) (fun _ => ht)).2 R hR).2
  have hμT0 : ∀ t, 0 < t ∧ t ≤ t₁ →
      maMeasure A (fun i => th i + LocPot.ofFun (phT i t) + Θ) (bdry s) = 0 := fun t ht =>
    bdry_null A L s m W hL hS hSNC _ (fun i => (hpot t ht i).1)
  have hμTfin : ∀ t, 0 < t ∧ t ≤ t₁ →
      IsFiniteMeasure (maMeasure A (fun i => th i + LocPot.ofFun (phT i t) + Θ)) := fun t ht =>
    (maMeasure_thm A _ (fun i => (hpot t ht i).1) (fun i => (hpot t ht i).2)).1
  have hμ0 : maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ) (bdry s) = 0 :=
    conv_null_of_log_div _ _ K₁ fun R hR => (measure_mono Set.subset_union_left).trans (hK₁ R hR).1
  have hsm : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, A.Smooth (phT i t) := by
    rw [eventually_all]
    intro i
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (hR i).1] with t ht ht'
    exact ((hR i).2.2 t ht ht'.2.le).1
  set Kc : ℝ → Set X := fun R => {y | y ∉ bdry s ∧ rW L s y ≤ R} with hKc
  have hKcpt : ∀ R, IsCompact (Kc R) := fun R => isCompact_rW_sublevel A L s hL hS R
  have hKm : ∀ R, MeasurableSet (Kc R) := fun R => (hKcpt R).isClosed.measurableSet
  have hKU : ∀ R, Kc R ⊆ (bdry s)ᶜ := fun R y hy => hy.1
  have hSm : ∀ R : ℝ, MeasurableSet ((bdry s)ᶜ ∩ {y | R ≤ rW L s y}) := by
    intro R
    have : (bdry s)ᶜ ∩ {y | R ≤ rW L s y} = (bdry s)ᶜ \ {y | y ∉ bdry s ∧ rW L s y < R} := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_diff, not_and,
        not_lt]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun _ => h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, h2 h1⟩
    rw [this]
    exact hUo.measurableSet.diff ((rW_open A L s hL hS).2 R).measurableSet
  have hcp := fun R => compact_part_integrals_tendsto A (bdry s)ᶜ
    (fun i => th i + LocPot.ofFun (ph i) + Θ) (fun t i => th i + LocPot.ofFun (phT i t) + Θ) hUo
    (fun j => locDens_add_ofFun_continuousOn A (bdry s)ᶜ th ph Θ hUo (fun i => (hW i).1) hΘ
      (fun i => (hW i).2.1) j)
    (hsm.mono fun t ht i => isPotentialAdd A _ _ (isPotentialAdd A _ _ (hW i).1
      (isPotential_ofFun A _ (ht i))) hΘ)
    (conv_dens A Θ s th ph phT hB hΘ (fun i => (hW i).1) (fun i => (hW i).2.1) hsm hC2)
    g gT hgc hgl (Kc R) (Kc R) (hKcpt R) (hKU R) (hKm R) subset_rfl
  set K := max K₁ K₂ with hK
  set b : ℝ → ℝ := fun R => |C₆| * (K * Real.log R ^ 2 / R) with hbdef
  have hb : Tendsto b atTop (𝓝 0) := by
    have h1 := ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).const_mul K).const_mul |C₆|
    simp only [one_mul, add_zero, mul_zero] at h1
    refine h1.congr fun R => ?_
    simp only [hbdef]
    ring
  refine conv_tail_split (fun t => maMeasure A (fun i => th i + LocPot.ofFun (phT i t) + Θ)) _ gT g Kc b hb hKm
    (conv_aesm _ hB hμ0 hgcont) (hev.mono fun t ht => conv_aesm _ hB (hμT0 t ht) (hgc t)) ?_
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with R hR
  have hRpos : 0 ≤ Real.log R ^ 2 / R := div_nonneg (sq_nonneg _) ((Real.exp_pos 1).le.trans hR)
  have hKb : ∀ K', K' ≤ K → ENNReal.ofReal (K' * Real.log R ^ 2 / R) ≤
      ENNReal.ofReal (K * Real.log R ^ 2 / R) := fun K' hK' =>
    ENNReal.ofReal_le_ofReal (by
      rw [mul_div_assoc, mul_div_assoc]
      exact mul_le_mul_of_nonneg_right hK' hRpos)
  refine ⟨(hcp R).2.1, ?_, ?_, (hcp R).2.2⟩
  · exact conv_tail_enorm _ (bdry s) (rW L s) g C₆ R (K * Real.log R ^ 2 / R) (hSm R) hμ0
      (fun y hy => hgbd y hy) (fun y _ => hlog y)
      (((hK₁ R hR).2).trans (hKb K₁ (le_max_left _ _)))
  · filter_upwards [hev] with t ht
    haveI := hμTfin t ht
    refine ⟨ContinuousOn.integrableOn_compact (hKcpt R) ((hgc t).mono (hKU R)), ?_⟩
    exact conv_tail_enorm _ (bdry s) (rW L s) (gT t) C₆ R _ (hSm R) (hμT0 t ht) (fun y hy => hgb t y hy)
      (fun y _ => hlog y) ((htail t ht R hR).trans (hKb K₂ (le_max_right _ _)))

theorem convergence_holds : ConvergenceStatement := by
  intro e X _ _ _ _ _ A Θ L s n m W hΘ hpos hL hS hSNC hnorm th ph phT C₅ C t₀ hW hR hC2 g gT C₆
    hgc hgb hgl
  intro μT μ
  obtain ⟨hfin, -⟩ := GlobalTheory.T.mixed_energy_regularization_bound tailBound_holds A Θ L s m W hΘ hpos hL hS hSNC hnorm
    th ph phT C₅ C t₀ hW hR hC2
  obtain ⟨hg1, hg2, hg3⟩ := conv_core A Θ L s m W hΘ hpos hL hS hSNC hnorm th ph phT C₅ C t₀
    hW hR hC2 g gT C₆ hgc hgb hgl
  refine ⟨hfin, ?_, hg1, hg2, hg3⟩
  have hlog1 : ∀ y, 1 ≤ Real.log (rW L s y) := fun y => by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (rW_ge L s hnorm y)
  have hconst : TendstoLocallyUniformlyOn (fun (_ : ℝ) (_ : X) => (1 : ℝ)) (fun _ => 1)
      (𝓝[>] 0) (bdry s)ᶜ := by
    intro u hu x _
    exact ⟨Set.univ, Filter.univ_mem, Eventually.of_forall fun _ y _ => refl_mem_uniformity hu⟩
  have hc1 := (conv_core A Θ L s m W hΘ hpos hL hS hSNC hnorm th ph phT C₅ C t₀ hW hR hC2
    (fun _ => 1) (fun _ _ => 1) 1 (fun _ => continuousOn_const)
    (fun t y _ => by simpa using hlog1 y) hconst).2.2
  obtain ⟨K₂, t₁, ht₁, ht₁₀, hU⟩ := tail_uniform tailBound_holds A Θ L s m W hΘ hpos hL hS hSNC
    hnorm th ph phT C₅ C t₀ hW hR
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), mInt A (fun i => th i + Θ) (fun _ => 1) =
      ∫ y, (fun _ => (1 : ℝ)) y ∂maMeasure A (fun i => th i + LocPot.ofFun (phT i t) + Θ) := by
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT ht₁] with t ht ht'
    have hp := (hU (fun _ => t) (fun _ => ⟨ht, ht'.2.le⟩)).1
    rw [integral_const, smul_eq_mul, mul_one, measureReal_def]
    exact (conv_mass_approx A th (fun i => phT i t) Θ (fun i => (hW i).1) hΘ
      (fun i => ((hR i).2.2 t ht (ht'.2.le.trans (ht₁₀ (hR i).1))).1) (fun i => (hp i).2)).symm
  have h2 := tendsto_nhds_unique hc1 (tendsto_const_nhds.congr' hev)
  rw [integral_const, smul_eq_mul, mul_one, measureReal_def] at h2
  exact h2

end GlobalTheory.CompanionTheory.Ar.Giv
