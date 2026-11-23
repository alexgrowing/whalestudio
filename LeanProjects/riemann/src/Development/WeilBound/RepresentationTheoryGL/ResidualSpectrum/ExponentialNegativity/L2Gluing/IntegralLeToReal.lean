import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralEnormSqLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TendstoSetLIntegralDiffCompactCovering
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralNormSqLeToRealLintegralEnormSq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SetLIntegralLeMulFundamentalDomainDiff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountableSubgroupClosure

noncomputable section

open NumberField MeasureTheory Filter Topology
open scoped ENNReal
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace PositivityTheory.Rg.Rs.l2glue

theorem cs_mean {α : Type} [MeasurableSpace α] (ν : Measure α) (s : Set α) (f : α → ℂ) :
    ‖((ν.real s : ℝ) : ℂ)⁻¹ * ∫ x in s, f x ∂ν‖ₑ ^ 2 * ν s ≤ ∫⁻ x in s, ‖f x‖ₑ ^ 2 ∂ν :=
  GlobalTheory.CompanionTheory.Dblock.enorm_mean_sq_mul_le ν s f

theorem tail {α : Type} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [T2Space α]
    [SigmaCompactSpace α] (μ : Measure α) (F : Set α) (h : α → ℝ≥0∞) (hF : ∫⁻ x in F, h x ∂μ < ⊤) :
    Tendsto (fun k : ℕ => ∫⁻ x in F \ compactCovering α k, h x ∂μ) atTop (𝓝 0) :=
  GlobalTheory.CompanionTheory.MeasureTails.tendsto_setLIntegral_diff_compactCovering μ F h hF

theorem integral_le_toReal {α : Type} [MeasurableSpace α] (μ : Measure α) (f : α → ℂ) :
    ∫ x, ‖f x‖ ^ 2 ∂μ ≤ (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ).toReal :=
  GlobalTheory.CompanionTheory.Dblock.integral_norm_sq_le_toReal_lintegral_enorm_sq μ f

theorem unfold {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G)
    [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant] (F S T : Set G)
    (hF : IsFundamentalDomain Γ F μ) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (h : G → ℝ≥0∞) (hh : Measurable h) (hinv : ∀ γ ∈ Γ, ∀ x, h (γ * x) = h x) (N : ℕ)
    (hN : ∀ x, {γ : Γ | (γ : G) * x ∈ S}.encard ≤ N) (hST : ∀ γ ∈ Γ, ∀ x, γ * x ∈ S → x ∉ T) :
    ∫⁻ x in S, h x ∂μ ≤ N * ∫⁻ x in F \ T, h x ∂μ :=
  GlobalTheory.CompanionTheory.Unfolding.setLIntegral_le_mul_fundamentalDomain_diff Γ μ F S T hF hS hT h hh hinv N hN hST

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

instance countable_lat : Countable (An.lat K n) := GlobalTheory.CompanionTheory.LatCount.countable_lat K n

def sset (K : Type) [Field K] [NumberField K] (n r : ℕ) (t : ℝ) (D : Set (UPos n r → AdeleRing (𝓞 K) K))
    (Q : Set (AdelicGLn.AdelicGL K n)) : Set (AdelicGLn.AdelicGL K n) :=
  (fun p : (UPos n r → AdeleRing (𝓞 K) K) × AdelicGLn.AdelicGL K n => unipGL p.1 * An.aR K n r t * p.2) '' (D ×ˢ Q)

theorem isCompact_sset (r : ℕ) (t : ℝ) {D : Set (UPos n r → AdeleRing (𝓞 K) K)}
    {Q : Set (AdelicGLn.AdelicGL K n)} (hD : IsCompact D) (hQ : IsCompact Q) : IsCompact (sset K n r t D Q) :=
  (hD.prod hQ).image ((continuous_unipGL.comp continuous_fst).mul continuous_const |>.mul continuous_snd)

theorem swap (μ : Measure (AdelicGLn.AdelicGL K n)) [μ.IsHaarMeasure] (φ : AdelicGLn.AdelicGL K n → ℂ)
    (hφ : Continuous φ) (r : ℕ) (t : ℝ) {D : Set (UPos n r → AdeleRing (𝓞 K) K)}
    (hD : IsCompact D) (hD0 : unipFundamentalDomain K n r ⊆ D) {Q : Set (AdelicGLn.AdelicGL K n)} (hQ : IsCompact Q) :
    ∫⁻ g in Q, ‖An.ctn r φ (An.aR K n r t * g)‖ₑ ^ 2 ∂μ ≤ ∫⁻ x in sset K n r t D Q, ‖φ x‖ₑ ^ 2 ∂μ := by
  have hS : MeasurableSet (sset K n r t D Q) := (isCompact_sset r t hD hQ).isClosed.measurableSet
  by_cases hc : (unipMeasure K n r).real (unipFundamentalDomain K n r) = 0
  · have h0 : ∀ g, An.ctn r φ g = 0 := fun g => by simp [An.ctn, hc]
    simp [h0]
  have hν0 : unipMeasure K n r (unipFundamentalDomain K n r) ≠ 0 := fun h => hc (by simp [Measure.real, h])
  have hνt : unipMeasure K n r (unipFundamentalDomain K n r) ≠ ⊤ := fun h => hc (by simp [Measure.real, h])
  have hpt : ∀ g, ‖An.ctn r φ g‖ₑ ^ 2 * unipMeasure K n r (unipFundamentalDomain K n r) ≤
      ∫⁻ X in unipFundamentalDomain K n r, ‖φ (unipGL X * g)‖ₑ ^ 2 ∂unipMeasure K n r := fun g =>
    cs_mean (unipMeasure K n r) (unipFundamentalDomain K n r) (fun X => φ (unipGL X * g))
  have hcont : Measurable fun p : AdelicGLn.AdelicGL K n × (UPos n r → AdeleRing (𝓞 K) K) =>
      ‖φ (unipGL p.2 * (An.aR K n r t * p.1))‖ₑ ^ 2 :=
    (hφ.comp ((continuous_unipGL.comp continuous_snd).mul
      (continuous_const.mul continuous_fst))).measurable.enorm.pow_const 2
  have key : (∫⁻ g in Q, ‖An.ctn r φ (An.aR K n r t * g)‖ₑ ^ 2 ∂μ) * unipMeasure K n r (unipFundamentalDomain K n r)
      ≤ (∫⁻ x in sset K n r t D Q, ‖φ x‖ₑ ^ 2 ∂μ) * unipMeasure K n r (unipFundamentalDomain K n r) := by
    calc (∫⁻ g in Q, ‖An.ctn r φ (An.aR K n r t * g)‖ₑ ^ 2 ∂μ) * unipMeasure K n r (unipFundamentalDomain K n r)
        = ∫⁻ g in Q, ‖An.ctn r φ (An.aR K n r t * g)‖ₑ ^ 2 * unipMeasure K n r (unipFundamentalDomain K n r) ∂μ :=
          (lintegral_mul_const' _ _ hνt).symm
      _ ≤ ∫⁻ g in Q, ∫⁻ X in unipFundamentalDomain K n r, ‖φ (unipGL X * (An.aR K n r t * g))‖ₑ ^ 2
            ∂unipMeasure K n r ∂μ := lintegral_mono fun g => hpt _
      _ = ∫⁻ X in unipFundamentalDomain K n r, ∫⁻ g in Q, ‖φ (unipGL X * (An.aR K n r t * g))‖ₑ ^ 2
            ∂μ ∂unipMeasure K n r := lintegral_lintegral_swap hcont.aemeasurable
      _ ≤ ∫⁻ X in unipFundamentalDomain K n r, ∫⁻ x in sset K n r t D Q, ‖φ x‖ₑ ^ 2 ∂μ ∂unipMeasure K n r := by
          refine setLIntegral_mono' measurableSet_unipFundamentalDomain fun X hX => ?_
          calc ∫⁻ g in Q, ‖φ (unipGL X * (An.aR K n r t * g))‖ₑ ^ 2 ∂μ
              ≤ ∫⁻ g, (sset K n r t D Q).indicator (fun x => ‖φ x‖ₑ ^ 2) (unipGL X * An.aR K n r t * g) ∂μ := by
                rw [← lintegral_indicator hQ.isClosed.measurableSet]
                refine lintegral_mono fun g => ?_
                by_cases hg : g ∈ Q
                · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (show unipGL X * An.aR K n r t * g ∈ sset K n r t D Q from ⟨(X, g), ⟨hD0 hX, hg⟩, rfl⟩), mul_assoc]
                · rw [Set.indicator_of_notMem hg]; exact bot_le
            _ = ∫⁻ x, (sset K n r t D Q).indicator (fun x => ‖φ x‖ₑ ^ 2) x ∂μ :=
                lintegral_mul_left_eq_self _ (unipGL X * An.aR K n r t)
            _ = ∫⁻ x in sset K n r t D Q, ‖φ x‖ₑ ^ 2 ∂μ := lintegral_indicator hS _
      _ = (∫⁻ x in sset K n r t D Q, ‖φ x‖ₑ ^ 2 ∂μ) * unipMeasure K n r (unipFundamentalDomain K n r) := by
          rw [setLIntegral_const]
  exact (ENNReal.mul_le_mul_iff_left hν0 hνt).1 key

theorem count_le (hC : An.Count) {r : ℕ} (hr : 0 < r) (hrn : r < n) {D : Set (UPos n r → AdeleRing (𝓞 K) K)}
    {Q : Set (AdelicGLn.AdelicGL K n)} (hD : IsCompact D) (hQ : IsCompact Q) :
    ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → ∀ x, {γ : An.lat K n | (γ : AdelicGLn.AdelicGL K n) * x ∈ sset K n r t D Q}.encard ≤
      (⌈C * Real.exp (2 * An.rho K n r * t)⌉₊ : ℕ) := by
  have hQ' : IsCompact ((fun p : AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n => p.1 * p.2⁻¹) '' (Q ×ˢ Q)) :=
    (hQ.prod hQ).image (continuous_fst.mul continuous_snd.inv)
  obtain ⟨C, hC'⟩ := hC K n r hr hrn D _ hD hQ'
  refine ⟨C, fun t ht x => ?_⟩
  rcases Set.eq_empty_or_nonempty {γ : An.lat K n | (γ : AdelicGLn.AdelicGL K n) * x ∈ sset K n r t D Q}
    with hA | ⟨γ₀, hγ₀⟩
  · rw [hA, Set.encard_empty]; exact bot_le
  refine le_trans ?_ (hC' t ht)
  have hinj : Set.InjOn (fun γ : An.lat K n => γ * γ₀⁻¹)
      {γ : An.lat K n | (γ : AdelicGLn.AdelicGL K n) * x ∈ sset K n r t D Q} :=
    fun a _ b _ h => mul_right_cancel h
  rw [← hinj.encard_image]
  refine Set.encard_le_encard ?_
  rintro _ ⟨γ, hγ, rfl⟩
  obtain ⟨⟨X, q₁⟩, ⟨hX, hq₁⟩, e1⟩ := hγ
  obtain ⟨⟨Y, q₂⟩, ⟨hY, hq₂⟩, e2⟩ := hγ₀
  refine ⟨X, hX, Y, hY, q₁ * q₂⁻¹, ⟨(q₁, q₂), ⟨hq₁, hq₂⟩, rfl⟩, ?_⟩
  simp only at e1 e2
  have e3 : ((γ * γ₀⁻¹ : An.lat K n) : AdelicGLn.AdelicGL K n) =
      ((γ : AdelicGLn.AdelicGL K n) * x) * ((γ₀ : AdelicGLn.AdelicGL K n) * x)⁻¹ := by
    push_cast; group
  rw [e3, ← e1, ← e2]; group

end PositivityTheory.Rg.Rs.l2glue

namespace PositivityTheory.Rg.Rs

theorem l2glue_holds : An.L2DecayOfCountEscape := by
  intro hCount hEsc K _ _ n r hr hrn μ _ φ F hφ hinv hF hfin Q hQ
  obtain ⟨D, hD, hD0⟩ := exists_isCompact_superset_unipFundamentalDomain (K := K) (n := n) (r := r)
  obtain ⟨C, hC⟩ := l2glue.count_le hCount hr hrn hD hQ
  have hhm : Measurable fun x : AdelicGLn.AdelicGL K n => ‖φ x‖ₑ ^ 2 := hφ.measurable.enorm.pow_const 2
  have hρ : 0 ≤ An.rho K n r := by
    unfold An.rho
    have : (r : ℝ) ≤ n := by exact_mod_cast hrn.le
    exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.2 this)) two_pos.le)
  have hC₁ : 0 < max C 0 + 1 := by positivity
  have key : ∀ T : Set (AdelicGLn.AdelicGL K n), IsCompact T → ∀ᶠ t in atTop,
      Real.exp (-(2 * An.rho K n r * t)) * ∫ g in Q, ‖An.ctn r φ (An.aR K n r t * g)‖ ^ 2 ∂μ ≤
        (max C 0 + 1) * (∫⁻ x in F \ T, ‖φ x‖ₑ ^ 2 ∂μ).toReal := by
    intro T hT
    filter_upwards [hEsc K n r hr hrn D Q T hD hQ hT, eventually_ge_atTop 0] with t ht ht0
    have hS := l2glue.isCompact_sset r t hD hQ
    have h1 := l2glue.integral_le_toReal (μ.restrict Q) (fun g => An.ctn r φ (An.aR K n r t * g))
    have h2 := l2glue.swap μ φ hφ r t hD hD0 hQ
    have h3 := l2glue.unfold (An.lat K n) μ F (l2glue.sset K n r t D Q) T hF hS.isClosed.measurableSet
      hT.isClosed.measurableSet (fun x => ‖φ x‖ₑ ^ 2) hhm
      (fun γ hγ x => by show ‖φ (γ * x)‖ₑ ^ 2 = ‖φ x‖ₑ ^ 2; rw [hinv γ hγ x]) _ (hC t ht0) (by
        intro γ hγ x hx hxT
        obtain ⟨⟨X, q⟩, ⟨hX, hq⟩, e⟩ := hx
        simp only at e
        exact ht γ⁻¹ (inv_mem hγ) X hX q hq (by rw [e, ← mul_assoc, inv_mul_cancel, one_mul]; exact hxT))
    have hfinT : ∫⁻ x in F \ T, ‖φ x‖ₑ ^ 2 ∂μ ≠ ⊤ :=
      (lt_of_le_of_lt (lintegral_mono_set Set.sdiff_subset) hfin).ne
    have h4 : (∫ g in Q, ‖An.ctn r φ (An.aR K n r t * g)‖ ^ 2 ∂μ) ≤
        (⌈C * Real.exp (2 * An.rho K n r * t)⌉₊ : ℝ) * (∫⁻ x in F \ T, ‖φ x‖ₑ ^ 2 ∂μ).toReal := by
      calc _ ≤ _ := h1
        _ ≤ (((⌈C * Real.exp (2 * An.rho K n r * t)⌉₊ : ℕ) : ℝ≥0∞) * ∫⁻ x in F \ T, ‖φ x‖ₑ ^ 2 ∂μ).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hfinT) (h2.trans h3)
        _ = _ := by rw [ENNReal.toReal_mul]; simp
    have hE := Real.exp_pos (2 * An.rho K n r * t)
    have hx : 0 ≤ 2 * An.rho K n r * t := mul_nonneg (mul_nonneg zero_le_two hρ) ht0
    have hN : (⌈C * Real.exp (2 * An.rho K n r * t)⌉₊ : ℝ) ≤ max C 0 * Real.exp (2 * An.rho K n r * t) + 1 := by
      have h6 : (⌈C * Real.exp (2 * An.rho K n r * t)⌉₊ : ℝ) ≤ ⌈max C 0 * Real.exp (2 * An.rho K n r * t)⌉₊ := by
        exact_mod_cast Nat.ceil_mono (mul_le_mul_of_nonneg_right (le_max_left C 0) hE.le)
      exact h6.trans (Nat.ceil_lt_add_one (by positivity)).le
    have he1 : Real.exp (-(2 * An.rho K n r * t)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hee : Real.exp (-(2 * An.rho K n r * t)) * Real.exp (2 * An.rho K n r * t) = 1 := by
      rw [← Real.exp_add]; simp
    have h5 : Real.exp (-(2 * An.rho K n r * t)) * (⌈C * Real.exp (2 * An.rho K n r * t)⌉₊ : ℝ) ≤ max C 0 + 1 := by
      calc _ ≤ Real.exp (-(2 * An.rho K n r * t)) * (max C 0 * Real.exp (2 * An.rho K n r * t) + 1) :=
            mul_le_mul_of_nonneg_left hN (Real.exp_pos _).le
        _ = max C 0 + Real.exp (-(2 * An.rho K n r * t)) := by linear_combination max C 0 * hee
        _ ≤ max C 0 + 1 := by linarith
    calc _ ≤ Real.exp (-(2 * An.rho K n r * t)) * ((⌈C * Real.exp (2 * An.rho K n r * t)⌉₊ : ℝ) *
            (∫⁻ x in F \ T, ‖φ x‖ₑ ^ 2 ∂μ).toReal) := mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le
      _ = (Real.exp (-(2 * An.rho K n r * t)) * (⌈C * Real.exp (2 * An.rho K n r * t)⌉₊ : ℝ)) *
            (∫⁻ x in F \ T, ‖φ x‖ₑ ^ 2 ∂μ).toReal := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h5 ENNReal.toReal_nonneg
  have htail := l2glue.tail μ F (fun x => ‖φ x‖ₑ ^ 2) hfin
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun t => lt_of_lt_of_le ha
    (mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => by positivity)), fun ε hε => ?_⟩
  have hε' : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / (2 * (max C 0 + 1))) := by
    rw [ENNReal.ofReal_pos]; positivity
  obtain ⟨k, hk⟩ := (htail.eventually (gt_mem_nhds hε')).exists
  filter_upwards [key _ (isCompact_compactCovering _ k)] with t ht
  have hk' : (∫⁻ x in F \ compactCovering _ k, ‖φ x‖ₑ ^ 2 ∂μ).toReal < ε / (2 * (max C 0 + 1)) := by
    have := ENNReal.toReal_strict_mono ENNReal.ofReal_ne_top hk
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  calc _ ≤ _ := ht
    _ < (max C 0 + 1) * (ε / (2 * (max C 0 + 1))) := mul_lt_mul_of_pos_left hk' hC₁
    _ = ε / 2 := by field_simp
    _ ≤ ε := by linarith

end PositivityTheory.Rg.Rs
