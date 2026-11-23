import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShellMassIntegrableNearNondegenerateZero
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

open MeasureTheory Filter Topology Metric in
open scoped ENNReal ContDiff in
private lemma continuous_sqn_of_isSec' {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι La : Type*}
    [AddCommGroup La] (A : _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas n Y ι La) {L : La} {N : ℕ} {s : Fin N → ι → Y → ℂ}
    (hs : ∀ k, A.IsSec L (s k)) : Continuous (A.sqn L s) := by
  have hsum : A.sqn L s = fun y => ∑ k, A.nsq L (s k) y := by
    funext y
    rfl
  rw [hsum]
  refine continuous_finset_sum _ fun k _ => ?_
  have hk : A.IsSecOn L Set.univ (s k) := hs k
  exact continuousOn_univ.mp (_root_.ReciprocityTheory.L2DbarEstimates.Y.api_nsq_contOn A isOpen_univ hk)

open MeasureTheory Filter Topology Metric in
open scoped ENNReal ContDiff in
private lemma mem_zeroSet_of_sqn_eq_zero {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι La : Type*}
    [AddCommGroup La] (A : _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas n Y ι La) {L : La} {N : ℕ} (s : Fin N → ι → Y → ℂ) {y : Y}
    (hy : A.sqn L s y = 0) : y ∈ A.zeroSet s := by
  have hy' : ∑ k, A.nsq L (s k) y = 0 := hy
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun k _ => A.nsq_nonneg L (s k) y)] at hy'
  simp only [_root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.zeroSet, Set.mem_setOf_eq]
  intro k
  have hk : ‖s k (A.pick y) y‖ ^ 2 * Real.exp (-A.ph L (A.pick y) y) = 0 :=
    hy' k (Finset.mem_univ _)
  have h2 := (mul_eq_zero.mp hk).resolve_right (Real.exp_pos _).ne'
  simpa using h2

open MeasureTheory Filter Topology Metric in
open scoped ENNReal ContDiff in
private lemma lintegral_le_sum_of_pairwiseDisjoint_pieces {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    (Z : Finset Y) (V W : Y → Set Y) (hd : (↑Z : Set Y).PairwiseDisjoint V)
    (hV : ∀ P ∈ Z, MeasurableSet (V P)) (hVW : ∀ P ∈ Z, V P ⊆ W P) (F : Y → ℝ≥0∞)
    (G : Y → Y → ℝ≥0∞) (hF0 : ∀ y, y ∉ ⋃ P ∈ Z, V P → F y = 0)
    (hFG : ∀ P ∈ Z, ∀ y ∈ V P, F y = G P y) :
    ∫⁻ y, F y ∂ν ≤ ∑ P ∈ Z, ∫⁻ y in W P, G P y ∂ν := by
  rw [← setLIntegral_eq_of_support_subset (s := ⋃ P ∈ Z, V P), lintegral_biUnion_finset hd hV]
  · refine Finset.sum_le_sum fun P hP => ?_
    rw [setLIntegral_congr_fun (hV P hP) (fun y hy => hFG P hP y hy)]
    exact lintegral_mono_set (hVW P hP)
  · intro y hy
    by_contra hyn
    exact hy (hF0 y hyn)

open MeasureTheory Filter Topology Metric in
open scoped ENNReal ContDiff in
private lemma resSq_nonneg {n : ℕ} {Y : Type*} [TopologicalSpace Y]
    [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι La : Type*}
    [AddCommGroup La] (A : _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas n Y ι La) (E L : La) (s : Fin n → ι → Y → ℂ) (P : Y) (c : ℂ) :
    0 ≤ _root_.GlobalTheory.Published.L2Extension.resSq A E L s P c := by
  unfold _root_.GlobalTheory.Published.L2Extension.resSq
  positivity

open MeasureTheory Filter Topology Metric in
open scoped ENNReal ContDiff in

theorem _root_.GlobalTheory.OTY.exists_local_extension : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas n Y ι La), 1 ≤ n → ∀ (E L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → ∀ hS : (A.zeroSet s).Finite, (∀ P ∈ A.zeroSet s, _root_.GlobalTheory.Published.L2Extension.jacAt A s P ≠ 0) → ∀ (f : Y → ℂ) (δ : ℝ), 0 < δ → ∃ (Ω : Set Y) (h : ι → Y → ℂ) (m : ℝ), (IsOpen Ω ∧ A.IsSecOn (A.kap + E) Ω h ∧ (∀ i y, y ∉ Ω → h i y = 0)) ∧ 0 < m ∧ (∀ y, A.sqn L s y < m → y ∈ Ω) ∧ (∀ P ∈ A.zeroSet s, h (A.pick P) P = f P) ∧ (∀ T : ℝ, 2 ≤ T → ∫⁻ y in {y | -T - 1 ≤ δ * _root_.GlobalTheory.Published.L2Extension.psi A L s y ∧ δ * _root_.GlobalTheory.Published.L2Extension.psi A L s y ≤ -T + 1}, ENNReal.ofReal (A.nsq (A.kap + E) h y * Real.exp (-_root_.GlobalTheory.Published.L2Extension.psi A L s y)) ∂A.mu ≤ ENNReal.ofReal (62 / 30 * (Real.pi ^ n / ((n - 1).factorial : ℝ)) / δ * ∑ P ∈ hS.toFinset, _root_.GlobalTheory.Published.L2Extension.resSq A E L s P (f P))) ∧ ∫⁻ y, ENNReal.ofReal (1 / (1 + (δ * _root_.GlobalTheory.Published.L2Extension.psi A L s y) ^ 2) * A.nsq (A.kap + E) h y * Real.exp (-_root_.GlobalTheory.Published.L2Extension.psi A L s y)) ∂A.mu < ⊤ := by
  intro n Y _ _ _ _ _ _ ι La _ A hn E L s hs hS hjac f δ hδ
  choose! N hNo hPN hNsub hNT hNfin using fun P (hP : P ∈ A.zeroSet s) =>
    _root_.GlobalTheory.OTY.ShellZero.shell_near_zero n Y ι La A hn E L s hs P hP (hjac P hP) (f P) δ hδ
  obtain ⟨U, hU, hUd⟩ := hS.t2_separation
  set Z := hS.toFinset with hZ
  have hmemZ : ∀ {P}, P ∈ Z → P ∈ A.zeroSet s := fun hP => hS.mem_toFinset.mp hP
  have hd : (↑Z : Set Y).PairwiseDisjoint (fun P => N P ∩ U P) := by
    intro P hP Q hQ hPQ
    exact Disjoint.mono Set.inter_subset_right Set.inter_subset_right
      (hUd (hmemZ (Finset.mem_coe.mp hP)) (hmemZ (Finset.mem_coe.mp hQ)) hPQ)
  have hVo : ∀ P ∈ Z, IsOpen (N P ∩ U P) := fun P hP => (hNo P (hmemZ hP)).inter (hU P).2
  obtain ⟨h, hh⟩ : ∃ h : ι → Y → ℂ, h = fun i y =>
      ∑ P ∈ Z, (N P ∩ U P).indicator (fun y => A.g (A.kap + E) i (A.pick P) y * f P) y :=
    ⟨_, rfl⟩
  have hloc : ∀ P ∈ Z, ∀ y ∈ N P ∩ U P, ∀ i, h i y = A.g (A.kap + E) i (A.pick P) y * f P := by
    intro P hP y hy i
    rw [hh]
    dsimp only
    rw [Finset.sum_eq_single P]
    · exact Set.indicator_of_mem hy _
    · intro Q hQ hQP
      refine Set.indicator_of_notMem (fun hyQ => ?_) _
      exact Set.disjoint_left.mp (hd (Finset.mem_coe.mpr hQ) (Finset.mem_coe.mpr hP) hQP) hyQ hy
    · intro hPn
      exact absurd hP hPn
  have hout : ∀ y, y ∉ ⋃ P ∈ Z, N P ∩ U P → ∀ i, h i y = 0 := by
    intro y hy i
    rw [hh]
    exact Finset.sum_eq_zero fun P hP =>
      Set.indicator_of_notMem (fun hyP => hy (Set.mem_iUnion₂.mpr ⟨P, hP, hyP⟩)) _
  have hZΩ : ∀ y ∈ A.zeroSet s, y ∈ ⋃ P ∈ Z, N P ∩ U P := fun y hy =>
    Set.mem_iUnion₂.mpr ⟨y, hS.mem_toFinset.mpr hy, hPN y hy, (hU y).1⟩
  have hΩo : IsOpen (⋃ P ∈ Z, N P ∩ U P) :=
    isOpen_iUnion fun P => isOpen_iUnion fun hP => hVo P hP
  have hnsq : ∀ P ∈ Z, ∀ y ∈ N P ∩ U P, A.nsq (A.kap + E) h y =
      A.nsq (A.kap + E) (fun i y => A.g (A.kap + E) i (A.pick P) y * f P) y := by
    intro P hP y hy
    unfold _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.nsq
    rw [hloc P hP y hy]
  have hnsq0 : ∀ y, y ∉ ⋃ P ∈ Z, N P ∩ U P → A.nsq (A.kap + E) h y = 0 := by
    intro y hy
    unfold _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.nsq
    rw [hout y hy]
    simp
  obtain ⟨m, hm, hmΩ⟩ : ∃ m : ℝ, 0 < m ∧ ∀ y, A.sqn L s y < m → y ∈ ⋃ P ∈ Z, N P ∩ U P := by
    rcases (⋃ P ∈ Z, N P ∩ U P)ᶜ.eq_empty_or_nonempty with he | hne
    · refine ⟨1, one_pos, fun y _ => ?_⟩
      by_contra hy
      have hyc : y ∈ (⋃ P ∈ Z, N P ∩ U P)ᶜ := hy
      rw [he] at hyc
      exact hyc
    · obtain ⟨x0, hx0, hmin⟩ := hΩo.isClosed_compl.isCompact.exists_isMinOn hne
        (continuous_sqn_of_isSec' A hs).continuousOn
      refine ⟨A.sqn L s x0, lt_of_le_of_ne (A.sqn_nonneg L s x0)
        (fun h0 => hx0 (hZΩ x0 (mem_zeroSet_of_sqn_eq_zero A s h0.symm))), fun y hy => ?_⟩
      by_contra hyΩ
      exact (not_le.mpr hy) (isMinOn_iff.mp hmin y hyΩ)
  refine ⟨⋃ P ∈ Z, N P ∩ U P, h, m, ⟨hΩo, ⟨?_, ?_⟩, fun i y hy => hout y hy i⟩, hm, hmΩ, ?_, ?_, ?_⟩
  · intro i x hx
    obtain ⟨P, hP, hxP⟩ := Set.mem_iUnion₂.mp hx.2
    have hWo : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (N P ∩ U P)) :=
      (A.chart i).isOpen_inter_preimage_symm (hVo P hP)
    have hW : (A.chart i).target ∩ (A.chart i).symm ⁻¹' (N P ∩ U P) ∈ 𝓝 x :=
      hWo.mem_nhds ⟨hx.1, hxP⟩
    have hg : DifferentiableAt ℂ (A.g (A.kap + E) i (A.pick P) ∘ (A.chart i).symm) x := by
      refine ((A.holo_g (A.kap + E) i (A.pick P)).mono ?_).differentiableAt hW
      intro z hz
      unfold _root_.ReciprocityTheory.L2DbarEstimates.Y.ovl
      exact ⟨hz.1, hNsub P (hmemZ hP) hz.2.1⟩
    refine ((hg.mul_const (f P)).congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hW] with z hz
    simp only [Function.comp_apply]
    exact hloc P hP _ hz.2 i
  · intro i j y hy hi hj
    obtain ⟨P, hP, hyP⟩ := Set.mem_iUnion₂.mp hy
    rw [hloc P hP y hyP i, hloc P hP y hyP j, ← mul_assoc,
      ← A.g_cocycle _ i j _ y hi hj (hNsub P (hmemZ hP) hyP.1)]
  · intro P hP
    rw [hloc P (hS.mem_toFinset.mpr hP) P ⟨hPN P hP, (hU P).1⟩, A.g_self _ _ (A.mem_pick P),
      one_mul]
  · intro T hT
    refine (lintegral_le_sum_of_pairwiseDisjoint_pieces _ Z (fun P => N P ∩ U P) N hd
      (fun P hP => (hVo P hP).measurableSet) (fun P _ => Set.inter_subset_left) _
      (fun P y => ENNReal.ofReal (A.nsq (A.kap + E)
        (fun i y => A.g (A.kap + E) i (A.pick P) y * f P) y *
          Real.exp (-_root_.GlobalTheory.Published.L2Extension.psi A L s y)))
      (fun y hy => by simp only [hnsq0 y hy, zero_mul, ENNReal.ofReal_zero])
      (fun P hP y hy => by simp only [hnsq P hP y hy])).trans ?_
    calc _ ≤ ∑ P ∈ Z, ENNReal.ofReal (62 / 30 * (Real.pi ^ n / ((n - 1).factorial : ℝ)) / δ *
          _root_.GlobalTheory.Published.L2Extension.resSq A E L s P (f P)) := by
          refine Finset.sum_le_sum fun P hP => ?_
          rw [Measure.restrict_restrict (hNo P (hmemZ hP)).measurableSet]
          exact hNT P (hmemZ hP) T hT
      _ = _ := by
          rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg]
          intro P _
          exact mul_nonneg (by positivity) (resSq_nonneg A E L s P (f P))
  · refine lt_of_le_of_lt (lintegral_le_sum_of_pairwiseDisjoint_pieces A.mu Z (fun P => N P ∩ U P) N hd
      (fun P hP => (hVo P hP).measurableSet) (fun P _ => Set.inter_subset_left) _
      (fun P y => ENNReal.ofReal (1 / (1 + (δ * _root_.GlobalTheory.Published.L2Extension.psi A L s y) ^ 2) *
        A.nsq (A.kap + E) (fun i y => A.g (A.kap + E) i (A.pick P) y * f P) y *
          Real.exp (-_root_.GlobalTheory.Published.L2Extension.psi A L s y)))
      (fun y hy => by simp only [hnsq0 y hy, mul_zero, zero_mul, ENNReal.ofReal_zero])
      (fun P hP y hy => by simp only [hnsq P hP y hy])) ?_
    exact ENNReal.sum_lt_top.2 fun P hP => hNfin P (hmemZ hP)

end GlobalTheory.OTY
