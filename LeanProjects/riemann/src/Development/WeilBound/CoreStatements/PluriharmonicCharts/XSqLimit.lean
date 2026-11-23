import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.TsgPolyVolPolyCoeffEven
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.WeilBound.CoreStatements.PluriharmonicCharts.ContinuousOnLogNormSec
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticSystemRegularityProperties
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace PositivityTheory.Xgp.sq_limit

open scoped ContDiff

section Gen

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem continuousOn_of_smoothOn (A : FinHolAtlas e X) {U : Set X} (hU : IsOpen U) {f : X → ℝ}
    (hf : A.SmoothOn U f) : ContinuousOn f U := by
  intro x hx
  obtain ⟨j, hj⟩ := A.cover x
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) :=
    (A.chart j).isOpen_inter_preimage_symm hU
  have hmem : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U :=
    ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hx⟩
  have h1 : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j x) :=
    (hf j).continuousOn.continuousAt (hO.mem_nhds hmem)
  have h2 : ContinuousAt (A.chart j) x := (A.chart j).continuousAt hj
  have h3 : ContinuousAt (fun y => (f ∘ (A.chart j).symm) (A.chart j y)) x := h1.comp h2
  refine (h3.congr ?_).continuousWithinAt
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]

theorem member_unif (A : FinHolAtlas e X) {U : Set X} (hU : IsOpen U) {ph : X → ℝ} {phT : ℝ → X → ℝ}
    (hC2 : ∀ j, ∀ K ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U, IsCompact K →
      TendstoUniformlyOn (fun t => phT t ∘ (A.chart j).symm) (ph ∘ (A.chart j).symm) (𝓝[>] 0) K)
    {x : X} (hx : x ∈ U) {δ : ℝ} (hδ : 0 < δ) :
    ∃ V ∈ 𝓝 x, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ y ∈ V, |phT t y - ph y| < δ := by
  obtain ⟨j, hj⟩ := A.cover x
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) :=
    (A.chart j).isOpen_inter_preimage_symm hU
  have hmem : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U :=
    ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hx⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hO _ hmem
  have hK : Metric.closedBall (A.chart j x) (r / 2) ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hu := Metric.tendstoUniformlyOn_iff.1 (hC2 j _ hK (isCompact_closedBall _ _)) δ hδ
  refine ⟨(A.chart j).source ∩ (A.chart j) ⁻¹' Metric.ball (A.chart j x) (r / 2), ?_, ?_⟩
  · exact Filter.inter_mem ((A.chart j).open_source.mem_nhds hj)
      ((A.chart j).continuousAt hj (Metric.ball_mem_nhds _ (by linarith)))
  · filter_upwards [hu] with t ht y hy
    have h1 := ht (A.chart j y) (Metric.ball_subset_closedBall hy.2)
    simp only [Function.comp, (A.chart j).left_inv hy.1, Real.dist_eq] at h1
    rwa [abs_sub_comm] at h1

theorem sum_unif (A : FinHolAtlas e X) {U : Set X} (hU : IsOpen U) {ι : Type} [Fintype ι]
    (ph : ι → X → ℝ) (phT : ι → ℝ → X → ℝ) (c : ι → ℝ) (cst : ℝ)
    (hC2 : ∀ i, ∀ j, ∀ K ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U, IsCompact K →
      TendstoUniformlyOn (fun t => phT i t ∘ (A.chart j).symm) (ph i ∘ (A.chart j).symm) (𝓝[>] 0) K)
    (t₀ : ℝ) (ht₀ : 0 < t₀) :
    TendstoLocallyUniformlyOn
      (fun t x => if 0 < t ∧ t ≤ t₀ then cst + ∑ i, c i * phT i t x else cst + ∑ i, c i * ph i x)
      (fun x => cst + ∑ i, c i * ph i x) (𝓝[>] 0) U := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε x hx
  have hM0 : 0 ≤ ∑ i, |c i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hδ : 0 < ε / (∑ i, |c i| + 1) := div_pos hε (by linarith)
  choose V hV hev using fun i => member_unif A hU (hC2 i) hx hδ
  refine ⟨⋂ i, V i, mem_nhdsWithin_of_mem_nhds (Filter.iInter_mem.2 hV), ?_⟩
  filter_upwards [Filter.eventually_all.2 hev, Ioc_mem_nhdsGT ht₀] with t ht htt y hy
  rw [if_pos ⟨htt.1, htt.2⟩, Real.dist_eq]
  have hy' : ∀ i, y ∈ V i := Set.mem_iInter.1 hy
  have e1 : cst + ∑ i, c i * ph i y - (cst + ∑ i, c i * phT i t y) = ∑ i, c i * (ph i y - phT i t y) := by
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1]
  calc |∑ i, c i * (ph i y - phT i t y)| ≤ ∑ i, |c i * (ph i y - phT i t y)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |c i| * (ε / (∑ i, |c i| + 1)) := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (by rw [abs_sub_comm]; exact (ht i y (hy' i)).le) (abs_nonneg _)
    _ = (∑ i, |c i|) * (ε / (∑ i, |c i| + 1)) := by rw [Finset.sum_mul]
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
        nlinarith

theorem abs_lin_le {ι : Type} [Fintype ι] (c : ι → ℝ) (cst : ℝ) (f : ι → ℝ) {B l : ℝ}
    (hf : ∀ i, |f i| ≤ B * l) (hl : 1 ≤ l) :
    |cst + ∑ i, c i * f i| ≤ (|cst| + ∑ i, |c i| * B) * l := by
  have h1 : |cst + ∑ i, c i * f i| ≤ |cst| + ∑ i, |c i| * |f i| := by
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun i _ => abs_mul _ _
  have h2 : ∑ i, |c i| * |f i| ≤ ∑ i, |c i| * (B * l) :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hf i) (abs_nonneg _)
  have h3 : |cst| ≤ |cst| * l := le_mul_of_one_le_right (abs_nonneg _) hl
  have h4 : (|cst| + ∑ i, |c i| * B) * l = |cst| * l + ∑ i, |c i| * (B * l) := by
    rw [add_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h4]
  linarith

end Gen

theorem regular (hC : ConvergenceSignedStatement) {e : ℕ} {τ : Type} (S : AnSys e τ) (w : Fin e → τ)
    {ι : Type} [Fintype ι] (mm : ι → τ) (c : ι → ℝ) (cst : ℝ) (ht₀ : 0 < S.t₀) :
    MIntegrable S.A (fun r => S.potH (w r)) (fun x => cst + ∑ i, c i * S.ph (mm i) x) ∧
      Tendsto (fun t => mInt S.A (fun r => S.potT (w r) t) (fun x => cst + ∑ i, c i * S.phT (mm i) t x))
        (𝓝[>] 0) (𝓝 (mInt S.A (fun r => S.potH (w r)) (fun x => cst + ∑ i, c i * S.ph (mm i) x))) := by
  letI : MeasurableSpace S.X := borel S.X
  haveI : BorelSpace S.X := ⟨rfl⟩
  obtain ⟨hopen, -, -, -, hrW⟩ := GlobalTheory.CompanionTheory.Ar.PB.anSys_open_basics e τ S
  have hU : IsOpen (bdry S.s)ᶜ := hopen
  have hl : ∀ y, y ∉ bdry S.s → 1 ≤ Real.log (rW S.L S.s y) := fun y hy => by
    have h := hrW y hy
    have h1 := Real.log_le_log (Real.exp_pos 1) h
    rwa [Real.log_exp] at h1
  have hph : ∀ o y, y ∉ bdry S.s → |S.ph o y| ≤ (|S.C| + |S.C₅|) * Real.log (rW S.L S.s y) := by
    intro o y hy
    obtain ⟨h1, h2⟩ := (S.sing o).2.2.2 y hy
    have := hl y hy
    refine abs_le.2 ⟨?_, ?_⟩ <;> nlinarith [abs_nonneg S.C, abs_nonneg S.C₅, le_abs_self S.C₅,
      neg_abs_le S.C₅, le_abs_self S.C]
  have hphT : ∀ o t, 0 < t → t ≤ S.t₀ → ∀ y, y ∉ bdry S.s →
      |S.phT o t y| ≤ (|S.C| + |S.C₅|) * Real.log (rW S.L S.s y) := by
    intro o t h0 h1 y hy
    obtain ⟨-, hle, hge, -⟩ := (S.reg o).2.2 t h0 h1
    have a1 := hle y
    have a2 := hge y hy
    obtain ⟨b1, -⟩ := (S.sing o).2.2.2 y hy
    have := hl y hy
    refine abs_le.2 ⟨?_, ?_⟩ <;> nlinarith [abs_nonneg S.C, abs_nonneg S.C₅, le_abs_self S.C₅,
      neg_abs_le S.C₅, le_abs_self S.C]
  have hgc : ∀ t, ContinuousOn (fun x => if 0 < t ∧ t ≤ S.t₀ then cst + ∑ i, c i * S.phT (mm i) t x
      else cst + ∑ i, c i * S.ph (mm i) x) (bdry S.s)ᶜ := by
    intro t
    by_cases ht : 0 < t ∧ t ≤ S.t₀
    · simp only [ht, and_self, if_true]
      refine continuousOn_const.add (continuousOn_finset_sum _ fun i _ => continuousOn_const.mul ?_)
      exact (continuousOn_of_smoothOn S.A isOpen_univ ((S.reg (mm i)).2.2 t ht.1 ht.2).1).mono
        (Set.subset_univ _)
    · simp only [ht, if_false]
      exact continuousOn_const.add (continuousOn_finset_sum _ fun i _ => continuousOn_const.mul
        (continuousOn_of_smoothOn S.A hU (S.sing (mm i)).2.1))
  have hgb : ∀ t y, y ∉ bdry S.s → |(fun x => if 0 < t ∧ t ≤ S.t₀ then cst + ∑ i, c i * S.phT (mm i) t x
      else cst + ∑ i, c i * S.ph (mm i) x) y| ≤
      (|cst| + ∑ i, |c i| * (|S.C| + |S.C₅|)) * Real.log (rW S.L S.s y) := by
    intro t y hy
    by_cases ht : 0 < t ∧ t ≤ S.t₀
    · simp only [ht, and_self, if_true]
      exact abs_lin_le c cst _ (fun i => hphT (mm i) t ht.1 ht.2 y hy) (hl y hy)
    · simp only [ht, if_false]
      exact abs_lin_le c cst _ (fun i => hph (mm i) y hy) (hl y hy)
  have hlim := sum_unif S.A hU (fun i => S.ph (mm i)) (fun i => S.phT (mm i)) c cst
    (fun i j K hK hKc => ((S.c2 (mm i)) j K hK hKc).1) S.t₀ ht₀
  have h := hC S.A S.Θ S.L S.s S.m S.W S.potΘ S.posΘ S.potL S.sec S.snc S.norm_le
    (fun r => S.th (w r)) (fun r => S.ph (w r)) (fun r => S.phT (w r)) S.C₅ S.C S.t₀
    (fun r => S.sing (w r)) (fun r => S.reg (w r)) (fun r => S.c2 (w r))
    (fun x => cst + ∑ i, c i * S.ph (mm i) x) _ _ hgc hgb hlim
  refine ⟨h.1, h.2.congr' ?_⟩
  filter_upwards [Ioc_mem_nhdsGT ht₀] with t ht
  have e1 : (fun x => if 0 < t ∧ t ≤ S.t₀ then cst + ∑ i, c i * S.phT (mm i) t x
      else cst + ∑ i, c i * S.ph (mm i) x) = fun x => cst + ∑ i, c i * S.phT (mm i) t x := by
    funext x
    rw [if_pos ⟨ht.1, ht.2⟩]
  rw [e1]
  rfl

section Lin

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem mIntegrable_add' (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) {f g : X → ℝ}
    (hf : MIntegrable A Φ f) (hg : MIntegrable A Φ g) : MIntegrable A Φ (fun x => f x + g x) := by
  intro j K hK hKc
  refine ((hf j K hK hKc).add (hg j K hK hKc)).congr_fun (fun y _ => ?_) hKc.measurableSet
  simp only [Pi.add_apply]
  ring

theorem mInt_add' [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) {f g : X → ℝ}
    (hf : MIntegrable A Φ f) (hg : MIntegrable A Φ g) :
    mInt A Φ (fun x => f x + g x) = mInt A Φ f + mInt A Φ g := by
  unfold mInt
  split_ifs with h
  · unfold integralWith
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← integral_add (ReciprocityTheory.AnForm.M.integrableOn_weight A h.some Φ f hf j)
      (ReciprocityTheory.AnForm.M.integrableOn_weight A h.some Φ g hg j)]
    congr 1
    funext y
    ring
  · simp

theorem mIntegrable_of_continuous (A : FinHolAtlas e X) (Φ : Fin e → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) {g : X → ℝ} (hg : Continuous g) : MIntegrable A Φ g := by
  intro j K hK hKc
  exact ((hg.comp_continuousOn ((A.chart j).continuousOn_symm.mono hK)).mul
    ((ReciprocityTheory.AnForm.M.locDensCont A Φ hΦ j).mono hK)).integrableOn_compact hKc

end Lin

end PositivityTheory.Xgp.sq_limit
