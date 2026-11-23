import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.LocalModel

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem continuousAt_of_chart {E : Type} [TopologicalSpace E] (A : FinHolAtlas e X) (j : Fin A.n) {p : X}
    (hp : p ∈ (A.chart j).source) (f : X → E)
    (h : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j p)) : ContinuousAt f p := by
  have h1 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ (A.chart j)) p :=
    ContinuousAt.comp (f := A.chart j) h ((A.chart j).continuousAt hp)
  refine h1.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hp] with z hz
  simp [(A.chart j).left_inv hz]

theorem continuousAt_of_holoOn (A : FinHolAtlas e X) {U : Set X} {g : X → ℂ} (hg : A.HoloOn U g)
    {p : X} (hp : p ∈ U) : ContinuousAt g p := by
  obtain ⟨j, hj⟩ := A.cover p
  refine continuousAt_of_chart A j hj g ?_
  refine (hg j _ ⟨(A.chart j).map_source hj, ?_⟩).continuousAt
  simpa [(A.chart j).left_inv hj] using hp

theorem continuousAt_of_smoothOn (A : FinHolAtlas e X) {U : Set X} (hU : IsOpen U) {f : X → ℝ}
    (hf : A.SmoothOn U f) {p : X} (hp : p ∈ U) : ContinuousAt f p := by
  obtain ⟨j, hj⟩ := A.cover p
  refine continuousAt_of_chart A j hj f ?_
  have hmem : A.chart j p ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U :=
    ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hp⟩
  exact (hf j).continuousOn.continuousAt
    (((A.chart j).isOpen_inter_preimage_symm hU).mem_nhds hmem)

theorem zero_set_and_bound : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ), IsPotential A L → IsSection A L s → ∀ (x : X) (φ : OpenPartialHomeomorph X (Fin e → ℂ)) (S : Finset (Fin e)) (μ : Fin e → ℕ) (v : X → ℂ), IsCompatChart A φ → Metric.closedBall (0 : Fin e → ℂ) 2 ⊆ φ.target → φ.source ⊆ L.U x → (∀ i ∈ S, 1 ≤ μ i) → A.HoloOn φ.source v → (∀ y ∈ φ.source, v y ≠ 0) → (∀ y ∈ φ.source, s x y = v y * ∏ i ∈ S, φ y i ^ μ i) → (∀ y ∈ φ.target, (φ.symm y ∈ bdry s ↔ ∃ i ∈ S, y i = 0)) ∧ ∃ M : ℝ, ∀ y ∈ Metric.closedBall (0 : Fin e → ℂ) 2, φ.symm y ∉ bdry s → |rW L s (φ.symm y) - rLoc S μ y| ≤ M := by
  intro e X _ A L s hL hs x φ S μ v hφ hball hsrc hμ hv hv0 hsv

  have glue : ∀ y ∈ φ.target, ‖s x (φ.symm y)‖ * Real.exp (-L.φ x (φ.symm y)) =
      ‖s (φ.symm y) (φ.symm y)‖ * Real.exp (-L.φ (φ.symm y) (φ.symm y)) := fun y hy =>
    hs.2 x (φ.symm y) (φ.symm y) ⟨hsrc (φ.map_target hy), L.mem_U _⟩
  have hform : ∀ y ∈ φ.target, s x (φ.symm y) = v (φ.symm y) * ∏ i ∈ S, y i ^ μ i := by
    intro y hy
    rw [hsv _ (φ.map_target hy)]
    simp only [φ.right_inv hy]
  have hzero : ∀ y ∈ φ.target, (φ.symm y ∈ bdry s ↔ ∃ i ∈ S, y i = 0) := by
    intro y hy
    have h1 : s (φ.symm y) (φ.symm y) = 0 ↔ s x (φ.symm y) = 0 := by
      have hg := glue y hy
      constructor
      · intro h0
        rw [h0] at hg
        simpa [Real.exp_ne_zero] using hg
      · intro h0
        rw [h0, norm_zero, zero_mul] at hg
        rcases mul_eq_zero.1 hg.symm with h | h
        · exact norm_eq_zero.1 h
        · exact absurd h (Real.exp_ne_zero _)
    change s (φ.symm y) (φ.symm y) = 0 ↔ _
    rw [h1, hform y hy, mul_eq_zero, Finset.prod_eq_zero_iff]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact absurd h (hv0 _ (φ.map_target hy))
      · exact ⟨i, hi, (pow_eq_zero_iff (Nat.one_le_iff_ne_zero.1 (hμ i hi))).1 h⟩
    · rintro ⟨i, hi, h⟩
      refine Or.inr ⟨i, hi, ?_⟩
      rw [h]
      exact zero_pow (Nat.one_le_iff_ne_zero.1 (hμ i hi))
  refine ⟨hzero, ?_⟩

  have hcont : ContinuousOn (fun y => -2 * Real.log ‖v (φ.symm y)‖ + 2 * L.φ x (φ.symm y)) φ.target := by
    intro y hy
    have hp := φ.map_target hy
    have cs : ContinuousAt φ.symm y := φ.continuousAt_symm hy
    have c1 : ContinuousAt (fun y => v (φ.symm y)) y :=
      ContinuousAt.comp (f := φ.symm) (continuousAt_of_holoOn A hv hp) cs
    have c2 : ContinuousAt (fun y => L.φ x (φ.symm y)) y :=
      ContinuousAt.comp (f := φ.symm)
        (continuousAt_of_smoothOn A (L.isOpen_U x) (hL.1 x) (hsrc hp)) cs
    have c3 : ContinuousAt (fun y => Real.log ‖v (φ.symm y)‖) y :=
      c1.norm.log (norm_ne_zero_iff.2 (hv0 _ hp))
    exact ((continuousAt_const.mul c3).add (continuousAt_const.mul c2)).continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Fin e → ℂ) 2).exists_bound_of_continuousOn
    (hcont.mono hball)
  refine ⟨C + |(∑ i ∈ S, (μ i : ℝ)) * Real.log 4|, fun y hy hnb => ?_⟩
  have hyt := hball hy
  have hnz : ∀ i ∈ S, y i ≠ 0 := fun i hi h0 => hnb ((hzero y hyt).2 ⟨i, hi, h0⟩)
  have hs0 : s (φ.symm y) (φ.symm y) ≠ 0 := hnb
  have hvn : ‖v (φ.symm y)‖ ≠ 0 := norm_ne_zero_iff.2 (hv0 _ (φ.map_target hyt))
  have hlogS : Real.log (∏ i ∈ S, ‖y i‖ ^ μ i) = ∑ i ∈ S, (μ i : ℝ) * Real.log ‖y i‖ := by
    rw [Real.log_prod (fun i hi => pow_ne_zero _ (norm_ne_zero_iff.2 (hnz i hi)))]
    exact Finset.sum_congr rfl fun i _ => Real.log_pow _ _
  have hlog : logNormSec L s (φ.symm y) = Real.log ‖v (φ.symm y)‖ +
      ∑ i ∈ S, (μ i : ℝ) * Real.log ‖y i‖ - L.φ x (φ.symm y) := by
    unfold logNormSec
    rw [← glue y hyt, hform y hyt, norm_mul, norm_prod]
    simp only [norm_pow]
    rw [Real.log_mul (mul_ne_zero hvn (Finset.prod_ne_zero_iff.2 fun i hi =>
        pow_ne_zero _ (norm_ne_zero_iff.2 (hnz i hi)))) (Real.exp_ne_zero _),
      Real.log_mul hvn (Finset.prod_ne_zero_iff.2 fun i hi =>
        pow_ne_zero _ (norm_ne_zero_iff.2 (hnz i hi))), hlogS, Real.log_exp]
    ring
  have hloc : rLoc S μ y = Real.exp 1 + (∑ i ∈ S, (μ i : ℝ)) * Real.log 4 -
      2 * ∑ i ∈ S, (μ i : ℝ) * Real.log ‖y i‖ := by
    unfold rLoc
    rw [Finset.sum_mul, Finset.mul_sum, add_sub_assoc, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hn : ‖y i‖ ≠ 0 := norm_ne_zero_iff.2 (hnz i hi)
    rw [Real.log_div (by norm_num) (pow_ne_zero _ hn), Real.log_pow]
    push_cast
    ring
  have hdiff : rW L s (φ.symm y) - rLoc S μ y =
      (-2 * Real.log ‖v (φ.symm y)‖ + 2 * L.φ x (φ.symm y)) -
        (∑ i ∈ S, (μ i : ℝ)) * Real.log 4 := by
    unfold rW
    rw [hlog, hloc]
    ring
  rw [hdiff]
  have hb := hC y hy
  rw [Real.norm_eq_abs] at hb
  exact (abs_sub _ _).trans (add_le_add hb le_rfl)

end GlobalTheory.CompanionTheory.Ar.PB.LocalModel
