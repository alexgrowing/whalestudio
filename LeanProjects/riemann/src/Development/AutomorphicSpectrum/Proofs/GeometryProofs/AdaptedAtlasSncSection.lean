import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.SimilitudeFactorFormGroupBoundedOfTestSupport
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverPrOfFnAlgClosed
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import ReciprocityTheory.AnalyticForms.LeviForms.TailBoundA
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsSncAdaptedChartAtPoint
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCEqZeroOfEventuallyEqZero
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffMulOfTsupport
open GlobalTheory.CompanionTheory.Ar AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam
open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open Classical

namespace GlobalTheory.CompanionTheory.Ar.Adapt

open ReciprocityTheory.AnForm.M.PLAux in

theorem exists_adaptedAtlas : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (L : LocPot X)
    (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ) (W : Fin n → Set X), IsPotential A L → IsSection A L s → IsSNC A L s m W →
    (∀ y, logNormSec L s y ≤ 0) → ∃ B : FinHolAtlas e X, IsAdaptedAtlas A B L s := by
  intro e X _ _ _ A L s n m W hL hs hsnc _hle
  have hgood : ∀ x : X, ∃ φ : OpenPartialHomeomorph X (Fin e → ℂ), IsCompatChart A φ ∧
      x ∈ φ.source ∧ φ x = 0 ∧ Metric.closedBall (0 : Fin e → ℂ) 2 ⊆ φ.target ∧
      ∃ (S : Finset (Fin e)) (μ : Fin e → ℕ) (M : ℝ), (∀ i ∈ S, 1 ≤ μ i) ∧
        (∀ y ∈ φ.target, (φ.symm y ∈ bdry s ↔ ∃ i ∈ S, y i = 0)) ∧
        ∀ y ∈ Metric.closedBall (0 : Fin e → ℂ) 2, φ.symm y ∉ bdry s →
          |rW L s (φ.symm y) - rLoc S μ y| ≤ M := by
    intro x
    obtain ⟨φ, S, μ, v, hφc, hxφ, hball, hφx, hsrcU, hμ, hv, hv0, hsv⟩ :=
      GlobalTheory.CompanionTheory.Ar.PB.LocalForm.exists_local_form e X A L s n m W hsnc x
    refine ⟨φ, hφc, hxφ, hφx, hball, S, μ, ?_⟩

    have hnorm : ∀ y ∈ φ.source,
        ‖s y y‖ * Real.exp (-L.φ y y) = ‖s x y‖ * Real.exp (-L.φ x y) := fun y hy =>
      (hs.2 x y y ⟨hsrcU hy, L.mem_U y⟩).symm
    have hzero : ∀ y ∈ φ.source, (s y y = 0 ↔ s x y = 0) := by
      intro y hy
      have h := hnorm y hy
      constructor
      · intro h0
        rw [h0, norm_zero, zero_mul] at h
        have := (mul_eq_zero.1 h.symm).resolve_right (Real.exp_pos _).ne'
        exact norm_eq_zero.1 this
      · intro h0
        rw [h0, norm_zero, zero_mul] at h
        have := (mul_eq_zero.1 h).resolve_right (Real.exp_pos _).ne'
        exact norm_eq_zero.1 this
    have hmono : ∀ y ∈ φ.source, (s x y = 0 ↔ ∃ i ∈ S, φ y i = 0) := by
      intro y hy
      rw [hsv y hy, mul_eq_zero, Finset.prod_eq_zero_iff]
      constructor
      · rintro (h | ⟨i, hi, h⟩)
        · exact absurd h (hv0 y hy)
        · exact ⟨i, hi, pow_eq_zero_iff (Nat.one_le_iff_ne_zero.1 (hμ i hi)) |>.1 h⟩
      · rintro ⟨i, hi, h⟩
        exact Or.inr ⟨i, hi, by rw [h, zero_pow (Nat.one_le_iff_ne_zero.1 (hμ i hi))]⟩
    have hbd : ∀ y ∈ φ.target, (φ.symm y ∈ bdry s ↔ ∃ i ∈ S, y i = 0) := by
      intro y hy
      have hp := φ.map_target hy
      show s (φ.symm y) (φ.symm y) = 0 ↔ _
      rw [hzero _ hp, hmono _ hp, φ.right_inv hy]

    have hK : IsCompact (Metric.closedBall (0 : Fin e → ℂ) 2) := isCompact_closedBall _ _
    have hF : ContinuousOn (fun z => Real.log ‖v (φ.symm z)‖) (Metric.closedBall (0 : Fin e → ℂ) 2) := by
      intro z hz
      have hzt := hball hz
      have han := analyticAt_compat_fun hφc hv hzt (φ.map_target hzt)
      exact (han.continuousAt.norm.log (by simpa using hv0 _ (φ.map_target hzt))).continuousWithinAt
    have hG : ContinuousOn (fun z => L.φ x (φ.symm z)) (Metric.closedBall (0 : Fin e → ℂ) 2) := by
      have h := contDiffOn_compat hφc (L.isOpen_U x) (hL.1 x)
      refine h.continuousOn.mono ?_
      intro z hz
      exact ⟨hball hz, hsrcU (φ.map_target (hball hz))⟩
    obtain ⟨C₁, hC₁⟩ := hK.exists_bound_of_continuousOn hF
    obtain ⟨C₂, hC₂⟩ := hK.exists_bound_of_continuousOn hG
    refine ⟨2 * C₁ + 2 * C₂ + ∑ i ∈ S, (μ i : ℝ) * Real.log 4, hμ, hbd, ?_⟩
    intro y hy hyb
    have hyt := hball hy
    have hp := φ.map_target hyt
    set p := φ.symm y with hpdef
    have hφp : φ p = y := φ.right_inv hyt
    have hspp : s p p ≠ 0 := hyb
    have hsxp : s x p ≠ 0 := fun h => hspp ((hzero p hp).2 h)
    have hyi : ∀ i ∈ S, y i ≠ 0 := fun i hi h0 =>
      hsxp ((hmono p hp).2 ⟨i, hi, by rw [hφp]; exact h0⟩)
    have hvp : v p ≠ 0 := hv0 p hp

    have hlogN : logNormSec L s p = Real.log ‖v p‖ + ∑ i ∈ S, (μ i : ℝ) * Real.log ‖y i‖ - L.φ x p := by
      unfold logNormSec
      rw [hnorm p hp, Real.log_mul (norm_ne_zero_iff.2 hsxp) (Real.exp_pos _).ne', Real.log_exp,
        hsv p hp, norm_mul, Real.log_mul (norm_ne_zero_iff.2 hvp), norm_prod,
        Real.log_prod]
      · rw [hφp]
        congr 2
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [norm_pow, Real.log_pow]
      · intro i hi
        rw [hφp, norm_pow]
        exact pow_ne_zero _ (norm_ne_zero_iff.2 (hyi i hi))
      · rw [norm_ne_zero_iff, Finset.prod_ne_zero_iff]
        intro i hi
        rw [hφp]
        exact pow_ne_zero _ (hyi i hi)
    have hloc : rLoc S μ y = Real.exp 1 + ∑ i ∈ S, (μ i : ℝ) * (Real.log 4 - 2 * Real.log ‖y i‖) := by
      unfold rLoc
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Real.log_div (by norm_num) (pow_ne_zero _ (norm_ne_zero_iff.2 (hyi i hi))), Real.log_pow]
      push_cast
      ring
    have hdiff : rW L s p - rLoc S μ y =
        -2 * Real.log ‖v p‖ + 2 * L.φ x p - ∑ i ∈ S, (μ i : ℝ) * Real.log 4 := by
      unfold rW
      rw [hlogN, hloc]
      simp only [mul_sub, Finset.sum_sub_distrib]
      rw [show ∑ i ∈ S, (μ i : ℝ) * (2 * Real.log ‖y i‖) = 2 * ∑ i ∈ S, (μ i : ℝ) * Real.log ‖y i‖ by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring]
      ring
    rw [hdiff]
    have h1 : |Real.log ‖v p‖| ≤ C₁ := by simpa [Real.norm_eq_abs] using hC₁ y hy
    have h2 : |L.φ x p| ≤ C₂ := by simpa [Real.norm_eq_abs] using hC₂ y hy
    have h3 : 0 ≤ ∑ i ∈ S, (μ i : ℝ) * Real.log 4 :=
      Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  choose φ hφc hφx hφ0 hφb hrest using hgood
  choose S μ M hμ hbd hbnd using hrest
  have hU : ∀ x, φ x ⁻¹' Metric.ball 0 1 ∩ (φ x).source ∈ nhds x := by
    intro x
    refine IsOpen.mem_nhds ?_ ⟨by simp [hφ0 x], hφx x⟩
    rw [Set.inter_comm]
    exact (φ x).continuousOn.isOpen_inter_preimage (φ x).open_source Metric.isOpen_ball
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover _ hU
  have hcov : ∀ x, ∃ y ∈ t, x ∈ φ y ⁻¹' Metric.ball 0 1 ∩ (φ y).source := by
    intro x
    have : x ∈ (⊤ : Set X) := trivial
    rw [← ht] at this
    simp only [Set.mem_iUnion] at this
    obtain ⟨y, hy, hx⟩ := this
    exact ⟨y, hy, hx⟩
  obtain ⟨B, hAB, h1, h2⟩ := ReciprocityTheory.AnForm.M.atlasOfCompat A (fun i => φ (t.equivFin.symm i))
    (fun i => hφc _) (fun x => by
      obtain ⟨y, hy, hx⟩ := hcov x
      exact ⟨t.equivFin ⟨y, hy⟩, by simpa using hx.2⟩)
  refine ⟨B, hAB, fun j => ?_, fun x => ?_, ∑ y ∈ t, |M y|, fun j => ?_⟩
  · obtain ⟨i, hi⟩ := h2 j
    rw [hi]
    exact hφb _
  · obtain ⟨y, hy, hx⟩ := hcov x
    obtain ⟨j, hj⟩ := h1 (t.equivFin ⟨y, hy⟩)
    refine ⟨j, ?_, ?_⟩
    · rw [hj]; simpa using hx.2
    · rw [hj]; simpa using hx.1
  · obtain ⟨i, hi⟩ := h2 j
    set y : X := (t.equivFin.symm i : X) with hydef
    have hyt : y ∈ t := (t.equivFin.symm i).2
    refine ⟨S y, μ y, hμ y, ?_, ?_⟩
    · rw [hi]; exact hbd y
    · intro z hz hzb
      rw [hi] at hzb ⊢
      refine (hbnd y z hz hzb).trans ((le_abs_self _).trans ?_)
      exact Finset.single_le_sum (f := fun y => |M y|) (fun _ _ => abs_nonneg _) hyt

end GlobalTheory.CompanionTheory.Ar.Adapt
