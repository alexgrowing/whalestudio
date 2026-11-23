import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RwAppend
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA

theorem one_mem_GLs (n : ℕ) : (1 : Mat n) ∈ GLs n := by
  simp [GLs]

theorem exists_mollifiers (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] :
    ∃ φ : ℕ → Mat n → ℝ, (∀ k, IsTest (φ k)) ∧ (∀ k y, 0 ≤ φ k y) ∧
      (∀ k, ∫ y : G n, φ k y.val ∂μ = 1) ∧
      ∀ N ∈ 𝓝 (1 : G n), ∀ᶠ k in atTop, ∀ y : G n, φ k y.val ≠ 0 → y ∈ N := by
  haveI : ProperSpace (Mat n) := FiniteDimensional.proper ℝ _
  have hemb := GlobalTheory.CompanionTheory.SobGL.HaarDom.isOpenEmbedding_valG n
  obtain ⟨r, hr0, hr⟩ : ∃ r > 0, Metric.closedBall (1 : Mat n) r ⊆ GLs n :=
    Metric.nhds_basis_closedBall.mem_iff.1 (isOpen_GLs.mem_nhds (one_mem_GLs n))
  have hrange : ∀ x ∈ GLs n, x ∈ Set.range (Units.val : G n → Mat n) := by
    intro x hx
    have hu : IsUnit x := (Matrix.isUnit_iff_isUnit_det x).2 (isUnit_iff_ne_zero.2 hx)
    exact ⟨hu.unit, rfl⟩
  let b : ℕ → ContDiffBump (1 : Mat n) := fun k =>
    { rIn := r / (2 * ((k : ℝ) + 1))
      rOut := r / ((k : ℝ) + 1)
      rIn_pos := by positivity
      rIn_lt_rOut := by
        have : (0 : ℝ) < (k : ℝ) + 1 := by positivity
        exact div_lt_div_of_pos_left hr0 this (by linarith) }
  have hbOut : ∀ k, (b k).rOut ≤ r := by
    intro k
    exact div_le_self hr0.le (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
  have hcont : ∀ k, Continuous fun y : G n => b k y.val := fun k =>
    (b k).continuous.comp Units.continuous_val
  have hcomp : ∀ k, HasCompactSupport fun y : G n => b k y.val := by
    intro k
    have hK : IsCompact ((Units.val : G n → Mat n) ⁻¹' Metric.closedBall (1 : Mat n) r) :=
      (hemb.isInducing.isCompact_preimage_iff (fun x hx => hrange x (hr hx))).2
        (isCompact_closedBall _ _)
    refine HasCompactSupport.intro hK ?_
    intro y hy
    have : y.val ∉ Function.support (b k) := by
      rw [(b k).support_eq]
      intro h
      exact hy (Metric.closedBall_subset_closedBall (hbOut k) (Metric.ball_subset_closedBall h))
    simpa using this
  have hpos : ∀ k, 0 < ∫ y : G n, b k y.val ∂μ := by
    intro k
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := (1 : G n)) (hcont k)
      (hcomp k) (fun y => (b k).nonneg) ?_
    simpa using (b k).one_of_mem_closedBall (x := (1 : Mat n)) (by simp [(b k).rIn_pos.le]) |>.symm ▸ one_ne_zero
  refine ⟨fun k x => (∫ y : G n, b k y.val ∂μ)⁻¹ * b k x, ?_, ?_, ?_, ?_⟩
  · intro k
    have hts : tsupport (b k) ⊆ Metric.closedBall (1 : Mat n) r := by
      exact (b k).tsupport_eq.le.trans (Metric.closedBall_subset_closedBall (hbOut k))
    have hsub : tsupport (fun x => (∫ y : G n, b k y.val ∂μ)⁻¹ * b k x) ⊆ tsupport (b k) :=
      closure_mono fun x hx h => hx (by simp [h])
    refine ⟨contDiff_const.mul (b k).contDiff, ((b k).hasCompactSupport).mul_left, ?_⟩
    exact hsub.trans (hts.trans hr)
  · intro k y
    exact mul_nonneg (inv_nonneg.2 (hpos k).le) (b k).nonneg
  · intro k
    simp only []
    rw [integral_const_mul, inv_mul_cancel₀ (hpos k).ne']
  · intro N hN
    have himg : (Units.val : G n → Mat n) '' N ∈ 𝓝 (1 : Mat n) := by
      have := hemb.isOpenMap.image_mem_nhds hN
      simpa using this
    obtain ⟨ε, hε0, hε⟩ := Metric.mem_nhds_iff.1 himg
    obtain ⟨K, hK⟩ := exists_nat_gt (r / ε)
    filter_upwards [eventually_ge_atTop K] with k hk y hy
    have hne : b k y.val ≠ 0 := right_ne_zero_of_mul hy
    have hsupp : y.val ∈ Metric.ball (1 : Mat n) (b k).rOut := by
      rw [← (b k).support_eq]
      exact hne
    have hlt : (b k).rOut < ε := by
      have h1 : r / ε < (k : ℝ) + 1 := by
        have : (K : ℝ) ≤ k := by exact_mod_cast hk
        linarith
      have h2 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      show r / ((k : ℝ) + 1) < ε
      rw [div_lt_iff₀ h2]
      rw [div_lt_iff₀ hε0] at h1
      linarith
    obtain ⟨z, hz, e⟩ := hε (Metric.ball_subset_ball hlt.le hsupp)
    have : z = y := hemb.injective e
    exact this ▸ hz

end GlobalTheory.CompanionTheory.PresSobA
