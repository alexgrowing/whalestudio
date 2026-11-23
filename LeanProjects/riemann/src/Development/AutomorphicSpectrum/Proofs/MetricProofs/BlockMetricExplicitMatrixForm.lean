import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HasStepCharts
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SelM
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsValueAtOfTorus
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMetricGrassmannChartLocalStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.ExactStep

theorem prod_base_split {K : Type} [Fintype K] {σ : Type} (blk : σ → Option K) (p : σ) (k₀ : K)
    (hp : blk p = some k₀) (f : K → ℝ)
    (hf : ∀ k, (¬ ∀ p', blk p' ≠ some k) → k ≠ k₀ → f k = 1) :
    ∏ k, f k = (∏ k : NonPluckerBlocks blk, f k.1) * f k₀ := by
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ fun k => ∀ p', blk p' ≠ some k]
  congr 1
  · exact Finset.prod_subtype _ (by simp) f
  · refine Finset.prod_eq_single_of_mem k₀ ?_ ?_
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, fun e => e p hp⟩
    · intro k hk e
      exact hf k (Finset.mem_filter.1 hk).2 e

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (k₀ : K) (l : Fin BM.q) (x₀ : BM.Rb.X) (z : (Σ k, ι k) → ℂ) (I₀ : Finset (Fin N)) (C : Matrix (Fin N) (Fin N) ℂ) (B : Finset (Fin N) → Matrix (Fin N) (Fin N) ℂ), M.blk p = some k₀ → IsGrChart N j p.2 I₀ C B → x₀ ∈ BM.O l \ bdry BM.s → z ∈ mcPts (mCoordIdeal y) → SameOrbit (basePart M.blk z) (BM.Rb.lift x₀ x₀) → plk M (BM.F l) k₀ z I₀ ≠ 0 → Real.log ((BM.hom p).h z) = blockPot j p.2 (BM.G l p.1 x₀) (grMat C B I₀ (plk M (BM.F l) k₀ z)) + Real.log ‖baseMono M (BM.F l) p z * plk M (BM.F l) k₀ z I₀‖ := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p k₀ l x₀ z I₀ C B hp hC hx hz hor hw
  obtain ⟨h, a, hb, hd, ha, hstep, hzk⟩ := GlobalTheory.T.block_metric_grassmann_chart_local K ι Φ y Ψ N j M n BM p k₀ l x₀ z hp hx.1 hz hor
  obtain ⟨hHb, hHd, hHm⟩ := hC h a _ hb hd ha hstep hw
  have hL : BM.Rb.lift x₀ x₀ ∈ mcPts (mCoordIdeal M.x) := BM.Rb.mem x₀ x₀ (BM.Rb.mem_U x₀)
  have hor' := hor
  obtain ⟨c0, hc0, e0⟩ := hor'
  have hbz : basePart M.blk z ∈ mcPts (mCoordIdeal M.x) := by
    rw [e0]
    exact ((TorusAct.main _ _ _ M.x _ c0 hc0).2 hL).1
  have hne : ∀ k : NonPluckerBlocks M.blk, basePart M.blk z ⟨k, (BM.F l).c k⟩ ≠ 0 := by
    intro k h0
    have hl : BM.Rb.lift x₀ x₀ ⟨k, (BM.F l).c k⟩ = 0 := by
      have e1 := congrFun e0 ⟨k, (BM.F l).c k⟩
      rw [h0] at e1
      exact (mul_eq_zero.1 e1.symm).resolve_left (hc0 k)
    refine (BM.good l x₀ hx.1).1 k ?_
    show mConeMap (BM.Rb.lift x₀ x₀) (X ⟨k, (BM.F l).c k⟩) = 0
    rw [mConeMap, aeval_X, hl, map_zero, zero_mul]
  let c : K → ℂ := fun k => if hk : ∀ p', M.blk p' ≠ some k then
    (basePart M.blk z ⟨⟨k, hk⟩, (BM.F l).c ⟨k, hk⟩⟩)⁻¹ else if k = k₀ then (plk M (BM.F l) k₀ z I₀)⁻¹ else 1
  have hcb : ∀ k : NonPluckerBlocks M.blk, c k.1 = (basePart M.blk z ⟨k, (BM.F l).c k⟩)⁻¹ := fun k => dif_pos k.2
  have hk₀ : ¬ ∀ p', M.blk p' ≠ some k₀ := fun e => e p hp
  have hck : c k₀ = (plk M (BM.F l) k₀ z I₀)⁻¹ := (dif_neg hk₀).trans (if_pos rfl)
  have hc : ∀ k, c k ≠ 0 := by
    intro k
    by_cases hk : ∀ p', M.blk p' ≠ some k
    · rw [hcb ⟨k, hk⟩]
      exact inv_ne_zero (hne ⟨k, hk⟩)
    · by_cases e : k = k₀
      · rw [e, hck]
        exact inv_ne_zero hw
      · rw [show c k = 1 from (dif_neg hk).trans (if_neg e)]
        exact one_ne_zero
  have hz₂ := ((TorusAct.main K ι Φ y z c hc).2 hz).1
  have hval := ((TorusAct.main _ _ _ M.x _ (fun k : NonPluckerBlocks M.blk => c k.1) (fun k => hc _)).2 hbz).2
  have hbp : basePart M.blk (fun q : Σ k, ι k => c q.1 * z q) =
      fun q : Σ k, baseIdx ι M.blk k => c q.1.1 * basePart M.blk z q := rfl
  have hso : SameOrbit (basePart M.blk (fun q : Σ k, ι k => c q.1 * z q)) (BM.Rb.lift x₀ x₀) := by
    refine ⟨fun k => c k.1 * c0 k, fun k => mul_ne_zero (hc _) (hc0 k), ?_⟩
    rw [hbp, e0]
    funext q
    exact (mul_assoc _ _ _).symm
  have hnorm : ∀ k, basePart M.blk (fun q : Σ k, ι k => c q.1 * z q) ⟨k, (BM.F l).c k⟩ = 1 := fun k => by
    rw [hbp]
    show c k.1 * basePart M.blk z ⟨k, (BM.F l).c k⟩ = 1
    rw [hcb k, inv_mul_cancel₀ (hne k)]
  have hlog := (BM.induced l x₀ hx p _ hz₂ hso hnorm _ hHb hHd).1 k₀ hp (fun m => by
    rw [hbp, hzk m, hck]
    simp only [hval]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [mul_left_comm a, ← hHm I, mul_left_comm, ← mul_assoc _ _ (plk M (BM.F l) k₀ z I₀), mul_comm _ (plk M (BM.F l) k₀ z I₀),
      mul_inv_cancel_left₀ hw])
  have hs := (BM.hom p).smul c z hc
  rw [BM.hom_deg p] at hs
  have hdy : M.dy p k₀ = 1 := (dif_neg hk₀).trans (if_pos hp)
  have hdy0 : ∀ k, (¬ ∀ p', M.blk p' ≠ some k) → k ≠ k₀ → M.dy p k = 0 := fun k hk e =>
    (dif_neg hk).trans (if_neg fun e' => e (Option.some_injective _ (hp.symm.trans e')).symm)
  have hsplit := prod_base_split M.blk p k₀ hp (fun k => ‖c k‖ ^ M.dy p k)
    (fun k hk e => by simp only [hdy0 k hk e, zpow_zero])
  have hPQ : (∏ k, ‖c k‖ ^ M.dy p k) * ‖baseMono M (BM.F l) p z * plk M (BM.F l) k₀ z I₀‖ = 1 := by
    rw [hsplit, hdy, zpow_one, hck, norm_mul, baseMono, norm_prod, norm_inv]
    simp only [norm_zpow]
    rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib, inv_mul_cancel₀ (norm_ne_zero_iff.2 hw), mul_one]
    refine Finset.prod_eq_one fun k _ => ?_
    rw [hcb k, norm_inv, _root_.inv_zpow, inv_mul_cancel₀ (zpow_ne_zero _ (norm_ne_zero_iff.2 (hne k)))]
  have hpos := (BM.hom p).pos (fun q => c q.1 * z q) hz₂.1
  have hQ : ‖baseMono M (BM.F l) p z * plk M (BM.F l) k₀ z I₀‖ ≠ 0 := fun e => by
    rw [e, mul_zero] at hPQ
    exact zero_ne_one hPQ
  have hh : (BM.hom p).h z =
      ‖baseMono M (BM.F l) p z * plk M (BM.F l) k₀ z I₀‖ * (BM.hom p).h fun q => c q.1 * z q := by
    rw [hs, ← mul_assoc, mul_comm ‖baseMono M (BM.F l) p z * plk M (BM.F l) k₀ z I₀‖, hPQ, one_mul]
  rw [hh, Real.log_mul hQ hpos.ne', hlog, add_comm]

end GlobalTheory.CompanionTheory.Ar.PB.StepW.ExactStep
