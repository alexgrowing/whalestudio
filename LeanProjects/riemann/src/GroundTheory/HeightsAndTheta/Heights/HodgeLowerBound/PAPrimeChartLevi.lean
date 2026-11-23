import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StAPrimeChartLeviLocal
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StChartVelLift
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm (levi)
open scoped ContDiff

theorem continuousOn_levi_of_contDiffOn {n : ℕ} {f : (Fin n → ℂ) → ℝ} {W : Set (Fin n → ℂ)} (hW : IsOpen W)
    (hf : ContDiffOn ℝ 2 f W) :
    ContinuousOn (fun p : (Fin n → ℂ) × (Fin n → ℂ) => levi f p.1 p.2) (W ×ˢ Set.univ) := by
  have h1 : ContDiffOn ℝ 1 (fun y => fderiv ℝ f y) W := hf.fderiv_of_isOpen hW (by norm_num)
  have h2 : ContinuousOn (fderiv ℝ (fderiv ℝ f)) W := h1.continuousOn_fderiv_of_isOpen hW le_rfl
  have hH : ContinuousOn (fun p : (Fin n → ℂ) × (Fin n → ℂ) => fderiv ℝ (fderiv ℝ f) p.1) (W ×ˢ Set.univ) :=
    h2.comp continuousOn_fst fun p hp => hp.1
  have hI : ContinuousOn (fun p : (Fin n → ℂ) × (Fin n → ℂ) => Complex.I • p.2) (W ×ˢ Set.univ) :=
    continuousOn_snd.const_smul Complex.I
  unfold levi
  exact (((hH.clm_apply continuousOn_snd).clm_apply continuousOn_snd).add
    ((hH.clm_apply hI).clm_apply hI)).div_const 4

theorem APrimeChartLevi.proof (hL : APrimeChartLeviLocal.Statement) (hV : ChartVelLift.Statement) :
    APrimeChartLevi.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X k
  set e := X.S.R.chart k with he
  have hloc : ∀ y : Fin D.n → ℂ, ∃ W : Set (Fin D.n → ℂ), ∃ f : (Fin D.n → ℂ) → ℝ,
      y ∈ e.target → IsOpen W ∧ y ∈ W ∧ ContDiffOn ℝ ∞ f W ∧
        ∀ z ∈ mcPts (mCoordIdeal D.y), X.M.proj z ∈ e.source → e (X.M.proj z) ∈ W → ∀ w v,
          IsChartVel X.M e z w v →
            levi (fun y => Real.log (D.A'.h y)) z w = levi f (e (X.M.proj z)) v := by
    intro y
    by_cases hy : y ∈ e.target
    · obtain ⟨W, hW, hyW, f, hf, hrep⟩ := hL II Ψ K ι Ω E D O Lt X k y hy
      exact ⟨W, f, fun _ => ⟨hW, hyW, hf, hrep⟩⟩
    · exact ⟨∅, 0, fun h => absurd h hy⟩
  choose W f hWf using hloc
  have hagree : ∀ y₁ ∈ e.target, ∀ y ∈ e.target, y ∈ W y₁ → ∀ v, levi (f y₁) y v = levi (f y) y v := by
    intro y₁ hy₁ y hy hyW v
    rcases eq_or_ne v 0 with rfl | hv
    · simp [levi]
    obtain ⟨z, hz, hpz, w, hw, -, -⟩ := hV II Ψ K ι Ω E D O Lt X k y hy v hv
    have hs : X.M.proj z ∈ e.source := by rw [hpz]; exact e.map_target hy
    have hez : e (X.M.proj z) = y := by rw [hpz]; exact e.right_inv hy
    have h1 := (hWf y₁ hy₁).2.2.2 z hz hs (by rw [hez]; exact hyW) w v hw
    have h2 := (hWf y hy).2.2.2 z hz hs (by rw [hez]; exact (hWf y hy).2.1) w v hw
    rw [hez] at h1 h2
    rw [← h1, ← h2]
  refine ⟨fun y v => levi (f y) y v, ?_, ?_⟩
  · intro p hp
    obtain ⟨hW, hyW, hf, -⟩ := hWf p.1 hp.1
    have hN : W p.1 ∩ e.target ∈ 𝓝 p.1 := inter_mem (hW.mem_nhds hyW) (e.open_target.mem_nhds hp.1)
    have hc : ContinuousAt (fun q : (Fin D.n → ℂ) × (Fin D.n → ℂ) => levi (f p.1) q.1 q.2) p :=
      (continuousOn_levi_of_contDiffOn hW (hf.of_le (WithTop.coe_le_coe.2 le_top))).continuousAt
        (prod_mem_nhds (hW.mem_nhds hyW) univ_mem)
    refine (hc.congr ?_).continuousWithinAt
    filter_upwards [prod_mem_nhds hN univ_mem] with q hq
    exact hagree p.1 hp.1 q.1 hq.1.2 hq.1.1 q.2
  · intro z hz hs w v hw
    have hy : e (X.M.proj z) ∈ e.target := e.map_source hs
    exact (hWf _ hy).2.2.2 z hz hs (hWf _ hy).2.1 w v hw

end GroundTheory.Heights₂.Heights.LowerBoundFree
