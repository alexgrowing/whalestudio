import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsLocSec
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJMap
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedChartTransitionAnalyticStatement
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFsInvPow
import ReciprocityTheory.AnalyticForms.LeviForms.TailCutA
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

theorem isOpen_blocksNonzero {κ : Type} [Fintype κ] (ρ : κ → Type) :
    IsOpen {z : (Σ k, ρ k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  simp only [Set.setOf_forall, Set.setOf_exists]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem logNormSec_secPot_le : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (ψ : RW.X → OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : RW.X → Fin Rb.A.n) (σ : RW.X → Fin n ↪ Fin e) (i₀ : RW.X → Fin e) (V : RW.X → Set RW.X) (u : RW.X → RW.X → ℂ) (hL : ∀ x, IsLocSec M Rb τ a k₀ ca cb RW pr x (ψ x) (kb x) (σ x) (i₀ x) (V x) (u x)), M.blk (τ, a) = some k₀ → IsWAtlas M Rb τ a k₀ ca cb RW pr → ∃ c : ℝ, ∀ w, logNormSec (secPot RW (potA M τ a k₀) V (fun x => (hL x).2.1) (fun x => (hL x).2.2.1) c) (diagSec ψ i₀ u) w ≤ 0 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a k₀ ca cb RW pr ψ kb σ i₀ V u hL hb hW
  have hAs : ContinuousOn (potA M τ a k₀).h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    ContDiffOn.continuousOn (GroundTheory.Heights₂.Heights.LowerBoundFree.FsInvPow.isSmoothHerm_fsHerm (ι := fun o : Option _ => ι (o.getD k₀)) (aDeg M τ a k₀))
  have hg : Continuous fun w => ‖diagSec ψ i₀ u w w‖ / (potA M τ a k₀).h (RW.lift w w) := by
    rw [continuous_iff_continuousAt]
    intro x
    obtain ⟨-, hVo, hxV, hVs, -, hu, -⟩ := hL x
    have hlift : ContinuousAt (RW.lift x) x := continuousAt_pi.2 fun p =>
      ReciprocityTheory.AnForm.P.LeviFormBoundaryTopology.continuousAt_of_holoOn RW.A (RW.holo x p) (RW.mem_U x)
    have hmem := (RW.mem x x (RW.mem_U x)).1
    have hh : ContinuousAt (fun w => (potA M τ a k₀).h (RW.lift x w)) x :=
      ContinuousAt.comp (g := (potA M τ a k₀).h)
        (hAs.continuousAt ((isOpen_blocksNonzero _).mem_nhds hmem)) hlift
    have hψ : ContinuousAt (fun w => ψ x w (i₀ x)) x :=
      (continuous_apply (i₀ x)).continuousAt.comp ((ψ x).continuousAt (hVs hxV))
    have hloc : ContinuousAt (fun w => ‖u x w * ψ x w (i₀ x)‖ / (potA M τ a k₀).h (RW.lift x w)) x :=
      (((ReciprocityTheory.AnForm.P.LeviFormBoundaryTopology.continuousAt_of_holoOn RW.A hu hxV).mul hψ).norm).div hh
        ((potA M τ a k₀).pos _ hmem).ne'
    refine hloc.congr ?_
    filter_upwards [hVo.mem_nhds hxV] with w hw
    exact GlobalTheory.T.twisted_chart_transition_analytic K ι Φ y Ψ N j M n e Rb τ a k₀ ca cb RW pr x w (ψ x) (ψ w) (kb x) (kb w) (σ x) (σ w)
      (i₀ x) (i₀ w) (V x) (V w) (u x) (u w) hb hW (hL x) (hL w) w ⟨hw, (hL w).2.2.1⟩
  obtain ⟨Cb, hCb⟩ := (isCompact_range hg).bddAbove
  refine ⟨Real.log (max Cb 1), fun w => ?_⟩
  have hgw : ‖diagSec ψ i₀ u w w‖ / (potA M τ a k₀).h (RW.lift w w) ≤ max Cb 1 :=
    (hCb ⟨w, rfl⟩).trans (le_max_left _ _)
  have hpos : 0 < (potA M τ a k₀).h (RW.lift w w) := (potA M τ a k₀).pos _ (RW.mem w w (RW.mem_U w)).1
  have hm : (0 : ℝ) < max Cb 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hexp : Real.exp (-(Real.log ((potA M τ a k₀).h (RW.lift w w)) + Real.log (max Cb 1))) =
      ((potA M τ a k₀).h (RW.lift w w))⁻¹ * (max Cb 1)⁻¹ := by
    rw [neg_add, Real.exp_add, Real.exp_neg, Real.exp_neg, Real.exp_log hpos, Real.exp_log hm]
  show Real.log (‖diagSec ψ i₀ u w w‖ *
    Real.exp (-(Real.log ((potA M τ a k₀).h (RW.lift w w)) + Real.log (max Cb 1)))) ≤ 0
  rw [hexp]
  refine Real.log_nonpos (by positivity) ?_
  have : ‖diagSec ψ i₀ u w w‖ * (((potA M τ a k₀).h (RW.lift w w))⁻¹ * (max Cb 1)⁻¹) =
      (‖diagSec ψ i₀ u w w‖ / (potA M τ a k₀).h (RW.lift w w)) / max Cb 1 := by
    rw [div_div, div_eq_mul_inv, mul_inv]
  rw [this]
  exact (div_le_one hm).2 hgw

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec
