import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsLocSec
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJMap
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedChartTransitionAnalytic
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

theorem isSection_diagSec : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (ψ : RW.X → OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : RW.X → Fin Rb.A.n) (σ : RW.X → Fin n ↪ Fin e) (i₀ : RW.X → Fin e) (V : RW.X → Set RW.X) (u : RW.X → RW.X → ℂ) (hL : ∀ x, IsLocSec M Rb τ a k₀ ca cb RW pr x (ψ x) (kb x) (σ x) (i₀ x) (V x) (u x)), M.blk (τ, a) = some k₀ → IsWAtlas M Rb τ a k₀ ca cb RW pr → ∀ c : ℝ, IsSection RW.A (secPot RW (potA M τ a k₀) V (fun x => (hL x).2.1) (fun x => (hL x).2.2.1) c) (diagSec ψ i₀ u) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a k₀ ca cb RW pr ψ kb σ i₀ V u hL hblk hW c
  refine ⟨fun x => ?_, fun x x' w hw => ?_⟩
  · obtain ⟨⟨F, H, hC⟩, -, -, hsrc, -, hu, -⟩ := hL x
    intro l z hz
    have hz' : z ∈ (RW.A.chart l).target ∩ (RW.A.chart l).symm ⁻¹' (ψ x).source :=
      ⟨hz.1, hsrc hz.2⟩
    have h1 : AnalyticAt ℂ (u x ∘ (RW.A.chart l).symm) z := hu l z hz
    have h2 : AnalyticAt ℂ ((ψ x) ∘ (RW.A.chart l).symm) z := (hC.1 l).1 z hz'
    have h3 : AnalyticAt ℂ (fun w => ((ψ x) ∘ (RW.A.chart l).symm) w (i₀ x)) z :=
      analyticAt_pi_iff.1 h2 (i₀ x)
    exact h1.mul h3
  · have hx : 0 < (potA M τ a k₀).h (RW.lift x w) :=
      (potA M τ a k₀).pos _ (RW.mem x w ((hL x).2.2.2.2.1 hw.1)).1
    have hx' : 0 < (potA M τ a k₀).h (RW.lift x' w) :=
      (potA M τ a k₀).pos _ (RW.mem x' w ((hL x').2.2.2.2.1 hw.2)).1
    have hg := locSec_norm_eq K ι Φ y Ψ N j M n e Rb τ a k₀ ca cb RW pr x x' (ψ x) (ψ x') (kb x) (kb x') (σ x) (σ x')
      (i₀ x) (i₀ x') (V x) (V x') (u x) (u x') hblk hW (hL x) (hL x') w hw
    have key : ∀ (s h : ℝ), 0 < h → s * Real.exp (-(Real.log h + c)) = s / h * Real.exp (-c) := by
      intro s h hh
      rw [neg_add, Real.exp_add, Real.exp_neg (Real.log h), Real.exp_log hh, div_eq_mul_inv, mul_assoc]
    show ‖u x w * ψ x w (i₀ x)‖ * Real.exp (-(Real.log ((potA M τ a k₀).h (RW.lift x w)) + c)) =
      ‖u x' w * ψ x' w (i₀ x')‖ * Real.exp (-(Real.log ((potA M τ a k₀).h (RW.lift x' w)) + c))
    rw [key _ _ hx, key _ _ hx', hg]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec
