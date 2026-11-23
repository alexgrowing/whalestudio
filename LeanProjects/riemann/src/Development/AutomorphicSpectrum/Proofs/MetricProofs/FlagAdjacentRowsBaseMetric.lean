import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsLocSec
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedMeasureStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedChartHolomorphicStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedChartHolomorphicAltBis
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedChartCoordinatesRegularStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedChartContinuousProjectionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedChartLocalCoordinatesStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedChartLocalCoordinatesAltBis
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (pr : RW.X → BM.Rb.X) (hc : Continuous pr), IsWAtlas M BM.Rb τ a k₀ ca cb RW pr → ∃ (L' : LocPot RW.X) (v : RW.X → RW.X → ℂ) (Dg : Set RW.X) (cst : ℝ), IsPotential RW.A L' ∧ IsSection RW.A L' v ∧ IsSNC RW.A L' v ![1] ![Dg] ∧ IsSNC RW.A (BM.L.pullback pr hc + L') (fun x y => BM.s (pr x) (pr y) * v x y) (Fin.snoc BM.m 1) (Fin.snoc (fun k => pr ⁻¹' BM.W k) Dg) ∧ (∀ w, logNormSec L' v w ≤ 0) ∧ IsNormFn M τ a k₀ ca cb RW fun x => logNormSec L' v x + cst := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM τ a b k₀ ca cb hb hj hblk hca hcb _ RW pr hc hW
  choose ψ kb σ i₀ V u hL using
    GlobalTheory.T.flag_adjacent_twisted_measure K ι Φ y Ψ N j M n (d + 2) BM.Rb τ a b k₀ ca cb hb hj hblk hca hcb RW pr hW
  obtain ⟨c, hc0⟩ := GlobalTheory.T.twisted_chart_local_coordinates K ι Φ y Ψ N j M n (d + 2) BM.Rb τ a k₀ ca cb RW pr ψ kb σ i₀ V u hL hblk hW
  refine ⟨GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.secPot RW (GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.potA M τ a k₀) V
      (fun x => (hL x).2.1) (fun x => (hL x).2.2.1) c,
    GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.diagSec ψ i₀ u, GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.diagSet k₀ RW, c, ?_, ?_, ?_, ?_, hc0, ?_⟩
  · exact GlobalTheory.T.secPot_isPotential K ι Φ y Ψ N j M n (d + 2) BM.Rb τ a k₀ ca cb RW pr ψ kb σ i₀ V u hL c
  · exact GlobalTheory.T.twisted_chart_holomorphic_alt K ι Φ y Ψ N j M n (d + 2) BM.Rb τ a k₀ ca cb RW pr ψ kb σ i₀ V u hL hblk hW c
  · exact GlobalTheory.T.twisted_chart_coordinates_regular K ι Φ y Ψ N j M n (d + 2) BM.Rb τ a k₀ ca cb RW pr ψ kb σ i₀ V u hL c
  · exact GlobalTheory.T.twisted_chart_continuous_projection K ι Φ y Ψ N j M n (d + 2) BM τ a k₀ ca cb RW pr hc ψ kb σ i₀ V u hL hW.1 c
  · exact GlobalTheory.T.twisted_chart_local_coordinates_alt K ι Φ y Ψ N j M n (d + 2) BM.Rb τ a k₀ ca cb RW pr ψ kb σ i₀ V u hL b hb hj hblk hca hcb hW c

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec
