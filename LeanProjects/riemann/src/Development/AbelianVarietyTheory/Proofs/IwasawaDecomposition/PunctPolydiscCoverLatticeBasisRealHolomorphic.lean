import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExponentialOfSemiAbelianFibreLinearChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CombMatAddMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeBasisRealBasisOfHolomorphicFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PunctPolydiscUniversalCoverOpenConvexExpAnalytic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackAnalytic
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.ShFam.Hor.LogCh

theorem latBasis_logCover_real_holo : ∀ (n a g r : ℕ) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ), IsLatFam (Metric.ball 0 1) K → ContinuousOn lam (logDom n a) → (∀ s ∈ logDom n a, LinearIndependent ℤ (lam s) ∧ Submodule.span ℝ (Set.range (lam s)) = ⊤ ∧ ∀ w, w ∈ K (logExp a s) ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) → r = 2 * g ∧ (∀ s ∈ logDom n a, LinearIndependent ℝ (lam s)) ∧ ∀ (j : Fin r) (k : Fin g), DifferentiableOn ℂ (fun s => lam s j k) (logDom n a) := by
  intro n a g r K lam hK hlam hB

  have hne : (fun k : Fin n => if (k : ℕ) < a then (-1 : ℂ) else 0) ∈ logDom n a := by
    intro k
    by_cases h : (k : ℕ) < a <;> simp [h]
  obtain ⟨hOpen, -, hAn, hMaps⟩ := GlobalTheory.logDom_chart_props n a

  have hmem : ∀ s ∈ logDom n a, ∀ j, lam s j ∈ K (logExp a s) := by
    intro s hs j
    refine ((hB s hs).2.2 _).2 ⟨Pi.single j 1, ?_⟩
    simp [Pi.single_apply]
  have hreal : ∀ s ∈ logDom n a, LinearIndependent ℝ (lam s) := by
    intro s hs
    obtain ⟨hli, hsp, hK'⟩ := hB s hs
    have hspanK : Submodule.span ℝ (K (logExp a s)) = ⊤ := by
      rw [eq_top_iff, ← hsp]
      exact Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact hmem s hs j)
    exact (GlobalTheory.LatReal.isRealBasis_of_isLatFam n g r (Metric.ball 0 1) K (logExp a s) (lam s) hK
      (hMaps hs) hspanK hli hK').1
  refine ⟨?_, hreal, ?_⟩
  · set s₀ := (fun k : Fin n => if (k : ℕ) < a then (-1 : ℂ) else 0)
    have hli := hreal s₀ hne
    have hsp := (hB s₀ hne).2.1
    have h1 := linearIndependent_iff_card_eq_finrank_span.1 hli
    rw [Set.finrank, hsp, finrank_top, Fintype.card_fin] at h1
    rw [h1, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  · intro j k
    have hF := IsLatFam.pullback_analytic n n g (Metric.ball 0 1) (logDom n a) K (logExp a) hK hOpen
      (fun s _ => hAn s) hMaps
    intro s₀ hs₀
    have hnhds : logDom n a ∈ 𝓝 s₀ := hOpen.mem_nhds hs₀
    obtain ⟨ζ, hζ0, hζa, hev⟩ := hF.2.2.2 s₀ hs₀ (lam s₀ j) (hmem s₀ hs₀ j)
    have hc : ContinuousAt (fun s => (s, lam s j)) s₀ :=
      continuousAt_id.prodMk ((continuous_apply j).continuousAt.comp (hlam.continuousAt hnhds))
    have hev' : ∀ᶠ s in 𝓝 s₀, (lam s j ∈ K (logExp a s) ↔ lam s j = ζ s) := by
      have := hc.tendsto.eventually hev
      simpa [hζ0] using this
    have heq : (fun s => lam s j) =ᶠ[𝓝 s₀] ζ := by
      filter_upwards [hev', hnhds] with s h1 h2
      exact h1.1 (hmem s h2 j)
    have hd : DifferentiableAt ℂ (fun s => lam s j) s₀ :=
      hζa.differentiableAt.congr_of_eventuallyEq heq
    exact (differentiableAt_pi.1 hd k).differentiableWithinAt

end GlobalTheory.ShFam.Hor.LogCh
