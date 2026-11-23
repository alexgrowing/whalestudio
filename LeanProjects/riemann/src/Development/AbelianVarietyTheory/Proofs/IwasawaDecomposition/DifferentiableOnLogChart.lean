import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentialKernelsIsHolomorphicLatticeFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackAnalytic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PunctPolydiscUniversalCoverOpenConvexExpAnalytic
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Topology ComplexOrder
open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.ShFam.Hor.LogCh

theorem differentiableOn_lam_of_isLogChart : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (σ : κ.c.F →+* ℂ) (n g r k : ℕ) (ch : OpenPartialHomeomorph (CxPts (genStr s.T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps s.T.Z σ g) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (ρ : Fin g → Fin r → ℂ), IsLogChart k ch ex lam ρ → DifferentiableOn ℂ lam (logDom n k) := by
  intro D A N j S κ s σ n g r k ch ex lam ρ h
  obtain ⟨hE, -, hlc, hlat, -⟩ := h
  obtain ⟨htar, -, -, hadd, hhol, htan⟩ := hE
  obtain ⟨hDo, -, hEa, hEm⟩ := GlobalTheory.logDom_chart_props n k
  have hKB : IsLatFam ch.target (fun b => {w | ex (ch.symm b) w = 1}) := by
    refine isLatFam_ker _ _ _ s.T.Z.t n g ch.target (fun b => (ch.symm b).1 ≫ genι s.T.Z)
      (fun b => ex (ch.symm b)) ch.open_target hhol fun b hb => ?_
    have hx := ch.map_target hb
    exact ⟨hadd _ hx, (htan _ hx).1, (htan _ hx).2⟩
  have hK := IsLatFam.pullback_analytic n n g ch.target (logDom n k) _ (logExp k) hKB hDo
    (fun s _ => hEa s) (by rw [htar]; exact hEm)
  intro s₀ hs₀
  have hgr : ∀ i : Fin r, ∃ ζ : (Fin n → ℂ) → Fin g → ℂ, AnalyticAt ℂ ζ s₀ ∧ (fun s => lam s i) =ᶠ[𝓝 s₀] ζ := by
    intro i
    have hw₀ : lam s₀ i ∈ {w | ex (ch.symm (logExp k s₀)) w = 1} :=
      ((hlat s₀ hs₀).2.1 (lam s₀ i)).2 ⟨Pi.single i 1, by simp [Pi.single_apply]⟩
    obtain ⟨ζ, hζ0, hζa, hζ⟩ := hK.2.2.2 s₀ hs₀ (lam s₀ i) hw₀
    refine ⟨ζ, hζa, ?_⟩
    have hci : ContinuousAt (fun s => lam s i) s₀ :=
      (continuous_apply i).continuousAt.comp (hlc.continuousAt (hDo.mem_nhds hs₀))
    have ht : Filter.Tendsto (fun s => (s, lam s i)) (𝓝 s₀) (𝓝 (s₀, lam s₀ i)) :=
      (continuousAt_id.prodMk hci).tendsto
    filter_upwards [ht.eventually hζ, hDo.mem_nhds hs₀] with s h1 h2
    refine h1.1 ?_
    exact ((hlat s h2).2.1 (lam s i)).2 ⟨Pi.single i 1, by simp [Pi.single_apply]⟩
  choose ζ hζa hζe using hgr
  have hA : AnalyticAt ℂ (fun s i => ζ i s) s₀ := AnalyticAt.pi hζa
  have hEq : lam =ᶠ[𝓝 s₀] fun s i => ζ i s := by
    filter_upwards [Filter.eventually_all.2 hζe] with s hs
    exact funext hs
  exact (hA.differentiableAt.congr_of_eventuallyEq hEq).differentiableWithinAt

end GlobalTheory.ShFam.Hor.LogCh
