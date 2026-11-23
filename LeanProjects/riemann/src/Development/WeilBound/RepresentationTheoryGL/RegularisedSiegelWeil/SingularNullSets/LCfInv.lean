import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LCfInv

variable {D : D7} {n : ℕ}

theorem fam_mul {H : G D n → ℝ≥0} {φ : G D n → ℂ} {u : G D n} (hH : ∀ g, H (g * u) = H g)
    (hφ : ∀ g, φ (g * u) = φ g) (s₁ z : ℂ) (g : G D n) : fam H φ s₁ z (g * u) = fam H φ s₁ z g := by
  simp only [fam, hH, hφ]

theorem eisS_mul {f : G D n → ℂ} {u : G D n} (hf : ∀ g, f (g * u) = f g) (g : G D n) :
    eisS f (g * u) = eisS f g := by
  unfold eisS GlobalTheory.Eis.cosetSum
  refine tsum_congr fun q => ?_
  simp only [GlobalTheory.Eis.term, ← mul_assoc, hf]

theorem E_mul {H : G D n → ℝ≥0} {φ : G D n → ℂ} {s₀ : ℂ} {U : Set ℂ} {d : Polynomial ℂ} {E : ℂ → G D n → ℂ} {σ : ℝ}
    (hc : IsCont H φ s₀ U d E σ) {u : G D n} (hH : ∀ g, H (g * u) = H g) (hφ : ∀ g, φ (g * u) = φ g) (g : G D n) :
    ∀ z ∈ U, E z (g * u) = E z g := by
  have ah : AnalyticOnNhd ℂ (E · (g * u)) U := (hc.hol (g * u)).analyticOnNhd hc.isOpen
  have ag : AnalyticOnNhd ℂ (E · g) U := (hc.hol g).analyticOnNhd hc.isOpen
  obtain ⟨τ, hτ⟩ := hc.right.1
  have hx : ((max τ σ + 1 : ℝ) : ℂ) ∈ rightOf (max τ σ) := by simp
  have hxU : ((max τ σ + 1 : ℝ) : ℂ) ∈ U := hτ (rightOf_subset (le_max_left _ _) hx)
  have ev : (E · (g * u)) =ᶠ[𝓝 ((max τ σ + 1 : ℝ) : ℂ)] (E · g) := by
    filter_upwards [(isOpen_rightOf (max τ σ)).mem_nhds hx] with w hw
    have hw' : σ < w.re := lt_of_le_of_lt (le_max_right _ _) hw
    simp only [hc.eq w hw', eisS_mul (fam_mul hH hφ s₀ w)]
  exact fun z hz => ah.eqOn_of_preconnected_of_eventuallyEq ag hc.right.isPreconnected hxU ev hz

end PositivityTheory.Rg.Rsw.L.LCfInv

namespace PositivityTheory.Rg.Rsw.L

open LCfInv in
theorem cfInv : CfInv := by
  intro D n H s₀ φ U d E σ hc ε hε u hH hφ k g
  unfold cf
  congr 1
  refine circleIntegral.integral_congr hε.1.le fun z hz => ?_
  have hzU : z ∈ U := hε.2.1 (Metric.sphere_subset_closedBall hz)
  simp only [E_mul hc hH hφ g z hzU]

end PositivityTheory.Rg.Rsw.L

end
