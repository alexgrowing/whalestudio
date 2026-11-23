import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSiegelChartOfPolarisedMonomialPeriodChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorLbPowMonoOfGeneratedStatement
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg

theorem siegelToroidalIntegral_of_polCharts
    (hfan : ∀ g : ℕ, ∃ φ : InvFun ℤ, IsPolFan (id : ℤ → ℤ) g φ ∧ NoSelfInt (id : ℤ → ℤ) g φ)
    (h : GlobalTheory.Published.SiegelToroidalPolCharts) : GlobalTheory.Published.SiegelToroidalIntegral := by
  intro g hg
  obtain ⟨φ, hφ, hns⟩ := hfan g
  refine ⟨φ, hφ, fun n hn hodd => ?_⟩
  obtain ⟨F, S, s, j, hj, G, hG, e, BD, d, N, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, k, hk⟩ :=
    h g hg φ hφ hns n hn hodd
  have hn0 : n ≠ 0 := by omega
  refine ⟨F, S, s, j, hj, G, hG, e, BD, d, N, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    fun x => GlobalTheory.T.hasSiegelChart_of_polarisedMonomialPeriodChart F s j e φ BD d x hn0 (h10 x), h11, h12, k, fun k' hk' => ?_⟩
  exact GlobalTheory.T.isAmple_tensor_lbPow_mono_of_generated S (hodge G g) (CechPic.dual BD.lb) N k (isLB_hodge G g)
    (CechPic.isLB_dual BD.isLB_lb) h12 hk k' hk'

example : (∀ g : ℕ, ∃ φ : InvFun ℤ, IsPolFan (id : ℤ → ℤ) g φ ∧ NoSelfInt (id : ℤ → ℤ) g φ) →
    GlobalTheory.Published.SiegelToroidalPolCharts → GlobalTheory.Published.SiegelToroidalIntegral := siegelToroidalIntegral_of_polCharts

end GlobalTheory.PolDeg
