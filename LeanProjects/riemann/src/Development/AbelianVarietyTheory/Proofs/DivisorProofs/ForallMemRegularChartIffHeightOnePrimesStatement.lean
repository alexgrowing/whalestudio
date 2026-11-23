import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForallMemRegularChartIffHeightOnePrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.forall_mem_regularChart_iff_heightOne_primes : ∀ (σ : Setup) (u : σ.A.left.functionField), (∀ x : Sp σ.R, u ∈ σ.W x) ↔ ∀ p : Sp σ.R, p.asIdeal.height = 1 → σ.f ∈ p.asIdeal → u ∈ σ.W p := by
  first | exact @GlobalTheory.Desc.Setup.forall_mem_W_iff | exact GlobalTheory.Desc.Setup.forall_mem_W_iff | (intros; apply GlobalTheory.Desc.Setup.forall_mem_W_iff <;> assumption)
