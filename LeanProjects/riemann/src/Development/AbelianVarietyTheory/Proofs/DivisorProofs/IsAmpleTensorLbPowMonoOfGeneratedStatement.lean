import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorLbPowMonoOfGenerated
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAmple_tensor_lbPow_mono_of_generated : ∀ (S : Scheme.{0}) (L M : LB S) (N k : ℕ), L.IsLB → M.IsLB → GlobalTheory.IsGenerated (lbPow L N) → GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens (lbPow L (N * k)) M) → ∀ k', k ≤ k' → GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens (lbPow L (N * k')) M) := by
  first | exact @GlobalTheory.AmpleTwistLarger.isAmpleLB_tens_lbPow_of_le | exact GlobalTheory.AmpleTwistLarger.isAmpleLB_tens_lbPow_of_le | (intros; apply GlobalTheory.AmpleTwistLarger.isAmpleLB_tens_lbPow_of_le <;> assumption)
