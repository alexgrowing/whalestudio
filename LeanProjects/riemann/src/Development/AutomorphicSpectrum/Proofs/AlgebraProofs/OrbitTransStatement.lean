import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.OrbitTrans
import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HasAffineChartId
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FiniteFreeHom
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_orbit_trans : ∀ {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X] (x y w : X.left), y ∈ orbit G X x → w ∈ orbit G X y → w ∈ orbit G X x := by
  first | exact @GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.orbit_trans | exact GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.orbit_trans | (intros; apply GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.orbit_trans <;> assumption)
