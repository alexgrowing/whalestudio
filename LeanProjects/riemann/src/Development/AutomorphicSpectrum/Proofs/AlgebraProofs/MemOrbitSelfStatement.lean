import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MemOrbitSelf
import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HasAffineChartId
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FiniteFreeHom
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_orbit_self' : ∀ {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X] (x : X.left), x ∈ orbit G X x := by
  first | exact @GlobalTheory.CompanionTheory.FreeQuotProof.mem_orbit_self | exact GlobalTheory.CompanionTheory.FreeQuotProof.mem_orbit_self | (intros; apply GlobalTheory.CompanionTheory.FreeQuotProof.mem_orbit_self <;> assumption)
