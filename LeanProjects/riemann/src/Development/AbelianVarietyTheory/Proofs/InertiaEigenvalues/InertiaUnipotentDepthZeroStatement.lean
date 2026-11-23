import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaUnipotentDepthZero
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_unipotent_depth_zero : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.DepthZeroWild → GlobalTheory.Published.DepthZeroSupport → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (w : PlE D.host) (n : ℕ) (π : Irr (w.adicCompletion D.host.E) n), (∃ v ∈ GlobalTheory.PRep.fixed π.π (GlobalTheory.SplitWeil.KOne (w.adicCompletion D.host.E) (Fin n)), v ≠ 0) → ∀ σ ∈ wildSet D.nd (D.nd.plOm.1 w), (rcAt hL D w n π).inePol σ = (X - 1) ^ n := by
  first | exact @GlobalTheory.DepthZeroLoc.main | exact GlobalTheory.DepthZeroLoc.main | (intros; apply GlobalTheory.DepthZeroLoc.main <;> assumption)
