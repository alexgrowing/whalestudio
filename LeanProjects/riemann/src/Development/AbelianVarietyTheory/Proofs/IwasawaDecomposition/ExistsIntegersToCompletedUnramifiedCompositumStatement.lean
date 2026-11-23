import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegersToCompletedUnramifiedCompositum
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integers_to_completedUnramifiedCompositum : ∀ (l : ℕ) [Fact l.Prime] (K₀ L : Loc.FinExt l), ∃ f : ↥(Loc.OL K₀) →+* ↥(clC l (Kt l K₀ L)), ∀ y, (f y : ℂ_[l]) = algebraMap (PadicAlgCl l) ℂ_[l] ((y : ↥K₀.1) : PadicAlgCl l) := by
  first | exact @GlobalTheory.HeightCounting.ToClC.exists_toClC | exact GlobalTheory.HeightCounting.ToClC.exists_toClC | (intros; apply GlobalTheory.HeightCounting.ToClC.exists_toClC <;> assumption)
