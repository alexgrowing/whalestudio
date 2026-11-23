import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormNotMemIff
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_not_mem_iff_forall_over_not_mem : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Free A B] (f : B) (P : PrimeSpectrum A), Algebra.norm A f ∉ P.asIdeal ↔ ∀ Q : PrimeSpectrum B, Q.asIdeal.comap (algebraMap A B) = P.asIdeal → f ∉ Q.asIdeal := by
  first | exact @GlobalTheory.Mum.norm_not_mem_iff | exact GlobalTheory.Mum.norm_not_mem_iff | (intros; apply GlobalTheory.Mum.norm_not_mem_iff <;> assumption)
