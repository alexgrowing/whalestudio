import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationRescaleTauBimultExists
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degeneration_rescale_tau_bimult_exists : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), ∃ g : D.X → (FractionRing R)ˣ, (GlobalTheory.PolDeg.rescale D g).TauBimult := by
  first | exact @GlobalTheory.RescaleBimult.exists_rescale_tauBimult | exact GlobalTheory.RescaleBimult.exists_rescale_tauBimult | (intros; apply GlobalTheory.RescaleBimult.exists_rescale_tauBimult <;> assumption)
