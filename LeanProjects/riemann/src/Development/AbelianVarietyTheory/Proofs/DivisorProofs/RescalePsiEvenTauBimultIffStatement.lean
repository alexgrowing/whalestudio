import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RescalePsiEvenTauBimultIff
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
theorem _root_.GlobalTheory.T.rescale_psi_even_tau_bimult_iff : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (g : D.X → (FractionRing R)ˣ), (D.PsiEven → ((GlobalTheory.PolDeg.rescale D g).PsiEven ↔ ∀ a : D.X, g (-a) = g a)) ∧ (D.TauBimult → ((GlobalTheory.PolDeg.rescale D g).TauBimult ↔ (∀ a a' b : D.X, g (a + a' + b) * g a * g a' * g b = g (a + a') * g (a + b) * g (a' + b)))) := by
  first | exact @GlobalTheory.PolDeg.QuadIff.rescale_even_bimult_iff | exact GlobalTheory.PolDeg.QuadIff.rescale_even_bimult_iff | (intros; apply GlobalTheory.PolDeg.QuadIff.rescale_even_bimult_iff <;> assumption)
