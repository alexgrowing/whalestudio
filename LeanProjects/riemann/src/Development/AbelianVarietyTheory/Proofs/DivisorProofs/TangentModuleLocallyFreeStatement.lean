import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentModuleLocallyFree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LnStepFalse
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.HeightParts
open GlobalTheory.GradedNorm GlobalTheory.LieHt
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LieSmooth

open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_module_locally_free : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}} (t : SAB H X) {R : Type} [CommRing R] (x : Sp R ⟶ X) (p : PrimeSpectrum R), ∃ r ∉ p.asIdeal, ∃ (d : ℕ) (D : Fin d → TanM (spMap (algebraMap R (Localization.Away r)) ≫ x) t.G), LinearIndependent (Localization.Away r) D ∧ Submodule.span (Localization.Away r) (Set.range D) = ⊤ := by
  first | exact @GlobalTheory.LieFreeAway.tan_free_away | exact GlobalTheory.LieFreeAway.tan_free_away | (intros; apply GlobalTheory.LieFreeAway.tan_free_away <;> assumption)
