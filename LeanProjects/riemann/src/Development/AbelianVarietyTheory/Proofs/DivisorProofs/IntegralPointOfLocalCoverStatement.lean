import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointOfLocalCover
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
theorem _root_.GlobalTheory.T.integral_point_of_local_cover : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}} (t : SAB H X) {R F : Type} [CommRing R] [CommRing F] (f : R →+* F), Function.Injective f → ∀ {m : ℕ} (r : Fin m → R), Ideal.span (Set.range r) = ⊤ → ∀ (g : ∀ i, Localization.Away (r i) →+* F), (∀ i, (g i).comp (algebraMap R (Localization.Away (r i))) = f) → ∀ {xO : Sp R ⟶ X} {xF : Sp F ⟶ X} (hx : spMap f ≫ xO = xF) (hxi : ∀ i, spMap (g i) ≫ spMap (algebraMap R (Localization.Away (r i))) ≫ xO = xF) (w : TanM xF t.G) (u : ∀ i, TanM (spMap (algebraMap R (Localization.Away (r i))) ≫ xO) t.G), (∀ i, bcTan (g i) (hxi i) (u i) = w) → ∃ v : TanM xO t.G, bcTan f hx v = w := by
  first | exact @GlobalTheory.LieHt.CoverGlue.exists_tan_of_cover | exact GlobalTheory.LieHt.CoverGlue.exists_tan_of_cover | (intros; apply GlobalTheory.LieHt.CoverGlue.exists_tan_of_cover <;> assumption)
