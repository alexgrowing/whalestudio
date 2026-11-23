import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianMapLieModelFieldPoint
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFrameVec
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalFractionField
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecFracExt
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_map_lie_model_field_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (X : Scheme.{0}) (tX : SAB H X) (f : X ⟶ Y.X) (m : SABMap tX Y.t f) (F : Type) [Field F] [Algebra c.F F] (g : Spec (CommRingCat.of F) ⟶ X) (EC : Type) [AddCommGroup EC] [Module F EC] (MC : LieModel tX.G g EC) (y : FrPt Xo c F), Small.ptY Y y = g ≫ f → ∀ (n : ℕ) (v : Fin n → (Spec (CommRingCat.of (DualNumber F)) ⟶ Xo.univ.t.G.left)) (hv : ∀ j, Formalism.L2.Pj.IsTanAt y.x (v j)) (e : Fin n → EC), (∀ j, (MC.pt (e j)).left ≫ m.φ = FinRd.Roots.LieBasis.tanW Y y (v j) (hv j).1) → ∀ (cf : Fin n → F) (w : Spec (CommRingCat.of (DualNumber F)) ⟶ Xo.univ.t.G.left), IsCombAt y.x v cf w → ∃ hw : w ≫ Xo.univ.t.G.hom = spMap (algebraMap F (DualNumber F)) ≫ y.x, (MC.pt (∑ j, cf j • e j)).left ≫ m.φ = FinRd.Roots.LieBasis.tanW Y y w hw := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.comb_val | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.comb_val | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.comb_val <;> assumption)
