import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FramePointAbelianMapCompat
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
theorem _root_.GlobalTheory.T.frame_point_abelian_map_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (X : Scheme.{0}) (tX : SAB H X) (f : X ⟶ Y.X) (m : SABMap tX Y.t f) (F : Type) [Field F] [Algebra c.F F] (y : FrPt Xo c F) (t' : SAB H (Spec (CommRingCat.of F))) (m1 : SABMap t' Xo.univ.t y.x) (g : Spec (CommRingCat.of F) ⟶ X), Small.ptY Y y = g ≫ f → ∃ b : t'.G.left ⟶ tX.G.left, IsGrpPullback t'.G tX.G g b ∧ (∀ a, (t'.act.act a).left ≫ b = b ≫ (tX.act.act a).left) ∧ ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) (u' : Spec (CommRingCat.of (DualNumber F)) ⟶ t'.G.left), u' ≫ m1.φ = y.u τ i → u' ≫ t'.G.hom = Spec.map (CommRingCat.ofHom (algebraMap F (DualNumber F))) → u' ≫ b ≫ m.φ = Small.tanY Y y τ i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.genFibre_pullback_cover | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.genFibre_pullback_cover | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.genFibre_pullback_cover <;> assumption)
