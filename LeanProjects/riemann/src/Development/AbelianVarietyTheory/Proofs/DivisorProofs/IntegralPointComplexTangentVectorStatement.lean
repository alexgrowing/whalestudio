import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointComplexTangentVector
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DrAtNonneg
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenframeGenericAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianMapModelOfIntegralFramedPoint
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
open AlgebraicGeometry CategoryTheory
open GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_point_complex_tangent_vector : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (xV : Sp T.V ⟶ Z.X), letI := io.toAlgebra; spMap (algebraMap T.V T.Fr) ≫ xV = AllWt.ptF y.1 ≫ Z.jQ ≫ genι Z → ∀ τ : E →+* ℂ, ∃ v : Fin (Dw.mult τ) → (Sp (DualNumber T.V) ⟶ Z.t.G.left), (∀ i, IsTanAtG Z.t xV (v i)) ∧ (∀ i, ∃ w : Sp (DualNumber T.Fr) ⟶ Z.oF.t.G.left, w ≫ Z.oF.t.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ AllWt.ptF y.1 ∧ w ≫ Z.m0.toSABMap.φ = y.1.u τ i ∧ w ≫ Z.m.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ v i) ∧ ∀ (cf : Fin (Dw.mult τ) → T.Fr) (u : Sp (DualNumber T.V) ⟶ Z.t.G.left), IsTanAtG Z.t xV u → IsCombAtG Z.t (spMap (algebraMap T.V T.Fr) ≫ xV) (fun i => spMap (dualMap (algebraMap T.V T.Fr)) ≫ v i) cf (spMap (dualMap (algebraMap T.V T.Fr)) ≫ u) → ∀ i, ∃ a : T.V, algebraMap T.V T.Fr a = cf i := by
  first | exact @GlobalTheory.IntFrameSat.intFrame_model_sat | exact GlobalTheory.IntFrameSat.intFrame_model_sat | (intros; apply GlobalTheory.IntFrameSat.intFrame_model_sat <;> assumption)
