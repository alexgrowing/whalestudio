import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPointTangentBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LnStepFalse
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.HeightParts
open GlobalTheory.GradedNorm GlobalTheory.LieHt
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LieSmooth

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_point_tangent_base_change : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} (y : FlagPt Z Qb) {K : Type} [Field K] (io : K →+* Qb) (fK : c.F →+* K) (yK : Sp K ⟶ gen Z) (hio : spMap io ≫ yK = y.y), yK ≫ genStr Z = spMap fK → ∀ {n : ℕ} (e : Fin n ≃ Letter Dw) (b : Fin n → TanM (yK ≫ genι Z) Z.t.G), (∀ i, spMap (dualMap io) ≫ (tv (b i)).left = y.u (e i).1 (e i).2) → TanBasis Z.t b ∧ ∃ g : EigFrame Z fK (yK ≫ genι Z), ∀ z : Letter Dw, g.vec z.1 z.2 = b (e.symm z) := by
  first | exact @GlobalTheory.LieSmooth.tanBasis_and_eigFrame_of_baseChange | exact GlobalTheory.LieSmooth.tanBasis_and_eigFrame_of_baseChange | (intros; apply GlobalTheory.LieSmooth.tanBasis_and_eigFrame_of_baseChange <;> assumption)
