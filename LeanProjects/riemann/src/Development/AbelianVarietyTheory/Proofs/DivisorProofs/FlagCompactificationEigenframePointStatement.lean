import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCompactificationEigenframePoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LnStepFalse
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.HeightParts
open GlobalTheory.GradedNorm GlobalTheory.LieHt
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LieSmooth

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_compactification_eigenframe_point : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e) {k : Type} [Field k] [NumberField k] {φ : c.F →+* k} {x : Sp k ⟶ Z.X} (p : Sp k ⟶ Y.Y.X) (g : EigFrame Z φ x) (n : Letter Dw → ℤ), Y.Carries p g → ∃ a : k, a ≠ 0 ∧ IsCoord Y p g n (((eqn (divOf Y n) (below p))⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn) a := by
  first | exact @GlobalTheory.LieSmooth.coord_eqn_inv_ne_zero | exact GlobalTheory.LieSmooth.coord_eqn_inv_ne_zero | (intros; apply GlobalTheory.LieSmooth.coord_eqn_inv_ne_zero <;> assumption)
