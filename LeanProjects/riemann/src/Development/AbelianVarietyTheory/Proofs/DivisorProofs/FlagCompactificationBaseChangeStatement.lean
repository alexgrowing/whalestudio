import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCompactificationBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LnStepFalse
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.HeightParts
open GlobalTheory.GradedNorm GlobalTheory.LieHt
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LieSmooth

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_compactification_base_change : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e) {k k' : Type} [Field k] [Field k'] (θ : k →+* k') {φ : c.F →+* k} {x : Sp k ⟶ Z.X} {φ' : c.F →+* k'} {x' : Sp k' ⟶ Z.X} (p : Sp k ⟶ Y.Y.X) (g : EigFrame Z φ x) (g' : EigFrame Z φ' x') (n : Letter Dw → ℤ) (s : Y.Y.Fn) (a : k), φ' = θ.comp φ → x' = spMap θ ≫ x → g.IsMap θ g' → IsCoord Y p g n s a → IsCoord Y (spMap θ ≫ p) g' n s (θ a) := by
  first | exact @GlobalTheory.CoordBC.isCoord_map | exact GlobalTheory.CoordBC.isCoord_map | (intros; apply GlobalTheory.CoordBC.isCoord_map <;> assumption)
