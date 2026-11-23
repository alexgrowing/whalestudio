import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitTorsOfGenericLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasPRatio
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitTors_of_generic_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (R : Type) [CommRing R] [IsDomain R] (x : Sp R ⟶ Y.X) (y : Sp (FractionRing R) ⟶ Xo.XF c), spMap (algebraMap R (FractionRing R)) ≫ x = y ≫ Y.j → ∀ N : ℕ, N ∣ l.A → GlobalTheory.LineNorm.SplitTors Y.t x N := by
  first | exact @GlobalTheory.HTLine.splitTors_of_moduli | exact GlobalTheory.HTLine.splitTors_of_moduli | (intros; apply GlobalTheory.HTLine.splitTors_of_moduli <;> assumption)
