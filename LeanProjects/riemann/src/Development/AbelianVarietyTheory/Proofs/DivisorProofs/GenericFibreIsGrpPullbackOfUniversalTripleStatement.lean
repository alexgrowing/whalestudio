import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreIsGrpPullbackOfUniversalTriple
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericFibre_isGrpPullback_of_universalTriple : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] (y : Sp (FractionRing R) ⟶ Xo.XF c) (t : SAB H (Sp R)) (tF : SAB H (Xo.XF c)), GlobalTheory.UPoinc.GenOf Xo c y t → SABMap tF Xo.univ.t (pullback.fst _ _) → ∃ α : pullback t.G.hom (jK R) ⟶ tF.G.left, IsGrpPullback ((Over.pullback (jK R)).obj t.G) tF.G y α := by
  first | exact @GlobalTheory.UPoinc.genOf_isGrpPullback | exact GlobalTheory.UPoinc.genOf_isGrpPullback | (intros; apply GlobalTheory.UPoinc.genOf_isGrpPullback <;> assumption)
