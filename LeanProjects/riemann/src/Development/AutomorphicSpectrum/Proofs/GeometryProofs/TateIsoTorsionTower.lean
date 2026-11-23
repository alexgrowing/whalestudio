import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HTChartExists
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Development.WeilBound.CoreStatements.HodgeTatePoints.Twexists
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem tower_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (S : Scheme.{0}) [IsLocallyNoetherian S] (t : SAB H S) (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [CharZero O] [IsAlgClosed (FractionRing O)] (y : Sp O ⟶ S) (I : TateIso D (FractionRing O) (Over.mk ((BT.genPt O).hom ≫ y) ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c))), ∃ X : TorsTower p t.G y D.La, (∀ n (a : D.La), ((X.Γ n).pt (lev p n a)).left ≫ X.i n = (I.ev (p ^ n) a).left) ∧ ∀ a : 𝓞 E, X.Induces (t.act.act a) (DistribMulAction.toAddMonoidHom D.La a) :=
  PositivityTheory.HtPt.Twexists.tower_exists

end GlobalTheory.CompanionTheory.Ar.HT
