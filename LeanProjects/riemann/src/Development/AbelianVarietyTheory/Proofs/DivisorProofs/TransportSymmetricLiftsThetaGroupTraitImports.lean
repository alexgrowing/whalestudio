import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabExt
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaMove

variable {XA XP XG XT Y Y' : Scheme.{0}} {LA : LB XA} {LP : LB XP} {LG : LB XG} {LT : LB XT}
  {α : XA ⟶ XP} {β : XG ⟶ XP} {c : XT ⟶ XG}

def tf (wA : LB.Iso LA (LP.pull α)) (ℓ : LB.Iso LG (LP.pull β)) (w : LB.Iso LT (LG.pull c)) (f : Y' ⟶ Y)
    (sA : Y ⟶ XA) (sT : Y' ⟶ XT) {Z : Scheme.{0}} (q : Z ⟶ Y') (z : Z) (JP : (Z ⟶ XP) → LP.ι)
    (JA : (Z ⟶ XA) → LA.ι) (JG : (Z ⟶ XG) → LG.ι) (Jt : (Z ⟶ XT) → LT.ι) : (Z.presheaf.stalk z)ˣ :=
  (gw wA (q ≫ f ≫ sA) z (JP (q ≫ sT ≫ c ≫ β)) (JA (q ≫ f ≫ sA)))⁻¹ *
    gw ℓ (q ≫ sT ≫ c) z (JP (q ≫ sT ≫ c ≫ β)) (JG (q ≫ sT ≫ c)) *
    gw w (q ≫ sT) z (JG (q ≫ sT ≫ c)) (Jt (q ≫ sT))

end GlobalTheory.ThetaMove
