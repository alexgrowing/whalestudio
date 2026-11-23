import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RosatiNormLEOfStarNormLE
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.DimEqZero

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

def RosatiTracePosSt : Prop := RosatiPositiveSt

namespace RosatiTracePosSt

open GlobalTheory.ThetaDetCompare GlobalTheory.ThetaCoord

variable {K : Type} [Field K] [IsAlgClosed K]

end RosatiTracePosSt

end GlobalTheory.Published
