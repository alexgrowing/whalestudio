import Formalism.LocalToGlobal.CharacterGerms.NormOneIntegral
import Formalism.LocalToGlobal.CharacterGerms.FinTwoNeOneSub
import Formalism.LocalToGlobal.CharacterGerms.NormOneRowInvariant
import Formalism.LocalToGlobal.CharacterGerms.NormOneRowDegrees
import Formalism.LocalToGlobal.CharacterGerms.RowTieGermI
import Formalism.LocalToGlobal.CharacterGerms.RowTiePHStab
import Formalism.LocalToGlobal.CharacterGerms.CoeffSingleSubstOfLowDegree
import Formalism.LocalToGlobal.CharacterGerms.RowTiePCEq2
import Formalism.LocalToGlobal.CharacterGerms.IndependenceBoundRaw
import Formalism.LocalToGlobal.CharacterGerms.RowTieAxes
import Formalism.LocalToGlobal.CharacterGerms.RankMaximalOfNondegenerate
import Formalism.LocalToGlobal.CharacterGerms.RowTieCH
import Formalism.LocalToGlobal.CharacterGerms.RowTieChar
import Formalism.LocalToGlobal.CharacterGerms.RowTieLab
import Formalism.LocalToGlobal.CharacterGerms.RowTieDesc
import Formalism.LocalToGlobal.CharacterGerms.RowTiePNabMapSt
import Formalism.LocalToGlobal.CharacterGerms.RowTiePNvalEqSt
import Formalism.LocalToGlobal.CharacterGerms.RowTiePDescSpanFinal
import Formalism.LocalToGlobal.CharacterGerms.RowTieValK
import Formalism.LocalToGlobal.CharacterGerms.RowTiePPTDone
import Formalism.LocalToGlobal.CharacterGerms.EndomorphismLimitIntegral
import Formalism.LocalToGlobal.CharacterGerms.RowTieP_TCoord
import Formalism.LocalToGlobal.CharacterGerms.CharacterHypothesisUnramified
import Formalism.LocalToGlobal.CharacterGerms.ConstantZeroMultiplicationEval
import Formalism.LocalToGlobal.CharacterGerms.CoeffSliceMultiplication
import Formalism.LocalToGlobal.CharacterGerms.RankMaximalSelfUnconditional

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField Formalism.L2.FormalSeriesBounds.RF
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

def TCoordFBSt : Prop := AllFB fun _ _ V _ _ _ _ X => ∀ Hc : ∀ g, X.CartHyp V g, RawChart.TCoordSt Hc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

structure GeoIn : Prop where

  lab : LabGeoCoreSt Xo c

  ndg : NondegenerateCharts Xo c

  ch : UpFBr.CharacterHypothesisUnramified Xo c

theorem descent_holds : DescentSt Xo c := descent_of (nabMapSt_holds Xo c) descent_span nvalEqSt_holds

variable {Xo c}
variable {C : Type} [Field C] [CharZero C] {V : VF C}
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} [Fintype Orb] {d : ℕ} [NeZero d]

end Formalism.L2.FormalSeriesBounds
