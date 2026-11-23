import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
import Formalism.LocalToGlobal.IndefiniteReal.NonzeroIndexPlaceIndepConstants
import Formalism.LocalToGlobal.Divisibility.TupUsed
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3

set_option maxHeartbeats 4000000 in

theorem rowConditions_at_companion_from_readings : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Yd cX) (x : TwIn ex) , (Lam3 x.Z → RowsHoldLam3 (divisionPairOfAdelicFormsFaceColumnsData x)) ∧ RowsHoldDcPt3 (divisionPairOfAdelicFormsFaceColumnsData x) ∧ DcPtG (divisionPairOfAdelicFormsFaceColumnsData x) ∧ (DivRows3 D x.A3 x.F.P0 x.F.ψ0 x.F.P1 x.F.ψ1 (zsOf x.R x.F) (s0Of x.R x.F) (s1Of x.R x.F) ex.p0 (colOf x.R x.F x.sEE) x.C.NuC (idsOf x.cG x.Z x.C) → DivRows3G (divisionPairOfAdelicFormsFaceColumnsData x)) := by
  intro D L hT Gi Gl K Yd cX ex x
  have hD : RowsHoldDcPt3 (divisionPairOfAdelicFormsFaceColumnsData x) := fun u t y F => x.C.pt u t y F
  exact ⟨fun h => h, hD, dcPtG_of hD, fun h => DivRows3.toG (P := divisionPairOfAdelicFormsFaceColumnsData x) h⟩

end GlobalTheory.Mem.R3
