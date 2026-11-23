import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
import Formalism.LocalToGlobal.IndefiniteReal.NonzeroIndexPlaceIndepConstants
import Formalism.LocalToGlobal.Divisibility.TupUsed
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.RecPinsTie

theorem main : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Yd cX) (x : TwIn ex) (Rc : Formalism.L2.RecT ex) (S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc) (y : RealIn x Rc S), ∀ r : RecIn y, (∀ hp : RealPins (realTOf y), Formalism.IndefR.principalLevelFrame.RowLocPin Rc.T.n.gal.lp x.R.θ x.Y.PY (x.R.MY 0) (fun b => levS _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 b))) (fun b => Formalism.IndefR.Lev.levChi _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 b))) (fun _ => x.R.e0) x.Y.eFT → RealRecPins hp (realRecOf r)) ∧ (Formalism.IndefR.RecTie.PartsRec x.R.toRealDat x.F.lv2 x.Y.tupT x.Y.hm x.Y.PY x.Y.PW x.Y.eFT r.E r.labPi r.piOf x.Y.Ish.prt x.Y.IL.prtW → (realRecOf r).PartsRow) ∧ PsiPPTie D (divisionPairOfAdelicFormsFaceColumnsData x).P0 (divisionPairOfAdelicFormsFaceColumnsData x).ψ0 (divisionPairOfAdelicFormsFaceColumnsData x).Ps (divisionPairOfAdelicFormsFaceColumnsData x).ψs (divisionPairOfAdelicFormsFaceColumnsData x).I.eG := by
  intro D L hT Gi Gl K Yd cX ex x Rc S y r
  refine ⟨fun hp h => ⟨?_, ?_⟩, fun h => ?_, ?_⟩
  · exact x.Y.stdPsi
  · exact h
  · exact h
  · exact x.pins.keep.psi

end GlobalTheory.Mem.R3.RecPinsTie
