import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermAttractorConstant.GenericityConstantDoubleCosets

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem term_function_const (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : Formalism.L2.SG.TermDef.TermFun D u u' :=
  PI.TermAttrConst.UnitaryGroupMassFormula.termFun_of PI.TermAttrConst.UnitaryGroupMassFormula.genericity_constant_double_cosets D u u'

theorem termAttrConst_gFun (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word)
    (F0 : Formalism.MainNotions.S.FlagG (Formalism.MainNotions.S.VS D) D.R.rS ((Formalism.MainNotions.S.Lat.Tu D u : ℕ) : D.host.E))
    (Λ : Submodule (NumberField.RingOfIntegers D.host.E) (Formalism.MainNotions.S.VS D).V) (hΛ : Formalism.MainNotions.S.IsRowLat D F0 Λ) :
    Formalism.L2.SG.TermDef.GFun Λ (Formalism.MainNotions.S.lf D F0) (Formalism.L2.SG.TermDef.PD D Λ (Formalism.MainNotions.S.lf D F0) u') :=
  PI.TermAttrConst.UnitaryGroupMassFormula.termGFun_holds D u u' F0 Λ hΛ
