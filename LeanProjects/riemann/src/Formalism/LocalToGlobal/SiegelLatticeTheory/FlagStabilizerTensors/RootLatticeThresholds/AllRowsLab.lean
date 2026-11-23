import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsDcount
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsClosed

noncomputable section

namespace Formalism.L2.SG.Pf.AllRowsLab

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.HidaSetting Formalism.L2.SG.AllRowsOf

variable {D : D7} (X : HidaSetting D)

theorem rowsGood_holds (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) (G : Formalism.L2.SG.RowDict.GoodOp X)
    (ι : D.s.HH ≃ₗᵢ[ℂ] Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) (hT : Formalism.L2.SG.RowDict.RowDictTie X G ι)
    (hL : Formalism.L2.SG.Pf.RowsGoodRed.LabTie X ι) : RowsGood X :=
  Formalism.L2.SG.Pf.RowsGoodRed.rowsGood_of X G ι hT hL (Formalism.L2.SG.Pf.AllRowsAdd.projT_holds X G)
    (Formalism.L2.SG.Pf.AllRowsDcount.dcountEq_holds X hG)

theorem rowsLab_holds (hHC : Formalism.L2.SG.RowsDef.RowsFinDim) (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D)
    (G : Formalism.L2.SG.RowDict.GoodOp X) (ι : D.s.HH ≃ₗᵢ[ℂ] Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X)
    (hT : Formalism.L2.SG.RowDict.RowDictTie X G ι) (hL : Formalism.L2.SG.Pf.RowsGoodRed.LabTie X ι)
    (hAT : AutTie D X.B X.pl) : RowsLab X :=
  rowsLab_of X (Formalism.L2.SG.Pf.AllRowsAddFin.rowsAdd_holds X hHC hG) (rowsGood_holds X hG G ι hT hL)
    (Formalism.L2.SG.Pf.AllRowsClosed.etUniv_holds X) hAT

end Formalism.L2.SG.Pf.AllRowsLab
