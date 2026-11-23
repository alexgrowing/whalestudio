import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsPos
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BDataOf
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SwxsOfSiegelWeil
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqualWordsNonGenericEstimatesChainStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormalCountLineIntegralitySeparationStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowGen1POfConstantsAndPoints
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneOnSingletonOfRows

namespace GlobalTheory.Core.Diag

theorem oneOn_singleton_of_siegelWeil_of_stepChoice :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → Formalism.L2.SG.NGAnalytic.StepChoiceConstantsC →
      Formalism.L2.SG.Pf.BDat.StepThmBG → Formalism.L2.SG.RowsPos.RowNGP →
      ∀ c : ℝ, GlobalTheory.Core.Diag.OneOn {c} true ∧ GlobalTheory.Core.Diag.OneOn {c} false := by
  intro h hB hTB hN c
  have hT : GlobalTheory.SnPos.StepThmBGP := by
    intro Cg cb Cw cT CT C0 _ _ A
    obtain ⟨CB, h0, a, b, H⟩ := hTB Cg cb Cw cT CT C0 A
    exact ⟨CB, h0, a, b, fun C' Cl h1 h2 D large₂ X Y u _ => H C' Cl h1 h2 D large₂ X Y u⟩
  obtain ⟨_h1, _h2, h3, h4, h5, h6, _h7, _h8, _h9⟩ := GlobalTheory.T.equalWords_nonGeneric_estimates_chain
  have hG : GlobalTheory.Core.One.RowGen1P :=
    GlobalTheory.Core.One.rowGen1P_of_siegelWeil_of_points (GlobalTheory.St.swxs_of_siegelWeil h)
      GlobalTheory.T.normalCount_line_integrality_separation.1 GlobalTheory.T.normalCount_line_integrality_separation.2.1 GlobalTheory.T.normalCount_line_integrality_separation.2.2 h3 h4 h5 hB h6 hT
  exact ⟨oneOn_singleton_of_rows.1 hG c, oneOn_singleton_of_rows.2 hN c⟩

end GlobalTheory.Core.Diag
