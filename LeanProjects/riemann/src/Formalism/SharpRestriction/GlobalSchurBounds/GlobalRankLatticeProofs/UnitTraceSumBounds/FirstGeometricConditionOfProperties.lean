import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.AdditionIdentityOfSigmaFormulaUnit
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.FirstKernelRemainderOfLevelRestrictionOfLinPtW
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.RetcutA
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremOfCubeOfAdditionFormulas
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.FormalGroupLawFirstHalfHolds
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.StmtEndIntWHolds
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.StmtPhDualWHolds
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.ReadWHolds

namespace Formalism.MainNotions.Ext

open Formalism.BasicNotions Formalism.MainNotions.GL3Theta Formalism.MainNotions.GL3r7 Formalism.MainNotions.Ext.CutA

theorem firstGeometricCondition_of_properties (D : D7) (hc : cube D) (he : endInt D) (hOK : PhNormOK D) :
    beBiadd D ∧ phNorm D ∧ beConj D ∧ beDiag D ∧ jetsPh D ∧ PhGram D ∧ PhUnitary D ∧ PhIsotropic D ∧ PhDual D ∧ SDiff D ∧
      endIntW D ∧ splitZero D := by
  have ha := addInt_holds D
  have hB := beBiadd_of_cube D hc
  have hn := phNorm_of' phNormOfUnits_holds phNormClosed_holds D hOK he ha hB
  have hb := beConj_of' beConjOfNorm_holds D he ha hn hB
  have hG := phGram_of phGramG_holds D he ha hn hb hB
  exact ⟨hB, hn, hb, beDiag_of' beDiagG_holds D he ha hn hb hB, jetsPh_of' jetsHigh_holds jetsOne_holds jetsTwo_holds D hc hn hb, hG,
    phUnitary_of gramUnitEq_holds D hG, phIsotropic_of gramIsoEq_holds D hG, phDual_of phDualOfGram_holds D hG,
    sDiff_of sDiffOfGram_holds D hG hb, stmt_endIntW_holds D he, splitZero_of' splitZeroG_holds D he ha hn hb hB⟩

theorem witt_conditions_of_cube_endInt_phW (D : D7) (hc : cube D) (he : endInt D) (hOK : PhNormOK D) (hW : phW D) :
    beW D ∧ PhDualW D ∧ SDiffW D ∧ FirstKernelRemainder D := by
  obtain ⟨hB, -, hb, -, -, -, -, -, hd, hs, heW, -⟩ := firstGeometricCondition_of_properties D hc he hOK
  have ha := addInt_holds D
  have h1 := stmt_beW_holds D hW readW_holds ha heW hB hb
  have h2 := stmt_PhDualW_holds D hW readW_holds ha heW hd
  have h3 := stmt_SDiffW_holds D hW readW_holds ha heW hs
  exact ⟨h1, h2, h3, firstKernelRemainder_of_levelRestriction_of_linPtW level_restriction_of_group_law_holds linPtW_holds D hW ha heW h3 h2⟩

end Formalism.MainNotions.Ext
