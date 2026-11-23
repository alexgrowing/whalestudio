import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitConstantsParameterConditionsLarge
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowNodeGapBlockLength
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowElevenLeSplitBound
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowAndImp
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BandWidthLeInvSqOfRankBounds

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_numAt :
    SzRow (fun C D L => HostArith D.host → Nonempty (NumAt C L) ∧ ChTT_at L ∧ ChCode_at L 3 C.P.CF) := by
  refine szRow_and_imp.2 _ _ (szRow_and_imp.1 _ _ (szRow_and_imp.1 _ _ explicitConstants_parameterConditions_large szRow_blockLengthParams)
    (szRow_and_imp.1 _ _ szRow_sizesAt szRow_band_lambda_primes)) ?_
  rintro C cD ch D L hC hV ⟨⟨h5, hT⟩, hS, hrho, hLa, hg, hp, hp', hTT, hCode⟩ hA
  obtain ⟨P, hPK, hPW⟩ := h5 hA
  obtain ⟨T, hTK, hTe⟩ := hT P hPW
  have hCt : C.Ct = 401 := hC.1.2.2.2.2.2.2.2.2.2
  obtain ⟨hn, hm, hk, -⟩ := hV.ranks
  obtain ⟨-, -, -, -, -, hLw, hcc, -⟩ := hV.host
  refine ⟨⟨{ params := P
             params_K := hPK
             CnW_eq := hPW
             parT := T
             parT_K := hTK
             eP_eq := hTe
             sizes := hS
             rho_le := hrho
             CGam_eq := hV.CGam_eq
             Cc_eq := hV.Cc_eq
             Ct_eq := hV.Ct_eq
             secondConstant_eq := hV.secondConstant_eq
             LaG_ge := hLa
             bT_le := hV.bT_le
             ccK_top := hcc
             g_le := hg
             pde_lt := ⟨hp, hp'⟩
             logFiveDepth_eq := hV.logFiveDepth_eq
             Lw_eq := ?_
             cloud1 := fun τ τ' => ?_
             win := ⟨hn, hm, hk⟩ }⟩, hTT, hCode⟩
  · rw [hLw, hCt]; unfold Lwv; norm_num
  · funext i
    rw [hV.hc.1 τ i, hV.hc.1 τ' i]

end GlobalTheory.EX
