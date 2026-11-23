import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowAndImp
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowRankSizesStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowSizeKRelStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowCondQdPdeStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowLaRhoBotStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitChoiceSizeEtaStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitChoiceSizeNodesStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitChoiceSizeLstarStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowSizeDelStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowSizeWSizeBmSizeXppStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowSizeGSizeWordsStatement

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

private theorem szRow_eleven_le_splitBound : SzRow (fun _ D _ => 11 ≤ D.host.splitBound) := by
  intro eps heps _ C _
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨(11 : ℝ) ^ (eps / C.P.Cpde / 5)⁻¹, ?_⟩⟩⟩
  intro D L hε hx hV
  have hH := hV.host
  have hC : (0 : ℝ) < C.P.Cpde := lt_of_lt_of_le one_pos hH.one_le
  have ha : 0 < eps / C.P.Cpde / 5 := by positivity
  have h1 : (11 : ℝ) ≤ L.sc.x ^ (eps / C.P.Cpde / 5) := by
    have h2 := Real.rpow_le_rpow (by positivity) hx ha.le
    rwa [Real.rpow_inv_rpow (by norm_num) ha.ne'] at h2
  have h3 : L.sc.x ^ (eps / C.P.Cpde / 5) ≤ L.sc.x ^ (L.sc.ez / 5) := by
    refine Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le ?_
    have := hH.eps_div_le_ez
    rw [hε] at this
    linarith
  have h4 : 11 ≤ ⌊L.sc.x ^ (L.sc.ez / 5)⌋₊ := Nat.le_floor (by exact_mod_cast h1.trans h3)
  exact h4.trans hH.split_tie

theorem szRow_sizesAt : SzRow (fun _ _ L => SizesAt L) := by
  have h := ((((((((((GlobalTheory.T.sizes_sizeN_sizeM_sizeK_sizeT_sizeTT_sizeDe2_sizeLw.and GlobalTheory.T.sizes_sizeKRel).and GlobalTheory.T.sizes_sizeCond_sizeQD_sizePde).and GlobalTheory.T.sizes_sizeLa_sizeRho_sizeBot).and GlobalTheory.T.explicitChoice_sizeEta).and
    GlobalTheory.T.explicitChoice_sizeNodes).and GlobalTheory.T.explicitChoice_sizeLstar).and GlobalTheory.T.sizes_sizeDel).and GlobalTheory.T.sizes_sizeW_sizeBm_sizeXpp).and GlobalTheory.T.sizes_sizeG_sizeWords).and
    szRow_eleven_le_splitBound)
  refine h.imp ?_
  rintro C cD ch D L - - ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hN, hM, hK, hT, hTT, hDe, hLw⟩, hKR⟩, hCo, hQD, hP⟩, hLa, hRho, hBot⟩, hEta⟩,
    hNo⟩, hLs⟩, hDel⟩, hW, hBm, hX⟩, hG, hWo⟩, h11⟩
  exact ⟨hN, hM, hK, hKR, hT, hCo, hQD, hTT, hLa, hRho, hBot, hDe, hLw, hEta, hNo, hLs, hDel, hW, hBm, hX, hG,
    hP, hWo, h11⟩

end GlobalTheory.EX
