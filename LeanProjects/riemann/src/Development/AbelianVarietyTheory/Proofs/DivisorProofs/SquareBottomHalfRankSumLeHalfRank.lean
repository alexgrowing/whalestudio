import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
open GlobalTheory.SqTop

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest

namespace GlobalTheory.SqTop

theorem exists_coord_ne_of_norm_ne {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ}
    (P : GlobalTheory.NormSum.Pair D cc δ t0 Q) (h : P.norm ≠ 0) : ∃ g T, P.coord g T ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply h
  simp [GlobalTheory.NormSum.Pair.norm, GlobalTheory.NormSum.Pair.sq, hc]

theorem squareBottomHalfRankSum_le_halfRank (D : D7) (i j : ℕ) : h0 D i j ≤ halfRank D i j := by
  simp only [h0, botBig, botSmall, halfRank]
  omega

end GlobalTheory.SqTop

end
