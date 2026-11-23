import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HBdNonneg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount

namespace GlobalTheory.DefRank

theorem rank_le_bigN : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (X : Node),
    DefNode D.R.m X → (G.V X).rank ≤ bigN D := by
  intro D T L sc G X hX
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hm := D.R.two_le_m
  rcases X with ⟨_ | i, j⟩ | i | j
  · obtain rfl := hX.2
    have e : G.V (.grid 0 D.R.m) = D.sp.X' := congrArg LSp.sp (colY_m L)
    rw [e, D.sp.X'_rank]
    show D.R.r + D.R.m * D.R.t ≤ D.R.k + D.R.m * (D.R.t + sLen D + 1)
    have e : D.R.m * (D.R.t + sLen D + 1) = D.R.m * D.R.t + D.R.m * sLen D + D.R.m := by ring
    omega
  · obtain ⟨hi, rfl⟩ := hX
    rw [(G.isV (X := .grid (i + 1) D.R.m) ⟨hi, le_rfl⟩ (by simp)).rank]
    show D.R.r + D.R.m * D.R.t + (i + 1) * sLen D ≤ D.R.k + D.R.m * (D.R.t + sLen D + 1)
    have := Nat.mul_le_mul_right (sLen D) hi
    have e : D.R.m * (D.R.t + sLen D + 1) = D.R.m * D.R.t + D.R.m * sLen D + D.R.m := by ring
    omega
  · exact hX.elim
  · rw [(G.isV (X := .top j) hX (by simp)).rank]
    show nRk D + D.R.m * (sLen D - 1) + j * (D.R.t + 1) ≤ D.R.k + D.R.m * (D.R.t + sLen D + 1)
    have h1 := Nat.mul_le_mul_right (D.R.t + 1) (show j ≤ D.R.m from hX)
    have hs : sLen D - 1 + 1 = sLen D := by unfold sLen; omega
    have hn : nRk D = D.R.r + 1 := rfl
    have e : D.R.m * (D.R.t + sLen D + 1) = D.R.m * (sLen D - 1) + D.R.m * (D.R.t + 1) + D.R.m := by
      conv_lhs => rw [← hs]
      ring
    have h2 : j * (D.R.t + 1) ≤ D.R.m * (D.R.t + 1) := h1
    omega

end GlobalTheory.DefRank
